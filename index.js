/**
 * Knight Bot - A WhatsApp Bot
 * Copyright (c) 2026 Professor
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the MIT License.
 */
require('./settings')
const { Boom } = require('@hapi/boom')
const fs = require('fs')
const chalk = require('chalk')
const FileType = require('file-type')
const path = require('path')
const axios = require('axios')
const { exec, spawn } = require('child_process')
const { handleMessages, handleGroupParticipantUpdate, handleStatus } = require('./main');
const PhoneNumber = require('awesome-phonenumber')
const { imageToWebp, videoToWebp, writeExifImg, writeExifVid } = require('./lib/exif')
const { smsg, isUrl, generateMessageTag, getBuffer, getSizeMedia, fetch, await, sleep, reSize } = require('./lib/myfunc')
const {
    default: makeWASocket,
    useMultiFileAuthState,
    DisconnectReason,
    fetchLatestBaileysVersion,
    generateForwardMessageContent,
    prepareWAMessageMedia,
    generateWAMessageFromContent,
    generateMessageID,
    downloadContentFromMessage,
    jidDecode,
    proto,
    jidNormalizedUser,
    makeCacheableSignalKeyStore,
    delay
} = require("@whiskeysockets/baileys")
const NodeCache = require("node-cache")
const pino = require("pino")
const readline = require("readline")
const { parsePhoneNumber } = require("libphonenumber-js")
const { PHONENUMBER_MCC } = require('@whiskeysockets/baileys/lib/Utils/generics')
const { rmSync, existsSync } = require('fs')
const { join } = require('path')
const { randomBytes } = require('crypto')
const crypto = require('crypto')
const vm = require('vm') // فك الـ packed JS بتاع MixDrop (v117)

// ── وحدة مشغّل m3u المستقلة (أوامر .playm3u / .stopplaym3u فقط) ──
const m3uPlayer = require('./lib/m3uplayer')

// ============================================================
// إعدادات Xtream Codes IPTV
// ============================================================
// ── الحد الأقصى المسموح به لحجم أي ملف يتم تحميله أو تسجيله (لتفادي مشاكل الذاكرة/القرص) ──
const MAX_DOWNLOAD_MB = 200;
const MAX_DOWNLOAD_BYTES = MAX_DOWNLOAD_MB * 1024 * 1024;

// ── إعدادات التسجيل المُجزّأ المتواصل (اتصال واحد بالبث، بدون أي انقطاع بين الأجزاء) ──
const RECORD_TARGET_MB = 100; // الحجم المستهدف لكل جزء
const RECORD_DEFAULT_SEGMENT_MIN = 6; // احتياطي إذا فشل فحص معدل البت
const RECORD_SEGMENT_SAFETY_BYTES = 180 * 1024 * 1024; // حد أمان 180 ميجا للجزء الواحد (أقل من مساحة القرص المتاحة)

// فحص معدل بت البث الفعلي عبر ffprobe لحساب مدة جزء تعطي ~100 ميجا بدقة أعلى
// headersStr اختياري (CRLF-separated) لبثات تتطلب Referer/Origin مثل مصادر .livefootball
function probeStreamBitrate(streamUrl, headersStr = null) {
    return new Promise((resolve) => {
        let settled = false;
        const finish = (val) => { if (!settled) { settled = true; resolve(val); } };

        const args = [
            '-v', 'quiet',
            '-print_format', 'json',
            '-show_format',
            '-analyzeduration', '4000000',
            '-probesize', '4000000',
            ...(headersStr ? ['-headers', headersStr] : []),
            streamUrl
        ];
        const proc = spawn('ffprobe', args);
        let out = '';
        proc.stdout.on('data', (d) => { out += d.toString(); });
        proc.on('close', () => {
            try {
                const data = JSON.parse(out);
                const bitrate = parseInt(data?.format?.bit_rate);
                if (bitrate && bitrate > 0) return finish(bitrate);
            } catch (_) {}
            finish(null);
        });
        proc.on('error', () => finish(null));

        // مهلة أمان: لا تنتظر الفحص أكثر من 12 ثانية
        setTimeout(() => {
            try { proc.kill(); } catch (_) {}
            finish(null);
        }, 12000);
    });
}

// حساب مدة الجزء بالثواني بناءً على معدل البت المُقاس، بحد أدنى دقيقتين وحد أقصى 20 دقيقة
function computeSegmentTimeSec(bitrateBps) {
    if (!bitrateBps || bitrateBps <= 0) return RECORD_DEFAULT_SEGMENT_MIN * 60;
    const targetBits = RECORD_TARGET_MB * 1024 * 1024 * 8;
    const seconds = Math.floor(targetBits / bitrateBps);
    return Math.max(120, Math.min(20 * 60, seconds));
}

// تسجيل متواصل: عملية ffmpeg واحدة فقط تقرأ البث بلا انقطاع، وتُقسّم المخرجات
// داخلياً إلى ملفات متتالية عبر segment muxer. يستدعي onSegmentReady لكل ملف
// فور اكتماله (بينما التسجيل مستمر)، ثم يرسل آخر جزء بعد توقف العملية.
// إذا تجاوز الجزء الحالي (قيد الكتابة) حد الأمان، يتم إيقاف كامل العملية فوراً
// لتفادي امتلاء القرص، ويُعاد abortedBySize=true.
async function recordContinuousSegmented(streamUrl, segDir, prefix, totalDurationSec, segmentTimeSec, onSegmentReady, control) {
    const pattern = path.join(segDir, `${prefix}_%03d.mp4`);
    const args = [
        '-y',
        // هيدرات اختيارية من control.streamHeaders (لبثات .livefootball التي تتطلب Referer/Origin)
        ...(control && control.streamHeaders ? ['-headers', control.streamHeaders] : []),
        '-i', streamUrl,
        '-t', String(totalDurationSec),
        '-c', 'copy',
        '-f', 'segment',
        '-segment_time', String(segmentTimeSec),
        '-reset_timestamps', '1',
        pattern
    ];

    const proc = spawn('ffmpeg', args);
    control.proc = proc; // كشف مرجع العملية لأمر .stoprecord الخارجي
    let stderr = '';
    proc.stderr.on('data', (d) => { stderr += d.toString(); });

    let finished = false;
    let abortedBySize = false;
    proc.on('close', () => { finished = true; });
    proc.on('error', () => { finished = true; });

    const getSegFiles = () => {
        try {
            return fs.readdirSync(segDir)
                .filter(f => f.startsWith(prefix + '_') && f.endsWith('.mp4'))
                .map(f => ({ file: f, idx: parseInt(f.match(/_(\d+)\.mp4$/)?.[1] || '-1') }))
                .filter(x => x.idx >= 0)
                .sort((a, b) => a.idx - b.idx);
        } catch (_) { return []; }
    };

    let lastSentIndex = -1;

    // أثناء التسجيل: أي ملف غير الأخير (الحالي قيد الكتابة) يكون قد اكتمل فعلاً
    while (!finished) {
        // إلغاء فوري مطلوب من المستخدم عبر .stoprecord
        if (control.cancelled) {
            proc.kill('SIGINT');
            break;
        }

        const files = getSegFiles();

        for (let i = 0; i < files.length - 1; i++) {
            if (files[i].idx > lastSentIndex && !control.cancelled) {
                lastSentIndex = files[i].idx;
                await onSegmentReady(path.join(segDir, files[i].file));
            }
        }

        // فحص أمان: هل تجاوز الجزء الحالي (قيد الكتابة) الحد الآمن؟
        if (!abortedBySize && files.length > 0) {
            const activeFile = files[files.length - 1];
            try {
                const activeSize = fs.statSync(path.join(segDir, activeFile.file)).size;
                if (activeSize >= RECORD_SEGMENT_SAFETY_BYTES) {
                    abortedBySize = true;
                    proc.kill('SIGINT'); // إيقاف آمن يسمح لـ ffmpeg بإغلاق الملف الحالي بشكل صحيح
                }
            } catch (_) {}
        }

        await new Promise(r => setTimeout(r, 3000));
    }

    // انتظار خروج العملية فعلياً إذا تم كسر الحلقة بسبب الإلغاء المباشر قبل أن يضبط finished
    if (!finished) {
        await new Promise((resolve) => {
            if (proc.exitCode !== null || proc.killed) return resolve();
            proc.once('close', resolve);
            proc.once('error', resolve);
        });
    }

    // بعد انتهاء العملية: إرسال أي أجزاء متبقية (بما فيها الجزء الأخير المُنهى الآن)
    // إلا إذا كان الإلغاء بطلب المستخدم — عندها نرسل الجزء الأخير فقط إن كان قد اكتمل فعلياً
    const finalFiles = getSegFiles();
    for (const item of finalFiles) {
        if (item.idx > lastSentIndex) {
            lastSentIndex = item.idx;
            if (!control.cancelled || item.idx === finalFiles[finalFiles.length - 1].idx) {
                await onSegmentReady(path.join(segDir, item.file));
            }
        }
    }

    return { stderr, segmentCount: lastSentIndex + 1, abortedBySize, cancelled: control.cancelled };
}

// ── تتبع التسجيلات النشطة لكل محادثة (لدعم أمر .stoprecord) ──
const activeRecordings = new Map(); // chatId -> { proc, cancelled }

// ── تتبع التسجيلات النشطة الخاصة بقائمة IPTV الثابتة فقط (منفصل عن UGEEN) ──
const activeIptvRecordings = new Map(); // chatId -> { proc, cancelled }

// ── تتبع تسجيلات .livefootball النشطة (منفصل عن .record/.recordiptv) ──
const activeLiveFootballRecordings = new Map(); // chatId -> { proc, cancelled, streamHeaders }
const activeLiveChannelRecordings = new Map(); // chatId -> { proc, cancelled, streamHeaders } — تسجيلات .livechannel

// ── تتبع تسجيلات .tflix النشطة وخطواتها التفاعلية ──
const activeTflixRecordings = new Map(); // chatId -> { stopped }
const tflixWizardCache = new Map(); // sentMsgId -> job (مراحل: channel/quality/duration/segment)
const tflixLists = new Map(); // chatId -> { events, at }

// ── دومين tflix قابل للتبديل بأمر .settflix (يُحفظ في data/ فيبقى بعد إعادة التشغيل) ──
const TFLIX_CONFIG_PATH = path.join(process.cwd(), 'data', 'tflix_config.json');
const TFLIX_CONFIG = { domain: 'tflix.su' };
try {
    if (fs.existsSync(TFLIX_CONFIG_PATH)) {
        const savedTflix = JSON.parse(fs.readFileSync(TFLIX_CONFIG_PATH, 'utf8'));
        if (savedTflix && savedTflix.domain) TFLIX_CONFIG.domain = String(savedTflix.domain).trim();
    }
} catch (_) {}
function tflixNormalizeDomain(input) {
    let s = String(input || '').trim().toLowerCase().replace(/^['"]+|['"]+$/g, '');
    s = s.replace(/^https?:\/\//, '').replace(/\/.*$/, '').replace(/^www\./, '');
    return /^[a-z0-9-]+(\.[a-z0-9-]+)+$/.test(s) ? s : null;
}
function tflixSaveDomain(newDomain) {
    TFLIX_CONFIG.domain = newDomain;
    try {
        const dataDir = path.dirname(TFLIX_CONFIG_PATH);
        if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
        fs.writeFileSync(TFLIX_CONFIG_PATH, JSON.stringify({ domain: newDomain }, null, 2));
    } catch (_) {}
}
// معالج .tflix -domain <جديد> / .settflix — عرض الدومين الحالي أو تبديله وحفظه دائماً
async function tflixDomainCommand(XeonBotInc, chatId, mek, rawValue) {
    if (!rawValue) {
        await XeonBotInc.sendMessage(chatId, {
            text: `🌐 *دومين tflix الحالي:* ${TFLIX_CONFIG.domain}\n\n💡 لتبديله إن تغيّر عنوان الموقع:\n\`.tflix -domain <الدومين الجديد>\`\nمثال: \`.tflix -domain tflix.su\``
        }, { quoted: mek });
        return;
    }
    const nd = tflixNormalizeDomain(rawValue);
    if (!nd) {
        await XeonBotInc.sendMessage(chatId, {
            text: `❌ هذا ليس دوميناً صالحاً: \`${rawValue}\`\nاكتبه بهذا الشكل: \`example.com\` (بلا https وبلا مسارات).`
        }, { quoted: mek });
        return;
    }
    const old = TFLIX_CONFIG.domain;
    tflixSaveDomain(nd);
    await XeonBotInc.sendMessage(chatId, {
        text: `✅ *تم تبديل دومين tflix:*\n${old} ← ${nd}\n\nيُطبَّق فوراً على كل أوامر .tflix ويبقى محفوظاً بعد إعادة تشغيل البوت.`
    }, { quoted: mek });
}

const UGEEN_CONFIG = {
    host: "https://ugeen.live",
    user: "Ugeen_VIPT8j6wm",
    pass: "LCCyLS"
};

// مسار حفظ إعدادات UGEEN بشكل دائم (يبقى فعّالاً حتى بعد إعادة تشغيل البوت)
const UGEEN_CONFIG_PATH = path.join(process.cwd(), 'data', 'ugeen_config.json');

// تحميل إعدادات محفوظة سابقاً (إن وُجدت) لتجاوز القيم الافتراضية أعلاه
try {
    if (fs.existsSync(UGEEN_CONFIG_PATH)) {
        const saved = JSON.parse(fs.readFileSync(UGEEN_CONFIG_PATH, 'utf8'));
        if (saved.host && saved.user && saved.pass) {
            UGEEN_CONFIG.host = saved.host;
            UGEEN_CONFIG.user = saved.user;
            UGEEN_CONFIG.pass = saved.pass;
            console.log('✅ تم تحميل إعدادات UGEEN المحفوظة من', UGEEN_CONFIG_PATH);
        }
    }
} catch (e) {
    console.log('⚠️ فشل تحميل إعدادات UGEEN المحفوظة:', e.message);
}

// ── تخزين مؤقت لقائمة قنوات UGEEN (M3U) لتفادي طلب القائمة الكاملة في كل مرة ──
let ugeenChannelsCache = [];
let ugeenChannelsCacheTime = 0;
const UGEEN_CACHE_TTL = 10 * 60 * 1000; // 10 دقائق

// تحليل نص M3U إلى مصفوفة قنوات {id, name, url}
function parseM3U(m3uText) {
    const channels = [];
    const lines = String(m3uText).split(/\r?\n/);
    let pendingName = null;

    for (const rawLine of lines) {
        const line = rawLine.trim();
        if (!line) continue;

        if (line.startsWith('#EXTINF')) {
            const nameMatch = line.match(/,(.*)$/);
            pendingName = nameMatch ? nameMatch[1].trim() : 'غير معروف';
        } else if (/^https?:\/\//i.test(line) && pendingName !== null) {
            const url = line;
            // استخراج ID من الرابط (عادة رقم قبل الامتداد أو في آخر جزء من المسار)
            const idMatch = url.match(/\/(\d+)(?:\.[a-zA-Z0-9]+)?(?:\?.*)?$/);
            const id = idMatch ? idMatch[1] : String(channels.length + 1);
            channels.push({ id, name: pendingName, url });
            pendingName = null;
        }
    }
    return channels;
}

// جلب قائمة القنوات مع استخدام الكاش إن كان حديثاً
async function fetchUgeenChannels(forceRefresh = false) {
    const now = Date.now();
    if (!forceRefresh && ugeenChannelsCache.length > 0 && (now - ugeenChannelsCacheTime) < UGEEN_CACHE_TTL) {
        return ugeenChannelsCache;
    }

    const res = await axios.get(
        `${UGEEN_CONFIG.host}/get.php?username=${UGEEN_CONFIG.user}&password=${UGEEN_CONFIG.pass}&type=m3u&output=ts`,
        { timeout: 30000 }
    );

    const channels = parseM3U(res.data);
    if (channels.length === 0) throw new Error('تعذر تحليل قائمة القنوات (M3U فارغة أو بصيغة غير متوقعة).');

    ugeenChannelsCache = channels;
    ugeenChannelsCacheTime = now;
    return channels;
}

// ============================================================
// قائمة IPTV ثابتة (iptv-org) — منفصلة تمامًا عن UGEEN
// ============================================================
const FIXED_IPTV_URL = 'https://iptv-org.github.io/iptv/index.m3u';
let fixedIptvCache = [];
let fixedIptvCacheTime = 0;
const FIXED_IPTV_CACHE_TTL = 10 * 60 * 1000; // 10 دقائق

async function fetchFixedIptvChannels(forceRefresh = false) {
    const now = Date.now();
    if (!forceRefresh && fixedIptvCache.length > 0 && (now - fixedIptvCacheTime) < FIXED_IPTV_CACHE_TTL) {
        return fixedIptvCache;
    }

    const res = await axios.get(FIXED_IPTV_URL, { timeout: 30000 });
    const channels = parseM3U(res.data);
    if (channels.length === 0) throw new Error('تعذر تحليل قائمة القنوات الثابتة.');

    fixedIptvCache = channels;
    fixedIptvCacheTime = now;
    return channels;
}

// ============================================================
// مصدر M3U مستقل قابل للاستبدال — أمر .setm3u / .m3usource
// مستقل تماماً عن UGEEN_CONFIG وعن قائمة iptv-org الثابتة، ومكتوب
// بالكامل هنا داخل index.js بدون أي اعتماد على ملفات خارجية.
// ============================================================
const M3U_SOURCE_CONFIG_PATH = path.join(process.cwd(), 'data', 'm3u_source_config.json');
const M3U_SOURCE_CONFIG = { url: null };

try {
    if (fs.existsSync(M3U_SOURCE_CONFIG_PATH)) {
        const savedSrc = JSON.parse(fs.readFileSync(M3U_SOURCE_CONFIG_PATH, 'utf8'));
        if (savedSrc.url) {
            M3U_SOURCE_CONFIG.url = savedSrc.url;
            console.log('✅ تم تحميل مصدر M3U المستقل المحفوظ من', M3U_SOURCE_CONFIG_PATH);
        }
    }
} catch (e) {
    console.log('⚠️ فشل تحميل مصدر M3U المستقل المحفوظ:', e.message);
}

let m3uSourceChannelsCache = [];
let m3uSourceChannelsCacheTime = 0;
const M3U_SOURCE_CACHE_TTL = 10 * 60 * 1000; // 10 دقائق

// جلب قنوات مصدر M3U المستقل الحالي (مع كاش)
async function fetchM3USourceChannels(forceRefresh = false) {
    if (!M3U_SOURCE_CONFIG.url) {
        throw new Error('لم يتم ضبط أي مصدر M3U بعد. استخدم أمر .setm3u [رابط] أولاً.');
    }

    const now = Date.now();
    if (!forceRefresh && m3uSourceChannelsCache.length > 0 && (now - m3uSourceChannelsCacheTime) < M3U_SOURCE_CACHE_TTL) {
        return m3uSourceChannelsCache;
    }

    const res = await axios.get(M3U_SOURCE_CONFIG.url, { timeout: 30000 });
    const channels = parseM3U(res.data);
    if (channels.length === 0) throw new Error('تعذر تحليل قائمة القنوات (M3U فارغة أو بصيغة غير متوقعة).');

    m3uSourceChannelsCache = channels;
    m3uSourceChannelsCacheTime = now;
    return channels;
}

// استبدال/تحديث رابط مصدر M3U — يتحقق أولاً قبل الحفظ الدائم لتفادي حفظ رابط لا يعمل
async function replaceM3USource(newUrl) {
    if (!newUrl || !/^https?:\/\//i.test(newUrl.trim())) {
        throw new Error('الرابط غير صحيح. يجب أن يبدأ بـ http:// أو https://');
    }

    const oldUrl = M3U_SOURCE_CONFIG.url;
    const oldCache = m3uSourceChannelsCache;
    const oldCacheTime = m3uSourceChannelsCacheTime;

    // تجربة الرابط الجديد مؤقتاً قبل الاعتماد النهائي
    M3U_SOURCE_CONFIG.url = newUrl.trim();
    m3uSourceChannelsCache = [];
    m3uSourceChannelsCacheTime = 0;

    try {
        const channels = await fetchM3USourceChannels(true);

        // نجح التحقق → حفظ دائم على القرص
        const dataDir = path.dirname(M3U_SOURCE_CONFIG_PATH);
        if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
        fs.writeFileSync(M3U_SOURCE_CONFIG_PATH, JSON.stringify({ url: M3U_SOURCE_CONFIG.url }, null, 2));

        return { url: M3U_SOURCE_CONFIG.url, channelCount: channels.length };
    } catch (err) {
        // فشل التحقق → استرجاع الإعدادات القديمة لتفادي كسر المصدر السابق
        M3U_SOURCE_CONFIG.url = oldUrl;
        m3uSourceChannelsCache = oldCache;
        m3uSourceChannelsCacheTime = oldCacheTime;
        throw err;
    }
}

// ============================================================
// إعدادات "المُنزّل عن بُعد" (Remote Downloader عبر GitHub Actions)
// يعتمد على مستودع خارجي (fork من sadekch1/file-splitter) يحتوي على
// split_upload.py + workflow بإسم REMOTE_DL_CONFIG.workflowFile.
// البوت يشغّل الـ workflow، ينتظر اكتماله، ثم يسحب روابط الأجزاء من
// الـ Release الناتج ويعيد تحميلها/إرسالها في المحادثة.
// ============================================================
const REMOTE_DL_CONFIG_PATH = path.join(process.cwd(), 'data', 'remotedl_config.json');
const REMOTE_DL_CONFIG = {
    owner: '',   // مثال: 'myuser'
    repo: '',    // مثال: 'file-splitter'
    workflowFile: 'remote-download.yml',
    token: process.env.REMOTE_DL_GITHUB_TOKEN || ''
};

try {
    if (fs.existsSync(REMOTE_DL_CONFIG_PATH)) {
        const saved = JSON.parse(fs.readFileSync(REMOTE_DL_CONFIG_PATH, 'utf8'));
        if (saved.owner) REMOTE_DL_CONFIG.owner = saved.owner;
        if (saved.repo) REMOTE_DL_CONFIG.repo = saved.repo;
        if (saved.workflowFile) REMOTE_DL_CONFIG.workflowFile = saved.workflowFile;
        if (saved.token) REMOTE_DL_CONFIG.token = saved.token;
        console.log('✅ تم تحميل إعدادات Remote Downloader المحفوظة من', REMOTE_DL_CONFIG_PATH);
    }
} catch (e) {
    console.log('⚠️ فشل تحميل إعدادات Remote Downloader:', e.message);
}

function saveRemoteDlConfig() {
    const dataDir = path.dirname(REMOTE_DL_CONFIG_PATH);
    if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
    fs.writeFileSync(REMOTE_DL_CONFIG_PATH, JSON.stringify(REMOTE_DL_CONFIG, null, 2));
}

function remoteDlHeaders() {
    return {
        'Authorization': `Bearer ${REMOTE_DL_CONFIG.token}`,
        'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
        'User-Agent': 'Sadek-RemoteDL'
    };
}

// ── تتبع التحميلات النشطة عن بُعد لكل محادثة (لدعم أمر .stopremotedl) ──
const activeRemoteDl = new Map(); // chatId -> { cancelled, runId }

// إلغاء تشغيل الـ workflow نفسه على GitHub (لا يفيد بعد اكتماله، فقط أثناء التشغيل)
async function cancelRemoteRun(runId) {
    try {
        await axios.post(
            `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/runs/${runId}/cancel`,
            {}, { headers: remoteDlHeaders(), timeout: 15000 }
        );
    } catch (_) {}
}

// تشغيل الـ workflow عن بُعد (workflow_dispatch) — يعيد وقت الإطلاق لاستخدامه لاحقاً
async function triggerRemoteDownload(fileUrl, chunkSizeMb = 100) {
    if (!REMOTE_DL_CONFIG.token || !REMOTE_DL_CONFIG.owner || !REMOTE_DL_CONFIG.repo) {
        throw new Error('لم يتم ضبط إعدادات Remote Downloader بعد. استخدم أمر .setremotedl أولاً.');
    }
    const dispatchTime = new Date();
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/workflows/${REMOTE_DL_CONFIG.workflowFile}/dispatches`;

    await axios.post(url, {
        ref: 'main',
        inputs: { file_url: fileUrl, chunk_size_mb: String(chunkSizeMb) }
    }, { headers: remoteDlHeaders(), timeout: 15000 });

    return dispatchTime;
}

// البحث عن الـ run الذي بدأ بعد وقت الإطلاق (workflow_dispatch لا يُرجع run id مباشرة)
async function findTriggeredRun(dispatchTime, maxWaitMs = 30000) {
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/workflows/${REMOTE_DL_CONFIG.workflowFile}/runs?event=workflow_dispatch&per_page=5`;
    const deadline = Date.now() + maxWaitMs;

    while (Date.now() < deadline) {
        const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
        const runs = res.data?.workflow_runs || [];
        const match = runs.find(r => new Date(r.created_at).getTime() >= dispatchTime.getTime() - 5000);
        if (match) return match;
        await new Promise(r => setTimeout(r, 3000));
    }
    throw new Error('تعذر العثور على الـ workflow run بعد إطلاقه (تأكد من اسم ملف الـ workflow والفرع main).');
}

// انتظار اكتمال الـ run، مع استدعاء onTick دورياً لإرسال تحديثات
// control (اختياري): إذا control.cancelled = true أثناء الانتظار، يتم إلغاء الـ run فعلياً على GitHub
// ويُرمى خطأ خاص (isCancelled = true) يُميَّز عن الفشل العادي في المستدعي
async function waitForRunCompletion(runId, maxWaitMs, onTick, control) {
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/runs/${runId}`;
    const deadline = Date.now() + maxWaitMs;
    let lastTick = Date.now();

    while (Date.now() < deadline) {
        if (control?.cancelled) {
            await cancelRemoteRun(runId);
            const err = new Error('تم إلغاء التحميل عن بُعد بطلبك.');
            err.isCancelled = true;
            throw err;
        }

        const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
        const run = res.data;
        if (run.status === 'completed') return run;

        if (onTick && Date.now() - lastTick > 120000) {
            lastTick = Date.now();
            await onTick(run);
        }
        await new Promise(r => setTimeout(r, 8000));
    }
    throw new Error('انتهت مهلة الانتظار (timeout) قبل اكتمال التحميل عن بُعد.');
}

// نمط اسم الـ tag الذي يولّده split_upload.py فعلياً: `split-` + 10 خانات hex من بصمة الرابط (sha1)
// (نُبقي النمط القديم `split-upload-` أيضاً للتوافق مع أي إصدار سابق من السكربت كان يستعمله)
function isSplitReleaseTag(tag) {
    return typeof tag === 'string' && (/^split-[0-9a-f]{10}$/.test(tag) || tag.startsWith('split-upload-'));
}

// جلب الإصدار (Release) الذي أنشأه الـ run والحصول على روابط الأجزاء من direct_links.txt
// ملاحظة: لا نعتمد على مقارنة أي توقيت (لا وقت إطلاق البوت ولا created_at) لأن اسم
// الـ tag يُولَّد داخل split_upload.py وقت تنفيذه الفعلي على GitHub، وقد يختلف عن ساعة
// سيرفر البوت. بدلاً من ذلك: قائمة releases عند GitHub تُرجَع دائماً مرتّبة من الأحدث
// للأقدم، فنأخذ أول عنصر مطابق لنمط split-* ببساطة (وهو الإصدار الذي أنشأه آخر تشغيل
// ناجح لهذا المستودع).
async function fetchRemoteDlResult() {
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/releases?per_page=10`;
    const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
    const releases = res.data || [];

    const release = releases.find(r => isSplitReleaseTag(r.tag_name));
    if (!release) throw new Error('تم تشغيل الـ workflow لكن تعذر العثور على الإصدار (Release) الناتج.');

    const linksAsset = release.assets?.find(a => a.name.startsWith('direct_links'));
    if (!linksAsset) throw new Error('لم يتم العثور على ملف الروابط (direct_links.txt) في الإصدار.');

    const linksRes = await axios.get(linksAsset.url, {
        headers: { ...remoteDlHeaders(), 'Accept': 'application/octet-stream' },
        timeout: 15000
    });

    const links = String(linksRes.data).split(/\r?\n/).map(l => l.trim()).filter(Boolean);
    if (links.length === 0) throw new Error('ملف الروابط فارغ.');

    return { release, links };
}

// حذف الإصدار والـ tag بعد إرسال الملفات (تنظيف اختياري لتفادي تراكم الإصدارات على المستودع)
async function cleanupRemoteDlRelease(release) {
    try {
        await axios.delete(
            `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/releases/${release.id}`,
            { headers: remoteDlHeaders(), timeout: 15000 }
        );
    } catch (_) {}
    try {
        await axios.delete(
            `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/git/refs/tags/${release.tag_name}`,
            { headers: remoteDlHeaders(), timeout: 15000 }
        );
    } catch (_) {}
}

// ============================================================
// مخازن مؤقتة (Cache)
// ============================================================
const animeCache = new Map();
const qualityCache = new Map();

// ── تثبيت مصدر واحد لـ .anime (عبر .setanime / .animeset) ──
let animeLockedSource = null; // null = البحث في كل المصادر
const ANIME_SOURCE_LIST = ['animeday', 'cimacloud', 'rift', 'witcher', 'shahiid', 'anime4up', 'animedar', 'kartoney', 'animerco', 'hianime', 'okru', 'arabanime', 'animezid', 'okanime', 'egyaflam'];
const ANIME_SOURCE_NAMES = {
    animeday: { source: 'cloudday', cdSource: 'AnimeDay', label: '☁️ CloudDay (AnimeDay)' },
    cimacloud: { source: 'cloudday', cdSource: 'CimaCloud', label: '☁️ CloudDay (CimaCloud)' },
    rift: { source: 'rift', cdSource: null, label: '🌐 AnimeRift' },
    animerift: { source: 'rift', cdSource: null, label: '🌐 AnimeRift' },
    witcher: { source: 'witcher', cdSource: null, label: '🧙 AnimeWitcher' },
    animewitcher: { source: 'witcher', cdSource: null, label: '🧙 AnimeWitcher' },
    shahiid: { source: 'shahiid', cdSource: null, label: '🎬 شهيد' },
    anime4up: { source: 'anime4up', cdSource: null, label: '📺 Anime4Up' },
    animedar: { source: 'animedar', cdSource: null, label: '🎞️ Animedar' },
    kartoney: { source: 'kartoney', cdSource: null, label: '🧒 Kartoney' },
    animerco: { source: 'animerco', cdSource: null, label: '🎭 Animerco' },
    hianime: { source: 'hianime', cdSource: null, label: '🌍 HiAnime EN' },
    okru: { source: 'okru', cdSource: null, label: '📺 ok.ru' },
    arabanime: { source: 'arabanime', cdSource: null, label: '🌸 ArabAnime' },
    animezid: { source: 'animezid', cdSource: null, label: '🌟 AnimeZid' },
    okanime: { source: 'okanime', cdSource: null, label: '🎬 OkAnime' },
    egyaflam: { source: 'egyaflam', cdSource: null, label: '🎞️ EgyAflam' }
};

// بحث مصدر واحد بالاسم (نفس دوال البحث — بلا تكرار كود)
async function animeSearchOne(name, query) {
    const e = ANIME_SOURCE_NAMES[name];
    if (!e) return [];
    if (e.source === 'cloudday') return await cloudDaySearch(query, e.cdSource);
    if (e.source === 'rift') return await riftSearch(query);
    if (e.source === 'witcher') return await witcherSearch(query);
    if (e.source === 'shahiid') return await shahiidSearch(query);
    if (e.source === 'anime4up') return await anime4upSearch(query);
    if (e.source === 'animedar') return await animedarSearch(query);
    if (e.source === 'kartoney') return await kartoneySearch(query);
    if (e.source === 'animerco') return await animercoSearch(query);
    if (e.source === 'hianime') return await hianimeSearch(query);
    if (e.source === 'okru') return (await okruSearchAnime(query)).map(v => ({ id: v.id, title: v.title }));
    if (e.source === 'arabanime') return await arabanimeSearch(query);
    if (e.source === 'animezid') return await animezidSearch(query);
    if (e.source === 'okanime') return await okanimeSearch(query);
    if (e.source === 'egyaflam') return await egyaflamSearch(query);
    return [];
}
const akwamCache = new Map();
const mangaCache = new Map();
const okruCache = new Map();

// Import lightweight store
const store = require('./lib/lightweight_store')
store.readFromFile()
const settings = require('./settings')
setInterval(() => store.writeToFile(), settings.storeWriteInterval || 10000)

// Memory optimization
setInterval(() => {
    if (global.gc) {
        global.gc()
        console.log('🧹 Garbage collection completed')
    }
}, 60_000)

// Memory monitoring
setInterval(() => {
    const used = process.memoryUsage().rss / 1024 / 1024
    if (used > 1500) {
        console.log('⚠️ RAM too high (>250MB), restarting bot...')
        process.exit(1)
    }
}, 30_000)

let phoneNumber = ""
let owner = JSON.parse(fs.readFileSync('./data/owner.json'))

global.botname = "KNIGHT BOT"
global.themeemoji = "•"
const pairingCode = process.argv.includes("--pairing-code")
const usePairing = pairingCode || !!process.env.GITHUB_ACTIONS
const useMobile = process.argv.includes("--mobile")

const rl = process.stdin.isTTY ? readline.createInterface({ input: process.stdin, output: process.stdout }) : null
const question = (text) => {
    if (rl) {
        return new Promise((resolve) => rl.question(text, resolve))
    } else {
        return Promise.resolve(settings.ownerNumber || phoneNumber)
    }
}

// ============================================================
// دوال مساعدة لـ akwam
// ============================================================
const AKWAM_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    'Accept-Language': 'ar,en;q=0.5',
    'Referer': 'https://akwam.ss/'
};

async function akwamFetch(url) {
    const res = await axios.get(url, {
        headers: AKWAM_HEADERS,
        timeout: 15000,
        validateStatus: s => s < 500
    });
    return res.data;
}

function extractAkwamSeries(html) {
    const results = [];
    const regex = /href="(https?:\/\/akwam\.ss\/series\/[^"#?]+)"/g;
    let m;
    while ((m = regex.exec(html)) !== null) {
        const url = m[1].split('?')[0];
        if (!results.some(r => r.url === url)) {
            const slug = url.replace(/.*\/series\//, '').replace(/\/$/, '');
            results.push({ url, name: decodeURIComponent(slug).replace(/-/g, ' ') });
        }
    }
    return results;
}

function extractAkwamEpisodes(html) {
    const results = [];
    const regex = /href="(https?:\/\/akwam\.ss\/episode\/[^"#?]+)"/g;
    let m;
    while ((m = regex.exec(html)) !== null) {
        const url = m[1].split('?')[0];
        if (!results.includes(url)) results.push(url);
    }
    return results;
}

async function extractAkwamMp4Links(epUrl) {
    const html = await akwamFetch(epUrl);
    const watchMatch = html.match(/"(https?:\/\/akwam\.ss\/watch[^"]+)"/);
    if (!watchMatch) return [];
    const watchHtml = await akwamFetch(watchMatch[1]);
    const mp4Links = [...new Set(
        (watchHtml.match(/https?:\/\/[^"'\s<>]+\.mp4[^"'\s<>]*/g) || [])
    )].filter(l => !l.includes('sample') && !l.includes('preview'));
    return mp4Links;
}

// ============================================================
// الأنمي العربي عبر ok.ru (بحث + تحميل مباشر)
// ok.ru لا يفرض حماية Cloudflare على البحث أو صفحات الفيديو، ونتائج
// بحثه مليئة بالحلقات المترجمة/المدبلجة عربياً المرفوعة من المستخدمين.
// نمط البحث: https://ok.ru/video/search/<كلمة البحث>
// ============================================================
const OKRU_UA = 'Mozilla/5.0 (Linux; Android 10) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36';
// ملاحظة: ok.ru يعرض نتائج البحث مُضمّنة في HTML فقط مع موبايل UA — نسخة الديسكتوب أصبحت React تُحمّل النتائج بـ AJAX
const OKRU_PAGE_HEADERS = {
    'User-Agent': OKRU_UA,
    'Accept-Language': 'en-US,en;q=0.9'
};

// أسماء عرض مفهومة لجودات ok.ru
const OKRU_QUALITY_LABELS = {
    ultra: '2160p (Ultra HD)',
    quad: '1440p (Quad HD)',
    full: '1080p (Full HD)',
    hd: '720p (HD)',
    sd: '480p (SD)',
    low: '360p',
    lowest: '240p',
    mobile: '144p (Mobile)'
};

// بحث فيديوهات ok.ru → [{id, title}]
// النتائج مضمّنة في HTML كـ JSON مُشفّر بـ HTML entities
async function okruSearchAnime(query) {
    const results = await okruSearchRaw(/^\s*انمي/.test(query) ? query.trim() : `انمي ${query.trim()}`);
    if (results.length) return results;
    // كرتون قديم/غير أنمي: "انمي <الاسم>" ترجع صفر — أعد البحث بدون البادئة
    if (!/^\s*انمي/.test(query)) return await okruSearchRaw(query.trim());
    return results;
}

async function okruSearchRaw(q) {
    const url = `https://ok.ru/video/search/${encodeURIComponent(q)}`;
    const res = await axios.get(url, { headers: OKRU_PAGE_HEADERS, timeout: 25000 });
    const html = res.data;

    const results = [];
    const seen = new Set();
    // كل نتيجة: "name":"العنوان" ... "href":"/video/ID"
    const re = /&quot;name&quot;:&quot;([^&]{3,160}?)&quot;[\s\S]{0,800}?&quot;href&quot;:&quot;\/video\/(\d+)&quot;/g;
    let m;
    while ((m = re.exec(html)) !== null) {
        const id = m[2];
        if (seen.has(id)) continue;
        seen.add(id);
        const title = m[1]
            .replace(/&quot;/g, '"')
            .replace(/&#39;|&apos;/g, "'")
            .replace(/&amp;/g, '&')
            .replace(/&#x2F;/g, '/')
            .replace(/\\u([\dA-Fa-f]{4})/g, (_, h) => String.fromCharCode(parseInt(h, 16)));
        results.push({ id, title });
        if (results.length >= 15) break;
    }
    return results;
}

// استخراج بيانات فيديو ok.ru من صفحة الفيديو → {title, videos:[{name,url}]}
// (نفس المنطق الذي كان داخل أمر .okru — مُستخرج لدالة قابلة لإعادة الاستخدام)
async function extractOkruVideo(pageUrl) {
    const pageRes = await axios.get(pageUrl, { headers: OKRU_PAGE_HEADERS, timeout: 15000 });
    const html = pageRes.data;

    // ok.ru يضع بيانات الفيديو داخل خاصية data-options كـ JSON مُشفّر بـ HTML entities
    const optionsMatch = html.match(/data-options="([^"]+)"/);
    if (!optionsMatch) {
        throw new Error('لم يتم العثور على بيانات الفيديو (قد يكون خاصاً أو محذوفاً أو الرابط غير صحيح).');
    }

    const decodedOptions = optionsMatch[1]
        .replace(/&quot;/g, '"')
        .replace(/&amp;/g, '&')
        .replace(/&#x2F;/g, '/');

    let options;
    try {
        options = JSON.parse(decodedOptions);
    } catch (e) {
        throw new Error('فشل تحليل بيانات الفيديو (بنية غير متوقعة، ربما تغيّر تصميم الموقع).');
    }

    const metadataRaw = options?.flashvars?.metadata;
    if (!metadataRaw) throw new Error('لم يتم العثور على معلومات الفيديو (metadata).');

    const metadata = typeof metadataRaw === 'string' ? JSON.parse(metadataRaw) : metadataRaw;
    const videos = metadata?.videos || [];
    if (videos.length === 0) throw new Error('لا توجد روابط فيديو متاحة (ربما الفيديو محمي أو يتطلب تسجيل دخول).');

    // ترتيب الجودات من الأعلى للأقل
    const qualityOrder = ['ultra', 'quad', 'full', 'hd', 'sd', 'low', 'lowest', 'mobile'];
    videos.sort((a, b) => {
        const ai = qualityOrder.indexOf(a.name);
        const bi = qualityOrder.indexOf(b.name);
        return (ai === -1 ? 999 : ai) - (bi === -1 ? 999 : bi);
    });

    return { title: metadata?.movie?.title || 'ok.ru video', videos };
}


// ===== ⚽ .football — BEGIN (v117) =====
// إعادة مباريات كرة القدم — مصادر: Footballzzz (قايمة اليوم) + footreplays (بديل)
// + SoccerFull (m3u8 مباشر للمباراة الكاملة) + ok.ru (رفوعات كاملة بجودات وحجم)
// + MixDrop (mp4 مباشر من fullmatchshows) — v117
// ملاحظة: لا وقت انطلاق في أي مصدر (التاريخ فقط) — لا يُخترع وقت أبداً.
// ولا نتائج/أهداف في أي رسالة (من غير حرق).
const footballCache = new Map();
const FOOTBALL_UA = 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36';
const FOOTBALLZZZ_BASE = 'https://footballzzz.com';
const FOOTREPLAYS_BASE = 'https://www.footreplays.com';
const SOCCERFULL_BASE = 'https://soccerfull.net';
const FULLMATCHSHOWS_BASE = 'https://fullmatchshows.com';
const FOOTBALL_LIST_SOURCE_LABEL = { footballzzz: 'Footballzzz', footreplays: 'footreplays', fullmatchshows: 'fullmatchshows' }; // وسم مصدر القايمة (v117 + v117.2)
const FOOTBALL_LIST_SOURCE_ORDER = ['footballzzz', 'footreplays', 'fullmatchshows']; // ترتيب ثابت لوسم المصادر (v117.3)
const FOOTBALL_FULL_MIN_SEC = 3600; // أقل مدة تُعتبر مباراة كاملة (60 دقيقة)
const FOOTBALL_MAX_DIRECT_BYTES = 2000 * 1048576; // حد واتساب 2GB — فوقه يروح .remotedl

function footballTodayUTC() {
    return new Date().toISOString().slice(0, 10); // YYYY-MM-DD (UTC)
}

function footballNorm(s) {
    return String(s || '').toLowerCase().replace(/&amp;/g, '&').replace(/[^a-z0-9\u0600-\u06FF]+/g, ' ').trim().replace(/\s+/g, ' ');
}

function footballWords(s) {
    return footballNorm(s).split(' ').filter(w => w.length > 1);
}

function footballHasTeam(text, team) {
    const t = footballNorm(text);
    return footballWords(team).every(w => t.includes(w));
}

function footballFmtDuration(sec) {
    const m = Math.round(sec / 60);
    return `${m} دقيقة`;
}

// ── دمج قوائم من مصادر متعددة (v117.3): الماتش يظهر مرة واحدة بسطر واحد،
// لكن الوسم يجمع كل المصادر اللي اتلاقى فيها (بترتيب ثابت) بدل حذف التكرار ──
function footballMergeMatches(lists) {
    const byKey = new Map();
    for (const list of lists) {
        for (const mt of (list || [])) {
            const key = footballNorm(mt.home) + '|' + footballNorm(mt.away) + '|' + (mt.date || '');
            if (!byKey.has(key)) {
                byKey.set(key, { ...mt, sources: mt.source ? [mt.source] : [] });
                continue;
            }
            const ex = byKey.get(key);
            if (mt.source && !ex.sources.includes(mt.source)) ex.sources.push(mt.source);
            if (mt.ready) ex.ready = true;
            if (!ex.url && mt.url) ex.url = mt.url;
        }
    }
    const out = [...byKey.values()];
    for (const mt of out) {
        mt.sources.sort((a, b) => FOOTBALL_LIST_SOURCE_ORDER.indexOf(a) - FOOTBALL_LIST_SOURCE_ORDER.indexOf(b));
        mt.source = mt.sources[0] || mt.source; // توافق: أول مصدر
    }
    return out;
}

function footballListLabel(mt) {
    const srcs = (mt.sources && mt.sources.length ? mt.sources : (mt.source ? [mt.source] : []));
    return srcs.map(s => FOOTBALL_LIST_SOURCE_LABEL[s] || s).filter(Boolean).join(', ');
}

// ── Footballzzz: قايمة مباريات اليوم من الصفحة الرئيسية (server-rendered) ──
async function footballFetchMatchesFootballzzz(onlyToday = true) {
    const res = await axios.get(FOOTBALLZZZ_BASE + '/', { headers: { 'User-Agent': FOOTBALL_UA }, timeout: 25000 });
    const html = res.data;
    const today = footballTodayUTC();
    const matches = [];
    const cardRe = /<article[^>]*class="match-card"[^>]*>([\s\S]*?)<\/article>/g;
    let m;
    while ((m = cardRe.exec(html)) !== null) {
        const card = m[1];
        const linkM = card.match(/href="(\/replay\/[^"]+)"/);
        const dateM = card.match(/datetime="(\d{4}-\d{2}-\d{2})/);
        if (!linkM || !dateM || (onlyToday && dateM[1] !== today)) continue;
        const leagueM = card.match(/comp-badge[^>]*>([^<]+)</);
        const h3M = card.match(/<h3[^>]*>([\s\S]*?)<\/h3>/);
        if (!h3M) continue;
        const h3Text = h3M[1].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
        const vsM = h3Text.match(/^(.+?)\s+vs\s+(.+)$/i);
        if (!vsM) continue;
        const stateM = card.match(/video-state[^>]*>(?:<span[^>]*>[\s\S]*?<\/span>)?\s*([^<]+)/);
        const state = stateM ? stateM[1].trim() : '';
        matches.push({
            home: vsM[1].trim(), away: vsM[2].trim(),
            league: leagueM ? leagueM[1].trim() : 'دوري',
            ready: /full match/i.test(state),
            url: FOOTBALLZZZ_BASE + linkM[1],
            source: 'footballzzz',
            date: dateM[1]
        });
    }
    return matches;
}

// ── footreplays: بديل لقايمة اليوم (روابط /بلد/دوري/فريق-ضد-فريق-DD-MM-YYYY/) ──
async function footballFetchMatchesFootreplays() {
    const res = await axios.get(FOOTREPLAYS_BASE + '/', { headers: { 'User-Agent': FOOTBALL_UA }, timeout: 25000 });
    const html = res.data;
    const today = footballTodayUTC(); // YYYY-MM-DD
    const [y, mo, d] = today.split('-');
    const todaySlug = `${d}-${mo}-${y}`; // DD-MM-YYYY كما في روابط footreplays
    const leagueNames = { 'premier-league': 'Premier League', 'la-liga': 'La Liga', 'serie-a': 'Serie A', 'bundesliga': 'Bundesliga', 'ligue-1': 'Ligue 1', 'champions-league': 'Champions League', 'europa-league': 'Europa League', 'conference-league': 'Conference League' };
    const matches = [];
    const seen = new Set();
    const aRe = /<a[^>]+href="(?:https?:\/\/www\.footreplays\.com)?(\/[^"]+?-\d{2}-\d{2}-\d{4}\/)"[^>]*>([\s\S]*?)<\/a>/g;
    let m;
    while ((m = aRe.exec(html)) !== null) {
        const href = m[1];
        if (!href.endsWith(todaySlug + '/')) continue;
        if (seen.has(href)) continue;
        seen.add(href);
        const title = m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
        const vsM = title.match(/^(.+?)\s+vs\s+(.+)$/i);
        if (!vsM) continue;
        const parts = href.split('/').filter(Boolean);
        const leagueSlug = parts.length > 1 ? parts[1] : '';
        const league = leagueNames[leagueSlug] || (leagueSlug ? leagueSlug.replace(/-/g, ' ').replace(/\b\w/g, c => c.toUpperCase()) : 'دوري');
        matches.push({ home: vsM[1].trim(), away: vsM[2].trim(), league, ready: true, url: FOOTREPLAYS_BASE + href, source: 'footreplays' });
    }
    return matches;
}

// ── قايمة اليوم (v117.3): Footballzzz + footreplays مدموجتين — كل المصادر، مش بديل ──
async function footballFetchTodayMatches() {
    const today = footballTodayUTC();
    const settled = await Promise.allSettled([
        footballFetchMatchesFootballzzz(),
        footballFetchMatchesFootreplays()
    ]);
    const lists = [];
    if (settled[0].status === 'fulfilled') lists.push(settled[0].value);
    if (settled[1].status === 'fulfilled') lists.push(settled[1].value.map(mt => ({ ...mt, date: mt.date || today }))); // footreplays بلا تاريخ — ماتشاته بتاعة النهاردة بالتعريف
    const matches = footballMergeMatches(lists);
    return { matches, source: matches.length ? (matches[0].sources[0] || 'footballzzz') : 'footballzzz' };
}

// ── بحث بالفريق (v117.2): fullmatchshows بحث ووردبريس ──
const FOOTBALL_SEARCH_DAYS = 14; // نطاق البحث بالفريق (يوم)
const FOOTBALL_SEARCH_MAX = 20; // أقصى مباريات في قايمة البحث
function footballSlugToName(slug) {
    return String(slug || '').replace(/-/g, ' ').replace(/\b\w/g, c => c.toUpperCase());
}
function footballMonthNum(mon) {
    return { jan: '01', feb: '02', mar: '03', apr: '04', may: '05', jun: '06', jul: '07', aug: '08', sep: '09', oct: '10', nov: '11', dec: '12' }[String(mon || '').toLowerCase()] || null;
}
async function footballSearchFullmatchshows(team) {
    const res = await axios.get(`${FULLMATCHSHOWS_BASE}/?s=${encodeURIComponent(team)}`, { headers: { 'User-Agent': FOOTBALL_UA }, timeout: 25000 });
    const html = res.data;
    const out = [];
    const seen = new Set();
    const linkRe = /<a[^>]+href="(https?:\/\/fullmatchshows\.com\/([a-z0-9-]+)-vs-([a-z0-9-]+)-full-match-replay-(\d{1,2})-([a-z]{3})-(\d{4})\/)"[^>]*>([\s\S]*?)<\/a>/gi;
    let m;
    while ((m = linkRe.exec(html)) !== null) {
        const href = m[1];
        if (seen.has(href)) continue;
        seen.add(href);
        const mon = footballMonthNum(m[5]);
        if (!mon) continue;
        const date = `${m[6]}-${mon}-${String(m[4]).padStart(2, '0')}`;
        const home = footballSlugToName(m[2]);
        const away = footballSlugToName(m[3]);
        const title = m[7].replace(/<[^>]+>/g, ' ');
        if (!footballHasTeam(title, team) && !footballHasTeam(home + ' ' + away, team)) continue;
        out.push({ home, away, league: 'دوري', ready: true, url: href, source: 'fullmatchshows', date });
    }
    return out;
}

// ── بحث بالفريق: Footballzzz (أيام أخيرة) + fullmatchshows (14 يوم) — الأحدث أولاً ──
async function footballSearchTeam(team) {
    const since = Date.now() - FOOTBALL_SEARCH_DAYS * 86400000;
    const lists = [];
    try {
        const zzz = await footballFetchMatchesFootballzzz(false);
        lists.push(zzz.filter(mt => footballHasTeam(mt.home + ' vs ' + mt.away, team)));
    } catch (_) {}
    try {
        const fms = await footballSearchFullmatchshows(team);
        lists.push(fms);
    } catch (_) {}
    const merged = footballMergeMatches(lists); // v117.3: تجميع المصادر بدل حذف المكرر
    const found = merged.filter(mt => {
        if (!mt.date) return false;
        const t = Date.parse(mt.date + 'T00:00:00Z');
        return !isNaN(t) && t >= since;
    });
    found.sort((a, b) => b.date.localeCompare(a.date));
    return found.slice(0, FOOTBALL_SEARCH_MAX);
}

// ── تحليل مدة قائمة m3u8 (مجموع #EXTINF) ──
function footballM3u8Duration(text) {
    let total = 0; let n = 0;
    const re = /#EXTINF:(\d+(?:\.\d+)?)/g;
    let m;
    while ((m = re.exec(text)) !== null) { total += parseFloat(m[1]); n++; }
    return n ? total : 0;
}

// ── حل رابط m3u8 نسبي مع الاحتفاظ ببارامترات الـ query (مثل token) من الرابط الأساسي ──
function footballM3u8Url(uri, base) {
    const u = new URL(uri, base);
    const b = new URL(base);
    if (!u.search && b.search) u.search = b.search;
    return u.href;
}

async function footballM3u8DurationOf(url, refererUrl, depth = 0) {
    const res = await axios.get(url, { headers: { 'User-Agent': FOOTBALL_UA, Referer: refererUrl || SOCCERFULL_BASE + '/' }, timeout: 30000 });
    const text = String(res.data);
    if (text.includes('#EXT-X-STREAM-INF') && depth < 1) {
        const lines = text.split(/\r?\n/).map(l => l.trim());
        for (let i = 0; i < lines.length; i++) {
            if (!lines[i].startsWith('#EXT-X-STREAM-INF')) continue;
            for (let j = i + 1; j < lines.length; j++) {
                if (!lines[j] || lines[j].startsWith('#')) continue;
                return footballM3u8DurationOf(footballM3u8Url(lines[j], url), url, depth + 1);
            }
        }
        return 0;
    }
    return footballM3u8Duration(text);
}

// ── تحليل master m3u8: الجودات + مدة أعلى جودة + حجم تقديري ──
async function footballM3u8Info(masterUrl) {
    const masterRes = await axios.get(masterUrl, { headers: { 'User-Agent': FOOTBALL_UA }, timeout: 25000 });
    const master = String(masterRes.data);
    const lines = master.split(/\r?\n/).map(l => l.trim());
    const variants = [];
    for (let i = 0; i < lines.length; i++) {
        if (!lines[i].startsWith('#EXT-X-STREAM-INF')) continue;
        const inf = lines[i];
        const bw = parseInt((inf.match(/AVERAGE-BANDWIDTH=(\d+)/) || inf.match(/BANDWIDTH=(\d+)/) || [])[1] || '0', 10) || 0;
        const res = (inf.match(/RESOLUTION=(\d+x\d+)/) || [])[1] || '';
        let uri = null;
        for (let j = i + 1; j < lines.length; j++) {
            if (!lines[j] || lines[j].startsWith('#')) continue;
            uri = lines[j]; break;
        }
        if (!uri) continue;
        variants.push({ bw, res, url: footballM3u8Url(uri, masterUrl) });
    }
    if (!variants.length) {
        const dur = footballM3u8Duration(master);
        if (!dur) return null;
        return { label: 'HD', durationSec: dur, sizeBytes: null, variants: [{ bw: 0, res: '', url: masterUrl }] };
    }
    variants.sort((a, b) => b.bw - a.bw);
    const best = variants[0];
    const dur = await footballM3u8DurationOf(best.url, masterUrl);
    if (!dur) return null;
    const sizeBytes = best.bw > 0 ? Math.round(best.bw * dur / 8) : null;
    const label = best.res ? `${best.res.split('x')[1]}p` : (best.bw ? `${Math.round(best.bw / 1000)} kbps` : 'HD');
    return { label, durationSec: dur, sizeBytes, variants };
}

// ── SoccerFull: رابط m3u8 مباشر للمباراة الكاملة ──
// الصفحة الرئيسية ← صفحة المباراة ← iframe /play/<id> ← رابط m3u8 مباشر
async function footballResolveSoccerFull(match) {
    const homePage = await axios.get(SOCCERFULL_BASE + '/', { headers: { 'User-Agent': FOOTBALL_UA }, timeout: 25000 });
    const html = homePage.data;
    const candidates = [];
    const aRe = /<a[^>]+href="([^"]+\.html)"[^>]*>([\s\S]*?)<\/a>/g;
    let m;
    while ((m = aRe.exec(html)) !== null) {
        const text = m[2].replace(/<[^>]+>/g, ' ');
        if (footballHasTeam(text, match.home) && footballHasTeam(text, match.away)) {
            const href = m[1].startsWith('http') ? m[1] : SOCCERFULL_BASE + (m[1].startsWith('/') ? m[1] : '/' + m[1]);
            if (!candidates.includes(href)) candidates.push(href);
        }
        if (candidates.length >= 3) break;
    }
    if (!candidates.length) return null;
    for (const matchUrl of candidates) {
        try {
            const pageRes = await axios.get(matchUrl, { headers: { 'User-Agent': FOOTBALL_UA, Referer: SOCCERFULL_BASE + '/' }, timeout: 25000 });
            const playM = pageRes.data.match(/<iframe[^>]+src="((?:https?:\/\/soccerfull\.net)?\/play\/\d+)"/);
            if (!playM) continue;
            const playUrl = playM[1].startsWith('http') ? playM[1] : SOCCERFULL_BASE + playM[1];
            const playRes = await axios.get(playUrl, { headers: { 'User-Agent': FOOTBALL_UA, Referer: matchUrl }, timeout: 25000 });
            const m3u8M = String(playRes.data).match(/https?:\/\/[^\s"'<>]+\.m3u8(?:[^\s"'<>]*)?/);
            if (!m3u8M) continue;
            const masterUrl = m3u8M[0];
            const info = await footballM3u8Info(masterUrl);
            if (!info || info.durationSec < FOOTBALL_FULL_MIN_SEC) continue;
            return { matchUrl, playUrl, m3u8Url: masterUrl, label: info.label, durationSec: info.durationSec, sizeBytes: info.sizeBytes, variants: info.variants };
        } catch (_) { continue; }
    }
    return null;
}

// ── ok.ru: مدة + تاريخ رفع فيديو من صفحة الفيديو (meta duration + uploadDate) ──
async function footballOkruMeta(videoId) {
    try {
        const res = await axios.get(`https://ok.ru/video/${videoId}`, { headers: OKRU_PAGE_HEADERS, timeout: 20000 });
        const html = String(res.data);
        const dM = html.match(/duration"\s*content="(\d+)"/);
        const uM = html.match(/"uploadDate" content="([^"]+)"/) || html.match(/uploadDate[^0-9]{0,30}(20\d\d-\d\d-\d\d)/);
        const uploadDate = uM ? new Date(uM[1]) : null;
        return { durationSec: dM ? parseInt(dM[1], 10) : null, uploadDate: uploadDate && !isNaN(uploadDate) ? uploadDate : null };
    } catch (_) { return { durationSec: null, uploadDate: null }; }
}

async function footballOkruDuration(videoId) {
    const meta = await footballOkruMeta(videoId);
    return meta.durationSec;
}

// ── حداثة الرفع: المباراة من قايمة اليوم، فالرفع لازم يكون حديث (آخر 7 أيام) ──
// لو مفيش تاريخ رفع في الصفحة، نرفض العناوين اللي فيها سنة قديمة (< 2026)
function footballOkruRecent(title, uploadDate) {
    if (uploadDate) {
        const ageMs = Date.now() - uploadDate.getTime();
        return ageMs >= -86400000 && ageMs <= 7 * 86400000;
    }
    const years = String(title || '').match(/\b(19|20)\d\d\b/g) || [];
    return !years.some(y => parseInt(y, 10) < 2026);
}

// ── حجم رابط مباشر عبر HEAD (Range bytes=0-0 — المجموع من Content-Range) ──
async function footballHeadSize(url) {
    try {
        const res = await axios.head(url, {
            headers: { 'User-Agent': WEB_UA, Range: 'bytes=0-0' },
            timeout: 15000, maxRedirects: 5,
            validateStatus: s => s >= 200 && s < 500
        });
        const cr = res.headers['content-range'] || '';
        const crM = cr.match(/\/(\d+)\s*$/);
        if (crM) return parseInt(crM[1], 10);
        const len = parseInt(res.headers['content-length'] || '0', 10);
        return len > 0 ? len : null;
    } catch (_) { return null; }
}

// ── ok.ru: ابحث عن رفع كامل للمباراة (≥ 60 دقيقة) + أطول ملخص كبديل ──
// يرجّع { full: {id,title,durationSec,qualities:[{name,label,url,sizeBytes}]} | null,
//         highlights: {id,title,durationSec} | null }
async function footballResolveOkruFull(home, away) {
    const queries = [`${home} vs ${away} full match`, `${home} vs ${away}`];
    const seen = new Set();
    const candidates = [];
    for (const q of queries) {
        try {
            const list = await okruSearchRaw(q);
            for (const v of list) {
                if (seen.has(v.id)) continue;
                seen.add(v.id);
                candidates.push(v);
                if (candidates.length >= 8) break;
            }
        } catch (_) {}
        if (candidates.length >= 8) break;
    }
    let highlights = null;
    for (const c of candidates) {
        const meta = await footballOkruMeta(c.id);
        const dur = meta.durationSec;
        if (!dur) continue;
        if (!footballOkruRecent(c.title, meta.uploadDate)) continue; // رفع قديم (موسم سابق) — مش مباراة اليوم
        if (dur >= FOOTBALL_FULL_MIN_SEC) {
            try {
                const { title, videos } = await extractOkruVideo(`https://ok.ru/video/${c.id}`);
                const qualities = [];
                const sized = await Promise.allSettled(videos.map(async v => {
                    const url = String(v.url).replace(/\\u0026/g, '&').replace(/\\\//g, '/');
                    return { name: v.name, label: OKRU_QUALITY_LABELS[v.name] || v.name || 'غير معروفة', url, sizeBytes: await footballHeadSize(url) };
                }));
                for (const s of sized) if (s.status === 'fulfilled') qualities.push(s.value);
                if (!qualities.length) continue;
                return { full: { id: c.id, title, durationSec: dur, qualities }, highlights };
            } catch (_) { continue; }
        }
        if (!highlights || dur > highlights.durationSec) highlights = { id: c.id, title: c.title, durationSec: dur };
    }
    return { full: null, highlights };
}
// ── MixDrop (v117): مباراة كاملة mp4 من fullmatchshows ──
// السلسلة: fullmatchshows (بحث ووردبريس ← صفحة المباراة) ← mixdrop.top/f/<id>
// ← صفحة التشغيل mxdrop.click/e/<id> ← فك packed JS ← MDCore.wurl
// ← mp4 مباشر على *.mxcontent.net (لازم كوكيز صفحة التشغيل + Referer وإلا 403).
// الرابط فيه توكن s= وتاريخ انتهاء e= (صلاحية ~6 ساعات) — يُجلب طازج كل مرة.
// التوكن مربوط بالجلسة/الـ IP اللي جابه، فلازم الحل والتحميل يكونوا من نفس
// الجهاز (نفس تشغيل البوت) — الكوكيز بتتمرّر مع رابط التحميل في headerSets.
const MIXDROP_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'; // نفس WEB_UA (معرّف في سطر 1634) — قيمة حرفية عشان سطر 1103 بيتنفذ قبله

// ── jar كوكيز بسيط للـ MixDrop: host -> {name: value} ──
function footballMixDropJarStore(jar, url, setCookie) {
    if (!setCookie || !setCookie.length) return;
    let host;
    try { host = new URL(url).hostname; } catch (_) { return; }
    jar[host] = jar[host] || {};
    for (const sc of setCookie) {
        const m = String(sc).match(/^\s*([^=;]+)=([^;]*)/);
        if (m) jar[host][m[1].trim()] = m[2].trim();
    }
}

function footballMixDropJarHeader(jar, url) {
    let host;
    try { host = new URL(url).hostname; } catch (_) { return ''; }
    const parts = [];
    for (const [h, cookies] of Object.entries(jar)) {
        if (host === h || host.endsWith('.' + h)) {
            for (const [k, v] of Object.entries(cookies)) parts.push(`${k}=${v}`);
        }
    }
    return parts.join('; ');
}

// ── GET مع تتبع يدوي للتحويلات وجمع الكوكيز من كل خطوة (axios مش بيحتفظ بكوكيز) ──
async function footballMixDropGet(url, jar, extraHeaders = {}) {
    let cur = url;
    for (let hop = 0; hop < 6; hop++) {
        const headers = { 'User-Agent': MIXDROP_UA, ...extraHeaders };
        const ck = footballMixDropJarHeader(jar, cur);
        if (ck) headers.Cookie = ck;
        const res = await axios.get(cur, {
            headers, timeout: 25000, maxRedirects: 0,
            validateStatus: s => s >= 200 && s < 400
        });
        footballMixDropJarStore(jar, cur, res.headers['set-cookie']);
        if ([301, 302, 303, 307, 308].includes(res.status) && res.headers.location) {
            cur = new URL(res.headers.location, cur).href;
            continue;
        }
        return { status: res.status, text: String(res.data), finalUrl: cur };
    }
    throw new Error('too many redirects');
}

// ── فك الـ packed JS (Dean Edwards) في سياق vm فارغ ──
function footballMixDropUnpack(packed) {
    const fnCall = packed.replace(/^eval\(/, '').replace(/\)\s*$/, '');
    return vm.runInNewContext('(' + fnCall + ')', {});
}

// ── حجم ملف من صفحة MixDrop (اسم الملف بخط عريض وجنبه "1.28 GB") ──
function footballMixDropParseSize(text) {
    const html = String(text);
    const m = html.match(/\.mp4<\/b>\s*([\d.]+)\s*(GB|MB|KB)/i)
        || html.match(/<b title="[^"]+">[^<]*<\/b>\s*([\d.]+)\s*(GB|MB|KB)/i);
    if (!m) return null;
    const n = parseFloat(m[1]);
    if (!n) return null;
    const mult = { GB: 1073741824, MB: 1048576, KB: 1024 }[m[2].toUpperCase()] || 0;
    return Math.round(n * mult);
}

// ── مدة mp4 عبر ffprobe (نفس الجهاز اللي جاب التوكن — نفس الـ IP) ──
function footballProbeMp4Duration(url, headers = {}) {
    return new Promise((resolve) => {
        let settled = false;
        const finish = (val) => { if (!settled) { settled = true; resolve(val); } };
        const hdrStr = Object.entries(headers || {})
            .filter(([k, v]) => v !== undefined && v !== null && String(v).length)
            .map(([k, v]) => `${k}: ${v}`).join('\r\n');
        const args = ['-v', 'quiet', '-print_format', 'json', '-show_format',
            '-analyzeduration', '8000000', '-probesize', '8000000'];
        if (hdrStr) args.push('-headers', hdrStr + '\r\n');
        args.push(url);
        let proc;
        try { proc = spawn('ffprobe', args); } catch (_) { return finish(null); }
        let out = '';
        proc.stdout.on('data', (d) => { out += d.toString(); });
        proc.on('close', () => {
            try {
                const data = JSON.parse(out);
                const dur = parseFloat(data && data.format && data.format.duration);
                if (dur && dur > 0) return finish(dur);
            } catch (_) {}
            finish(null);
        });
        proc.on('error', () => finish(null));
        setTimeout(() => { try { proc.kill(); } catch (_) {} finish(null); }, 25000);
    });
}

// ── MixDrop: حلّ مباراة كاملة من fullmatchshows ──
// يرجّع { mp4Url, sizeBytes, durationSec, cookie, eUrl, fUrl } أو null
async function footballResolveMixDrop(match) {
    const jar = {};
    // 1) بحث ووردبريس في fullmatchshows عن صفحة المباراة
    const q = `${match.home} vs ${match.away}`;
    const sRes = await footballMixDropGet(`${FULLMATCHSHOWS_BASE}/?s=${encodeURIComponent(q)}`, jar);
    const sHtml = sRes.text;
    const linkRe = /<a[^>]+href="(https?:\/\/fullmatchshows\.com\/[^"]+)"[^>]*>([\s\S]*?)<\/a>/g;
    const candidates = [];
    let m;
    while ((m = linkRe.exec(sHtml)) !== null) {
        const text = m[2].replace(/<[^>]+>/g, ' ');
        const href = m[1];
        if (!/\/[^/]+\/$/.test(new URL(href).pathname)) continue;
        if (!footballHasTeam(text, match.home) || !footballHasTeam(text, match.away)) continue;
        if (!/full-match/i.test(href + ' ' + text)) continue;
        candidates.push(href);
        if (candidates.length >= 3) break;
    }
    if (!candidates.length) return null;
    // فضّل صفحة بتاريخ اليوم أو امبارح (صيغة الرابط: ...-8-nov-2026/)
    const months = { jan: 0, feb: 1, mar: 2, apr: 3, may: 4, jun: 5, jul: 6, aug: 7, sep: 8, oct: 9, nov: 10, dec: 11 };
    const todayStart = new Date(footballTodayUTC() + 'T00:00:00Z').getTime();
    let matchUrl = candidates[0];
    const wantDate = match.date ? Date.parse(match.date + 'T00:00:00Z') : NaN; // مباراة البحث: نفس التاريخ المختار
    for (const href of candidates) {
        const dM = href.match(/(\d{1,2})-(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)-(\d{4})/i);
        if (!dM) continue;
        const t = Date.UTC(parseInt(dM[3], 10), months[dM[2].toLowerCase()], parseInt(dM[1], 10));
        if (!isNaN(wantDate) && t === wantDate) { matchUrl = href; break; }
        if (isNaN(wantDate) && t >= todayStart - 86400000 && t <= todayStart) { matchUrl = href; break; }
    }
    // 2) صفحة المباراة ← رابط mixdrop.top/f/<id>
    const pRes = await footballMixDropGet(matchUrl, jar, { Referer: FULLMATCHSHOWS_BASE + '/' });
    const mdM = pRes.text.match(/https?:\/\/(?:www\.)?mixdrop\.[a-z]+\/f\/[A-Za-z0-9]+/i);
    if (!mdM) return null;
    // 3) صفحة الملف /f/ (بعد التحويلات) ← الحجم + iframe صفحة التشغيل /e/
    const fRes = await footballMixDropGet(mdM[0], jar, { Referer: matchUrl });
    const fHtml = fRes.text;
    const fUrl = fRes.finalUrl;
    const sizeBytes = footballMixDropParseSize(fHtml);
    const ePath = (fHtml.match(/<iframe[^>]+src="(\/e\/[A-Za-z0-9]+)"/) || [])[1]
        || (fHtml.match(/href="(\/e\/[A-Za-z0-9]+)"/) || [])[1];
    const eUrl = ePath ? new URL(ePath, fUrl).href : fUrl.replace(/\/f\//, '/e/');
    // 4) صفحة التشغيل /e/ ← فك packed JS ← MDCore.wurl
    const eRes = await footballMixDropGet(eUrl, jar, { Referer: fUrl });
    const pkM = eRes.text.match(/eval\(function\(p,a,c,k,e,d\)\{[\s\S]*?\}\([\s\S]*?\)\)/);
    if (!pkM) return null;
    let unpacked;
    try { unpacked = footballMixDropUnpack(pkM[0]); } catch (_) { return null; }
    const wM = String(unpacked).match(/MDCore\.wurl\s*=\s*["']([^"']+)["']/);
    if (!wM) return null;
    let mp4Url = wM[1];
    if (mp4Url.startsWith('//')) mp4Url = 'https:' + mp4Url;
    if (!/^https?:\/\//i.test(mp4Url)) return null;
    // 5) الحجم (صفحة الملف أولاً، وHEAD بديل) + المدة عبر ffprobe
    let finalSize = sizeBytes;
    const cookie = footballMixDropJarHeader(jar, mp4Url);
    if (!finalSize) {
        try {
            const head = await axios.head(mp4Url, {
                headers: { 'User-Agent': MIXDROP_UA, Referer: eUrl, ...(cookie ? { Cookie: cookie } : {}) },
                timeout: 15000, maxRedirects: 5, validateStatus: s => s >= 200 && s < 500
            });
            const len = parseInt(head.headers['content-length'] || '0', 10);
            if (len > 0) finalSize = len;
        } catch (_) {}
    }
    const durationSec = await footballProbeMp4Duration(mp4Url, { 'User-Agent': MIXDROP_UA, Referer: eUrl, ...(cookie ? { Cookie: cookie } : {}) });
    if (durationSec && durationSec < FOOTBALL_FULL_MIN_SEC) return null;
    if (!durationSec && (!finalSize || finalSize < 500 * 1048576)) return null; // بلا مدة: لازم حجم يوحي بمباراة كاملة
    return { mp4Url, sizeBytes: finalSize, durationSec: durationSec || null, cookie, eUrl, fUrl };
}
// ===== ⚽ .football — END (v117) =====

// ===== 🎬 .tflix — BEGIN =====
// بث tflix مشفّر ClearKey (DASH/MPD): الموقع يرفض طلبات HTTP/1.1 بصمت (401)،
// فالاستخراج يتم عبر HTTP/2 بأدوات Node المدمجة وبلا أي متصفح أو مكتبة خارجية:
// صفحة المشاهدة ← صفحة المشغّل (التوكن) ← تسجيل المشاهدة (track) ← واجهة التشغيل
// تعطي رابط MPD + مفتاح ClearKey، ثم تُحمَّل المقاطع وتُفكّ بـ ffmpeg
// (-decryption_key) نسخاً بلا إعادة ترميز — بنفس منطق أجزاء .record تقريباً.
// الدومين من TFLIX_CONFIG ويُبدَّل بـ .tflix -domain <الدومين الجديد>.
const net = require('net');
const tls = require('tls');
const http2 = require('http2');
const https = require('https');
const zlib = require('zlib');

const TFLIX_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36';
const TFLIX_FETCH_H = { 'accept': '*/*', 'accept-language': 'en-US,en;q=0.9', 'accept-encoding': 'gzip, deflate, br', 'sec-fetch-dest': 'empty', 'sec-fetch-mode': 'cors', 'sec-fetch-site': 'same-origin', 'priority': 'u=1, i' };
const TFLIX_PAGE_H = { 'accept': 'text/html,application/xhtml+xml', 'accept-language': 'en-US,en;q=0.9', 'accept-encoding': 'gzip, deflate, br' };

function tflixTlsSocket(host) {
    return new Promise((resolve, reject) => {
        const proxy = process.env.https_proxy || process.env.HTTPS_PROXY;
        if (!proxy) {
            const s = tls.connect({ host, port: 443, servername: host, ALPNProtocols: ['h2'] });
            s.on('secureConnect', () => resolve(s));
            s.on('error', reject);
            return;
        }
        const u = new URL(proxy);
        const auth = 'Basic ' + Buffer.from(decodeURIComponent(u.username || '') + ':' + decodeURIComponent(u.password || '')).toString('base64');
        const raw = net.connect(parseInt(u.port, 10), u.hostname, () => {
            raw.write('CONNECT ' + host + ':443 HTTP/1.1\r\nHost: ' + host + ':443\r\nProxy-Authorization: ' + auth + '\r\n\r\n');
        });
        let buf = Buffer.alloc(0);
        raw.on('data', (d) => {
            buf = Buffer.concat([buf, d]);
            const idx = buf.indexOf('\r\n\r\n');
            if (idx >= 0) {
                const line = buf.slice(0, buf.indexOf('\r\n')).toString();
                if (!/ 200 /.test(line + ' ')) { raw.destroy(); return reject(new Error('CONNECT failed: ' + line)); }
                raw.removeAllListeners('data');
                const secure = tls.connect({ socket: raw, servername: host, ALPNProtocols: ['h2'], rejectUnauthorized: false });
                secure.on('secureConnect', () => resolve(secure));
                secure.on('error', reject);
            }
        });
        raw.on('error', reject);
    });
}

async function tflixH2Session(host) {
    const sock = await tflixTlsSocket(host);
    const client = http2.connect('https://' + host, { createConnection: () => sock });
    await new Promise((res, rej) => { client.on('connect', res); client.on('error', rej); setTimeout(() => rej(new Error('h2 connect timeout')), 20000); });
    const call = (method, p, headers, body) => new Promise((resolve, reject) => {
        const req = client.request({ ':method': method, ':path': p, 'user-agent': TFLIX_UA, ...headers });
        const chunks = [];
        let status = 0, enc = null;
        req.on('response', (h) => { status = h[':status']; enc = h['content-encoding']; });
        req.on('data', (c) => chunks.push(c));
        req.on('end', () => {
            let b = Buffer.concat(chunks);
            try {
                if (enc === 'gzip') b = zlib.gunzipSync(b);
                else if (enc === 'br') b = zlib.brotliDecompressSync(b);
                else if (enc === 'deflate') b = zlib.inflateSync(b);
            } catch (e) {}
            resolve({ status, body: b.toString('utf8') });
        });
        req.on('error', reject);
        req.setTimeout(30000, () => req.destroy(new Error('h2 req timeout')));
        if (body) req.end(body); else req.end();
    });
    return { call, close: () => { try { client.close(); } catch (e) {} } };
}

function tflixDecodeBody(buf, enc) {
    try {
        if (enc === 'gzip') return zlib.gunzipSync(buf);
        if (enc === 'br') return zlib.brotliDecompressSync(buf);
        if (enc === 'deflate') return zlib.inflateSync(buf);
    } catch (e) {}
    return buf;
}

// تحميل عادي (HTTP/1.1) — يُستخدم لشبكة CDN الخاصة بالمقاطع وقائمة MPD فقط،
// فهي تقبل الطلبات العادية؛ أما واجهات tflix نفسها فتمر عبر جلسة HTTP/2 أعلاه.
function tflixHttpGetBuffer(url, timeoutMs = 20000) {
    return new Promise((resolve, reject) => {
        const req = https.get(url, { headers: { 'User-Agent': TFLIX_UA, 'Accept': '*/*' } }, (res) => {
            if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
                res.resume();
                return resolve(tflixHttpGetBuffer(new URL(res.headers.location, url).toString(), timeoutMs));
            }
            const chunks = [];
            res.on('data', (c) => chunks.push(c));
            res.on('end', () => {
                if (res.statusCode !== 200) return reject(new Error('HTTP ' + res.statusCode + ' for ' + url.slice(0, 90)));
                resolve(tflixDecodeBody(Buffer.concat(chunks), res.headers['content-encoding']));
            });
        });
        req.on('error', reject);
        req.setTimeout(timeoutMs, () => req.destroy(new Error('timeout ' + url.slice(0, 90))));
    });
}

// قائمة أحداث كرة القدم من خلاصة الموقع العامة (تشمل القنوات المضمّنة لكل حدث)
async function tflixListEvents(domain) {
    const s = await tflixH2Session(domain);
    try {
        const r = await s.call('GET', '/api/public?scope=football', TFLIX_PAGE_H);
        if (r.status !== 200) throw new Error('خلاصة tflix أجابت HTTP ' + r.status);
        const j = JSON.parse(r.body);
        const now = Date.now();
        return (j.events || [])
            .filter(e => e && e.sport === 'Football' && e.watch_url)
            .map(e => {
                const start = Date.parse(e.starts_at || '') || 0;
                const end = Date.parse(e.ends_at || '') || 0;
                return {
                    feedId: e.id, title: e.title || ((e.home_name || '') + ' vs ' + (e.away_name || '')),
                    competition: e.competition || '', startsAt: start, endsAt: end,
                    live: start <= now && now < end, watchPath: e.watch_url,
                    channels: (e.channels || []).map(c => ({ id: c.id, name: c.name || c.id, playbackType: c.playbackType || '' })),
                };
            })
            .sort((a, b) => (b.live - a.live) || (a.startsAt - b.startsAt));
    } finally { s.close(); }
}

// قراءة بيانات الحدث من JSON المضمّن في صفحة المشاهدة (لروابط .tflix المباشرة)
function tflixParseWatchBootstrap(html) {
    const key = '"events":';
    const ki = html.indexOf(key);
    if (ki < 0) return null;
    let i = html.indexOf('[', ki);
    if (i < 0) return null;
    let depth = 0, j = i, inStr = false, esc = false;
    for (; j < html.length; j++) {
        const ch = html[j];
        if (inStr) { if (esc) esc = false; else if (ch === '\\') esc = true; else if (ch === '"') inStr = false; continue; }
        if (ch === '"') inStr = true;
        else if (ch === '[') depth++;
        else if (ch === ']') { depth--; if (depth === 0) break; }
    }
    try {
        const arr = JSON.parse(html.slice(i, j + 1));
        if (!Array.isArray(arr) || !arr.length) return null;
        const e = arr[0];
        return {
            feedId: e.id, title: e.title || '', watchPath: e.watch_url || '',
            channels: (e.channels || []).map(c => ({ id: c.id, name: c.name || c.id, playbackType: c.playbackType || '' })),
        };
    } catch (err) { return null; }
}

async function tflixGetWatchEvent(domain, watchPath) {
    const s = await tflixH2Session(domain);
    try {
        const w = await s.call('GET', watchPath, TFLIX_PAGE_H);
        if (w.status !== 200) throw new Error('صفحة المشاهدة أجابت HTTP ' + w.status);
        const ev = tflixParseWatchBootstrap(w.body);
        if (!ev || !ev.channels.length) throw new Error('لم يتم العثور على قنوات بث في صفحة هذه المباراة (ربما لم تُسند بعد — تظهر القنوات عند الانطلاق)');
        ev.watchPath = watchPath;
        return ev;
    } finally { s.close(); }
}

// التسلسل المُثبت لفتح واجهة التشغيل: مشاهدة ← مشغّل (توكن) ← track play ← محادثة ← track view ← الإعدادات
async function tflixExtractConfig(domain, watchPath, feedId, channelId) {
    const s = await tflixH2Session(domain);
    try {
        const w = await s.call('GET', watchPath, TFLIX_PAGE_H);
        if (w.status !== 200) throw new Error('صفحة المشاهدة أجابت HTTP ' + w.status);
        const p = await s.call('GET', '/player/' + channelId, TFLIX_PAGE_H);
        if (p.status !== 200) throw new Error('صفحة المشغّل أجابت HTTP ' + p.status);
        const m = p.body.match(/PLAYBACK_AUTHORIZATION="([^"]+)"/) || p.body.match(/(\d{13}\.[A-Za-z0-9_-]{8,}\.[A-Za-z0-9_-]{8,})/);
        if (!m) throw new Error('لم يتم العثور على توكن التشغيل في صفحة المشغّل');
        const token = m[1];
        const track = async (kind) => {
            const payload = JSON.stringify({ kind, path: watchPath, referrer: '', playing: true, campaign: '' });
            return s.call('POST', '/api/track', { ...TFLIX_FETCH_H, 'content-type': 'application/json', 'origin': 'https://' + domain, 'referer': 'https://' + domain + watchPath, 'content-length': Buffer.byteLength(payload) }, payload);
        };
        await track('play');
        if (feedId) { try { await s.call('GET', '/api/chat?room=' + encodeURIComponent('event:' + feedId), { ...TFLIX_FETCH_H, 'referer': 'https://' + domain + watchPath }); } catch (e) {} }
        await track('view');
        const api = await s.call('GET', '/api/player/channel/' + channelId, { ...TFLIX_FETCH_H, 'x-tflix-playback': token });
        if (api.status !== 200) throw new Error('واجهة التشغيل رفضت الطلب (' + api.status + ') — ربما لم يبدأ البث بعد');
        const cfg = JSON.parse(api.body);
        if (!cfg.url) throw new Error('إعدادات البث بلا رابط تشغيل');
        let kid = '', key = '';
        if (cfg.clearKey && cfg.clearKey.includes(':')) { const parts = cfg.clearKey.split(':'); kid = parts[0]; key = parts[1]; }
        if (!key) throw new Error('إعدادات البث بلا مفتاح ClearKey — نوع حماية غير مدعوم');
        return { mpdUrl: cfg.url, kid, key, type: cfg.type || 'mpd', name: cfg.name || '' };
    } finally { s.close(); }
}

function tflixAttr(tag, name) {
    const m = tag.match(new RegExp(name + '="([^"]*)"'));
    return m ? m[1] : '';
}

// تحليل MPD: جودات الفيديو والصوت مع قوالب المقاطع وأرقامها ومدة المقطع
function tflixParseMpd(xml) {
    const out = { videos: [], audios: [] };
    const asRe = /<AdaptationSet\b[^>]*>([\s\S]*?)<\/AdaptationSet>/g;
    let am;
    while ((am = asRe.exec(xml))) {
        const asTag = am[0].slice(0, am[0].indexOf('>') + 1);
        const mime = tflixAttr(asTag, 'mimeType');
        const asSt = (am[1].match(/<SegmentTemplate\b[^>]*>/) || [''])[0];
        const reps = [];
        const repRe = /<Representation\b[^>]*>([\s\S]*?)<\/Representation>/g;
        let rm;
        while ((rm = repRe.exec(am[1]))) {
            reps.push({ tag: rm[0].slice(0, rm[0].indexOf('>') + 1), stTag: (rm[1].match(/<SegmentTemplate\b[^>]*>/) || [''])[0] || asSt, inner: rm[1] });
        }
        if (!reps.length) {
            const selfRe = /<Representation\b[^>]*\/>/g;
            let sm;
            while ((sm = selfRe.exec(am[1]))) reps.push({ tag: sm[0], stTag: asSt, inner: '' });
        }
        for (const r of reps) {
            const stTag = r.stTag || asSt;
            const tl = (r.inner.match(/<SegmentTimeline>([\s\S]*?)<\/SegmentTimeline>/) || am[1].match(/<SegmentTimeline>([\s\S]*?)<\/SegmentTimeline>/) || [])[1] || '';
            let total = 0, segDur = 0;
            const sRe = /<S\b[^>]*>/g;
            let sM;
            while ((sM = sRe.exec(tl))) {
                total += (parseInt(tflixAttr(sM[0], 'r') || '0', 10) || 0) + 1;
                if (!segDur) segDur = parseInt(tflixAttr(sM[0], 'd') || '0', 10);
            }
            const timescale = parseInt(tflixAttr(stTag, 'timescale') || '1', 10) || 1;
            const entry = {
                id: tflixAttr(r.tag, 'id'), bandwidth: parseInt(tflixAttr(r.tag, 'bandwidth') || '0', 10) || 0,
                width: parseInt(tflixAttr(r.tag, 'width') || '0', 10) || 0, height: parseInt(tflixAttr(r.tag, 'height') || '0', 10) || 0,
                codecs: tflixAttr(r.tag, 'codecs'),
                media: tflixAttr(stTag, 'media'), init: tflixAttr(stTag, 'initialization'),
                startNumber: parseInt(tflixAttr(stTag, 'startNumber') || '1', 10) || 1,
                segDurSec: segDur ? segDur / timescale : 2, lastNumber: 0,
            };
            entry.lastNumber = entry.startNumber + Math.max(0, total - 1);
            if (!entry.media) continue;
            if (mime.startsWith('video')) out.videos.push(entry);
            else if (mime.startsWith('audio')) out.audios.push(entry);
        }
    }
    out.videos.sort((a, b) => (b.height - a.height) || (b.bandwidth - a.bandwidth));
    out.audios.sort((a, b) => b.bandwidth - a.bandwidth);
    return out;
}

// اختيار الجودة المطلوبة بالارتفاع: الأعلى الذي لا يتجاوز المطلوب، وإلا الأقرب فوقه (قاعدة .livefootball)
function tflixPickVariant(variants, qualityHeight) {
    if (!variants || !variants.length) return null;
    const sorted = [...variants].sort((a, b) => a.height - b.height);
    let best = null;
    for (const v of sorted) if (v.height && v.height <= qualityHeight) best = v;
    if (best) return best;
    return sorted.find(v => v.height >= qualityHeight) || sorted[sorted.length - 1];
}

function tflixRunFfmpeg(args) {
    return new Promise((resolve, reject) => {
        const p = spawn('ffmpeg', args, { stdio: ['ignore', 'ignore', 'pipe'] });
        let err = '';
        p.stderr.on('data', (d) => { err += d.toString(); });
        p.on('error', reject);
        p.on('close', (code) => code === 0 ? resolve() : reject(new Error('ffmpeg exit ' + code + ': ' + err.slice(-300))));
    });
}

// مسجّل DASH: يستطلع MPD، يحمّل المقاطع الجديدة من الحافة الحية، وعند اكتمال
// مدة كل جزء يفكّ تشفيره ويدمجه ويسلّمه عبر onPart — نسخ فقط، بلا إعادة ترميز.
async function tflixRecordDash(opts) {
    const { mpdUrl, keyHex, video, audio, totalSec, segmentTimeSec, dir, control, onPart } = opts;
    const base = mpdUrl.slice(0, mpdUrl.lastIndexOf('/') + 1);
    fs.mkdirSync(dir, { recursive: true });
    const segUrl = (tpl, n) => base + tpl.replace('$Number$', String(n));
    const vInit = await tflixHttpGetBuffer(base + video.init);
    let aInit = null;
    if (audio) { try { aInit = await tflixHttpGetBuffer(base + audio.init); } catch (e) { aInit = null; } }
    let nextV = null, nextA = null, recordedSec = 0, partIndex = 0;
    let vBuf = [], aBuf = [], partSec = 0;
    let lastProgress = Date.now();
    const startedAt = Date.now();
    async function finalizePart(final) {
        if (!vBuf.length) return;
        const vcat = path.join(dir, 'vcat_' + partIndex + '.mp4');
        const vdec = path.join(dir, 'vdec_' + partIndex + '.mp4');
        fs.writeFileSync(vcat, Buffer.concat([vInit, ...vBuf]));
        await tflixRunFfmpeg(['-y', '-v', 'error', '-decryption_key', keyHex, '-i', vcat, '-c', 'copy', vdec]);
        let out = vdec;
        if (audio && aBuf.length && aInit) {
            const acat = path.join(dir, 'acat_' + partIndex + '.mp4');
            const adec = path.join(dir, 'adec_' + partIndex + '.mp4');
            const mux = path.join(dir, 'part_' + partIndex + '.mp4');
            fs.writeFileSync(acat, Buffer.concat([aInit, ...aBuf]));
            await tflixRunFfmpeg(['-y', '-v', 'error', '-decryption_key', keyHex, '-i', acat, '-c', 'copy', adec]);
            await tflixRunFfmpeg(['-y', '-v', 'error', '-i', vdec, '-i', adec, '-c', 'copy', '-shortest', mux]);
            out = mux;
            try { fs.unlinkSync(acat); fs.unlinkSync(adec); } catch (e) {}
        }
        try { fs.unlinkSync(vcat); } catch (e) {}
        const finalPath = path.join(dir, 'tflix_part_' + (partIndex + 1) + '.mp4');
        fs.renameSync(out, finalPath);
        if (out !== vdec) { try { fs.unlinkSync(vdec); } catch (e) {} }
        partIndex++;
        vBuf = []; aBuf = []; partSec = 0;
        if (onPart) await onPart(finalPath, partIndex, final);
    }
    while (!control.stopped && recordedSec < totalSec) {
        let fresh;
        try {
            const mpdBuf = await tflixHttpGetBuffer(mpdUrl, 15000);
            fresh = tflixParseMpd(mpdBuf.toString('utf8'));
        } catch (e) {
            if (Date.now() - lastProgress > 120000) break;
            await new Promise(r => setTimeout(r, 4000));
            continue;
        }
        const fv = fresh.videos.find(v => v.id === video.id) || fresh.videos[0];
        const fa = audio ? (fresh.audios.find(a => a.id === audio.id) || fresh.audios[0]) : null;
        if (!fv) { await new Promise(r => setTimeout(r, 4000)); continue; }
        if (nextV === null) { nextV = Math.max(fv.startNumber, fv.lastNumber - 1); nextA = fa ? Math.max(fa.startNumber, fa.lastNumber - 1) : null; }
        const safeLast = fv.lastNumber - 1; // نبقى على بُعد مقطع من حافة البث المباشر
        let downloaded = false;
        while (nextV <= safeLast && recordedSec < totalSec && !control.stopped) {
            try {
                const vb = await tflixHttpGetBuffer(segUrl(fv.media, nextV), 15000);
                vBuf.push(vb);
                if (fa && nextA !== null) {
                    try { const ab = await tflixHttpGetBuffer(segUrl(fa.media, nextA), 15000); aBuf.push(ab); } catch (e) {}
                    nextA++;
                }
                nextV++;
                recordedSec += fv.segDurSec;
                partSec += fv.segDurSec;
                downloaded = true;
                lastProgress = Date.now();
                if (partSec >= segmentTimeSec) await finalizePart(false);
            } catch (e) {
                nextV++; if (nextA !== null) nextA++; // انزلق المقطع من نافذة البث — تخطَّه
            }
        }
        if (!downloaded) {
            if (Date.now() - lastProgress > 120000) break; // توقّف البث (انتهت المباراة غالباً)
            await new Promise(r => setTimeout(r, 3000));
        }
    }
    await finalizePart(true);
    return { recordedSec, parts: partIndex, elapsedMs: Date.now() - startedAt };
}

// بدء التسجيل الفعلي بعد اكتمال خطوات المعالج — بنفس أسلوب رسائل .livefootball
async function tflixStartRecording(XeonBotInc, chatId, mek, job) {
    if (activeTflixRecordings.has(chatId)) {
        await XeonBotInc.sendMessage(chatId, {
            text: `⚠️ يوجد تسجيل tflix نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoptflix\` قبل بدء تسجيل جديد.`
        }, { quoted: mek });
        return;
    }
    const duration = job.duration;
    const totalSec = duration * 60;
    let segmentTimeSec, segmentMinutes;
    if (job.manualSegmentMinutes !== null && job.manualSegmentMinutes !== undefined) {
        segmentMinutes = job.manualSegmentMinutes;
        segmentTimeSec = job.manualSegmentMinutes * 60;
    } else {
        const bps = ((job.videoRep.bandwidth || 0) + (job.audioRep ? (job.audioRep.bandwidth || 0) : 0)) / 8;
        const segDur = job.videoRep.segDurSec || 2;
        let segs = bps > 0 ? Math.round((RECORD_TARGET_MB * 1024 * 1024) / (bps * segDur)) : 30;
        segs = Math.max(5, Math.min(segs, 900));
        segmentTimeSec = segs * segDur;
        segmentMinutes = Math.max(1, Math.round(segmentTimeSec / 60));
    }
    const tmpDir = path.join(process.cwd(), 'dltmp');
    if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });
    const segDir = path.join(tmpDir, `tflix_${Date.now()}`);
    fs.mkdirSync(segDir, { recursive: true });
    await XeonBotInc.sendMessage(chatId, {
        text: `🎙️ *بدأ تسجيل المباراة من tflix!*\n⚽ ${job.title}\n📡 القناة: ${job.channelName || ''}\n🎞️ الجودة: *${job.qualityLabel || ''}*\n⏱️ المدة الكلية: *${duration} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${RECORD_TARGET_MB} MB)\n🔓 فكّ تشفير ClearKey أثناء التسجيل — بلا إعادة ترميز\n\n🛑 لإلغاء التسجيل في أي وقت: \`.stoptflix\``
    }, { quoted: mek });
    const control = { stopped: false };
    activeTflixRecordings.set(chatId, control);
    (async () => {
        let sentParts = 0;
        const onPart = async (filePath, idx) => {
            try {
                const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
                await XeonBotInc.sendMessage(chatId, {
                    document: { url: filePath },
                    mimetype: 'video/mp4',
                    fileName: `Tflix_part${idx}.mp4`,
                    caption: `📦 *الجزء ${idx}*\n⚽ ${job.title}\n📡 ${job.channelName || 'tflix'}${job.qualityLabel ? `\n🎞️ ${job.qualityLabel}` : ''}\n⚖️ ${sizeMB} MB`
                }, { quoted: mek });
                sentParts = idx;
            } catch (e) {
                await XeonBotInc.sendMessage(chatId, { text: `⚠️ فشل إرسال الجزء ${idx}: ${e.message}` }, { quoted: mek });
            } finally {
                try { fs.unlinkSync(filePath); } catch (_) {}
            }
        };
        try {
            const res = await tflixRecordDash({
                mpdUrl: job.cfg.mpdUrl, keyHex: job.cfg.key,
                video: job.videoRep, audio: job.audioRep,
                totalSec, segmentTimeSec, dir: segDir, control, onPart
            });
            if (control.stopped) {
                await XeonBotInc.sendMessage(chatId, { text: `🛑 *تم إلغاء تسجيل tflix بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${sentParts}` }, { quoted: mek });
            } else if (res.parts === 0) {
                await XeonBotInc.sendMessage(chatId, { text: `❌ لم تصل أي مقاطع قابلة للتسجيل من هذا البث (ربما انتهت المباراة أو توقّف البث).` }, { quoted: mek });
            } else {
                await XeonBotInc.sendMessage(chatId, { text: `✅ *اكتمل تسجيل المباراة من tflix!*\n⚽ ${job.title}\n📦 عدد الأجزاء المُرسلة: ${res.parts}` }, { quoted: mek });
            }
        } catch (err) {
            await XeonBotInc.sendMessage(chatId, { text: `❌ خطأ في تسجيل tflix: ${err.message}` }, { quoted: mek });
        } finally {
            activeTflixRecordings.delete(chatId);
            try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
        }
    })();
}

// خطوات ما بعد اختيار البث والجودة: مدة التسجيل ثم دقائق الجزء (تُتخطى إن أُعطيت في الأمر)
async function tflixWizardNext(XeonBotInc, chatId, mek, job) {
    if (job.duration === null || job.duration === undefined) {
        const sent = await XeonBotInc.sendMessage(chatId, {
            text: `⏱️ *كم دقيقة تريد أن أسجّل؟*\n⚽ ${job.title}\n\n💡 رد (Reply) على هذه الرسالة بعدد الدقائق (1 - 360). مثال: 100`
        }, { quoted: mek });
        tflixWizardCache.set(sent.key.id, { ...job, stage: 'duration' });
        setTimeout(() => tflixWizardCache.delete(sent.key.id), 300000);
        return;
    }
    if (!job.segDecided) {
        const sent = await XeonBotInc.sendMessage(chatId, {
            text: `📦 *كل كم دقيقة أبعث لك جزءاً من التسجيل؟*\n\n💡 رد (Reply) على هذه الرسالة بعدد الدقائق (1 - ${job.duration}). مثال: 1 تعني أن يصلك جزء جديد كل دقيقة.\nℹ️ أو رد بـ 0 للتقطيع التلقائي (~${RECORD_TARGET_MB} MB للجزء).`
        }, { quoted: mek });
        tflixWizardCache.set(sent.key.id, { ...job, stage: 'segment' });
        setTimeout(() => tflixWizardCache.delete(sent.key.id), 300000);
        return;
    }
    await tflixStartRecording(XeonBotInc, chatId, mek, job);
}

// بوابة التسجيل: اختيار القناة (إن تعددت) ← استخراج الإعدادات ← اختيار الجودة ← بقية الخطوات
async function tflixBeginFlow(XeonBotInc, chatId, mek, job) {
    if (!job.channelId) {
        if (!job.channels || !job.channels.length) {
            await XeonBotInc.sendMessage(chatId, { text: `❌ لا توجد قنوات بث لهذه المباراة على tflix حالياً.` }, { quoted: mek });
            return;
        }
        if (job.channels.length > 1 && !job.fastPath) {
            let cText = `📺 *اختر قناة البث:*\n⚽ ${job.title}\n\n`;
            job.channels.forEach((c, i) => { cText += `*${i + 1}.* ${c.name}\n`; });
            cText += `\n💡 رد (Reply) على هذه الرسالة برقم القناة خلال 5 دقائق.`;
            const sentC = await XeonBotInc.sendMessage(chatId, { text: cText }, { quoted: mek });
            tflixWizardCache.set(sentC.key.id, { ...job, stage: 'channel' });
            setTimeout(() => tflixWizardCache.delete(sentC.key.id), 300000);
            return;
        }
        job.channelId = job.channels[0].id;
        job.channelName = job.channels[0].name;
    }
    let cfg;
    try {
        await XeonBotInc.sendMessage(chatId, { text: `🔎 جاري استخراج بث القناة *${job.channelName || ''}* من tflix...` }, { quoted: mek });
        cfg = await tflixExtractConfig(job.domain, job.watchPath, job.feedId, job.channelId);
    } catch (e) {
        await XeonBotInc.sendMessage(chatId, { text: `❌ فشل استخراج البث:\n\`${e.message}\`` }, { quoted: mek });
        return;
    }
    job.cfg = cfg;
    let parsed;
    try {
        const mpdBuf = await tflixHttpGetBuffer(cfg.mpdUrl, 20000);
        parsed = tflixParseMpd(mpdBuf.toString('utf8'));
    } catch (e) {
        await XeonBotInc.sendMessage(chatId, { text: `❌ تعذر قراءة قائمة تشغيل البث:\n\`${e.message}\`` }, { quoted: mek });
        return;
    }
    if (!parsed.videos.length) {
        await XeonBotInc.sendMessage(chatId, { text: `❌ قائمة تشغيل هذا البث بلا مسارات فيديو قابلة للتسجيل.` }, { quoted: mek });
        return;
    }
    job.audioRep = parsed.audios[0] || null;
    if (job.requestedQuality) {
        const picked = tflixPickVariant(parsed.videos, job.requestedQuality);
        job.videoRep = picked;
        job.qualityLabel = picked && picked.height ? `${picked.height}p` : 'غير معروفة';
        await tflixWizardNext(XeonBotInc, chatId, mek, job);
        return;
    }
    if (parsed.videos.length > 1) {
        let qText = `🎞️ *اختر جودة التسجيل:*\n⚽ ${job.title}\n📡 ${job.channelName || 'tflix'}\n\n`;
        parsed.videos.forEach((v, i) => {
            const bw = v.bandwidth ? ` — ~${(v.bandwidth / 1000000).toFixed(1)} Mbps` : '';
            qText += `*${i + 1}.* ${v.height ? v.height + 'p' : 'جودة ' + (i + 1)}${v.width && v.height ? ` (${v.width}x${v.height})` : ''}${bw}\n`;
        });
        qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة خلال 5 دقائق، وبعدها سأسألك عن مدة التسجيل ودقائق كل جزء.`;
        const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
        tflixWizardCache.set(sentQ.key.id, { ...job, variants: parsed.videos, stage: 'quality' });
        setTimeout(() => tflixWizardCache.delete(sentQ.key.id), 300000);
        return;
    }
    job.videoRep = parsed.videos[0];
    job.qualityLabel = parsed.videos[0].height ? `${parsed.videos[0].height}p (المتاحة فقط)` : null;
    await tflixWizardNext(XeonBotInc, chatId, mek, job);
}
// ===== 🎬 .tflix — END =====

// ===== ⚽ .livefootball — BEGIN =====
// تسجيل مباريات مباشرة من مصادر بث رياضي مجمّعة (قائمة المستخدم)، بنفس منطق .record:
// فحص معدل البت → تسجيل متواصل مُجزّأ (~100MB للجزء) باتصال واحد → إرسال كل جزء فور
// اكتماله → إعادة اتصال تلقائية (مع إعادة استخراج رابط البث لأن توكنات m3u8 قصيرة العمر)
// → إيقاف بـ .stoplivefootball (خريطة تتبع منفصلة عن .record/.recordiptv).
const LF_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36';
const liveFootballLists = new Map(); // chatId -> { matches, at }

// سجل المصادر: auto=true يعني أن للبوت جالب أحداث تلقائياً لهذا المصدر.
// الباقي مصادر معروفة الدومين (قائمة FMHY الحالية) تُستخدم عبر الوضع المباشر:
// .livefootball <رابط صفحة المباراة من المصدر> [دقائق]
const LF_SOURCES = [
    { key: 'damitv', name: 'DamiTV', auto: true },
    { key: 'daddylive', name: 'DaddyLive', auto: true },
    { key: 'ppv', name: 'PPV.ST', auto: true },
    { key: 'sportsbite', name: 'SportsBite', auto: true },
    { key: 'fctv33', name: 'FCTV33', auto: true },
    { key: 'watchsports', name: 'WatchSports', auto: true },
    { key: 'roxie', name: 'RoxieStreams', auto: true },
    { key: 'strmfree', name: 'StreamFree', auto: true },
    { key: 'thetvapp', name: 'TheTVApp', auto: true },
    { key: 'timstreams', name: 'TimStreams', url: 'https://tim-streams.com' },
    { key: 'zlive', name: 'zlive', url: 'https://zlive.st' },
    { key: 'streameast', name: 'StreamEast', url: 'https://streameast.ga' },
    { key: 'streamcorner', name: 'StreamCorner', url: 'https://streamcorner.st' },
    { key: 'streamsports99', name: 'StreamSports99', url: 'https://streamsports99.ru' },
    { key: 'daddylivehd', name: 'DaddyLiveHD', url: 'https://daddylive.mov' },
    { key: 'strumyk', name: 'Strumyk / Strims24', url: 'https://strumyk.pk' },
    { key: 'totalsportek', name: 'TotalSportek / Sportsurge.st', url: 'https://totalsport-ek.st' },
    { key: 'sportsurge', name: 'Sportsurge', url: 'https://v2.sportsurge.net' },
    { key: 'sportontv', name: 'SportOnTV', url: 'https://sportontv.click' },
    { key: 'vipleague', name: 'VIP Box Sports', url: 'https://vipleague.me' },
    { key: 'crichd', name: 'CricHD', url: 'https://crichd.at' },
    { key: 'livetv', name: 'LiveTV', url: 'https://livetv.sx' },
    { key: 'futbolx', name: 'Futbol-X', url: 'https://www.futbol-x.xyz' },
    { key: 'aurasports', name: 'AURA Sports', url: 'https://aurasports.xyz' },
    { key: 'cinevid', name: 'Cinevid', url: 'https://cinevid.st' },
    { key: 'bintv', name: 'BINTV', url: 'https://www.bintv.cc' },
    { key: 'ntv', name: 'NTV', url: 'https://ntv.st' },
    { key: 'reedstreams', name: 'Reedstreams', url: 'https://reedstreams.to' },
    { key: 'xyzstreams', name: 'xyzstreams', url: 'https://xyzstreams.st' },
    { key: 'matchora', name: 'Matchora', url: 'https://matchora.to' },
    { key: 'tap4sport', name: 'Tap4Sport', url: 'https://tap4sport.st' },
    { key: 'streami', name: 'Streami', url: 'https://streamic.st' },
    { key: 'falconstreams', name: 'FalconStreams', url: 'https://falconstreams.app' },
    { key: 'fctv33b', name: 'FCTV33 (mirror)', url: 'https://www.fctv33go.hair' },
    { key: 'fawanews', name: 'FawaNews', url: 'https://www.fawanews.sc' },
];

async function lfGet(url, timeoutMs = 20000) {
    const res = await axios.get(url, {
        headers: { 'User-Agent': LF_UA, 'Accept': 'text/html,application/json,*/*' },
        timeout: timeoutMs, maxRedirects: 5, validateStatus: s => s >= 200 && s < 400
    });
    return res.data;
}

function lfDecodeEntities(s) {
    return String(s || '').replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
        .replace(/&quot;/g, '"').replace(/&#0?39;|&apos;/g, "'").replace(/&nbsp;/g, ' ');
}

// استخراج روابط <a> من HTML: [{title, url}] بعد حلّ الروابط النسبية وتنظيف النص
function lfParseAnchors(html, baseUrl) {
    const out = [];
    const seen = new Set();
    const re = /<a\s[^>]*href\s*=\s*["']([^"']+)["'][^>]*>([\s\S]*?)<\/a>/gi;
    let m;
    while ((m = re.exec(String(html || ''))) !== null) {
        const rawHref = lfDecodeEntities(m[1]).trim();
        if (!rawHref || /^(#|javascript:|mailto:)/i.test(rawHref)) continue;
        let abs;
        try { abs = new URL(rawHref, baseUrl).toString(); } catch (_) { continue; }
        if (seen.has(abs)) continue;
        const title = lfDecodeEntities(m[2].replace(/<[^>]+>/g, ' ')).replace(/\s+/g, ' ').trim();
        if (title.length < 4) continue;
        seen.add(abs);
        out.push({ title, url: abs });
    }
    return out;
}

// أول رابط m3u8 في نص/HTML (مع حلّه مقابل baseUrl إن كان نسبياً)
function lfExtractM3u8(text, baseUrl) {
    const m = String(text || '').match(/https?:\/\/[^\s"'<>\\]+?\.m3u8(?:\?[^\s"'<>\\]*)?/i)
        || String(text || '').match(/[^\s"'<>\\]+?\.m3u8(?:\?[^\s"'<>\\]*)?/i);
    if (!m) return null;
    try { return new URL(m[0], baseUrl).toString(); } catch (_) { return null; }
}

function lfIframeSrcs(html, baseUrl) {
    const out = [];
    const re = /<iframe\s[^>]*src\s*=\s*["']([^"']+)["']/gi;
    let m;
    while ((m = re.exec(String(html || ''))) !== null) {
        try { out.push(new URL(lfDecodeEntities(m[1]).trim(), baseUrl).toString()); } catch (_) {}
    }
    return out;
}

// ── DamiTV: API عام موثّق — GET ondemand.st/papi/api/streams ──
// يعيد فئات → بثوث فيها teams وstarts_at وstatus ومصفوفة sources وحقل iframe (صفحة embed).
async function lfFetchDamitv() {
    // البنية الحقيقية للـ API (تم التحقق منها): { streams: [ {category, streams: [event]} ] }
    // الفئات: football/cricket/basketball/... + فئة "24/7-streams" للقنوات.
    // الحدث: {name, starts_at (epoch), status, league, teams:{home:{name},away:{name}},
    //          always_live (1=قناة 24/7), sources:[{name:"Server 1", embed}], embed}
    // نأخذ فئة football فقط، ونستبعد القنوات (always_live=1) وأي عنصر بلا فريقين —
    // ولا ندخل أبداً داخل sources[] (أسماؤها "Server 1"... ليست مباريات).
    const data = await lfGet('https://ondemand.st/papi/api/streams', 25000);
    const groups = (data && Array.isArray(data.streams)) ? data.streams : [];
    const out = [];
    for (const group of groups) {
        const cat = String((group && (group.category || group.category_name)) || '').toLowerCase();
        if (cat !== 'football' && cat !== 'soccer') continue;
        const events = Array.isArray(group.streams) ? group.streams : [];
        for (const ev of events) {
            if (!ev || typeof ev !== 'object') continue;
            if (ev.always_live === 1 || ev.always_live === true) continue; // قناة 24/7
            const home = ev.teams && ev.teams.home && ev.teams.home.name ? String(ev.teams.home.name).trim() : '';
            const away = ev.teams && ev.teams.away && ev.teams.away.name ? String(ev.teams.away.name).trim() : '';
            const title = (home && away) ? `${home} vs ${away}` : String(ev.name || '').trim();
            if (!title || !/\bvs\b|\bv\b/i.test(title)) continue; // بلا "فريق ضد فريق" = ليست مباراة
            const embed = ev.embed || (Array.isArray(ev.sources) && ev.sources[0] && ev.sources[0].embed) || null;
            if (!embed) continue;
            let startsAt = null;
            const ts = typeof ev.starts_at === 'number' ? ev.starts_at : parseInt(ev.starts_at);
            if (ts && ts > 0) {
                const d = new Date(ts * 1000);
                startsAt = d.toISOString().slice(0, 16).replace('T', ' ') + ' UTC';
            }
            out.push({
                title,
                source: 'DamiTV',
                pageUrl: String(embed),
                status: ev.status || null,
                startsAt,
                startsAtTs: (ts && ts > 0) ? ts : null,
                endsAtTs: (typeof ev.ends_at === 'number' && ev.ends_at > 0) ? ev.ends_at : (parseInt(ev.ends_at) > 0 ? parseInt(ev.ends_at) : null),
                league: ev.league || null
            });
        }
    }
    const seen = new Set();
    return out.filter(x => !seen.has(x.pageUrl) && seen.add(x.pageUrl)).slice(0, 40);
}

// ── DaddyLive (DLHD): الصفحة الرئيسية = جدول أحداث + قنوات ──
// صفحات المشغّل على نمط /{stream|watch|player|cast}/stream-{id}.php
async function lfFetchDaddyLive() {
    let html = null, base = null;
    // dlive.sx قد لا يُحلّ DNS في بعض الشبكات، وdaddylive.pk مجرد دليل مرايا —
    // المرايا الفعلية الحاملة للجدول: dlhd.pk وdlhd.st (تم التحقق من dlhd.pk حياً)
    for (const cand of ['https://dlive.sx/', 'https://dlhd.pk/', 'https://dlhd.st/', 'https://daddylive.pk/']) {
        try { html = await lfGet(cand, 25000); base = cand; break; } catch (_) {}
    }
    if (!html) throw new Error('تعذر الوصول إلى DaddyLive');
    // نمط مرايا dlhd الحالي: المباريات داخل كتل schedule__event (عنوان + وقت + روابط قنوات watch.php)،
    // وروابط stream-N.php في الصفحة هي قنوات 24/7 فقط — لا تدخل قائمة المباريات أبداً
    const sched = lfParseDaddySchedule(html, base);
    if (sched.length) return sched;
    // النمط القديم (dlive.sx): روابط stream-N.php قد تحمل مباريات — نقبل فقط ما يدل عنوانه
    // على مباراة (ضد/وقت)، وإن لم يوجد دليل نعيد قائمة فارغة بدل تسريب القنوات
    const all = lfParseAnchors(html, base)
        .filter(a => /stream-\d+\.php/i.test(a.url))
        .map(a => ({ title: a.title, source: 'DaddyLive', pageUrl: a.url, status: null, startsAt: null }));
    return all.filter(x => /\bvs\b|\bv\b/i.test(x.title) || /\d{1,2}:\d{2}/.test(x.title)).slice(0, 40);
}

// قراءة كتل جدول dlhd: كل كتلة فيها data-title (فيه ⚽ لكرة القدم والوقت)،
// وعنوان الحدث، وأول رابط قناة watch.php?id=N هو صفحة تشغيل المباراة
function lfParseDaddySchedule(html, base) {
    const out = [];
    const seen = new Set();
    const parts = String(html).split('<div class="schedule__event">').slice(1);
    for (const part of parts) {
        const chunk = part.slice(0, 3000);
        const dtM = chunk.match(/data-title="([^"]+)"/i);
        const dataTitle = dtM ? lfDecodeEntities(dtM[1]) : '';
        const tM = chunk.match(/schedule__eventTitle">([^<]+)</i);
        const title = tM ? lfDecodeEntities(tM[1]).replace(/\s+/g, ' ').trim() : '';
        if (!title || !/\bvs\b/i.test(title)) continue; // مباريات فقط (فريق ضد فريق)
        if (!/⚽|soccer|football/i.test(dataTitle + ' ' + title)) continue; // كرة قدم فقط
        const linkM = chunk.match(/href="([^"]*watch\.php\?id=\d+)"/i);
        if (!linkM) continue;
        let pageUrl;
        try { pageUrl = new URL(lfDecodeEntities(linkM[1]), base).toString(); } catch (_) { continue; }
        const timeM = chunk.match(/schedule__time"[^>]*>([^<]+)</i);
        const startsAt = timeM ? `${timeM[1].trim()} UK` : null;
        const k = footballNorm(title);
        if (seen.has(k)) continue;
        seen.add(k);
        out.push({ title, source: 'DaddyLive', pageUrl, status: null, startsAt });
        if (out.length >= 40) break;
    }
    return out;
}

// ── PPV.ST: روابط أحداث حية على نمط /live/{sport}/{date}/{slug} ──
async function lfFetchPpv() {
    const html = await lfGet('https://ppv.st/', 25000);
    return lfParseAnchors(html, 'https://ppv.st/')
        .filter(a => {
            // النمط الموثق: /live/football/{date}/{slug}
            if (/\/live\/(football|soccer)\//i.test(a.url)) return true;
            // فحص حي (2026-11-09): بطاقات القنوات على نمط /live/<slug>، ولم يمكن تأكيد
            // نمط روابط بطاقات الأحداث المؤرخة — نقبل /live/<slug> أيضاً بشرط أن يدل
            // العنوان على مباراة (ضد/عند)، حتى لا تتسرب قنوات 24/7
            if (/\/live\/[a-z0-9][a-z0-9-]*\/?$/i.test(new URL(a.url).pathname) && /\bvs\.?\b|\bat\b/i.test(a.title)) return true;
            return false;
        })
        .map(a => ({ title: a.title, source: 'PPV.ST', pageUrl: a.url, status: null, startsAt: null }))
        .slice(0, 40);
}

// ── جالب عام لصفحات أحداث/كرة قدم عند مجمّعات أخرى ──
// تنظيفات مبنية على مخرجات حقيقية: روابط التنقل بين الأقسام ("Football"، "Soccer"،
// "Formula 1"، "YouTube")، روابط لمواقع خارجية، ونصوص قوالب JS غير مُنفّذة
// (مثل "${escapeHtml(stream.name)}" عند StreamFree) — كلها ليست مباريات.
// القاعدة: روابط من نفس نطاق الصفحة فقط + تفضيل (أو اشتراط عند strict)
// عناوين تدل على مباراة: "فريق vs فريق" أو وقت/تاريخ انطلاق.
async function lfFetchGeneric(sourceName, pageUrl, hrefFilter, opts = {}) {
    const html = await lfGet(pageUrl, 25000);
    const pageHost = new URL(pageUrl).hostname;
    let items = lfParseAnchors(html, pageUrl)
        .filter(a => { try { return new URL(a.url).hostname === pageHost; } catch (_) { return false; } })
        .filter(a => hrefFilter(a))
        .filter(a => !a.title.includes('${') && !/escapeHtml/i.test(a.title))
        .map(a => ({ title: a.title, source: sourceName, pageUrl: a.url, status: null, startsAt: null }));
    const evidence = items.filter(x => /\bvs\b|\bv\b/i.test(x.title) || /\d{1,2}:\d{2}/.test(x.title) || /\d{1,2}\/\d{1,2}/.test(x.title));
    if (evidence.length) items = evidence;
    else if (opts.strict) items = [];
    return items.slice(0, 40);
}

const LF_FETCHERS = [
    lfFetchDamitv,
    lfFetchDaddyLive,
    lfFetchPpv,
    () => lfFetchGeneric('SportsBite', 'https://sportsbite.org/sport/football', a => /football|soccer|match|watch|stream/i.test(a.url)),
    // صفحات الأقسام نفسها (.html) روابط تنقل وليست مباريات — نأخذ روابط الأحداث فقط، وبصرامة
    () => lfFetchGeneric('FCTV33', 'https://www.fctv33go.autos/football.html', a => !/\.html?$/i.test(new URL(a.url).pathname), { strict: true }),
    () => lfFetchGeneric('WatchSports', 'https://watchsports.su/', a => /\/football\//i.test(a.url)),
    () => lfFetchGeneric('RoxieStreams', 'https://roxiestreams.su/', a => /football|soccer/i.test(a.title + ' ' + a.url), { strict: true }),
    () => lfFetchGeneric('StreamFree', 'https://strmfree.pk/', a => /football|soccer|match|live|watch/i.test(a.title + ' ' + a.url), { strict: true }),
    () => lfFetchGeneric('TheTVApp', 'https://thetvapp.plus/', a => /soccer|football/i.test(a.title + ' ' + a.url), { strict: true }),
];

// جلب أحداث كل المصادر التلقائية بالتوازي — فشل مصدر لا يوقف الباقي
async function lfFetchAllEvents() {
    const results = await Promise.allSettled(LF_FETCHERS.map(f => f()));
    const all = [];
    const failed = [];
    results.forEach((r, i) => {
        if (r.status === 'fulfilled') all.push(...r.value);
        else failed.push(LF_SOURCES[i] ? LF_SOURCES[i].name : `مصدر ${i + 1}`);
    });
    const seen = new Set();
    const LF_NAV_TITLES = new Set(['football', 'soccer', 'american football', 'am football', 'formula 1', 'f1', 'youtube', 'home', 'live', 'live football', 'live soccer', 'basketball', 'hockey', 'tennis', 'cricket']);
    const deduped = all.filter(x => {
        if (!x.title || /^server\s*\d+$/i.test(x.title.trim())) return false; // أسماء سيرفرات ليست مباريات
        if (x.title.includes('${') || /escapeHtml/i.test(x.title)) return false; // نص قالب JS غير مُنفّذ
        if (LF_NAV_TITLES.has(footballNorm(x.title))) return false; // روابط تنقل بين الأقسام
        const k = footballNorm(x.title) + '|' + x.source;
        if (seen.has(k)) return false;
        seen.add(k); return true;
    });
    // خلط المصادر بالتناوب حتى لا يحتكر أول مصدر القائمة كلها ويحجب الباقي
    const bySource = new Map();
    for (const mt of deduped) {
        if (!bySource.has(mt.source)) bySource.set(mt.source, []);
        bySource.get(mt.source).push(mt);
    }
    const queues = [...bySource.values()];
    const mixed = [];
    let progressed = true;
    while (mixed.length < 30 && progressed) {
        progressed = false;
        for (const q of queues) {
            if (q.length) { mixed.push(q.shift()); progressed = true; if (mixed.length >= 30) break; }
        }
    }
    return { matches: mixed, failed };
}

// ── استخراج رابط البث الفعلي (m3u8) من صفحة مباراة/مشغّل ──
// يتبع iframes حتى مستويين، ويعيد الهيدرات اللازمة (Referer/Origin/User-Agent).
async function lfResolveStream(pageUrl) {
    if (isHlsUrl(pageUrl)) {
        return { streamUrl: pageUrl, headers: { 'User-Agent': LF_UA, Referer: pageUrl } };
    }
    // يتبع iframes وملفات JavaScript (بعض المشغلات تضع رابط m3u8 داخل ملف JS
    // أو بروابط مهربّة \/ داخل كود الصفحة) — حتى مستويين وبحد أقصى للزيارات.
    const queue = [{ url: pageUrl, depth: 0, kind: 'page', via: pageUrl }];
    const visited = new Set();
    while (queue.length && visited.size < 20) {
        const { url, depth, kind, via } = queue.shift();
        if (visited.has(url)) continue;
        visited.add(url);
        let body;
        try { body = await lfGet(url, 25000); } catch (_) { continue; }
        if (typeof body !== 'string') continue;
        const text = body.replace(/\\\//g, '/');
        // مشغّل مختوم (نمط dembed): الصفحة تحمل ثوابت SRC/CHANNEL/EDGE/TICKET
        // وقائمتها مشفّرة ومقاطعها مخبأة داخل صور — تُفكّ وقت التسجيل عبر بروكسي محلي
        const sealed = lfDembedInfo(text, url);
        if (sealed) {
            let origin = '';
            try { origin = new URL(url).origin; } catch (_) {}
            return { streamUrl: sealed.src, headers: { 'User-Agent': LF_UA, Referer: url, ...(origin ? { Origin: origin } : {}) }, sealedInfo: sealed };
        }
        const direct = lfExtractM3u8(text, url);
        if (direct) {
            // الـ Referer هو صفحة المشغّل التي وُجد فيها الرابط (أو الصفحة التي ضمّنت ملف JS)
            const referer = kind === 'js' ? (via || pageUrl) : url;
            let origin = '';
            try { origin = new URL(referer).origin; } catch (_) {}
            return { streamUrl: direct, headers: { 'User-Agent': LF_UA, Referer: referer, ...(origin ? { Origin: origin } : {}) } };
        }
        if (kind === 'page' && depth < 2) {
            let iframeCount = 0;
            for (const f of lfIframeSrcs(text, url)) {
                if (/player|embed|stream|watch|cast/i.test(f) || isHlsUrl(f)) { queue.push({ url: f, depth: depth + 1, kind: 'page', via: url }); iframeCount++; }
            }
            const scriptRe = /<script\s[^>]*src\s*=\s*["']([^"']+)["']/gi;
            let sm;
            while ((sm = scriptRe.exec(text)) !== null) {
                try {
                    const su = new URL(lfDecodeEntities(sm[1]).trim(), url).toString();
                    if (/\.js($|\?)/i.test(su)) queue.push({ url: su, depth: depth + 1, kind: 'js', via: url });
                } catch (_) {}
            }
            // صفحات مجمّعات بلا مشغّل خاص (مثل WatchSports): البث خلف روابط خارجية
            // لمضيفات مشغلات — نتبع أول مرشحين خارجيين (باستبعاد التواصل الاجتماعي والإعلانات الشائعة)
            if (depth === 0 && iframeCount === 0) {
                const hrefRe = /href\s*=\s*["'](https?:\/\/[^"']+)["']/gi;
                const seenCand = new Set();
                let candidates = 0;
                let hm;
                while ((hm = hrefRe.exec(text)) !== null && candidates < 5) {
                    const cand = lfDecodeEntities(hm[1]).trim();
                    if (seenCand.has(cand)) continue;
                    seenCand.add(cand);
                    try {
                        const cu = new URL(cand);
                        const pageU = new URL(url);
                        if (cu.host === pageU.host) continue;
                        if (/facebook|twitter|x\.com|telegram|whatsapp|instagram|youtube|tiktok|doubleclick|googlesyndication|adservice/i.test(cand)) continue;
                        queue.push({ url: cand, depth: depth + 1, kind: 'page', via: url });
                        candidates++;
                    } catch (_) {}
                }
            }
        }
    }
    throw new Error('لم يتم العثور على رابط بث (m3u8) داخل صفحة المباراة. إن كانت المباراة لم تبدأ بعد فالبث غير موجود أصلاً — أعد المحاولة عند انطلاقها، أو جرّب مصدراً آخر.');
}

function lfHeadersString(headers) {
    return Object.entries(headers || {})
        .filter(([k, v]) => v !== undefined && v !== null && !/^:/.test(k))
        .map(([k, v]) => `${k}: ${v}`).join('\r\n');
}

// ── جودات البث من قائمة m3u8 رئيسية (Master Playlist) ──
// يعيد [{height, bandwidth, url}] مرتبة تصاعدياً، أو [] إن لم تكن القائمة رئيسية.
async function lfFetchVariants(streamUrl, headers) {
    try {
        const res = await axios.get(streamUrl, {
            headers: { 'User-Agent': LF_UA, ...(headers || {}) },
            timeout: 20000, responseType: 'text', validateStatus: s => s >= 200 && s < 400
        });
        const text = String(res.data || '');
        if (!/#EXT-X-STREAM-INF/.test(text)) return [];
        const lines = text.split(/\r?\n/);
        const variants = [];
        for (let i = 0; i < lines.length; i++) {
            if (!lines[i].startsWith('#EXT-X-STREAM-INF')) continue;
            const resM = lines[i].match(/RESOLUTION=(\d+)x(\d+)/i);
            const bwM = lines[i].match(/BANDWIDTH=(\d+)/i);
            let uri = null;
            for (let j = i + 1; j < lines.length; j++) {
                const l = lines[j].trim();
                if (!l) continue;
                if (l.startsWith('#')) break;
                uri = l; break;
            }
            if (!uri) continue;
            let abs;
            try { abs = new URL(uri, streamUrl).toString(); } catch (_) { continue; }
            variants.push({
                height: resM ? parseInt(resM[2]) : 0,
                width: resM ? parseInt(resM[1]) : 0,
                bandwidth: bwM ? parseInt(bwM[1]) : 0,
                url: abs
            });
        }
        variants.sort((a, b) => (a.height - b.height) || (a.bandwidth - b.bandwidth));
        return variants;
    } catch (_) { return []; }
}

// اختيار أقرب جودة مطلوبة: الأعلى التي لا تتجاوز المطلوب، وإلا الأقرب فوقه
function lfPickVariant(variants, qualityHeight) {
    if (!variants || !variants.length) return null;
    const sorted = [...variants].sort((a, b) => a.height - b.height);
    let best = null;
    for (const v of sorted) if (v.height && v.height <= qualityHeight) best = v;
    if (best) return best;
    return sorted.find(v => v.height >= qualityHeight) || sorted[sorted.length - 1];
}

// طلبات .livefootball بانتظار اختيار الجودة بالرد (Reply) — مثل qualityCache
const liveFootballQualityCache = new Map(); // sentMsgId -> job

// بدء التسجيل الفعلي — نفس منطق .record (فحص بت، أجزاء ~100MB، إعادة اتصال مع إعادة استخراج)
async function lfStartRecording(XeonBotInc, chatId, mek, job) {
    const recMap = job.isChannel ? activeLiveChannelRecordings : activeLiveFootballRecordings;
    const stopCmd = job.isChannel ? '.stoplivechannel' : '.stoplivefootball';
    const kindWord = job.isChannel ? 'القناة' : 'المباراة';
    if (recMap.has(chatId)) {
        await XeonBotInc.sendMessage(chatId, {
            text: `⚠️ يوجد تسجيل ${job.isChannel ? 'قناة' : 'مباراة'} نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`${stopCmd}\` قبل بدء تسجيل جديد.`
        }, { quoted: mek });
        return;
    }

    // بث مختوم: شغّل البروكسي المحلي الذي يفك القائمة والمقاطع لـ ffmpeg
    if (job.sealedInfo && !job.proxy) {
        try {
            job.proxy = await lfStartSealedProxy(job.sealedInfo);
            job.streamUrl = job.proxy.url;
            job.headers = {};
            console.log('[LIVEFOOTBALL] sealed proxy started: ' + job.proxy.url);
        } catch (e) {
            await XeonBotInc.sendMessage(chatId, {
                text: `❌ تعذر تجهيز فك ختم البث: ${e.message}`
            }, { quoted: mek });
            return;
        }
    }

    const duration = job.duration;
    const manualSegmentMinutes = job.manualSegmentMinutes;
    const totalDurationSec = duration * 60;

    const tmpDir = path.join(process.cwd(), 'dltmp');
    if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

    let segmentTimeSec;
    let segmentMinutes;
    let bitrateNote = '';

    if (manualSegmentMinutes !== null && manualSegmentMinutes !== undefined) {
        segmentMinutes = manualSegmentMinutes;
        segmentTimeSec = manualSegmentMinutes * 60;
    } else {
        await XeonBotInc.sendMessage(chatId, {
            text: `🔍 جاري فحص معدل بت البث لتقدير حجم الجزء بدقة (~${RECORD_TARGET_MB} MB)...`
        }, { quoted: mek });

        const bitrate = await probeStreamBitrate(job.streamUrl, lfHeadersString(job.headers));
        segmentTimeSec = computeSegmentTimeSec(bitrate);
        segmentMinutes = Math.round(segmentTimeSec / 60);

        bitrateNote = bitrate
            ? `\n📊 معدل البت المُقاس: ~${(bitrate / 1000000).toFixed(2)} Mbps`
            : `\n⚠️ تعذر قياس معدل البت، تم استخدام تقدير احتياطي (${RECORD_DEFAULT_SEGMENT_MIN} دقائق)`;
    }

    const segDir = path.join(tmpDir, `livefb_${Date.now()}`);
    fs.mkdirSync(segDir, { recursive: true });

    const qualityNote = job.qualityLabel ? `\n🎞️ الجودة: *${job.qualityLabel}*` : '';

    // اطبع رابط البث نفسه ليتمكن المستخدم من تشغيله مباشرة بالتوازي مع التسجيل
    // (البث المختوم لا يُطبع رابطه الخام — لا يعمل خارج البوت)
    if (!job.sealedInfo) {
        try {
            await XeonBotInc.sendMessage(chatId, {
                text: `🔗 *رابط البث الجاري تسجيله (للتشغيل المباشر):*\n${job.streamUrl}`
            }, { quoted: mek });
        } catch (_) {}
    }
    await XeonBotInc.sendMessage(chatId, {
        text: `🎙️ *بدأ تسجيل ${kindWord} المباشرة!*\n⚽ ${job.title}\n📡 المصدر: ${job.source}${qualityNote}\n⏱️ المدة الكلية: *${duration} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${RECORD_TARGET_MB} MB)${bitrateNote}\n🔗 اتصال واحد متواصل بالبث — بدون أي انقطاع بين الأجزاء\n\n🛑 لإلغاء التسجيل في أي وقت: \`${stopCmd}\``
    }, { quoted: mek });

    const control = { proc: null, cancelled: false, streamHeaders: lfHeadersString(job.headers) };
    recMap.set(chatId, control);

    const MAX_RECONNECT_ATTEMPTS = 15;

    (async () => {
        let segmentIndex = 0;
        let abortedBySize = false;
        let wasCancelled = false;
        let remainingSec = totalDurationSec;
        let attempt = 0;
        let reconnectedCount = 0;
        let curStreamUrl = job.streamUrl;

        const onSegmentReady = async (filePath) => {
            segmentIndex++;
            try {
                const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
                await XeonBotInc.sendMessage(chatId, {
                    document: { url: filePath },
                    mimetype: 'video/mp4',
                    fileName: `LiveFootball_part${segmentIndex}.mp4`,
                    caption: `📦 *الجزء ${segmentIndex}*\n⚽ ${job.title}\n📡 ${job.source}${job.qualityLabel ? `\n🎞️ ${job.qualityLabel}` : ''}\n⚖️ ${sizeMB} MB`
                }, { quoted: mek });
            } catch (e) {
                await XeonBotInc.sendMessage(chatId, {
                    text: `⚠️ فشل إرسال الجزء ${segmentIndex}: ${e.message}`
                }, { quoted: mek });
            } finally {
                try { fs.unlinkSync(filePath); } catch (_) {}
            }
        };

        try {
            while (remainingSec > 60 && attempt < MAX_RECONNECT_ATTEMPTS && !control.cancelled) {
                attempt++;
                const startTs = Date.now();

                // إعادة استخراج الرابط عند كل إعادة اتصال (التوكنات قصيرة العمر)، مع إعادة اختيار نفس الجودة
                // (البث المختوم يُستثنى: بروكسيه المحلي يجدّد التوكن والتيكيت بنفسه)
                if (attempt > 1 && job.pageUrl && !isHlsUrl(job.pageUrl) && !job.sealedInfo) {
                    try {
                        const re = await lfResolveStream(job.pageUrl);
                        job.headers = re.headers;
                        control.streamHeaders = lfHeadersString(re.headers);
                        if (job.qualityHeight) {
                            const vs = await lfFetchVariants(re.streamUrl, re.headers);
                            const picked = lfPickVariant(vs, job.qualityHeight);
                            curStreamUrl = picked ? picked.url : re.streamUrl;
                        } else {
                            curStreamUrl = re.streamUrl;
                        }
                        console.log('[LIVEFOOTBALL] stream re-resolved for reconnect attempt ' + attempt);
                    } catch (e) {
                        console.log('[LIVEFOOTBALL] re-resolve failed: ' + e.message);
                    }
                }

                const result = await recordContinuousSegmented(
                    curStreamUrl, segDir, `part_a${attempt}`, remainingSec, segmentTimeSec,
                    onSegmentReady, control
                );

                const elapsedSec = Math.floor((Date.now() - startTs) / 1000);
                remainingSec -= elapsedSec;

                abortedBySize = result.abortedBySize;
                wasCancelled = result.cancelled;

                if (wasCancelled || abortedBySize) break;
                if (remainingSec <= 60) break;

                reconnectedCount++;
                const backoffMs = Math.min(3000 * Math.pow(2, Math.min(reconnectedCount - 1, 5)), 60000);
                await XeonBotInc.sendMessage(chatId, {
                    text: `⚠️ *انقطع الاتصال بالبث بشكل غير متوقع.*\n⏱️ الوقت المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🔄 جاري إعادة الاتصال (وإعادة استخراج الرابط) بعد ${Math.round(backoffMs / 1000)} ثانية... (محاولة ${attempt + 1}/${MAX_RECONNECT_ATTEMPTS})`
                }, { quoted: mek });
                await new Promise(r => setTimeout(r, backoffMs));
            }

            if (!wasCancelled && !abortedBySize && attempt >= MAX_RECONNECT_ATTEMPTS && remainingSec > 60) {
                await XeonBotInc.sendMessage(chatId, {
                    text: `❌ تعذر إكمال التسجيل بعد ${MAX_RECONNECT_ATTEMPTS} محاولات إعادة اتصال. قد يكون مصدر البث غير مستقر حالياً — جرّب مصدراً آخر من القائمة.`
                }, { quoted: mek });
            }
        } catch (err) {
            await XeonBotInc.sendMessage(chatId, {
                text: `❌ خطأ في التسجيل: ${err.message}`
            }, { quoted: mek });
        } finally {
            recMap.delete(chatId);
            if (job.proxy) { try { job.proxy.close(); } catch (_) {} job.proxy = null; }
            try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
        }

        if (wasCancelled) {
            await XeonBotInc.sendMessage(chatId, {
                text: `🛑 *تم إلغاء تسجيل ${kindWord} بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${segmentIndex}`
            }, { quoted: mek });
        } else if (abortedBySize) {
            await XeonBotInc.sendMessage(chatId, {
                text: `🛑 *تم إيقاف التسجيل مبكراً!*\nجودة البث كانت أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن للتخزين المتاح.\n📦 عدد الأجزاء المُرسلة قبل التوقف: ${segmentIndex}\n\n💡 جرّب تقليل مدة الجزء أو اختيار جودة أقل في المرة القادمة.`
            }, { quoted: mek });
        } else {
            const reconnectNote = reconnectedCount > 0 ? `\n🔄 حدثت ${reconnectedCount} إعادة اتصال بسبب انقطاعات مؤقتة في البث.` : '';
            await XeonBotInc.sendMessage(chatId, {
                text: `✅ *اكتمل تسجيل ${kindWord}!*\n⚽ ${job.title}\n📦 عدد الأجزاء المُرسلة: ${segmentIndex}${reconnectNote}`
            }, { quoted: mek });
        }
    })();
}

// بوابة بدء التسجيل مع اختيار الجودة:
// - جودة محددة صراحة (720p) → اختيارها مباشرة.
// - عدة جودات وبدون تحديد → إرسال قائمة والانتظار رداً برقم (liveFootballQualityCache).
// - جودة واحدة أو لا قائمة رئيسية → البدء كما هي.
// خطوات تفاعلية بعد اختيار البث والجودة: نسأل عن مدة التسجيل ثم عن دقائق الجزء،
// وكل خطوة تُتخطى إن كانت القيمة معطاة أصلاً في الأمر (مثال: .livefootball 1 100 1)
async function lfWizardNext(XeonBotInc, chatId, mek, job) {
    // وضع الرابط فقط: اطبع رابط البث للتشغيل المباشر ولا تسجّل شيئاً
    if (job.linkOnly) {
        if (job.sealedInfo) {
            await XeonBotInc.sendMessage(chatId, {
                text: `🔒 *${job.title}*\n📡 ${job.source}\n\nهذا البث *مختوم*: رابطه الخام لا يعمل في المشغّلات الخارجية لأنه مشفّر ومقاطعه مخبأة — يعمل فقط عبر التسجيل من البوت نفسه.\n▶️ سجّله بنفس الأمر بدون كلمة \`link\` وستصلك الأجزاء هنا مباشرة.`
            }, { quoted: mek });
            return;
        }
        const q = job.qualityLabel || 'الافتراضية';
        await XeonBotInc.sendMessage(chatId, {
            text: `🔗 *رابط البث المباشر — ${job.title}*\n📡 ${job.source} • الجودة: ${q}\n\n${job.streamUrl}\n\n▶️ انسخ الرابط وشغّله في أي مشغّل (VLC أو مشغّل IPTV أو المتصفح). إن توقّف لاحقاً فتوكن هذه المصادر قصير العمر — أعد طلبه بنفس الأمر.`
        }, { quoted: mek });
        return;
    }
    if (job.duration === null || job.duration === undefined) {
        const sent = await XeonBotInc.sendMessage(chatId, {
            text: `⏱️ *كم دقيقة تريد أن أسجّل؟*\n⚽ ${job.title}\n\n💡 رد (Reply) على هذه الرسالة بعدد الدقائق (1 - 360). مثال: 100`
        }, { quoted: mek });
        liveFootballQualityCache.set(sent.key.id, { ...job, stage: 'duration' });
        setTimeout(() => liveFootballQualityCache.delete(sent.key.id), 300000);
        return;
    }
    if (!job.segDecided) {
        const sent = await XeonBotInc.sendMessage(chatId, {
            text: `📦 *كل كم دقيقة أبعث لك جزءاً من التسجيل؟*\n\n💡 رد (Reply) على هذه الرسالة بعدد الدقائق (1 - ${job.duration}). مثال: 1 تعني أن يصلك جزء جديد كل دقيقة.\nℹ️ أو رد بـ 0 للتقطيع التلقائي (~${RECORD_TARGET_MB} MB للجزء).`
        }, { quoted: mek });
        liveFootballQualityCache.set(sent.key.id, { ...job, stage: 'segment' });
        setTimeout(() => liveFootballQualityCache.delete(sent.key.id), 300000);
        return;
    }
    await lfStartRecording(XeonBotInc, chatId, mek, job);
}

async function lfBeginRecording(XeonBotInc, chatId, mek, job) {
    // بث مختوم: لا قائمة جودات — جودة واحدة أصلية تُفكّ عبر البروكسي المحلي وقت التسجيل
    if (job.sealedInfo) {
        job.qualityLabel = job.qualityLabel || 'الأصلية';
        await lfWizardNext(XeonBotInc, chatId, mek, job);
        return;
    }
    const variants = await lfFetchVariants(job.streamUrl, job.headers);

    if (variants.length > 1) {
        if (job.requestedQuality) {
            const picked = lfPickVariant(variants, job.requestedQuality);
            if (picked) {
                job.streamUrl = picked.url;
                job.qualityHeight = picked.height;
                job.qualityLabel = picked.height ? `${picked.height}p` : 'غير معروفة';
            }
            await lfWizardNext(XeonBotInc, chatId, mek, job);
            return;
        }

        let qText = `🎞️ *اختر جودة التسجيل:*\n⚽ ${job.title}\n📡 ${job.source}\n\n`;
        variants.forEach((v, i) => {
            const bw = v.bandwidth ? ` — ~${(v.bandwidth / 1000000).toFixed(1)} Mbps` : '';
            qText += `*${i + 1}.* ${v.height ? v.height + 'p' : 'جودة ' + (i + 1)}${v.width && v.height ? ` (${v.width}x${v.height})` : ''}${bw}\n`;
        });
        qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة خلال 5 دقائق، وبعدها سأسألك عن مدة التسجيل ودقائق كل جزء.`;
        const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
        liveFootballQualityCache.set(sentQ.key.id, { ...job, variants, stage: 'quality' });
        setTimeout(() => liveFootballQualityCache.delete(sentQ.key.id), 300000);
        return;
    }

    if (variants.length === 1) {
        job.streamUrl = variants[0].url;
        job.qualityHeight = variants[0].height || null;
        job.qualityLabel = variants[0].height ? `${variants[0].height}p (المتاحة فقط)` : null;
    }
    await lfWizardNext(XeonBotInc, chatId, mek, job);
}
// ===== 📺 قنوات 24/7 (.livechannel) — من كل المواقع ذات القنوات، لا موقع واحد =====
const liveChannelLists = new Map(); // chatId -> { channels, at }

async function lfFetchDamitvChannels() {
    const res = await axios.get('https://ondemand.st/papi/api/streams', {
        timeout: 20000,
        headers: { 'User-Agent': LF_UA, 'Accept': 'application/json,*/*' }
    });
    const cats = (res.data && Array.isArray(res.data.streams)) ? res.data.streams : [];
    const out = [];
    const seen = new Set();
    for (const cat of cats) {
        for (const ev of (cat.streams || [])) {
            const is247 = /24\/7/i.test(cat.category || '') || ev.always_live === 1 || ev.always_live === '1';
            if (!is247) continue;
            const embed = ev.embed || (Array.isArray(ev.sources) && ev.sources[0] && ev.sources[0].embed);
            const name = ev.name || null;
            if (!embed || !name) continue;
            const k = footballNorm(name);
            if (seen.has(k)) continue;
            seen.add(k);
            out.push({ title: name, source: 'DamiTV', pageUrl: embed, status: 'live', startsAt: null });
        }
    }
    return out.slice(0, 60);
}

async function lfFetchDaddyChannels() {
    let html = null, base = null;
    for (const cand of ['https://dlive.sx/', 'https://dlhd.pk/', 'https://dlhd.st/', 'https://daddylive.pk/']) {
        try { html = await lfGet(cand, 25000); base = cand; break; } catch (_) {}
    }
    if (!html) throw new Error('تعذر الوصول إلى DaddyLive');
    const map = new Map();
    // نمط 1: صفحات قنوات stream-N.php من شبكة القنوات
    for (const a of lfParseAnchors(html, base)) {
        if (/stream-\d+\.php/i.test(a.url)) {
            const name = (a.title.split('|')[0] || a.title).replace(/^watch\s+/i, '').replace(/\s+live\s+streams?$/i, '').trim() || a.title;
            if (!map.has(a.url)) map.set(a.url, { title: name, source: 'DaddyLive', pageUrl: a.url, status: 'live', startsAt: null });
        }
    }
    // نمط 2: روابط قنوات الجدول watch.php?id=N (اسم القناة من خاصية title)
    const re = /<a[^>]+href\s*=\s*["']([^"']*watch\.php\?id=\d+)["'][^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const tm = m[0].match(/title\s*=\s*["']([^"']+)["']/i);
        const name = tm ? lfDecodeEntities(tm[1]).trim() : '';
        if (!name) continue;
        let u;
        try { u = new URL(lfDecodeEntities(m[1]), base).toString(); } catch (_) { continue; }
        if (!map.has(u)) map.set(u, { title: name, source: 'DaddyLive', pageUrl: u, status: 'live', startsAt: null });
    }
    // إزالة تكرار الاسم نفسه (القناة الواحدة قد تظهر في الجدول والدليل معاً)،
    // وترتيب أبجدي حتى يجد المستخدم أي قناة بالبحث — بلا قصّ مبكر يخفي قنوات الدليل
    const byTitle = new Map();
    for (const ch of map.values()) {
        const k = footballNorm(ch.title);
        if (!byTitle.has(k)) byTitle.set(k, ch);
    }
    return [...byTitle.values()]
        .sort((a, b) => a.title.localeCompare(b.title))
        .slice(0, 300);
}

// اكتشاف عام للقنوات عند أي موقع آخر: روابط تبدو كقنوات، وعنوانها اسم قناة
// (بلا "ضد" وبلا وقت/تاريخ مباراة وبلا روابط تنقل)
async function lfFetchGenericChannels(sourceName, homeUrl) {
    const html = await lfGet(homeUrl, 20000);
    const anchors = lfParseAnchors(html, homeUrl);
    const NAV = new Set(['home', 'live', 'football', 'soccer', 'channels', 'tv', 'sports', 'schedule', 'contact', 'dmca', 'privacy policy', 'terms', 'login', 'register', 'sign up', 'multiview', 'vip', 'archive', 'request']);
    let pageHost;
    try { pageHost = new URL(homeUrl).hostname; } catch (_) { return []; }
    const out = [];
    const seen = new Set();
    for (const a of anchors) {
        let u;
        try { u = new URL(a.url); } catch (_) { continue; }
        if (u.hostname !== pageHost) continue;
        const pth = u.pathname + u.search;
        if (!/channel|\/tv\/|watch\.php|stream-\d+\.php|\/live\/[a-z0-9][a-z0-9-]*\/?$|\/watch\/[a-z0-9-]+$/i.test(pth)) continue;
        const t = a.title.trim();
        if (!t || t.length < 3 || t.length > 60) continue;
        if (NAV.has(footballNorm(t))) continue;
        if (/\bvs\.?\b/i.test(t) || /\d{1,2}:\d{2}/.test(t) || /\d{4}-\d{2}-\d{2}/.test(t)) continue;
        if (t.includes('${') || /escapeHtml/i.test(t)) continue;
        const k = footballNorm(t);
        if (seen.has(k)) continue;
        seen.add(k);
        out.push({ title: t, source: sourceName, pageUrl: a.url, status: 'live', startsAt: null });
        if (out.length >= 30) break;
    }
    return out;
}

const LF_CHANNEL_FETCHERS = [
    { name: 'DamiTV', fn: lfFetchDamitvChannels },
    { name: 'DaddyLive', fn: lfFetchDaddyChannels },
    { name: 'PPV.ST', fn: () => lfFetchGenericChannels('PPV.ST', 'https://ppv.st/') },
    { name: 'TheTVApp', fn: () => lfFetchGenericChannels('TheTVApp', 'https://thetvapp.plus/') },
    { name: 'StreamFree', fn: () => lfFetchGenericChannels('StreamFree', 'https://strmfree.pk/') },
    ...LF_SOURCES.filter(s => !s.auto && s.url).map(s => ({ name: s.name, fn: () => lfFetchGenericChannels(s.name, s.url) })),
];

async function lfFetchAllChannels() {
    const results = await Promise.allSettled(LF_CHANNEL_FETCHERS.map(f => f.fn()));
    const all = [];
    const failed = [];
    results.forEach((r, i) => {
        if (r.status === 'fulfilled') all.push(...r.value);
        else failed.push(LF_CHANNEL_FETCHERS[i].name);
    });
    const seen = new Set();
    const deduped = all.filter(x => {
        if (!x.title || x.title.includes('${')) return false;
        const k = footballNorm(x.title) + '|' + x.source;
        if (seen.has(k)) return false;
        seen.add(k); return true;
    });
    // خلط المصادر بالتناوب حتى لا يحتكر مصدر واحد القائمة
    const bySource = new Map();
    for (const ch of deduped) {
        if (!bySource.has(ch.source)) bySource.set(ch.source, []);
        bySource.get(ch.source).push(ch);
    }
    const queues = [...bySource.values()];
    const mixed = [];
    let added = true;
    while (added && mixed.length < 200) {
        added = false;
        for (const q of queues) {
            if (q.length) { mixed.push(q.shift()); added = true; if (mixed.length >= 60) break; }
        }
    }
    return { channels: mixed, failed };
}
// ── بث مختوم (نمط dembed): قائمة مشفّرة AES-CTR ومقاطع مخبأة داخل صور PNG ──
// الصفحة تحمل: const SRC/CHANNEL/EDGE/TICKET. نقطة التوكن: {EDGE}/api/playlist-token?slug={CHANNEL}&tk={TICKET}
// تعيد {token, k, ttl}. القائمة تُجلب بـ SRC?t={token} ومقاطعها أسطر base64url مشفّرة
// بمفتاح k (AES-CTR بعدّاد = رقم التسلسل في القائمة). كل مقطع ملف "صورة" من TikTok CDN:
// بكسلات PNG (بعد فك فلاترها) تبدأ بـ "TIKTIKPX" + طول BE32 + حمولة gzip فيها الـ TS الحقيقي.
function lfDembedInfo(html, pageUrl) {
    if (typeof html !== 'string') return null;
    const grab = (n) => { const m = html.match(new RegExp('const\\s+' + n + '\\s*=\\s*"([^"]+)"')); return m ? m[1] : null; };
    const src = grab('SRC'), channel = grab('CHANNEL'), edge = grab('EDGE'), ticket = grab('TICKET');
    if (!src || !channel || !edge) return null;
    if (!/\.m3u8/i.test(src)) return null;
    return { src, channel, edge, ticket: ticket || '', pageUrl };
}

function lfB64UrlBytes(s) {
    let b = String(s || '').replace(/-/g, '+').replace(/_/g, '/');
    while (b.length % 4) b += '=';
    return Buffer.from(b, 'base64');
}

// فك ختم قائمة التشغيل: كل سطر مقطع يُفكّ بعدّاد AES-CTR مبني من رقم تسلسل الوسائط
function lfUnsealPlaylist(text, kB64) {
    const crypto = require('crypto');
    const key = lfB64UrlBytes(kB64);
    const algo = key.length === 32 ? 'aes-256-ctr' : key.length === 24 ? 'aes-192-ctr' : 'aes-128-ctr';
    const out = [];
    let seq = 0;
    for (const rawLine of String(text).split('\n')) {
        const line = rawLine.trim();
        if (!line) continue;
        if (line.startsWith('#')) {
            const m = line.match(/^#EXT-X-MEDIA-SEQUENCE:\s*(\d+)/);
            if (m) seq = Number(m[1]);
            out.push(line);
            continue;
        }
        const counter = Buffer.alloc(16);
        counter.writeBigUInt64BE(BigInt(seq), 8);
        const decipher = crypto.createDecipheriv(algo, key, counter);
        const plain = Buffer.concat([decipher.update(lfB64UrlBytes(line)), decipher.final()]);
        out.push(plain.toString('utf8'));
        seq++;
    }
    return out.join('\n');
}

function lfPaeth(a, b, c) {
    const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
    if (pa <= pb && pa <= pc) return a;
    if (pb <= pc) return b;
    return c;
}

// فك بكسلات PNG إلى RGB خام (تجميع IDAT + فك zlib + إزالة فلاتر الصفوف)
function lfPngRGB(buf) {
    const zlib = require('zlib');
    if (!buf || buf.length < 8 || buf[0] !== 0x89 || buf[1] !== 0x50) return null;
    let off = 8, width = 0, height = 0, bitDepth = 0, colorType = 0, interlace = 0;
    const idats = [];
    while (off + 8 <= buf.length) {
        const len = buf.readUInt32BE(off);
        if (len < 0 || off + 12 + len > buf.length + 4) break;
        const type = buf.slice(off + 4, off + 8).toString('latin1');
        const data = buf.slice(off + 8, off + 8 + len);
        if (type === 'IHDR' && data.length >= 13) {
            width = data.readUInt32BE(0); height = data.readUInt32BE(4);
            bitDepth = data[8]; colorType = data[9]; interlace = data[12];
        } else if (type === 'IDAT') idats.push(data);
        else if (type === 'IEND') break;
        off += 12 + len;
    }
    if (!width || !height || bitDepth !== 8 || interlace !== 0 || (colorType !== 2 && colorType !== 6)) return null;
    let raw;
    try { raw = zlib.inflateSync(Buffer.concat(idats)); } catch (_) { return null; }
    const bpp = colorType === 6 ? 4 : 3;
    const rowBytes = width * bpp;
    if (raw.length < height * (rowBytes + 1)) return null;
    const out = Buffer.alloc(width * height * 3);
    let pos = 0, outPos = 0;
    let prevRow = Buffer.alloc(rowBytes);
    for (let y = 0; y < height; y++) {
        const filter = raw[pos++];
        const row = Buffer.from(raw.slice(pos, pos + rowBytes));
        pos += rowBytes;
        for (let i = 0; i < rowBytes; i++) {
            const left = i >= bpp ? row[i - bpp] : 0, up = prevRow[i], upLeft = i >= bpp ? prevRow[i - bpp] : 0;
            if (filter === 1) row[i] = (row[i] + left) & 0xff;
            else if (filter === 2) row[i] = (row[i] + up) & 0xff;
            else if (filter === 3) row[i] = (row[i] + ((left + up) >> 1)) & 0xff;
            else if (filter === 4) row[i] = (row[i] + lfPaeth(left, up, upLeft)) & 0xff;
            else if (filter !== 0) return null;
        }
        if (colorType === 2) { row.copy(out, outPos); outPos += rowBytes; }
        else { for (let i = 0; i < rowBytes; i += 4) { out[outPos++] = row[i]; out[outPos++] = row[i + 1]; out[outPos++] = row[i + 2]; } }
        prevRow = row;
    }
    return out;
}

// استخراج الـ TS الحقيقي من مقطع "صورة": TIKTIKPX في البكسلات، أو TIKTIKRAW/TSGZ، أو TS بعد IEND
function lfUnwrapSegment(buf) {
    const zlib = require('zlib');
    if (!buf || !buf.length) return null;
    if (buf[0] === 0x89 && buf[1] === 0x50) {
        try {
            const rgb = lfPngRGB(buf);
            if (rgb && rgb.length >= 12 && rgb.slice(0, 8).toString('latin1') === 'TIKTIKPX') {
                const L = rgb.readUInt32BE(8);
                const payload = rgb.slice(12, 12 + L);
                if (payload.length >= 2 && payload[0] === 0x1f && payload[1] === 0x8b) {
                    const ts = zlib.gunzipSync(payload);
                    if (ts.length && ts[0] === 0x47) return ts;
                }
            }
        } catch (_) {}
        const iend = buf.indexOf('IEND');
        if (iend >= 0) {
            const after = iend + 8;
            if (buf[after] === 0x47 && buf[after + 188] === 0x47) return buf.slice(after);
        }
    }
    let i = buf.indexOf('TIKTIKRAW');
    if (i >= 0) { const ts = buf.slice(i + 9); if (ts.length && ts[0] === 0x47) return ts; }
    i = buf.indexOf('TIKTIKTSGZ');
    if (i >= 0) { try { const ts = zlib.gunzipSync(buf.slice(i + 10)); if (ts.length && ts[0] === 0x47) return ts; } catch (_) {} }
    for (let s = 0; s + 188 < buf.length; s++) if (buf[s] === 0x47 && buf[s + 188] === 0x47) return buf.slice(s);
    return null;
}

// جلسة بث مختوم: تدير التوكن (يُجدّد قبل انتهائه) وجلب القائمة وفكّها
function lfSealedSession(info) {
    const state = { info: { ...info }, token: null, k: null, tokenExp: 0 };
    const pageHeaders = () => {
        let origin = '';
        try { origin = new URL(state.info.pageUrl).origin; } catch (_) {}
        return { 'User-Agent': LF_UA, Referer: state.info.pageUrl, ...(origin ? { Origin: origin } : {}) };
    };
    async function refreshPage() {
        const html = await lfGet(state.info.pageUrl, 25000);
        const fresh = lfDembedInfo(html, state.info.pageUrl);
        if (fresh) state.info = fresh;
        state.token = null; state.k = null; state.tokenExp = 0;
    }
    async function ensureToken() {
        if (state.token && Date.now() < state.tokenExp - 15000) return;
        for (let attempt = 0; attempt < 2; attempt++) {
            const url = `${state.info.edge}/api/playlist-token?slug=${encodeURIComponent(state.info.channel)}&tk=${encodeURIComponent(state.info.ticket || '')}`;
            const res = await axios.get(url, { timeout: 15000, validateStatus: () => true, headers: pageHeaders() });
            if (res.status === 200 && res.data && res.data.token && res.data.k) {
                state.token = res.data.token;
                state.k = res.data.k;
                const ttl = Number(res.data.ttl) || 120;
                state.tokenExp = Date.now() + ttl * 500; // تجديد في منتصف العمر مثل المشغّل
                return;
            }
            if (attempt === 0) await refreshPage();
        }
        throw new Error('تعذر الحصول على توكن البث المختوم');
    }
    async function getPlaylistText(proxyBase) {
        let lastErr = null;
        for (let attempt = 0; attempt < 5; attempt++) {
            try {
                await ensureToken();
                const res = await axios.get(`${state.info.src}?t=${state.token}`, { timeout: 15000, validateStatus: () => true, responseType: 'text', headers: pageHeaders() });
                const text = String(res.data || '');
                if (res.status === 200 && text.startsWith('#EXTM3U')) {
                    const segLines = text.split('\n').map(l => l.trim()).filter(l => l && !l.startsWith('#'));
                    const sealed = segLines.length > 0 && segLines.some(l => !/^https?:\/\//i.test(l));
                    const opened = sealed ? lfUnsealPlaylist(text, state.k) : text;
                    // إعادة كتابة أسطر المقاطع لتمر عبر البروكسي المحلي (فك الخبء هناك)
                    const rewritten = opened.split('\n').map(l => {
                        const t = l.trim();
                        if (!t || t.startsWith('#')) return l;
                        let abs;
                        try { abs = new URL(t, state.info.src).toString(); } catch (_) { return l; }
                        // لاحقة .ts ضرورية: رافض HLS في ffmpeg يرفض المقاطع بلا امتداد معروف
                        return `${proxyBase}/seg.ts?u=${Buffer.from(abs, 'utf8').toString('base64url')}`;
                    }).join('\n');
                    state.lastGood = rewritten;
                    return rewritten;
                }
                lastErr = new Error('playlist HTTP ' + res.status);
                // رفض التوكن/التيكيت: أعد جلب الصفحة لتيكيت جديد قبل المحاولة التالية
                if (res.status === 401 || res.status === 403 || res.status === 404) { try { await refreshPage(); } catch (_) {} }
            } catch (e) { lastErr = e; }
            await new Promise(r => setTimeout(r, 1200 * (attempt + 1)));
        }
        // عند فشل التجديد مؤقتاً: قدّم آخر قائمة ناجحة بدل قطع البث (مقاطعها ما زالت قابلة للجلب)
        if (state.lastGood) return state.lastGood;
        throw lastErr || new Error('تعذر جلب قائمة البث المختوم');
    }
    async function getSegment(segUrl) {
        let lastErr = null;
        for (let attempt = 0; attempt < 3; attempt++) {
            try {
                const res = await axios.get(segUrl, { timeout: 25000, validateStatus: () => true, responseType: 'arraybuffer', headers: pageHeaders() });
                if (res.status !== 200) throw new Error('segment HTTP ' + res.status);
                const ts = lfUnwrapSegment(Buffer.from(res.data));
                if (!ts) throw new Error('تعذر فك خبء المقطع');
                return ts;
            } catch (e) { lastErr = e; await new Promise(r => setTimeout(r, 800)); }
        }
        throw lastErr || new Error('تعذر جلب المقطع');
    }
    return { getPlaylistText, getSegment };
}

// بروكسي محلي: يقدّم لـ ffmpeg قائمة حية مفكوكة الختم ومقاطع TS حقيقية
async function lfStartSealedProxy(info) {
    const http = require('http');
    const session = lfSealedSession(info);
    let base = '';
    const server = http.createServer(async (req, res) => {
        try {
            const u = new URL(req.url, base || 'http://127.0.0.1');
            if (u.pathname === '/pl.m3u8') {
                const text = await session.getPlaylistText(base);
                res.writeHead(200, { 'Content-Type': 'application/vnd.apple.mpegurl', 'Cache-Control': 'no-cache' });
                res.end(text);
            } else if (u.pathname === '/seg.ts') {
                const segUrl = Buffer.from(u.searchParams.get('u') || '', 'base64url').toString('utf8');
                const ts = await session.getSegment(segUrl);
                res.writeHead(200, { 'Content-Type': 'video/MP2T', 'Cache-Control': 'no-cache' });
                res.end(ts);
            } else {
                res.writeHead(404); res.end('not found');
            }
        } catch (e) {
            try { res.writeHead(502); res.end('sealed proxy error: ' + e.message); } catch (_) {}
        }
    });
    await new Promise((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', resolve); });
    base = `http://127.0.0.1:${server.address().port}`;
    return { url: `${base}/pl.m3u8`, close: () => { try { server.close(); } catch (_) {} } };
}

// ===== ⚽ .livefootball — END (helpers) =====

function isHlsUrl(url) {
    return /\.m3u8(\?|$)/i.test(String(url || ''));
}

// تحميل ذكي: روابط m3u8 تُحوَّل عبر ffmpeg إلى mp4، والروابط المباشرة تُحمَّل عادياً
// تحميل HLS بتنزيل المقاطع مباشرة (axios) ثم دمجها — لبعض السيرفرات (مثل Carateen)
// التي تسمّي المقاطع .jpg فيرفضها ffmpeg عند فتح الـ m3u8 مباشرة
async function downloadHlsSegments(url, outPath, headers = {}) {
    const hdrs = { 'User-Agent': 'Mozilla/5.0', ...(headers || {}) };
    // سيرفرات المقاطع تتعثر أحياناً (502) — إعادة المحاولة لكل طلب
    const getWithRetry = async (u, opts, tries = 3) => {
        let lastErr;
        for (let i = 0; i < tries; i++) {
            try { return await axios.get(u, opts); }
            catch (e) { lastErr = e; await new Promise(r => setTimeout(r, 2000 * (i + 1))); }
        }
        throw lastErr;
    };
    let pl = await getWithRetry(url, { headers: hdrs, timeout: 30000, responseType: 'text' });
    let text = String(pl.data || '');
    if (/#EXT-X-STREAM-INF/.test(text)) {
        const variants = parseM3u8Variants(text, url);
        if (!variants.length) throw new Error('لا توجد جودات في قائمة m3u8.');
        const best = variants[variants.length - 1];
        pl = await getWithRetry(best.url, { headers: hdrs, timeout: 30000, responseType: 'text' });
        text = String(pl.data || '');
        url = best.url;
    }
    const segUrls = text.split(/\r?\n/).map(l => l.trim()).filter(l => l && !l.startsWith('#'))
        .map(l => { try { return new URL(l, url).toString(); } catch (_) { return null; } })
        .filter(Boolean);
    if (!segUrls.length) throw new Error('لا توجد مقاطع في قائمة m3u8.');
    const tmpTs = outPath + '.ts';
    try { fs.unlinkSync(tmpTs); } catch (_) {}
    for (const seg of segUrls) {
        const r = await getWithRetry(seg, { headers: hdrs, timeout: 60000, responseType: 'arraybuffer' });
        fs.appendFileSync(tmpTs, Buffer.from(r.data));
    }
    const res = await runFfmpeg(['-i', tmpTs, '-c', 'copy', '-y', outPath], null);
    try { fs.unlinkSync(tmpTs); } catch (_) {}
    if (res.code !== 0 || !fs.existsSync(outPath) || fs.statSync(outPath).size === 0) {
        throw new Error('فشل دمج مقاطع HLS.');
    }
}

async function downloadVideoSmart(url, outPath, headers = {}, onProgress = null) {
    // onProgress اختياري: { downloaded, total, percent, elapsedMs } — يُستخدم لمسار .football فقط (لوج Actions)
    const notify = (p) => { try { if (typeof onProgress === 'function') onProgress(p); } catch (_) {} };
    const dlStartedAt = Date.now();
    if (isHlsUrl(url)) {
        notify({ downloaded: 0, total: null, percent: null, elapsedMs: 0 });
        // ffmpeg بياخد آخر -headers بس — اجمع كل الهيدرات في وسيط واحد مفصول بـ CRLF
        const hdrs = Object.entries(headers || {})
            .filter(([k, v]) => !/^:/.test(k) && v !== undefined && v !== null)
            .map(([k, v]) => `${k}: ${v}`).join('\r\n');
        const args = [];
        if (hdrs) args.push('-headers', hdrs);
        args.push('-i', url, '-c', 'copy', '-y', outPath);
        const res = await runFfmpeg(args, null);
        if (res.code === 0 && fs.existsSync(outPath) && fs.statSync(outPath).size > 0) {
            notify({ downloaded: fs.statSync(outPath).size, total: null, percent: 100, elapsedMs: Date.now() - dlStartedAt });
            return;
        }
        try { if (fs.existsSync(outPath)) fs.unlinkSync(outPath); } catch (_) {}
        // بعض سيرفرات HLS (مثل Carateen) مقاطعها بامتداد .jpg فيرفضها ffmpeg —
        // حمّل المقاطع مباشرة وادمجها بدلاً من ذلك
        await downloadHlsSegments(url, outPath, headers);
        if (!fs.existsSync(outPath) || fs.statSync(outPath).size === 0) {
            throw new Error('فشل تحويل بث m3u8 عبر ffmpeg');
        }
        notify({ downloaded: fs.statSync(outPath).size, total: null, percent: 100, elapsedMs: Date.now() - dlStartedAt });
        return;
    }
    let response;
    try {
        response = await axios({
            method: 'GET', url, responseType: 'stream', timeout: 1800000,
            headers: { 'User-Agent': WEB_UA, ...headers }
        });
    } catch (err) {
        // بعض سيرفرات الفيديو شهادتها مكسورة (سلسلة ناقصة) — أعد المحاولة بدون التحقق من الشهادة
        const msg = String((err && err.message) || '');
        const code = (err && err.code) || '';
        const isCertErr = /certificate|self signed|unable to get local issuer/i.test(msg)
            || ['UNABLE_TO_GET_ISSUER_CERT_LOCALLY', 'CERT_HAS_EXPIRED', 'DEPTH_ZERO_SELF_SIGNED_CERT', 'SELF_SIGNED_CERT_IN_CHAIN', 'CERT_UNTRUSTED'].includes(code);
        if (!isCertErr) throw err;
        response = await axios({
            method: 'GET', url, responseType: 'stream', timeout: 1800000,
            headers: { 'User-Agent': WEB_UA, ...headers },
            httpsAgent: new (require('https').Agent)({ rejectUnauthorized: false })
        });
    }
    if (response.status >= 400) throw new Error(`HTTP ${response.status}`);
    const totalBytes = parseInt(response.headers['content-length'] || '0', 10) || null;
    let downloadedBytes = 0;
    response.data.on('data', (chunk) => {
        downloadedBytes += chunk.length;
        notify({ downloaded: downloadedBytes, total: totalBytes, percent: totalBytes ? Math.min(100, Math.floor(downloadedBytes / totalBytes * 100)) : null, elapsedMs: Date.now() - dlStartedAt });
    });
    const writer = fs.createWriteStream(outPath);
    response.data.pipe(writer);
    await new Promise((resolve, reject) => {
        writer.on('finish', resolve);
        writer.on('error', reject);
        response.data.on('error', reject);
    });
    notify({ downloaded: downloadedBytes, total: totalBytes || downloadedBytes, percent: 100, elapsedMs: Date.now() - dlStartedAt });
    // ملف فارغ = السيرفر لم يرسل بيانات — لا ترسله كأنه تحميل ناجح
    if (!fs.existsSync(outPath) || fs.statSync(outPath).size === 0) {
        try { if (fs.existsSync(outPath)) fs.unlinkSync(outPath); } catch (_) {}
        throw new Error('التحميل رجّع ملفاً فارغاً (السيرفر لم يرسل بيانات).');
    }
}

// ============================================================
// CloudDay API — أنمي داي / سيما كلاود (API عربي حقيقي)
// البحث + الحلقات بدون مصادقة. السيرفرات تحتاج توكن تشفير:
// firebase_id (AES-256-GCM + RSA) + cloudflare-id + deviceId،
// والرد Base64 يُفك بـ AES-256-CBC. الدومينات بتدور، فالأساس
// يُحل من ملف الإعدادات وقت التشغيل مع بدائل ثابتة.
// ============================================================
const CLOUDDAY_UA = 'okhttp/4.10.0';
const CLOUDDAY_KEY_BASE = 'Gm4il@G00Gl3.Com';
const CLOUDDAY_ATTEST_APP_ID = '21406135';
const CLOUDDAY_ATTEST_CERT_PATH = '021bb8f6029e4e63e4b5b0ff922788b4fe24739e261e637dddf70bf95e0aacd7|/data/app/com.app.cimacloud-1/base.apk';
const CLOUDDAY_RSA_PUB_B64 =
    'MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAwDPYEppEb3xys/R99+zmZW54vhcQIcV+6' +
    '+BtHI/Qmb4I0M2hw0fQ9fzLY/RhKM33yuOOZNAulpq4ByJ7b556fkkplaPMI3vbESmoJqCk3Q' +
    'Ch65Nbi4mKRFFJyDkJVepBX2BDr3+zECzdSy0oVSn+nFqw5YJcS+d06Lgyyr5oZSaZSeGh9F' +
    'tgJkuz17n265rLB6ruUUrHQVeEDl8ph3t/x/NynwtwQDA5VX+a/AVmedgb2JZCQLry8Za/lvs' +
    'q4Lhuthcts6gtVq3uPExSKdLBpbqbwQNvhRgB3IEYV47OyddG32qbriJbxdvW+n5OzowiYQr' +
    'sC8hG65GPBGCuj3zO7wIDAQAB';
// معرّف جهاز عشوائي ثابت طوال تشغيل البوت (16 حرف hex)
const CLOUDDAY_DEVICE_ID = crypto.randomBytes(8).toString('hex');
const CLOUDDAY_SOURCES = [
    { name: 'AnimeDay', configUrl: 'https://backup-animeday.animegateshorts.workers.dev', apiPath: '/v3.8/api', fallback: 'https://20042026.site/v3.8/api' },
    { name: 'CimaCloud', configUrl: 'https://cloud-day.online/v1.3/CloudDay/uploads/config_v1.3.json', apiPath: '/v1.3/api', fallback: 'https://1654865.xyz/v1.3/api' }
];
let cloudDayBaseCache = {}; // name -> {base, at}

// حلّ الأساس الحالي للمصدر (كاش ساعة واحدة)
async function cloudDayResolveBase(src) {
    const cached = cloudDayBaseCache[src.name];
    if (cached && Date.now() - cached.at < 3600000) return cached.base;
    try {
        const res = await axios.get(src.configUrl, { headers: { 'User-Agent': CLOUDDAY_UA }, timeout: 12000 });
        const data = res.data;
        const host = (data && data.data && data.data[0] && data.data[0].cloudday) || data.cloudday || null;
        if (host) {
            const base = String(host).replace(/\/$/, '') + src.apiPath;
            cloudDayBaseCache[src.name] = { base, at: Date.now() };
            return base;
        }
    } catch (_) {}
    cloudDayBaseCache[src.name] = { base: src.fallback, at: Date.now() };
    return src.fallback;
}

// توكن firebase_id جديد لكل طلب (السيرفر يرفض إعادة الاستخدام)
function cloudDayMakeFirebaseId() {
    const payload = JSON.stringify({
        a: CLOUDDAY_ATTEST_APP_ID, b: CLOUDDAY_ATTEST_CERT_PATH,
        c: 'false', d: 'empty', e: 'empty', f: 'false', g: 'false', h: 'false',
        t: Math.floor(Date.now() / 1000),
        n: crypto.randomBytes(8).toString('hex')
    });
    const aesKey = crypto.randomBytes(32);
    const iv = crypto.randomBytes(12);
    const cipher = crypto.createCipheriv('aes-256-gcm', aesKey, iv);
    const ct = Buffer.concat([cipher.update(payload, 'utf8'), cipher.final(), cipher.getAuthTag()]);
    const pub = crypto.createPublicKey({ key: Buffer.from(CLOUDDAY_RSA_PUB_B64, 'base64'), format: 'der', type: 'spki' });
    const wrapped = crypto.publicEncrypt({ key: pub, padding: crypto.constants.RSA_PKCS1_PADDING }, aesKey);
    return [wrapped, iv, ct].map(b => b.toString('base64')).join('.');
}

function cloudDayMakeCloudflareId() {
    const abc = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    let s = '';
    for (let i = 0; i < 15; i++) s += abc[Math.floor(Math.random() * abc.length)];
    return s + CLOUDDAY_DEVICE_ID;
}

// فك تشفير رد السيرفرات (Base64 → AES-256-CBC → JSON)
function cloudDayDecryptServers(b64) {
    const ct = Buffer.from(String(b64).trim(), 'base64');
    const key = crypto.createHash('md5').update(CLOUDDAY_KEY_BASE + CLOUDDAY_DEVICE_ID).digest('hex');
    const iv = crypto.createHash('md5').update(CLOUDDAY_DEVICE_ID + CLOUDDAY_KEY_BASE).digest('hex').slice(0, 16);
    const decipher = crypto.createDecipheriv('aes-256-cbc', Buffer.from(key, 'utf8'), Buffer.from(iv, 'utf8'));
    const plain = Buffer.concat([decipher.update(ct), decipher.final()]).toString('utf8');
    const obj = JSON.parse(plain);
    const servers = Array.isArray(obj.servers) ? obj.servers : [];
    return servers.map(s => s.link).filter(l => typeof l === 'string' && l.startsWith('http'));
}

// بحث CloudDay → [{id, type, name}]
async function cloudDaySearch(query, srcName, type = '0') {
    const src = CLOUDDAY_SOURCES.find(s => s.name === srcName);
    const base = await cloudDayResolveBase(src);
    const res = await axios.post(`${base}/search`,
        new URLSearchParams({ title: query, type, sort: '1', page: '1' }).toString(),
        { headers: { 'User-Agent': CLOUDDAY_UA, 'Accept': 'application/json', 'Content-Type': 'application/x-www-form-urlencoded' }, timeout: 20000 });
    const results = Array.isArray(res.data && res.data.results) ? res.data.results : [];
    return results.map(r => ({ id: String(r.id), type: r.type || 'series', name: r.name || r.title || '' }));
}

// حلقات مسلسل CloudDay → [{id, number, title}]
async function cloudDayEpisodes(apiBase, animeId) {
    const res = await axios.get(`${apiBase}/series/${animeId}/episodes`,
        { headers: { 'User-Agent': CLOUDDAY_UA, 'Accept': 'application/json' }, timeout: 20000 });
    const seasons = Array.isArray(res.data && res.data.seasons) ? res.data.seasons : [];
    const eps = [];
    for (const s of seasons) {
        for (const e of (s.episodes || [])) {
            const numMatch = String(e.title || e.name || '').match(/\d+/);
            eps.push({ id: String(e.id), number: numMatch ? parseInt(numMatch[0]) : (eps.length + 1), title: e.title || e.name || '' });
        }
    }
    return eps;
}

// سيرفرات حلقة/فيلم CloudDay → [link, ...]
async function cloudDayServers(apiBase, kind, id) {
    const path = kind === 'movie' ? `movie/${id}/servers` : `episode/${id}/servers`;
    const res = await axios.get(`${apiBase}/${path}`, {
        headers: {
            'User-Agent': CLOUDDAY_UA, 'Accept': 'application/json',
            deviceId: CLOUDDAY_DEVICE_ID,
            'cloudflare-id': cloudDayMakeCloudflareId(),
            firebase_id: cloudDayMakeFirebaseId()
        },
        timeout: 25000, responseType: 'text', validateStatus: s => s < 500
    });
    if (res.status !== 200 || typeof res.data !== 'string') throw new Error('CloudDay servers: HTTP ' + res.status);
    return cloudDayDecryptServers(res.data);
}

// تحويل روابط سيرفرات CloudDay إلى روابط تحميل مباشرة [{url, label}]
async function cloudDayResolveLinks(links) {
    const out = [];
    for (const link of links) {
        try {
            if (/uqload/i.test(link)) {
                try {
                    const m3u8 = await extractUqloadM3u8(link);
                    out.push({ url: m3u8, label: 'UQLOAD — HLS', referer: 'https://uqload.com/' });
                } catch (_) {}
            }
            const pd = /uqload/i.test(link) ? null : link.match(/pixeldrain\.com\/u\/([A-Za-z0-9]+)/i);
            if (pd) {
                let label = 'PixelDrain';
                try {
                    const info = await axios.get(`https://pixeldrain.com/api/file/${pd[1]}/info`, { timeout: 10000 });
                    if (info.data && info.data.name) label = `PixelDrain — ${info.data.name}`;
                } catch (_) {}
                out.push({ url: `https://pixeldrain.com/api/file/${pd[1]}`, label });
            } else if (/developer-pro\.workers\.dev\/get-links/i.test(link)) {
                // الـ worker يعيد توجيه 302 إلى mp4 مباشر — نقرأ Location فقط بدون تحميل
                const r = await axios.get(link, { timeout: 15000, maxRedirects: 0, validateStatus: s => s >= 200 && s < 400 });
                if (r.headers && r.headers.location) out.push({ url: r.headers.location, label: 'ok.ru CDN' });
            } else if (/^https?:\/\/.*\.(mp4|m3u8)(\?|$)/i.test(link) && !/uqload/i.test(link)) {
                out.push({ url: link, label: 'رابط مباشر' });
            }
        } catch (_) {}
        if (out.length >= 6) break;
    }
    return out;
}

// ============================================================
// AnimeRift API — تطبيق أنمي ريفت (API عربي حقيقي)
// تسجيل جهاز مرة واحدة + تهدئة 1.3 ثانية بين الطلبات
// (البوابة تحظر الـ IP عند الإفراط في الطلبات).
// ============================================================
const RIFT_GATEWAYS = ['https://gateway.anime-rift.com/api/v4', 'https://gateway.embrassme.top/api/v4'];
const RIFT_APP_VERSION = '3.13.13';
const RIFT_DEVICE_OS_ID = 'UQ1A.240205.004';
const RIFT_UA = 'Dart/3.10 (dart:io)';
const _riftAlpha = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
const _riftTok = n => Array.from({ length: n }, () => _riftAlpha[Math.floor(Math.random() * _riftAlpha.length)]).join('');
const RIFT_FIREBASE_ID = _riftTok(22);
const RIFT_DEVICE_ID = RIFT_FIREBASE_ID + ':APA91b' + _riftTok(40);
let riftRegistered = false;
let riftLastCall = 0;

async function riftPace() {
    const wait = 1300 - (Date.now() - riftLastCall);
    if (wait > 0) await new Promise(r => setTimeout(r, wait));
    riftLastCall = Date.now();
}

function riftHeaders() {
    const ts = new Date().toISOString().replace('Z', '000000');
    return {
        'User-Agent': RIFT_UA, 'Accept': 'application/json',
        'Content-Type': 'application/json; charset=UTF-8',
        'x-os': 'android', 'x-platform': 'Mobile', 'x-device-language': 'ar',
        'x-installation-source': 'IS_INSTALLED_FROM_OTHER_SOURCE',
        'x-device-release-version': RIFT_APP_VERSION,
        'x-device-os-id': RIFT_DEVICE_OS_ID,
        'x-device-timezone': ts,
        'x-firebase-app-check': 'null',
        'x-firebase-id': RIFT_FIREBASE_ID,
        'x-device-id': RIFT_DEVICE_ID
    };
}

async function riftCall(method, path, body) {
    await riftPace();
    const res = await axios({
        method, url: RIFT_GATEWAYS[0] + path, data: body || undefined,
        headers: riftHeaders(), timeout: 25000,
        validateStatus: s => s < 500
    });
    if (res.status === 403) throw new Error('AnimeRift: حظر IP مؤقت (403)');
    if (res.status === 429) throw new Error('AnimeRift: تجاوز حد الطلبات (429)');
    if (res.status >= 400) throw new Error('AnimeRift: HTTP ' + res.status);
    return res.data;
}

async function riftEnsureRegistered() {
    if (riftRegistered) return;
    const data = await riftCall('POST', '/auth/register/device', {
        deviceId: RIFT_DEVICE_ID, current_app_version: RIFT_APP_VERSION,
        device_os: 'android', device_environment: 'production',
        device_info: JSON.stringify({ model: 'M2006C3MG', brand: 'Redmi', manufacturer: 'Xiaomi', device: 'angelica', hardware: 'mt6765', product: 'angelica_global', androidVersion: '14', sdkInt: 34, isPhysicalDevice: true, supportedAbis: ['arm64-v8a', 'armeabi-v7a'], tags: 'release-keys', type: 'user', buildId: RIFT_DEVICE_OS_ID })
    });
    if (data && data.sessionKey) riftRegistered = true;
    else throw new Error('AnimeRift: فشل تسجيل الجهاز');
}

// بحث AnimeRift → [{id, title, episodes, year}]
async function riftSearch(query) {
    await riftEnsureRegistered();
    const data = await riftCall('POST', '/library/search?page=0&sort_by=release_year&sort_direction=1&text_direction=jp', { query });
    const items = Array.isArray(data && data.items) ? data.items : [];
    return items.map(it => ({ id: String(it._id), title: it.title || it.alternative_title || '', episodes: it.available_episodes || 0, year: it.release_year || '' }));
}

// حلقات AnimeRift → [{id, number, title}]
async function riftEpisodes(animeId) {
    await riftEnsureRegistered();
    const data = await riftCall('GET', `/library/episodes/${animeId}?sort_by_latest=1&with_arcs=true&with_favorites=true`);
    const items = Array.isArray(data && data.items) ? data.items : [];
    return items.map(e => ({ id: String(e._id), number: e.episode_number, title: (e.title_translations && (e.title_translations.ar || e.title_translations.en)) || '' }));
}

// روابط حلقة AnimeRift (مترجم عربي أولاً) → [{url, label}]
async function riftEpisodeLinks(animeId, episode) {
    await riftEnsureRegistered();
    const data = await riftCall('POST', '/library/episode/sources', { animeId, episodeId: episode.id, episode_number: episode.number });
    const items = Array.isArray(data && data.items) ? data.items : [];
    const arSubs = items.filter(s => s.sub_title === 'ar_sub' && Array.isArray(s.qualities) && s.qualities.length);
    const picked = arSubs.length ? arSubs : items.filter(s => Array.isArray(s.qualities) && s.qualities.length);
    const out = [];
    const seenQ = new Set();
    for (const s of picked) {
        for (const q of s.qualities) {
            const qn = String(q).toUpperCase();
            if (seenQ.has(qn)) continue;
            seenQ.add(qn);
            try {
                const cp = await riftCall('POST', '/library/episode/source/can_play', { episodeId: episode.id, hostId: s._id, is_download: false, event_name: 'play_episode_unlocked' });
                const sessionId = (cp && cp.sessionId) || '';
                const dl = await riftCall('POST', '/library/episode/source/direct_link', { id: s._id, with_internal_player: '1', sessionId, quality: qn });
                if (dl && dl.videoUrl) out.push({ url: dl.videoUrl, label: `${qn} (${s.server_name || s.provider || 'AnimeRift'})` });
            } catch (_) {}
            if (out.length >= 3) break;
        }
        if (out.length >= 3) break;
    }
    return out;
}


// ============================================================
// المصادر الجديدة لـ .anime (5 مصادر — كلها مثبتة التحميل)
// shahiid-anime + anime4up + kartoney + animedar + AnimeWitcher
// ============================================================
const WEB_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

function decodeHtmlEntities(s) {
    return String(s || '')
        .replace(/&quot;/g, '"').replace(/&#39;|&apos;/g, "'").replace(/&amp;/g, '&')
        .replace(/&#x2F;/g, '/')
        .replace(/\\u([\dA-Fa-f]{4})/g, (_, h) => String.fromCharCode(parseInt(h, 16)));
}

// كوكيز بسيطة لجلسة واحدة (anime4up يحتاج نفس الجلسة لجلب التوكن)
function jarMerge(jar, setCookie) {
    const map = {};
    for (const c of String(jar || '').split(';')) { const i = c.indexOf('='); if (i > 0) map[c.slice(0, i).trim()] = c.slice(i + 1).trim(); }
    for (const c of (setCookie || [])) { const kv = String(c).split(';')[0]; const i = kv.indexOf('='); if (i > 0) map[kv.slice(0, i).trim()] = kv.slice(i + 1).trim(); }
    return Object.entries(map).map(([k, v]) => `${k}=${v}`).join('; ');
}

async function fetchText(url, opts = {}) {
    const headers = { 'User-Agent': WEB_UA, ...(opts.headers || {}) };
    if (opts.jar && opts.jar.cookie) headers['Cookie'] = opts.jar.cookie;
    const res = await axios.get(url, { timeout: 25000, maxRedirects: 5, headers });
    if (opts.jar && res.headers && res.headers['set-cookie']) opts.jar.cookie = jarMerge(opts.jar.cookie, res.headers['set-cookie']);
    return res.data;
}

async function fetchTextPost(url, form, opts = {}) {
    const headers = { 'User-Agent': WEB_UA, 'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8', 'X-Requested-With': 'XMLHttpRequest', ...(opts.headers || {}) };
    if (opts.jar && opts.jar.cookie) headers['Cookie'] = opts.jar.cookie;
    const res = await axios.post(url, new URLSearchParams(form).toString(), { timeout: 25000, headers });
    if (opts.jar && res.headers && res.headers['set-cookie']) opts.jar.cookie = jarMerge(opts.jar.cookie, res.headers['set-cookie']);
    return res.data;
}

// تحليل قائمة m3u8 رئيسية → جودات [{label, url}] (الروابط النسبية تُحلّ نسبةً للرابط الرئيسي)
function parseM3u8Variants(text, base) {
    const lines = String(text || '').split('\n').map(s => s.trim());
    const out = [];
    for (let i = 0; i < lines.length; i++) {
        if (lines[i].startsWith('#EXT-X-STREAM-INF')) {
            const res = lines[i].match(/RESOLUTION=\d+x(\d+)/);
            const bw = lines[i].match(/BANDWIDTH=(\d+)/);
            let url = lines[i + 1] && !lines[i + 1].startsWith('#') ? lines[i + 1] : null;
            if (url) {
                if (base && !/^https?:\/\//i.test(url)) { try { url = new URL(url, base).toString(); } catch (_) {} }
                out.push({ label: res ? `${res[1]}p` : (bw ? `${Math.round(bw[1] / 1000)}kbps` : 'HLS'), url });
            }
        }
    }
    return out;
}

// فك تشفير Dean Edwards packer — يرجّع الكود المفكوك كنص (لا ينفّذ الكود نفسه)
// يجرّب نهايات الاستدعاء المحتملة حتى ينجح الـ eval (الحمولة قد تحتوي '))' داخل نصها)
function deanEdwardsUnpack(packed) {
    const start = String(packed || '').indexOf('eval(function(p,a,c,k,e,d){');
    if (start === -1) return null;
    const tail = String(packed).slice(start + 5); // من 'function...' بدون 'eval('
    let idx = -1;
    let fallback = null;
    while (true) {
        idx = tail.indexOf('))', idx + 1);
        if (idx === -1 || idx > 300000) return fallback;
        const code = tail.slice(0, idx + 1);
        try {
            const out = eval('(' + code + ')');
            if (typeof out === 'string' && out.length) {
                if (/m3u8|jwplayer|sources|file\s*:/i.test(out)) return out;
                if (!fallback) fallback = out;
            }
        } catch (_) {}
    }
}

// UQLOAD: معرّف أو رابط embed كامل → رابط m3u8 مباشر
async function extractUqloadM3u8(target) {
    const url = /^https?:\/\//i.test(target) ? target : `https://uqload.com/embed-${target}.html`;
    const html = await fetchText(url, { headers: { Referer: 'https://uqload.com/' } });
    const unpacked = deanEdwardsUnpack(html);
    const src = unpacked || html;
    const m = src.match(/https?:\/\/[^\s"'<>]+\.m3u8[^\s"'<>]*/i);
    if (!m) throw new Error('لم يتم العثور على رابط m3u8 في UQLOAD (قد يكون الملف محذوفاً).');
    return m[0].replace(/\\u0026/g, '&').replace(/\\\//g, '/');
}

// Mp4upload: معرّف embed → رابط mp4 مباشر (يُستخرج طازجاً كل مرة — الروابط مؤقتة)
async function extractMp4uploadMp4(embedId) {
    const html = await fetchText(`https://www.mp4upload.com/embed-${embedId}.html`, { headers: { Referer: 'https://www.mp4upload.com/' } });
    if (/File was deleted/i.test(html)) throw new Error('ملف Mp4upload محذوف.');
    const m = html.match(/https?:\/\/[a-z0-9]+\.mp4upload\.com(?::\d+)?\/[^\s"'<>]+\.mp4[^\s"'<>]*/i)
        || html.match(/https?:\/\/[^\s"'<>]+\.mp4[^\s"'<>]*/i);
    if (!m) throw new Error('لم يتم العثور على رابط mp4 في Mp4upload.');
    return m[0];
}

// ---------- shahiid-anime.net ----------
const SHAHIID_BASE = 'https://shahiid-anime.net';

async function shahiidSearch(query) {
    const html = await fetchText(`${SHAHIID_BASE}/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    const re = /<a[^>]+href="(https:\/\/shahiid-anime\.net\/anime\/[^"]+)"[^>]*>([\s\S]{0,200}?)<\/a>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (url === SHAHIID_BASE + '/anime/' || seen.has(url)) continue;
        seen.add(url);
        let title = decodeHtmlEntities(m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim());
        if (!title || title.length < 2) {
            try { title = decodeURIComponent(url.split('/anime/')[1].replace(/\/$/, '')).replace(/[-_]+/g, ' ').trim(); } catch (_) { title = ''; }
        }
        if (!title) continue;
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    return out;
}

function shahiidEpNumber(url, text) {
    let src = '';
    try { src = decodeURIComponent(url); } catch (_) { src = url; }
    const fromText = String(text || '').match(/الحلقة\s*0*(\d+)/);
    if (fromText) return parseInt(fromText[1], 10);
    const fromUrl = src.match(/الحلقة-0*(\d+)/) || src.match(/الحلقة\s*0*(\d+)/);
    if (fromUrl) return parseInt(fromUrl[1], 10);
    return null;
}

function shahiidCollectEpisodes(html) {
    const eps = []; const seen = new Set();
    const re = /href="(https:\/\/shahiid-anime\.net\/episodes\/[^"]+)"[^>]*>([\s\S]{0,150}?)<\/a>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const text = decodeHtmlEntities(m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim());
        eps.push({ id: url, number: shahiidEpNumber(url, text), title: text || 'حلقة' });
    }
    return eps;
}

async function shahiidEpisodes(animeUrl) {
    const html = await fetchText(animeUrl);
    let eps = shahiidCollectEpisodes(html);
    if (!eps.length) {
        const seasons = [...new Set([...html.matchAll(/href="(https:\/\/shahiid-anime\.net\/seasons\/[^"]+)"/gi)].map(m => m[1]))];
        for (const s of seasons.slice(0, 5)) {
            try { eps = eps.concat(shahiidCollectEpisodes(await fetchText(s))); } catch (_) {}
        }
    }
    if (!eps.length) return [{ id: animeUrl, number: 1, title: 'فيلم / مشاهدة مباشرة' }];
    eps.forEach((e, i) => { if (!e.number) e.number = i + 1; });
    eps.sort((a, b) => a.number - b.number);
    return eps;
}

async function shahiidEpisodeLinks(episodeUrl) {
    const html = await fetchText(episodeUrl);
    const servers = [];
    const tagRe = /<a[^>]*class="[^"]*buttosn[^"]*"[^>]*>/gi;
    for (const tag of (html.match(tagRe) || [])) {
        const serv = (tag.match(/data-serv="([^"]+)"/) || [])[1];
        const fs = (tag.match(/data-frameserver='([^']*)'/) || tag.match(/data-frameserver="([^"]*)"/) || [])[1];
        const post = (tag.match(/data-post="([^"]+)"/) || [])[1];
        if (serv && post) servers.push({ serv, fs: fs || '', post });
    }
    const out = [];
    for (const s of servers) {
        if (out.length >= 6) break;
        try {
            const ajaxHtml = await fetchTextPost(`${SHAHIID_BASE}/wp-admin/admin-ajax.php`,
                { action: 'codecanal_ajax_request', post: s.post, serv: s.serv, frameserver: s.fs, _server_code_: '', is_film: '' },
                { headers: { Referer: episodeUrl } });
            let src = (String(ajaxHtml).match(/<iframe[^>]*src="([^"]+)"/i) || [])[1];
            if (!src) {
                // بعض الأزرار (مثل Megamax) تحتاج GET بدل POST
                try {
                    const getHtml = await fetchText(`${SHAHIID_BASE}/wp-admin/admin-ajax.php?action=codecanal_ajax_request&post=${encodeURIComponent(s.post)}&frameserver=${encodeURIComponent(s.fs)}`, { headers: { Referer: episodeUrl } });
                    src = (String(getHtml).match(/<iframe[^>]*src="([^"]+)"/i) || [])[1];
                } catch (_) {}
            }
            if (!src) continue;
            const mp4 = src.match(/mp4upload\.com\/embed-([^\.\/]+)\.html/i);
            if (mp4) { out.push({ url: await extractMp4uploadMp4(mp4[1]), label: 'Mp4upload — HD' }); continue; }
            const ok = src.match(/ok\.ru\/videoembed\/(\d+)/);
            if (ok) {
                const { videos } = await extractOkruVideo(`https://ok.ru/video/${ok[1]}`);
                for (const v of videos.slice(0, 2)) out.push({ url: v.url, label: 'ok.ru — ' + (OKRU_QUALITY_LABELS[v.name] || v.name) });
                continue;
            }
            // Megamax (share4max) — البديل الشغال بعد موت Mp4upload (403)
            const mega = src.match(/(?:share4max\.com|megamax\.me)\/iframe\/([A-Za-z0-9]+)/i);
            if (mega) {
                try {
                    const streams = await megaMaxStreams(src, episodeUrl);
                    for (const l of await megaMaxLinks(streams, 'شهيد — Megamax')) out.push(l);
                } catch (_) {}
                continue;
            }
        } catch (_) {}
    }
    return out;
}

// ---------- anime4up (w1.anime4up.rest) ----------
const A4_BASE = 'https://w1.anime4up.rest';

async function anime4upSearch(query) {
    const html = await fetchText(`${A4_BASE}/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    const re = /<a[^>]+href="(https:\/\/w1\.anime4up\.rest\/anime\/[^"]+)"[^>]*>([\s\S]{0,200}?)<\/a>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        let title = decodeHtmlEntities(m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim());
        if (!title || title.length < 2) {
            try { title = decodeURIComponent(url.split('/anime/')[1].replace(/\/$/, '')).replace(/[-_]+/g, ' ').trim(); } catch (_) { title = ''; }
        }
        if (!title) continue;
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    return out;
}

async function anime4upEpisodes(animeUrl) {
    const html = await fetchText(animeUrl);
    const eps = []; const seen = new Set();
    const re = /href="(https:\/\/w1\.anime4up\.rest\/episode\/[^"]+)"[^>]*>([\s\S]{0,150}?)<\/a>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const text = decodeHtmlEntities(m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim());
        let num = null;
        try { const dec = decodeURIComponent(url); const mm = dec.match(/الحلقة-0*(\d+)/); if (mm) num = parseInt(mm[1], 10); } catch (_) {}
        if (!num) { const tm = text.match(/الحلقة\s*0*(\d+)/); if (tm) num = parseInt(tm[1], 10); }
        eps.push({ id: url, number: num, title: text || 'حلقة' });
    }
    if (!eps.length) return [{ id: animeUrl, number: 1, title: 'فيلم / مشاهدة مباشرة' }];
    eps.forEach((e, i) => { if (!e.number) e.number = i + 1; });
    eps.sort((a, b) => a.number - b.number);
    return eps;
}

async function anime4upEpisodeLinks(episodeUrl) {
    const jar = { cookie: '' };
    const html = await fetchText(episodeUrl, { jar });
    const iframes = [...String(html).matchAll(/<iframe[^>]*src="([^"]+)"[^>]*>/gi)].map(m => m[1]);
    const out = [];
    // السيرفر S2 أولاً: VnxPlayer ← توكن قصير العمر ← m3u8 بثلاث جودات (يُجلب ويُستخدم فوراً)
    const s2 = iframes.find(u => /Anime4up-S2/i.test(u));
    if (s2) {
        try {
            const playerUrl = s2.replace(/^https?:\/\/[^\/]+\//, A4_BASE + '/');
            const playerHtml = await fetchText(s2, { jar, headers: { Referer: episodeUrl } });
            const stream = (String(playerHtml).match(/let\s+streamUrl\s*=\s*"([^"]+)"/) || [])[1];
            if (stream) {
                const master = await fetchText(stream, { jar, headers: { Referer: playerUrl } });
                const variants = parseM3u8Variants(master);
                if (variants.length) return variants.map(v => ({ url: v.url, label: `anime4up — ${v.label}` }));
                out.push({ url: stream, label: 'anime4up — HLS' });
            }
        } catch (_) {}
    }
    // بدائل من نفس الصفحة
    for (const src of iframes) {
        if (out.length >= 6) break;
        try {
            const mp4 = src.match(/mp4upload\.com\/embed-([^\.\/]+)\.html/i);
            if (mp4) { out.push({ url: await extractMp4uploadMp4(mp4[1]), label: 'Mp4upload — HD' }); continue; }
            const uq = src.match(/uqload\.(?:is|com|vc)\/e\/([A-Za-z0-9]+)/i) || src.match(/uqload\.com\/embed-([^\.\/]+)\.html/i);
            if (uq) { out.push({ url: await extractUqloadM3u8(uq[1]), label: 'UQLOAD — HLS' }); continue; }
            const ok = src.match(/ok\.ru\/videoembed\/(\d+)/);
            if (ok) {
                const { videos } = await extractOkruVideo(`https://ok.ru/video/${ok[1]}`);
                for (const v of videos.slice(0, 2)) out.push({ url: v.url, label: 'ok.ru — ' + (OKRU_QUALITY_LABELS[v.name] || v.name) });
                continue;
            }
        } catch (_) {}
    }
    return out;
}

// ---------- kartoney.com (مدبلج) ----------
const KART_BASE = 'https://kartoney.com';

function normAr(s) {
    return String(s || '').toLowerCase()
        .replace(/[\u064B-\u0652\u0670]/g, '').replace(/أ|إ|آ/g, 'ا').replace(/ة/g, 'ه').replace(/ى/g, 'ي').trim();
}

async function kartoneySearch(query) {
    const html = await fetchText(`${KART_BASE}/library/`);
    const out = []; const seen = new Set();
    const q = String(query).trim();
    const nq = normAr(q);
    const matches = (url, title) => {
        if (!nq) return true;
        const slug = decodeURIComponent(url.split('/cartoon/')[1].replace(/\/$/, ''));
        const hay = normAr(title) + ' ' + normAr(slug.replace(/[-_]+/g, ' '));
        if (hay.includes(nq) || title.toLowerCase().includes(q.toLowerCase())) return true;
        // مطابقة بأي كلمة (≥3 أحرف) — "الكرة الملتهبة" تجد "الرمية الملتهبة"
        const words = nq.split(/\s+/).filter(w => w.length >= 3);
        return words.some(w => hay.includes(w));
    };
    // المصدر الأساسي: JSON-LD في صفحة المكتبة (166 عمل — الاسم العربي + الرابط)
    const items = [...String(html).matchAll(/\{"@type":"ListItem","position":\d+,"url":"(https:\/\/kartoney\.com\/cartoon\/[^"]+\/)","name":"([^"]+)"/g)];
    for (const m of items) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = decodeHtmlEntities(m[2]);
        if (!matches(url, title)) continue;
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    if (out.length) return out;
    // احتياطي: روابط /cartoon/ في HTML
    const re = /href="(\/cartoon\/[^"]+\/)"[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = KART_BASE + m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = decodeURIComponent(m[1].split('/cartoon/')[1].replace(/\/$/, '')).replace(/[-_]+/g, ' ').trim();
        if (!matches(url, title)) continue;
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    return out;
}

async function kartoneyEpisodes(cartoonUrl) {
    const html = await fetchText(cartoonUrl);
    const eps = []; const seen = new Set();
    const re = /href="(\/watch\/[^"]+\/(\d+)-(\d+)\/)"[^>]*>/gi;
    let m; let idx = 0;
    while ((m = re.exec(html)) !== null) {
        const url = KART_BASE + m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        idx++;
        eps.push({ id: url, number: idx, title: `الموسم ${m[2]} — الحلقة ${m[3]}` });
    }
    return eps;
}

async function kartoneyEpisodeLinks(watchUrl) {
    const html = await fetchText(watchUrl);
    const out = [];
    const re = /<source[^>]+src="(https?:\/\/[^"]+\.mp4[^"]*)"[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        if (/servallvid\.com/i.test(m[1])) continue; // محظور من IP الداتا سنتر
        out.push({ url: m[1], label: 'MP4 — مباشر' });
    }
    if (!out.length) {
        const m2 = String(html).match(/https?:\/\/[^"'\s<>]+\.mp4[^"'\s<>]*/i);
        if (m2 && !/servallvid\.com/i.test(m2[0])) out.push({ url: m2[0], label: 'MP4 — مباشر' });
    }
    return out;
}

// ---------- animedar (web.animedar.net) ----------
const AD_BASE = 'https://web.animedar.net';

async function animedarSearch(query) {
    const html = await fetchText(`${AD_BASE}/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    const re = /<a[^>]+href="(https:\/\/web\.animedar\.net\/anime-page\/[^"]+)"[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const tag = m[0];
        let title = (tag.match(/title="([^"]+)"/) || [])[1] || '';
        title = decodeHtmlEntities(title.trim());
        if (!title) {
            try { title = decodeURIComponent(url.split('/anime-page/')[1].replace(/\/$/, '')).replace(/[-_]+/g, ' ').trim(); } catch (_) { title = ''; }
        }
        if (!title) continue;
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    return out;
}

async function animedarEpisodes(animeUrl) {
    const html = await fetchText(animeUrl);
    const epNums = [...String(html).matchAll(/<div class='CSB' id='IDSB(\d+)'[^>]*>/g)].map(m => parseInt(m[1], 10));
    const blocks = [...String(html).matchAll(/<ul class="ul-server-position\d+">([\s\S]*?)<\/ul>/g)].map(m => m[1]);
    const eps = [];
    const n = Math.min(epNums.length, blocks.length);
    for (let i = 0; i < n; i++) {
        const uq = blocks[i].match(/(?:^|\s)data="([A-Za-z0-9]+)"[^>]*class="uqload"/) || blocks[i].match(/class="uqload"[^>]*\sdata="([A-Za-z0-9]+)"/);
        if (!uq) continue; // الحلقات بلا سيرفر UQLOAD تُتخطى — باقي السيرفرات ميتة
        eps.push({ id: uq[1], number: epNums[i], title: 'الحلقة ' + epNums[i] });
    }
    return eps;
}

async function animedarEpisodeLinks(uqloadId) {
    const m3u8 = await extractUqloadM3u8(uqloadId);
    try {
        const master = await fetchText(m3u8, { headers: { Referer: 'https://uqload.com/' } });
        const variants = parseM3u8Variants(master);
        if (variants.length) return variants.map(v => ({ url: v.url, label: `UQLOAD — ${v.label}` }));
    } catch (_) {}
    return [{ url: m3u8, label: 'UQLOAD — HLS' }];
}

// ---------- AnimeWitcher (Algolia + Firestore) ----------
// مفتاح عميل Firebase العام من مزوّد AnimeWitcher مفتوح المصدر (ليس سراً —
// مفاتيح Firebase للويب معرّفات عميل، والحماية بقواعد Firestore نفسها)
const WITCHER_FIREBASE_KEY = 'AIzaSyCrrf3G-3GkS7uCQoF6wKXh6xYz5YjXqZzQ';
const WITCHER_FB = 'https://firestore.googleapis.com/v1/projects/animewitcher-1c66d/databases/(default)/documents';
let _witcherKeys = null;
let _witcherKeysAt = 0;

async function witcherAlgoliaKeys() {
    if (_witcherKeys && Date.now() - _witcherKeysAt < 3600000) return _witcherKeys;
    const res = await axios.get(`${WITCHER_FB}/Settings/constants?key=${WITCHER_FIREBASE_KEY}`, { timeout: 20000 });
    const ss = res.data?.fields?.search_settings?.mapValue?.fields || {};
    const appId = ss.app_id_v3?.stringValue || ss.app_id?.stringValue;
    const apiKey = ss.api_key?.stringValue;
    if (!appId || !apiKey) throw new Error('تعذّر جلب مفاتيح AnimeWitcher.');
    _witcherKeys = { appId, apiKey };
    _witcherKeysAt = Date.now();
    return _witcherKeys;
}

async function witcherSearch(query) {
    const { appId, apiKey } = await witcherAlgoliaKeys();
    const attrs = encodeURIComponent('["objectID","name","poster_uri","type","details","tags","story","english_title","poster","rating","dubbed","path"]');
    const params = `attributesToRetrieve=${attrs}&hitsPerPage=10&page=0&query=${encodeURIComponent(query)}`;
    const res = await axios.post(`https://${appId}-dsn.algolia.net/1/indexes/series/query`, { params },
        { timeout: 20000, headers: { 'X-Algolia-Application-Id': appId, 'X-Algolia-API-Key': apiKey, 'User-Agent': 'Algolia for Android (3.27.0); Android (16)', 'Content-Type': 'application/json' } });
    const hits = Array.isArray(res.data?.hits) ? res.data.hits : [];
    return hits.filter(h => h && h.name).map(h => ({ id: String(h.objectID), title: h.name }));
}

async function witcherEpisodes(objectId) {
    const enc = encodeURIComponent(objectId).replace(/\+/g, '%20');
    const res = await axios.get(`${WITCHER_FB}/anime_list/${enc}/episodes_summery/summery?key=${WITCHER_FIREBASE_KEY}`, { timeout: 20000 });
    const values = res.data?.fields?.episodes?.arrayValue?.values || [];
    const eps = [];
    for (const v of values) {
        const f = v?.mapValue?.fields || {};
        const docId = f.doc_id?.stringValue;
        if (!docId) continue;
        const numRaw = f.number?.integerValue || f.number?.stringValue;
        const number = parseInt(numRaw, 10) || (eps.length + 1);
        const ar = f.title_translated?.mapValue?.fields?.ar?.stringValue;
        eps.push({ id: docId, number, title: ar || f.name?.stringValue || ('الحلقة ' + number) });
    }
    eps.sort((a, b) => a.number - b.number);
    return eps;
}

async function witcherEpisodeLinks(objectId, episode) {
    const encA = encodeURIComponent(objectId).replace(/\+/g, '%20');
    const encE = encodeURIComponent(episode.id).replace(/\+/g, '%20');
    const res = await axios.get(`${WITCHER_FB}/anime_list/${encA}/episodes/${encE}/servers2/all_servers?key=${WITCHER_FIREBASE_KEY}`, { timeout: 20000 });
    const values = res.data?.fields?.servers?.arrayValue?.values || [];
    const out = [];
    for (const v of values) {
        const f = v?.mapValue?.fields || {};
        const link = f.link?.stringValue || '';
        const quality = f.quality?.stringValue || '';
        const name = f.name?.stringValue || '';
        const pd = link.match(/pixeldrain\.com\/u\/([A-Za-z0-9_-]+)/);
        if (pd) { out.push({ url: `https://pixeldrain.com/api/file/${pd[1]}`, label: `PixelDrain — ${quality || name || 'HD'}` }); continue; }
        if (/\.mp4(\?|$)/i.test(link) || /\.m3u8(\?|$)/i.test(link)) out.push({ url: link, label: `${name || 'مباشر'} — ${quality}`.trim() });
    }
    return out.slice(0, 6);
}

// ---------- animerco (eva.animerco.org) ----------
const AM_BASE = 'https://eva.animerco.org';

async function animercoSearch(query) {
    const html = await fetchText(`${AM_BASE}/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    const re = /<a[^>]+href="(https:\/\/eva\.animerco\.org\/animes\/[^"]+)"[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (url === AM_BASE + '/animes/' || seen.has(url)) continue;
        seen.add(url);
        const tag = m[0];
        let title = (tag.match(/title="([^"]+)"/) || [])[1] || '';
        title = decodeHtmlEntities(title.trim());
        if (!title) {
            try { title = decodeURIComponent(url.split('/animes/')[1].replace(/\/$/, '')).replace(/[-_]+/g, ' ').trim(); } catch (_) { title = ''; }
        }
        if (!title) continue;
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    return out;
}

function animercoCollectEpisodes(html) {
    const eps = []; const seen = new Set();
    const re = /href=["'](https:\/\/eva\.animerco\.org\/episodes\/[^"']+)["']/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        let num = null;
        try { const dec = decodeURIComponent(url); const mm = dec.match(/الحلقة-0*(\d+)/); if (mm) num = parseInt(mm[1], 10); } catch (_) {}
        eps.push({ id: url, number: num, title: num ? 'الحلقة ' + num : 'حلقة' });
    }
    return eps;
}

async function animercoEpisodes(animeUrl) {
    const html = await fetchText(animeUrl);
    let eps = [];
    const seasons = [...new Set([...String(html).matchAll(/href=["'](https:\/\/eva\.animerco\.org\/seasons\/[^"']+)["']/gi)].map(m => m[1]))];
    for (const s of seasons.slice(0, 8)) {
        try { eps = eps.concat(animercoCollectEpisodes(await fetchText(s))); } catch (_) {}
    }
    if (!eps.length) eps = animercoCollectEpisodes(html);
    if (!eps.length) return [{ id: animeUrl, number: 1, title: 'فيلم / مشاهدة مباشرة' }];
    eps.forEach((e, i) => { if (!e.number) e.number = i + 1; });
    eps.sort((a, b) => a.number - b.number);
    return eps;
}

async function animercoEpisodeLinks(episodeUrl) {
    const html = await fetchText(episodeUrl);
    const tags = String(html).match(/<a[^>]*class='btn small option'[^>]*>/gi) || [];
    const names = [...String(html).matchAll(/<span class='server'>([^<]+)<\/span>/g)].map(m => m[1].trim().toLowerCase());
    const order = tags.map((t, i) => ({ tag: t, name: names[i] || '' }))
        .sort((a, b) => ((/yourupload|mp4upload/.test(b.name) ? 1 : 0) - (/yourupload|mp4upload/.test(a.name) ? 1 : 0)));
    const out = [];
    for (const { tag } of order) {
        if (out.length >= 3) break;
        const embed = (tag.match(/data-embed-url='([^']+)'/) || tag.match(/data-embed-url="([^"]+)"/) || [])[1];
        if (!embed) continue;
        try {
            const playerHtml = await fetchText(decodeHtmlEntities(embed), { headers: { Referer: episodeUrl } });
            const iframe = (String(playerHtml).match(/<iframe[^>]*src="([^"]+)"/i) || [])[1];
            if (!iframe) continue;
            const yu = iframe.match(/yourupload\.com\/embed\/([A-Za-z0-9]+)/i);
            if (yu) {
                const yuHtml = await fetchText(`https://www.yourupload.com/embed/${yu[1]}`, { headers: { Referer: 'https://www.yourupload.com/' } });
                const mp4 = String(yuHtml).match(/file:\s*'(https?:\/\/[^']+\.mp4[^']*)'/i) || String(yuHtml).match(/https?:\/\/[^\s"'<>]+\.mp4[^\s"'<>]*/i);
                if (mp4) { out.push({ url: mp4[1] || mp4[0], label: 'yourupload — FHD', referer: 'https://www.yourupload.com/' }); continue; }
            }
            const mp4u = iframe.match(/mp4upload\.com\/embed-([^\.\/]+)\.html/i);
            if (mp4u) { out.push({ url: await extractMp4uploadMp4(mp4u[1]), label: 'Mp4upload — HD' }); continue; }
        } catch (_) {}
    }
    return out;
}

// ---------- hianime.at (إنجليزي sub/dub — احتياطي) ----------
const HI_BASE = 'https://hianime.at';
const HI_API = 'https://hianime.at/api/theme';
const HI_XOR_KEY = 'otaku-embed-v1';

async function hianimeSearch(query) {
    const html = await fetchText(`${HI_BASE}/search?keyword=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    const re = /<a[^>]+href="(https:\/\/hianime\.at\/watch\/[^"]+)"[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const tag = m[0];
        let title = (tag.match(/title="([^"]+)"/) || [])[1] || '';
        title = decodeHtmlEntities(title.trim());
        if (!title) {
            const slug = url.split('/watch/')[1].replace(/-\d+$/, '').replace(/-/g, ' ').trim();
            title = slug.replace(/\b\w/g, c => c.toUpperCase());
        }
        out.push({ id: url, title });
        if (out.length >= 10) break;
    }
    return out;
}

async function hianimeEpisodes(watchUrl) {
    const idm = String(watchUrl).match(/-(\d+)$/);
    if (!idm) return [];
    const res = await axios.get(`${HI_API}/episode/list/${idm[1]}`, { timeout: 20000, headers: { 'User-Agent': WEB_UA, Referer: watchUrl } });
    const html = res.data?.html || '';
    const ids = [...String(html).matchAll(/data-id="(\d+)"/g)].map(m => m[1]);
    const nums = [...String(html).matchAll(/<div class="ssli-order"[^>]*>(\d+)<\/div>/g)].map(m => parseInt(m[1], 10));
    const eps = [];
    const n = Math.min(ids.length, nums.length);
    for (let i = 0; i < n; i++) eps.push({ id: ids[i], number: nums[i], title: 'الحلقة ' + nums[i] });
    return eps;
}

async function hianimeEpisodeLinks(watchUrl, episode) {
    const res = await axios.get(`${HI_API}/episode/servers?episodeId=${episode.id}`, { timeout: 20000, headers: { 'User-Agent': WEB_UA, Referer: watchUrl } });
    const html = res.data?.html || '';
    const items = [];
    for (const tag of (String(html).match(/<div[^>]*server-item[^>]*>/g) || [])) {
        const type = (tag.match(/data-type="([^"]+)"/) || [])[1];
        const name = (tag.match(/data-server-name="([^"]+)"/) || [])[1];
        const hash = (tag.match(/data-hash="([^"]+)"/) || [])[1];
        if (name && hash) items.push({ type, name, hash });
    }
    const pick = items.find(i => /zoko/i.test(i.name) && i.type === 'sub')
        || items.find(i => /zoko/i.test(i.name))
        || items.find(i => i.type === 'sub')
        || items[0];
    if (!pick) return [];
    const embedUrl = Buffer.from(pick.hash, 'base64').toString('utf8');
    const page = await fetchText(embedUrl, { headers: { Referer: watchUrl } });
    const p = (String(page).match(/window\.__P="([^"]+)"/) || [])[1];
    if (!p) throw new Error('تعذّر فك تشفير مشغل ZokoAnime.');
    const raw = Buffer.from(p, 'base64');
    const key = Buffer.from(HI_XOR_KEY, 'utf8');
    const dec = Buffer.from(raw.map((b, i) => b ^ key[i % key.length]));
    let info;
    try { info = JSON.parse(dec.toString('utf8')); } catch (_) { throw new Error('تعذّر فك تشفير مشغل ZokoAnime.'); }
    const src = info && info.src;
    if (!src) return [];
    try {
        const master = await fetchText(src, { headers: { Referer: embedUrl } });
        const variants = parseM3u8Variants(master, src);
        if (variants.length) return variants.map(v => ({ url: v.url, label: `HiAnime — ${v.label}`, referer: embedUrl }));
    } catch (_) {}
    return [{ url: src, label: 'HiAnime — HLS', referer: embedUrl }];
}

// حل روابط حلقة واحدة من أي مصدر (مشترك بين الحلقة الواحدة والمدى)
async function resolveAnimeEpisodeLinks(source, cdSource, animeId, ep) {
    if (source === 'cloudday') {
        const base = await cloudDayResolveBase(CLOUDDAY_SOURCES.find(s => s.name === cdSource));
        const links = await cloudDayServers(base, 'episode', ep.id);
        return await cloudDayResolveLinks(links);
    }
    if (source === 'rift') return await riftEpisodeLinks(animeId, ep);
    if (source === 'witcher') return await witcherEpisodeLinks(animeId, ep);
    if (source === 'shahiid') return await shahiidEpisodeLinks(ep.id);
    if (source === 'anime4up') return await anime4upEpisodeLinks(ep.id);
    if (source === 'animedar') return await animedarEpisodeLinks(ep.id);
    if (source === 'kartoney') return await kartoneyEpisodeLinks(ep.id);
    if (source === 'cartoondub') return [{ url: ep.url || ep.id, label: 'CartoonDub — MP4', referer: '' }];
    if (source === 'carateen') return await carateenEpisodeLinks(ep);
    if (source === 'dimakids') return await dimaEpisodeLinks(ep);
    if (source === 'animezid') return await animezidEpisodeLinks(ep);
    if (source === 'stardima') return await stardimaEpisodeLinks(ep);
    if (source === 'animerco') return await animercoEpisodeLinks(ep.id);
    if (source === 'hianime') return await hianimeEpisodeLinks(animeId, ep);
    if (source === 'arabanime') return await arabanimeEpisodeLinks(ep);
    if (source === 'okanime') return await okanimeEpisodeLinks(ep);
    if (source === 'egyaflam') return await egyaflamEpisodeLinks(ep.id);
    return [];
}


// ============================================================
// كرتون قديم مدبلج — 7 مصادر (CartoonDub + Carateen + Kartoney + ok.ru + DimaKids + AnimeZid + Stardima)
// نفس منطق .anime: بحث متوازي → قائمة مرقّمة → حلقات → جودات → تحميل
// ============================================================
const cartoonCache = new Map();

// ── تثبيت مصدر واحد لـ .cartoon (عبر .setcartoon) ──
let cartoonLockedSource = null; // null = البحث في كل المصادر
const CARTOON_SOURCE_LIST = ['cartoondub', 'carateen', 'kartoney', 'okru', 'dimakids', 'animezid', 'stardima'];
const CARTOON_SOURCE_NAMES = {
    cartoondub: { source: 'cartoondub', label: '🎨 CartoonDub' },
    carateen: { source: 'carateen', label: '📺 Carateen' },
    kartoney: { source: 'kartoney', label: '🧒 Kartoney' },
    okru: { source: 'okru', label: '📺 ok.ru' },
    dimakids: { source: 'dimakids', label: '🎬 DimaKids' },
    animezid: { source: 'animezid', label: '🌟 AnimeZid' },
    stardima: { source: 'stardima', label: '⭐ Stardima' }
};

// ---------- CartoonDub (e-droid cards API) ----------
// الرئيسية idsec=38314274 ← مسلسل (حقل 11 = id القسم) ← أجزاء ← حلقات (رابط mp4 مباشر)
const CARTOONDUB_API = 'https://srv11.e-droid.net/srv/obtener_cards.php';
const CARTOONDUB_UA = 'Android Vinebre Software';
const CARTOONDUB_HOME = '38314274';

async function cartoonDubFetchCards(idsec) {
    const res = await axios.get(CARTOONDUB_API, {
        params: { idusu: '1234567890', ind_ini: 0, idsec },
        headers: { 'User-Agent': CARTOONDUB_UA }, timeout: 20000, responseType: 'text'
    });
    return String(res.data || '').replace(/^ANDROID:OK DATOS:/, '');
}

function cartoonDubParseCards(raw) {
    const out = [];
    for (const card of String(raw || '').split(';')) {
        const c = card.trim();
        if (!c || c === 'N') continue;
        const f = c.split(',');
        const title = (f[5] || '').trim();
        if (!title) continue;
        const urlM = c.match(/https?:\/\/[^\s,;]+\.mp4/i);
        if (urlM) {
            out.push({ kind: 'episode', title, url: urlM[0] });
            continue;
        }
        const sec = (f[11] || '').trim();
        if (/^\d{7,}$/.test(sec)) out.push({ kind: 'section', title, sectionId: sec });
    }
    return out;
}

async function cartoonDubSearch(query) {
    const cards = cartoonDubParseCards(await cartoonDubFetchCards(CARTOONDUB_HOME));
    const q = normAr(query);
    // كلمات من حرفين فأكثر (لازم "بن" في "بن تن" يطابق "بن 10")
    const words = q.split(/\s+/).filter(w => w.length >= 2);
    const hits = cards.filter(c => {
        if (c.kind !== 'section') return false;
        const t = normAr(c.title);
        if (!t) return false;
        if (t.includes(q)) return true;
        return words.some(w => t.includes(w));
    });
    return hits.slice(0, 5).map(h => ({ id: h.sectionId, title: h.title }));
}

async function cartoonDubEpisodes(sectionId) {
    const eps = [];
    const walk = async (idsec, partLabel) => {
        const cards = cartoonDubParseCards(await cartoonDubFetchCards(idsec));
        for (const c of cards) {
            if (c.kind === 'episode') {
                eps.push({
                    number: eps.length + 1,
                    title: partLabel ? `${partLabel} — ${c.title}` : c.title,
                    id: c.url, url: c.url
                });
            }
        }
        for (const c of cards) {
            if (c.kind === 'section') await walk(c.sectionId, c.title);
        }
    };
    await walk(sectionId, '');
    return eps;
}

// ---------- Carateen (carateen.tv — كتالوج AES + HLS) ----------
// الكتالوج مغلّف AES-256-CBC: {iv (hex), encryptedData (hex)}، المفتاح نص عادي UTF-8
const CARATEEN_API = 'https://carateen.tv';
const CARATEEN_KEY = '7annaba3l_loves_crypto_safe_key!';
const CARATEEN_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Linux; Android 10) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36',
    'Referer': 'https://carateen.tv/'
};
let carateenCatalogCache = null;
let carateenCatalogAt = 0;

function carateenDecrypt(d) {
    const iv = Buffer.from(d.iv, 'hex');
    const decipher = crypto.createDecipheriv('aes-256-cbc', Buffer.from(CARATEEN_KEY, 'utf8'), iv);
    let out = decipher.update(Buffer.from(d.encryptedData, 'hex'), undefined, 'utf8');
    out += decipher.final('utf8');
    return JSON.parse(out);
}

async function carateenCatalog() {
    if (carateenCatalogCache && Date.now() - carateenCatalogAt < 3600000) return carateenCatalogCache;
    const [sp, tg] = await Promise.all([
        axios.get(`${CARATEEN_API}/api/sp/tvshows`, { headers: CARATEEN_HEADERS, timeout: 30000 }),
        axios.get(`${CARATEEN_API}/api/tvshows`, { headers: CARATEEN_HEADERS, timeout: 30000 })
    ]);
    const shows = [];
    for (const s of carateenDecrypt(sp.data)) shows.push({ id: s.id, kind: 'sp', title: s.name || '' });
    for (const s of carateenDecrypt(tg.data)) shows.push({ id: s.id, kind: 'tg', title: s.title || '' });
    carateenCatalogCache = shows;
    carateenCatalogAt = Date.now();
    return shows;
}

async function carateenSearch(query) {
    const shows = await carateenCatalog();
    const q = normAr(query);
    const words = q.split(/\s+/).filter(w => w.length >= 3);
    const hits = shows.filter(s => {
        const t = normAr(s.title);
        if (!t) return false;
        if (t.includes(q)) return true;
        return words.some(w => t.includes(w));
    });
    return hits.slice(0, 5).map(h => ({ id: h.id, kind: h.kind, title: h.title }));
}

async function carateenEpisodes(show) {
    const path = show.kind === 'sp' ? `/api/sp/episodes?id=${show.id}` : `/api/episodes?id=${show.id}`;
    const res = await axios.get(`${CARATEEN_API}${path}`, { headers: CARATEEN_HEADERS, timeout: 30000 });
    const list = carateenDecrypt(res.data);
    const eps = [];
    (Array.isArray(list) ? list : []).forEach((e, i) => {
        const n = parseInt(e.number, 10) || parseInt(String(e.title || '').match(/(\d+)/)?.[1] || '', 10) || (i + 1);
        eps.push({ number: n, title: e.title || e.pref || (`الحلقة ${n}`), id: e.id, kind: show.kind, showId: show.id });
    });
    eps.sort((a, b) => a.number - b.number);
    eps.forEach((e, i) => { e.number = i + 1; });
    return eps;
}

async function carateenEpisodeLinks(ep) {
    let m3u8;
    if (ep.kind === 'sp') {
        const res = await axios.post(`${CARATEEN_API}/api/sp/episode/link`, { episodeId: ep.id }, { headers: { ...CARATEEN_HEADERS, 'Content-Type': 'application/json' }, timeout: 30000 });
        m3u8 = carateenDecrypt(res.data).link;
    } else {
        const res = await axios.get(`${CARATEEN_API}/api/episode`, { params: { episodeId: ep.id, showId: ep.showId }, headers: CARATEEN_HEADERS, timeout: 30000 });
        m3u8 = carateenDecrypt(res.data).streamUrl;
    }
    if (!m3u8) throw new Error('لا يوجد رابط بث لهذه الحلقة.');
    const pl = await axios.get(m3u8, { headers: CARATEEN_HEADERS, timeout: 30000, responseType: 'text' });
    const lines = String(pl.data || '').split(/\r?\n/);
    const variants = [];
    for (let i = 0; i < lines.length; i++) {
        if (lines[i].startsWith('#EXT-X-STREAM-INF')) {
            const nameM = lines[i].match(/NAME="([^"]+)"/);
            const resM = lines[i].match(/RESOLUTION=\d+x(\d+)/);
            const bwM = lines[i].match(/BANDWIDTH=(\d+)/);
            let url = lines[i + 1] && !lines[i + 1].startsWith('#') ? lines[i + 1].trim() : null;
            if (url) {
                if (!/^https?:\/\//i.test(url)) { try { url = new URL(url, m3u8).toString(); } catch (_) {} }
                variants.push({ label: nameM ? nameM[1] : (resM ? `${resM[1]}p` : (bwM ? `${Math.round(bwM[1] / 1000)}kbps` : 'HLS')), url });
            }
        }
    }
    if (!variants.length) return [{ url: m3u8, label: 'Carateen — HLS', referer: 'https://carateen.tv/' }];
    return variants.map(v => ({ url: v.url, label: `Carateen — ${v.label}`, referer: 'https://carateen.tv/' }));
}

// ok.ru للكرتون: بدون بادئة "انمي "
async function okruSearchCartoon(query) {
    return await okruSearchRaw(query.trim());
}

// ---------- Stardima (watch.stardima.com — DooPlay، كرتون مدبلج عربي) ----------
// بحث WP: ?s= ← صفحات /tvshows/<slug>/ ← حلقات /episodes/<slug>-الموسم-N-الحلقة-M/ ←
// admin-ajax doo_player_ajax ← base64 embed_url ← strema.top ← UQLOAD ← فك packed JS ← HLS master
const STARDIMA_BASE = 'https://watch.stardima.com/watch';
const STARDIMA_AJAX = STARDIMA_BASE + '/wp-admin/admin-ajax.php';

// عنوان من داخل وسام <a> (نص، أو img alt في وسام الصورة المصغّرة) — وإلا من الـ slug
function stardimaAnchorTitle(inner, url) {
    const clean = s => String(s || '').replace(/&amp;/g, '&').replace(/&quot;/g, '"').replace(/&#0?39;/g, "'").replace(/&#8211;/g, '–').replace(/&#8212;/g, '—').replace(/&#\d+;/g, ' ').replace(/\s+/g, ' ').trim();
    const text = String(inner || '').replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
    if (text && !/^(TV|Movie|Movies)$/i.test(text)) return clean(text);
    const alt = String(inner || '').match(/alt="([^"]+)"/);
    if (alt) return clean(alt[1]);
    let slug = '';
    try { slug = decodeURIComponent(String(url || '').split('/').filter(Boolean).pop() || ''); } catch (_) {}
    return slug.replace(/[-_]+/g, ' ').trim();
}

// مطابقة العنوان/الـ slug مع البحث (كلمة كاملة أو أي كلمة ≥ حرفين — لازم "بن" في "بن تن")
function stardimaMatches(query, title, url) {
    const nq = normAr(query);
    if (!nq) return true;
    let slug = '';
    try { slug = decodeURIComponent(String(url || '').split('/').filter(Boolean).pop() || ''); } catch (_) {}
    const hay = normAr(title) + ' ' + normAr(slug.replace(/[-_]+/g, ' '));
    if (hay.includes(nq)) return true;
    const words = nq.split(/\s+/).filter(w => w.length >= 2);
    return words.some(w => hay.includes(w));
}

async function stardimaSearch(query) {
    const html = await fetchText(`${STARDIMA_BASE}/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    for (const m of String(html).matchAll(/<a[^>]+href="(https:\/\/watch\.stardima\.com\/watch\/tvshows\/[^"]+)"[^>]*>([\s\S]*?)<\/a>/g)) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = stardimaAnchorTitle(m[2], url);
        if (!title || !stardimaMatches(query, title, url)) continue;
        out.push({ id: url, title });
    }
    return out.slice(0, 5);
}

// صفحة المسلسل → قائمة الحلقات (مرتّبة موسم ثم حلقة، وترقيم متسلسل ليناسب اختيار/مدى البوت)
async function stardimaEpisodes(showUrl) {
    const html = await fetchText(showUrl);
    const eps = []; const seen = new Set();
    for (const m of String(html).matchAll(/https:\/\/watch\.stardima\.com\/watch\/episodes\/[^\s"'\\<>]+/g)) {
        const url = m[0];
        if (seen.has(url)) continue;
        seen.add(url);
        let slug = '';
        try { slug = decodeURIComponent(url.split('/').filter(Boolean).pop() || ''); } catch (_) {}
        const sm = slug.match(/الموسم-(\d+)-الحلقة-(\d+)/);
        if (!sm) continue;
        eps.push({ id: url, season: parseInt(sm[1], 10), epNum: parseInt(sm[2], 10) });
    }
    eps.sort((a, b) => (a.season - b.season) || (a.epNum - b.epNum));
    return eps.map((e, i) => ({ id: e.id, number: i + 1, title: `الموسم ${e.season} — الحلقة ${e.epNum}` }));
}

// فك رابط سيرفر UQLOAD: صفحة السيرفر ← packed JS ← file (m3u8 master) ← جودات
async function stardimaResolveHost(hostUrl, epUrl) {
    const page = await fetchText(hostUrl, { headers: { Referer: epUrl } });
    const unpacked = deanEdwardsUnpack(page) || String(page || '');
    const fileM = unpacked.match(/file\s*:\s*"(https?:\/\/[^"]+\.m3u8[^"]*)"/) || unpacked.match(/file\s*:\s*'(https?:\/\/[^']+\.m3u8[^']*)'/);
    if (!fileM) return null;
    const masterUrl = fileM[1];
    try {
        const master = await fetchText(masterUrl, { headers: { Referer: hostUrl } });
        const variants = parseM3u8Variants(master, masterUrl);
        if (variants.length) return variants.map(v => ({ url: v.url, label: `Stardima — ${v.label}`, referer: hostUrl }));
    } catch (_) {}
    return [{ url: masterUrl, label: 'Stardima — HLS', referer: hostUrl }];
}

// حل روابط حلقة Stardima: صفحة الحلقة ← خيارات dooplay ← admin-ajax ← embed ← سيرفر (UQLOAD أولاً)
async function stardimaEpisodeLinks(ep) {
    const epUrl = ep.id || ep.url;
    if (!epUrl) return [];
    const html = await fetchText(epUrl);
    const opts = [];
    const seen = new Set();
    for (const m of String(html).matchAll(/dooplay_player_option[^>]*>/g)) {
        const tag = m[0];
        const post = (tag.match(/data-post='(\d+)'/) || tag.match(/data-post="(\d+)"/) || [])[1];
        const nume = (tag.match(/data-nume='(\d+)'/) || tag.match(/data-nume="(\d+)"/) || [])[1];
        if (!post || !nume) continue;
        const key = post + ':' + nume;
        if (seen.has(key)) continue;
        seen.add(key);
        opts.push({ post, nume });
    }
    // جرّب السيرفرات بالترتيب المفضّل (2 ثم 3 ثم 1)، ثم الباقي
    const pref = ['2', '3', '1'];
    opts.sort((a, b) => {
        const ai = pref.indexOf(a.nume), bi = pref.indexOf(b.nume);
        if (ai === -1 && bi === -1) return 0;
        if (ai === -1) return 1;
        if (bi === -1) return -1;
        return ai - bi;
    });
    for (const o of opts) {
        try {
            const j = await fetchTextPost(STARDIMA_AJAX, { action: 'doo_player_ajax', post: o.post, nume: o.nume, type: 'tv' }, { headers: { Referer: epUrl } });
            const data = typeof j === 'string' ? JSON.parse(j) : j;
            const b64 = data && data.embed_url;
            if (!b64) continue;
            const decoded = Buffer.from(String(b64), 'base64').toString('utf8');
            let hostUrl = decoded;
            try { const u = new URL(decoded); const u2 = u.searchParams.get('url'); if (u2) hostUrl = u2; } catch (_) {}
            if (!/^https?:\/\//i.test(hostUrl)) continue;
            if (/uqload\.(com|vc)/i.test(hostUrl)) {
                const links = await stardimaResolveHost(hostUrl, epUrl);
                if (links && links.length) return links;
                continue;
            }
            // سيرفر غير UQLOAD: جرّب استخراج mp4/m3u8 مباشر من صفحته
            try {
                const hp = await fetchText(hostUrl, { headers: { Referer: epUrl } });
                const mm = String(hp).match(/https?:\/\/[^"'\s<>]+\.(?:mp4|m3u8)(?:\?[^"'\s<>]*)?/i);
                if (mm) return [{ url: mm[0], label: 'Stardima — ' + (mm[0].includes('.m3u8') ? 'HLS' : 'MP4'), referer: hostUrl }];
            } catch (_) {}
        } catch (_) {}
    }
    return [];
}

async function cartoonSearchOne(name, query) {
    const e = CARTOON_SOURCE_NAMES[name];
    if (!e) return [];
    if (e.source === 'cartoondub') return await cartoonDubSearch(query);
    if (e.source === 'carateen') return await carateenSearch(query);
    if (e.source === 'kartoney') return await kartoneySearch(query);
    if (e.source === 'okru') return (await okruSearchCartoon(query)).map(v => ({ id: v.id, title: v.title }));
    if (e.source === 'dimakids') return await dimaSearch(query);
    if (e.source === 'animezid') return await animezidSearch(query);
    if (e.source === 'stardima') return await stardimaSearch(query);
    return [];
}

// ============================================================
// كرتون إنجليزي — .cartoon-en (ToonTales + SuperCartoons + FunnierMoments + Archive.org)
// فيديوهات منفردة (شورت) — نتائج البحث تذهب مباشرة للجودات (مثل ok.ru)، بلا قائمة حلقات
// ============================================================
const cartoonEnCache = new Map();

// ── تثبيت مصدر واحد لـ .cartoon-en (عبر .setcartoon-en) ──
let cartoonEnLockedSource = null; // null = البحث في كل المصادر
const CARTOON_EN_SOURCE_LIST = ['toontales', 'supercartoons', 'funniermoments', 'archiveorg'];
const CARTOON_EN_SOURCE_NAMES = {
    toontales: { source: 'toontales', label: '🎬 ToonTales' },
    supercartoons: { source: 'supercartoons', label: '🐰 SuperCartoons' },
    funniermoments: { source: 'funniermoments', label: '😂 FunnierMoments' },
    archiveorg: { source: 'archiveorg', label: '📚 Archive.org' }
};

// عنوان من داخل وسام <a> (نص أو img alt) — وإلا من الـ slug
function cenAnchorTitle(inner, url) {
    const clean = s => String(s || '').replace(/&amp;/g, '&').replace(/&quot;/g, '"').replace(/&#0?39;/g, "'").replace(/&#8217;/g, "'").trim();
    const text = String(inner || '').replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
    if (text) return clean(text);
    const alt = String(inner || '').match(/alt="([^"]+)"/);
    if (alt) return clean(alt[1]);
    let slug = '';
    try { slug = decodeURIComponent(String(url || '').split('/').filter(Boolean).pop() || ''); } catch (_) {}
    return slug.replace(/[-_]+/g, ' ').replace(/\b\w/g, c => c.toUpperCase()).trim();
}

// مطابقة العنوان/الـ slug مع البحث (كلمة كاملة أو أي كلمة ≥3 أحرف)
function cenMatches(query, title, url) {
    const nq = normAr(query);
    if (!nq) return true;
    let slug = '';
    try { slug = decodeURIComponent(String(url || '').split('/').filter(Boolean).pop() || ''); } catch (_) {}
    const hay = normAr(title) + ' ' + normAr(slug.replace(/[-_]+/g, ' '));
    if (hay.includes(nq)) return true;
    const words = nq.split(/\s+/).filter(w => w.length >= 3);
    return words.some(w => hay.includes(w));
}

// ---------- ToonTales (toontales.net — كرتون كلاسيكي، mp4 مباشر على ww.toontales.net) ----------
// بحث WP: ?s= ← روابط /short/<slug>/ (العناوين في img alt)
async function toontalesSearch(query) {
    const html = await fetchText(`https://www.toontales.net/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    for (const m of String(html).matchAll(/<a[^>]+href="(https:\/\/www\.toontales\.net\/short\/[^"]+)"[^>]*>([\s\S]*?)<\/a>/g)) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = cenAnchorTitle(m[2], url);
        if (!title || !cenMatches(query, title, url)) continue;
        out.push({ id: url, title });
    }
    return out.slice(0, 5);
}

// ---------- SuperCartoons (supercartoons.net — كرتون كلاسيكي، mp4 مباشر على ww.supercartoons.net) ----------
// بحث WP: ?s= ← روابط /cartoon/<slug>/
async function supercartoonsSearch(query) {
    const html = await fetchText(`https://www.supercartoons.net/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    for (const m of String(html).matchAll(/<a[^>]+href="(https:\/\/www\.supercartoons\.net\/cartoon\/[^"]+)"[^>]*>([\s\S]*?)<\/a>/g)) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = cenAnchorTitle(m[2], url);
        if (!title || !cenMatches(query, title, url)) continue;
        out.push({ id: url, title });
    }
    return out.slice(0, 5);
}

// ---------- FunnierMoments (funniermoments.net — كرتون، mp4 مباشر على ww.funniermoments.net) ----------
// بحث WP: ?s= ← روابط منشورات /<slug>/ (العنوان نص الوسام)
async function funniermomentsSearch(query) {
    const html = await fetchText(`https://www.funniermoments.net/?s=${encodeURIComponent(query)}`);
    const out = []; const seen = new Set();
    for (const m of String(html).matchAll(/<a[^>]+href="(https:\/\/www\.funniermoments\.net\/([a-z0-9-]+)\/)"[^>]*>([\s\S]*?)<\/a>/g)) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = cenAnchorTitle(m[3], url);
        if (!title || !cenMatches(query, title, url)) continue;
        out.push({ id: url, title });
    }
    return out.slice(0, 5);
}

// ---------- Archive.org (API عام — بلا سكراب) ----------
// advancedsearch ← metadata ← أكبر ملف MPEG4 mp4 ← رابط /download/ مباشر
async function archiveorgSearch(query) {
    // بحث في حقل العنوان فقط — البحث العام يرجع أخبار تلفزيون (نصوصها تذكر الاسم)
    const q = encodeURIComponent(`title:(${query})`) + '+AND+mediatype%3A%28movies%29';
    const res = await axios.get(`https://archive.org/advancedsearch.php?q=${q}&fl%5B%5D=identifier&fl%5B%5D=title&rows=10&output=json`, { headers: { 'User-Agent': WEB_UA }, timeout: 30000 });
    const docs = (res.data && res.data.response && res.data.response.docs) || [];
    return docs.filter(d => d && d.identifier).slice(0, 5).map(d => ({ id: d.identifier, title: (d.title || d.identifier) }));
}

async function archiveorgResolve(identifier) {
    const res = await axios.get(`https://archive.org/metadata/${encodeURIComponent(identifier)}`, { headers: { 'User-Agent': WEB_UA }, timeout: 30000 });
    const files = (res.data && res.data.files) || [];
    const mp4s = files.filter(f => f && /\.mp4$/i.test(f.name || ''));
    if (!mp4s.length) throw new Error('لا يوجد ملف mp4 في هذا العنصر.');
    mp4s.sort((a, b) => ((b.format === 'MPEG4') - (a.format === 'MPEG4')) || ((b.size || 0) - (a.size || 0)));
    const f = mp4s[0];
    const url = `https://archive.org/download/${encodeURIComponent(identifier)}/${encodeURIComponent(f.name)}`;
    return [{ url, label: 'Archive.org — MP4', referer: `https://archive.org/details/${identifier}` }];
}

// حل رابط شورت من مواقع ووردبريس الثلاثة: صفحة المنشور فيها mp4 مباشر على ww.<domain>
async function wpCartoonResolve(pageUrl) {
    const html = await fetchText(pageUrl);
    const m = String(html).match(/https:\/\/ww\.[a-z0-9-]+\.net\/[^"'\s]+\.mp4/i);
    if (!m) throw new Error('لا يوجد رابط فيديو في هذه الصفحة.');
    return [{ url: m[0], label: 'MP4', referer: pageUrl }];
}

async function cartoonEnResolveLinks(source, item) {
    if (source === 'archiveorg') return await archiveorgResolve(item.id);
    return await wpCartoonResolve(item.id);
}

async function cartoonEnSearchOne(name, query) {
    const e = CARTOON_EN_SOURCE_NAMES[name];
    if (!e) return [];
    if (e.source === 'toontales') return await toontalesSearch(query);
    if (e.source === 'supercartoons') return await supercartoonsSearch(query);
    if (e.source === 'funniermoments') return await funniermomentsSearch(query);
    if (e.source === 'archiveorg') return await archiveorgSearch(query);
    return [];
}

// ---------- DimaKids (dimakids.com — بحث JSON + mp4 مباشر موقّع) ----------
// البحث حرفي: الاسم الكامل قد يرجع صفر ("بن تن") — جرّب الكلمات منفردة ("بن 10")
const DIMA_API = 'https://www.dimakids.com';
const DIMA_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

async function dimaSearch(query) {
    const tryOnce = async (q) => {
        const res = await axios.get(`${DIMA_API}/search_results.php`, {
            params: { q, ajax: 1 },
            headers: { 'User-Agent': DIMA_UA }, timeout: 20000
        });
        const list = (res.data && res.data.results && res.data.results.series) || [];
        return list.map(s => ({ id: String(s.id), title: s.title, slug: String(s.subtitle || '').trim() }));
    };
    let results = await tryOnce(query);
    if (!results.length) {
        const words = String(query).split(/\s+/).filter(w => w.length >= 3).sort((a, b) => b.length - a.length);
        for (const w of words) {
            results = await tryOnce(w);
            if (results.length) break;
        }
    }
    const q = normAr(query);
    const words = q.split(/\s+/).filter(w => w.length >= 2);
    const hits = results.filter(r => {
        const t = normAr(r.title);
        if (!t) return false;
        if (t.includes(q)) return true;
        return words.some(w => t.includes(w));
    });
    return (hits.length ? hits : results).slice(0, 5);
}

async function dimaEpisodes(series) {
    const slug = String(series.slug || '').trim().toLowerCase().replace(/\s+/g, '-').replace(/[^a-z0-9\-]/g, '');
    const ep1Url = `${DIMA_API}/${slug}-${series.id}-anime-streaming.html`;
    const res = await axios.get(ep1Url, { headers: { 'User-Agent': DIMA_UA, 'Referer': DIMA_API + '/' }, timeout: 20000, responseType: 'text' });
    const html = String(res.data || '');
    const eps = [];
    const seen = new Set();
    for (const it of html.matchAll(/<a[^>]*href="([^"]+?-\d+\.html)#sets"[^>]*title="([^"]+)"/g)) {
        const title = it[2].trim();
        const m = title.match(/الحلقة\s*(\d+)/) || title.match(/(\d+)\s*$/);
        const num = parseInt((m || [])[1] || '', 10);
        if (!num || seen.has(num)) continue;
        seen.add(num);
        const pageUrl = it[1].startsWith('http') ? it[1] : `${DIMA_API}/${it[1]}`;
        eps.push({ number: num, title, id: pageUrl, url: pageUrl });
    }
    eps.sort((a, b) => a.number - b.number);
    eps.forEach((e, i) => { e.number = i + 1; });
    return eps;
}

async function dimaEpisodeLinks(ep) {
    const pageUrl = ep.url || ep.id;
    const res = await axios.get(pageUrl, { headers: { 'User-Agent': DIMA_UA, 'Referer': DIMA_API + '/' }, timeout: 20000, responseType: 'text' });
    const mp4s = [...new Set((String(res.data || '').match(/https?:\/\/[^\s"'<>]+\.mp4[^\s"'<>]*/g) || []))];
    if (!mp4s.length) throw new Error('لا يوجد رابط mp4 في صفحة الحلقة.');
    return [{ url: mp4s[0], label: 'DimaKids — MP4', referer: pageUrl }];
}

// ---------- AnimeZid (animezid.org — playback session + MegaMax/Uqload) ----------
// play.php (كوكيز + CSRF) ← POST /web-playback/sessions ← resolve ← launch (60 ثانية) ← المزوّد
// بلا Referer في طلبات الـ session (بيرجع 403)
const AZ_API = 'https://animezid.org';
const AZ_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

async function animezidSearch(query) {
    const res = await axios.get(`${AZ_API}/search.php`, {
        params: { keywords: query },
        headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const out = [];
    const seen = new Set();
    // البطاقة: <a href=".../series/<slug>/" aria-label="فتح مسلسل <العنوان>"> (العنوان أيضاً في alt الصورة)
    for (const m of html.matchAll(/<a[^>]*href="(?:https?:\/\/animezid\.org)?\/series\/([^"\/]+)\/?"[^>]*>/g)) {
        const slug = decodeURIComponent(m[1]);
        if (seen.has(slug)) continue;
        seen.add(slug);
        const tag = m[0];
        let title = (tag.match(/aria-label="فتح\s+([^"]+)"/) || [])[1] || '';
        title = title.replace(/^(مسلسل|فيلم|أنمي|انمي|كرتون)\s+/, '').trim();
        if (!title) title = slug.replace(/-/g, ' ');
        out.push({ id: slug, title });
    }
    return out.slice(0, 5);
}

async function animezidEpisodes(slug) {
    // صفحة المسلسل → أحدث حلقة → play.php فيها قائمة الحلقات كاملة
    const sp = await axios.get(`${AZ_API}/series/${encodeURIComponent(slug)}`, {
        headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text'
    });
    const firstVid = (String(sp.data || '').match(/watch\.php\?vid=([0-9a-f]{9})/) || [])[1];
    if (!firstVid) throw new Error('لا توجد حلقات في صفحة المسلسل.');
    const play = await axios.get(`${AZ_API}/play.php`, {
        params: { vid: firstVid },
        headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text'
    });
    const phtml = String(play.data || '');
    const eps = [];
    const seen = new Set();
    for (const m of phtml.matchAll(/<a[^>]*>/g)) {
        const tag = m[0];
        const vid = (tag.match(/watch\.php\?vid=([0-9a-f]{9})/) || [])[1];
        const num = parseInt((tag.match(/الحلقة\s*(\d+)/) || [])[1] || '', 10);
        if (vid && num && !seen.has(num)) {
            seen.add(num);
            eps.push({ number: num, title: `الحلقة ${num}`, id: vid });
        }
    }
    if (!eps.length) {
        const vids = [...new Set(phtml.match(/watch\.php\?vid=([0-9a-f]{9})/g) || [])].map(x => x.match(/vid=([0-9a-f]{9})/)[1]);
        vids.forEach((v, i) => eps.push({ number: i + 1, title: `الحلقة ${i + 1}`, id: v }));
    }
    eps.sort((a, b) => a.number - b.number);
    return eps;
}

async function animezidEpisodeLinks(ep) {
    const vid = ep.id;
    const play = await axios.get(`${AZ_API}/play.php`, {
        params: { vid },
        headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text'
    });
    const cookies = (play.headers['set-cookie'] || []).map(c => c.split(';')[0]).join('; ');
    const csrf = (String(play.data || '').match(/data-playback-csrf\s*=\s*"([^"]+)"/) || [])[1];
    if (!csrf) throw new Error('لم يتم العثور على توكن التشغيل.');
    const H = { 'User-Agent': AZ_UA, 'Content-Type': 'application/json', 'X-Playback-CSRF': csrf, 'Origin': AZ_API, 'Cookie': cookies };
    const sess = await axios.post(`${AZ_API}/web-playback/sessions`, { content_id: vid }, { headers: H, timeout: 20000 });
    const sid = sess.data && sess.data.session_id;
    const sources = (sess.data && sess.data.sources) || [];
    if (!sid || !sources.length) throw new Error('لا توجد سيرفرات متاحة لهذه الحلقة.');
    const links = [];
    const resolve = async (srcId) => {
        const r = await axios.post(`${AZ_API}/web-playback/sessions/${sid}/sources/${srcId}/resolve`, {}, { headers: H, timeout: 20000 });
        return r.data && r.data.launch_url;
    };
    const followLaunch = async (launchUrl) => {
        const r = await axios.get(launchUrl, { headers: { 'User-Agent': AZ_UA, 'Cookie': cookies }, timeout: 20000, maxRedirects: 0, validateStatus: s => s < 500 });
        return r.headers.location || null;
    };
    // 1) MegaMax أولاً (أعلى جودة) — جرّب mp4upload في كل جودة (ملفاته بتموت أحياناً)
    const mega = sources.find(s => s.provider === 'MegaMax');
    if (mega) {
        try {
            const launch = await resolve(mega.id);
            const dest = launch ? await followLaunch(launch) : null;
            if (dest && dest.includes('megamax.me/iframe/')) {
                const page = await axios.get(dest, { headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text' });
                const appM = String(page.data || '').match(/<script[^>]*data-page="app"[^>]*>([\s\S]*?)<\/script>/);
                if (appM) {
                    const app = JSON.parse(appM[1]);
                    const partial = await axios.get(dest, {
                        headers: { 'User-Agent': AZ_UA, 'X-Inertia': 'true', 'X-Inertia-Version': app.version, 'X-Inertia-Partial-Component': 'files/mirror/video', 'X-Inertia-Partial-Data': 'streams' },
                        timeout: 20000, responseType: 'text'
                    });
                    const streams = (JSON.parse(partial.data).props && JSON.parse(partial.data).props.streams && JSON.parse(partial.data).props.streams.data) || [];
                    for (const st of streams) {
                        // mp4upload أولاً (mp4 مباشر)، ثم uqload (m3u8)
                        const mp4 = (st.mirrors || []).find(m => m.driver === 'mp4upload');
                        if (mp4) {
                            try {
                                const embUrl = mp4.link.startsWith('http') ? mp4.link : 'https:' + mp4.link;
                                const emb = await axios.get(embUrl, { headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text' });
                                const mm = String(emb.data || '').match(/player\.src\(\{\s*type:\s*"video\/mp4",\s*src:\s*"(https:\/\/a\d+\.mp4upload\.com:183\/d\/[^"]+\/video\.mp4)"/);
                                if (mm) links.push({ url: mm[1], label: `AnimeZid — ${st.label} (mp4upload)`, referer: embUrl });
                            } catch (_) {}
                        }
                        const uqm = (st.mirrors || []).find(m => m.driver === 'uqload');
                        if (uqm) {
                            try {
                                const embUrl = uqm.link.startsWith('http') ? uqm.link : 'https:' + uqm.link;
                                const m3u8 = await extractUqloadM3u8(embUrl);
                                const plRes = await axios.get(m3u8, { headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text' });
                                const variants = parseM3u8Variants(String(plRes.data || ''), m3u8);
                                if (variants.length) {
                                    for (const v of variants) links.push({ url: v.url, label: `AnimeZid — ${st.label} ${v.label} (Uqload)`, referer: 'https://uqload.com/' });
                                } else {
                                    links.push({ url: m3u8, label: `AnimeZid — ${st.label} (Uqload)`, referer: 'https://uqload.com/' });
                                }
                            } catch (_) {}
                        }
                    }
                }
            }
        } catch (_) {}
    }
    // 2) Uqload (احتياطي موثوق) — m3u8 بجوداته
    const uq = sources.find(s => s.provider === 'Uqload' && s.type === 'embedded_web');
    if (uq) {
        try {
            const launch = await resolve(uq.id);
            const dest = launch ? await followLaunch(launch) : null;
            if (dest && dest.includes('uqload')) {
                const m3u8 = await extractUqloadM3u8(dest);
                const plRes = await axios.get(m3u8, { headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text' });
                const variants = parseM3u8Variants(String(plRes.data || ''), m3u8);
                if (variants.length) {
                    for (const v of variants) links.push({ url: v.url, label: `AnimeZid — ${v.label} (Uqload)`, referer: 'https://uqload.com/' });
                } else {
                    links.push({ url: m3u8, label: 'AnimeZid — HLS (Uqload)', referer: 'https://uqload.com/' });
                }
            }
        } catch (_) {}
    }
    if (!links.length) throw new Error('لا توجد روابط تحميل متاحة لهذه الحلقة (كل السيرفرات ميتة حالياً).');
    return links;
}

// ============================================================
// v108 — دوال جديدة: MegaMax المشترك + ArabAnime + okanime + EgyAflam
// ============================================================

// ---------- MegaMax / share4max (مشترك: animezid + okanime + shahiid) ----------
// iframe (share4max/megamax.me) → streams (جودات + مرايا) عبر طلب Inertia الجزئي
async function megaMaxStreams(iframeUrl, referer) {
    const page = await axios.get(iframeUrl, { headers: { 'User-Agent': AZ_UA, 'Referer': referer || iframeUrl }, timeout: 20000, responseType: 'text' });
    const appM = String(page.data || '').match(/<script[^>]*data-page="app"[^>]*>([\s\S]*?)<\/script>/);
    if (!appM) throw new Error('لم يتم العثور على بيانات MegaMax.');
    const app = JSON.parse(appM[1]);
    const partial = await axios.get(iframeUrl, {
        headers: { 'User-Agent': AZ_UA, 'X-Inertia': 'true', 'X-Inertia-Version': app.version, 'X-Inertia-Partial-Component': 'files/mirror/video', 'X-Inertia-Partial-Data': 'streams', 'Referer': referer || iframeUrl },
        timeout: 20000, responseType: 'text'
    });
    const pdata = JSON.parse(partial.data);
    return (pdata.props && pdata.props.streams && pdata.props.streams.data) || [];
}

// streams من MegaMax → روابط تحميل (mp4upload mp4 + uqload m3u8 + lulustream m3u8)
async function megaMaxLinks(streams, labelPrefix) {
    const links = [];
    for (const st of streams) {
        const mp4 = (st.mirrors || []).find(m => m.driver === 'mp4upload');
        if (mp4) {
            try {
                const embUrl = mp4.link.startsWith('http') ? mp4.link : 'https:' + mp4.link;
                const emb = await axios.get(embUrl, { headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text' });
                const mm = String(emb.data || '').match(/player\.src\(\{\s*type:\s*"video\/mp4",\s*src:\s*"(https:\/\/a\d+\.mp4upload\.com:183\/d\/[^"]+\/video\.mp4)"/);
                if (mm) links.push({ url: mm[1], label: `${labelPrefix} — ${st.label} (mp4upload)`, referer: embUrl });
            } catch (_) {}
        }
        const uqm = (st.mirrors || []).find(m => m.driver === 'uqload');
        if (uqm) {
            try {
                const embUrl = uqm.link.startsWith('http') ? uqm.link : 'https:' + uqm.link;
                const m3u8 = await extractUqloadM3u8(embUrl);
                const plRes = await axios.get(m3u8, { headers: { 'User-Agent': AZ_UA }, timeout: 20000, responseType: 'text' });
                const variants = parseM3u8Variants(String(plRes.data || ''), m3u8);
                if (variants.length) {
                    for (const v of variants) links.push({ url: v.url, label: `${labelPrefix} — ${st.label} ${v.label} (Uqload)`, referer: 'https://uqload.com/' });
                } else {
                    links.push({ url: m3u8, label: `${labelPrefix} — ${st.label} (Uqload)`, referer: 'https://uqload.com/' });
                }
            } catch (_) {}
        }
        const lulu = (st.mirrors || []).find(m => /lulu/i.test(m.driver || ''));
        if (lulu) {
            try {
                const embUrl = lulu.link.startsWith('http') ? lulu.link : 'https:' + lulu.link;
                const m3u8 = await extractLuluM3u8(embUrl);
                links.push({ url: m3u8, label: `${labelPrefix} — ${st.label} (LuluStream)`, referer: embUrl });
            } catch (_) {}
        }
    }
    return links;
}

// LuluStream: صفحة التضمين ← JS مضغوط ← m3u8 (Referer صفحة التضمين؛ إعادة بالكوكيز لو رفض)
async function extractLuluM3u8(embedUrl) {
    const clean = u => String(u || '').replace(/\\u0026/g, '&').replace(/\\\//g, '/');
    const res = await axios.get(embedUrl, { headers: { 'User-Agent': AZ_UA, 'Referer': embedUrl }, timeout: 20000, responseType: 'text' });
    const cookies = (res.headers['set-cookie'] || []).map(c => c.split(';')[0]).join('; ');
    let src = deanEdwardsUnpack(String(res.data || '')) || String(res.data || '');
    let m = src.match(/https?:\/\/[^\s"'<>]+\.m3u8[^\s"'<>]*/i);
    if (m) return clean(m[0]);
    if (cookies) {
        const res2 = await axios.get(embedUrl, { headers: { 'User-Agent': AZ_UA, 'Referer': embedUrl, 'Cookie': cookies }, timeout: 20000, responseType: 'text' });
        src = deanEdwardsUnpack(String(res2.data || '')) || String(res2.data || '');
        m = src.match(/https?:\/\/[^\s"'<>]+\.m3u8[^\s"'<>]*/i);
        if (m) return clean(m[0]);
    }
    throw new Error('لم يتم العثور على رابط m3u8 في LuluStream.');
}

// ---------- ArabAnime (arabanime.net — mp4 مباشر على server.sanime.net) ----------
// البحث API يعمل بـ axios عادي؛ العرض والحلقات بيانات base64 في الصفحة؛
// الرابط المباشر = https://server.sanime.net/Video3/{anime_id}/{episode_number}.mp4
// تم التحقق 2026-11-06: ناروتو شيبودن ح1 193,625,987 بايت، 1450.6 ثانية
const ARABANIME_API = 'https://www.arabanime.net';
const ARABANIME_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

function arabanimeDecodeB64(s) {
    return JSON.parse(Buffer.from(String(s || ''), 'base64').toString('utf-8'));
}

async function arabanimeSearch(query) {
    const res = await axios.get(`${ARABANIME_API}/api/search`, {
        params: { q: query },
        headers: { 'User-Agent': ARABANIME_UA }, timeout: 20000
    });
    const list = (res.data && res.data.SearchResaults) || [];
    return list.map(x => {
        try {
            const d = arabanimeDecodeB64(x);
            return { id: `${d.anime_id}:${d.anime_slug}`, title: d.anime_name, type: /movie|ova/i.test(d.anime_type || '') ? 'movie' : 'series' };
        } catch (_) { return null; }
    }).filter(Boolean).slice(0, 5);
}

async function arabanimeEpisodes(animeId) {
    const [id, slug] = String(animeId || '').split(':');
    if (!id) throw new Error('معرّف أنمي غير صالح.');
    const res = await axios.get(`${ARABANIME_API}/show-${id}/${slug || ''}`, {
        headers: { 'User-Agent': ARABANIME_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const m = html.match(/[A-Za-z0-9+/=]{500,}/);
    if (!m) throw new Error('لم يتم العثور على بيانات الحلقات.');
    const data = arabanimeDecodeB64(m[0]);
    const eps = (data.EPS || []).map(e => ({
        id: `${id}:${e.episode_number}`,
        number: parseInt(e.episode_number, 10) || 0,
        title: e.episode_name || `الحلقة ${e.episode_number}`,
        animeId: String(id)
    })).filter(e => e.number > 0);
    eps.sort((a, b) => a.number - b.number);
    if (!eps.length) throw new Error('لا توجد حلقات.');
    return eps;
}

async function arabanimeEpisodeLinks(ep) {
    const url = `https://server.sanime.net/Video3/${ep.animeId}/${ep.number}.mp4`;
    try {
        const h = await axios.head(url, { headers: { 'User-Agent': ARABANIME_UA }, timeout: 15000, maxRedirects: 3 });
        const len = parseInt(h.headers['content-length'] || '0', 10);
        if (h.status >= 400 || len < 1000000) throw new Error('ملف غير صالح');
    } catch (e) {
        throw new Error('رابط ArabAnime غير متاح لهذه الحلقة.');
    }
    return [{ url, label: 'ArabAnime — MP4', referer: '' }];
}

// ---------- okanime (ww3.okanime.xyz — MegaMax ← mp4upload) ----------
// تم التحقق: ناروتو شيبودن ح1 170,831,185 بايت، 1388.3 ثانية، 720p
// ملحوظة: ناروتو الكلاسيكي غير موجود (شيبودن وبوروتو والأفلام فقط)
const OKANIME_API = 'https://ww3.okanime.xyz';
const OKANIME_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

async function okanimeSearch(query) {
    const res = await axios.get(`${OKANIME_API}/anime-list`, {
        params: { q: query },
        headers: { 'User-Agent': OKANIME_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const out = []; const seen = new Set();
    for (const m of html.matchAll(/<a[^>]*href="(?:https?:\/\/ww3\.okanime\.xyz)?\/anime\/([^"\/\?]+)"[^>]*>([\s\S]{0,200}?)<\/a>/g)) {
        const slug = decodeURIComponent(m[1]);
        if (seen.has(slug)) continue;
        seen.add(slug);
        let title = m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
        if (!title) title = slug.replace(/-/g, ' ');
        out.push({ id: slug, title });
    }
    return out.slice(0, 5);
}

async function okanimeEpisodes(slug) {
    const res = await axios.get(`${OKANIME_API}/anime/${encodeURIComponent(slug)}`, {
        headers: { 'User-Agent': OKANIME_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const eps = []; const seen = new Set();
    const esc = slug.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const re = new RegExp(`href="(?:https?:\\/\\/ww3\\.okanime\\.xyz)?\\/episode\\/(${esc}-episode-(\\d+))\\/?"`, 'g');
    let m;
    while ((m = re.exec(html)) !== null) {
        const epSlug = m[1];
        const num = parseInt(m[2], 10);
        if (seen.has(num)) continue;
        seen.add(num);
        eps.push({ id: epSlug, number: num, title: `الحلقة ${num}` });
    }
    eps.sort((a, b) => a.number - b.number);
    if (!eps.length) throw new Error('لا توجد حلقات.');
    return eps;
}

async function okanimeEpisodeLinks(ep) {
    const res = await axios.get(`${OKANIME_API}/episode/${encodeURIComponent(ep.id)}`, {
        headers: { 'User-Agent': OKANIME_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const iframe = (html.match(/https?:\/\/(?:www\.)?(?:share4max\.com|megamax\.me)\/iframe\/[A-Za-z0-9]+/i) || [])[0];
    if (iframe) {
        const streams = await megaMaxStreams(iframe, `${OKANIME_API}/episode/${encodeURIComponent(ep.id)}`);
        const links = await megaMaxLinks(streams, 'OkAnime');
        if (links.length) return links;
    }
    // احتياطي: تضمين mp4upload مباشر في الصفحة
    const mp4 = (html.match(/mp4upload\.com\/embed-([^\.\/"']+)\.html/i) || [])[1];
    if (mp4) {
        try { return [{ url: await extractMp4uploadMp4(mp4), label: 'OkAnime — MP4 (mp4upload)', referer: `https://www.mp4upload.com/embed-${mp4}.html` }]; } catch (_) {}
    }
    throw new Error('لا توجد روابط تحميل متاحة لهذه الحلقة.');
}

// ---------- EgyAflam (egyaflam.com — DooPlay + vidspeed HLS) ----------
// البحث يرجّع حلقات منفردة بلا صفحة مسلسل — الاختيار يذهب للجودات فوراً
// تم التحقق: ناروتو شيبودن ح1 74,408,110 بايت، 1384.6 ثانية، 480p
const EGYAFLAM_BASE = 'https://egyaflam.com';
const EGYAFLAM_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

async function egyaflamSearch(query) {
    const res = await axios.get(`${EGYAFLAM_BASE}/`, {
        params: { s: query },
        headers: { 'User-Agent': EGYAFLAM_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const out = []; const seen = new Set();
    for (const m of html.matchAll(/<a[^>]*href="(https:\/\/egyaflam\.com\/watch\/[^"\/]+\/?)"[^>]*>([\s\S]{0,400}?)<\/a>/g)) {
        const url = m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        // العنوان الحقيقي في alt الصورة (نص الرابط نفسه مجرد كلمة "مسلسل")
        const alt = (m[2].match(/alt="([^"]{3,160})"/) || [])[1];
        let title = alt ? decodeHtmlEntities(alt).trim()
            : m[2].replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
        if (!title || title === 'مسلسل') {
            try { title = decodeURIComponent(url.replace(/.*\/watch\//, '').replace(/\/$/, '')).replace(/-/g, ' '); } catch (_) { title = ''; }
        }
        if (!title) continue;
        out.push({ id: url, title });
    }
    return out.slice(0, 5);
}

async function extractVidspeedM3u8(embedUrl) {
    const html = await fetchText(embedUrl, { headers: { 'User-Agent': EGYAFLAM_UA, 'Referer': embedUrl } });
    const unpacked = deanEdwardsUnpack(String(html));
    const src = unpacked || String(html);
    const m = src.match(/https?:\/\/[^\s"'<>]+\.m3u8[^\s"'<>]*/i);
    if (!m) throw new Error('لم يتم العثور على رابط m3u8 في vidspeed.');
    return m[0].replace(/\\u0026/g, '&').replace(/\\\//g, '/');
}

async function egyaflamEpisodeLinks(episodeUrl) {
    const html = await fetchText(episodeUrl, { headers: { 'User-Agent': EGYAFLAM_UA } });
    const post = (String(html).match(/data-post=["'](\d+)["']/) || [])[1];
    if (!post) throw new Error('لم يتم العثور على رقم المنشور.');
    const nums = [...new Set([...String(html).matchAll(/data-nume=["'](\d+)["']/g)].map(m => m[1]))].slice(0, 7);
    for (const nume of nums) {
        try {
            const ajax = await fetchTextPost(`${EGYAFLAM_BASE}/wp-admin/admin-ajax.php`,
                { action: 'doo_player_ajax', post, nume, type: 'movie' },
                { headers: { 'User-Agent': EGYAFLAM_UA, 'Referer': episodeUrl } });
            // axios بيفك JSON تلقائياً أحياناً فيرجّع كائناً جاهزاً لا نصاً
            const parsed = (ajax && typeof ajax === 'object') ? ajax : JSON.parse(String(ajax));
            const embed = parsed.embed_url;
            if (!embed || !/vidspeed/i.test(embed)) continue;
            const m3u8 = await extractVidspeedM3u8(embed);
            return [{ url: m3u8, label: 'EgyAflam — HLS (vidspeed)', referer: embed }];
        } catch (_) {}
    }
    throw new Error('لا توجد سيرفرات شغالة لهذه الحلقة.');
}


// ============================================================
// دالة بناء ZIP بدون مكتبات خارجية
// ============================================================

// ============================================================
// أفلام ومسلسلات — 5 مصادر (akwam + CloudDay + MeowTv + CinemaPlus + VioLa)
// نفس منطق .anime: بحث متوازي → قائمة مرقّمة → حلقات (للمسلسلات) → جودات → تحميل
// ============================================================
const mvCache = new Map();

// ── تثبيت مصدر واحد لـ .movie / .series (عبر .setmv) ──
let mvLockedSource = null; // null = البحث في كل المصادر
const MV_SOURCE_LIST = ['akwam', 'cimacloud', 'meowtv', 'cinemaplus', 'viola', 'egywatch', 'okru', 'myseed'];
const MV_SOURCE_NAMES = {
    akwam: { source: 'akwam', label: '📺 Akwam' },
    cimacloud: { source: 'cloudday', cdSource: 'CimaCloud', label: '☁️ CloudDay (CimaCloud)' },
    cloudday: { source: 'cloudday', cdSource: 'CimaCloud', label: '☁️ CloudDay (CimaCloud)' },
    meowtv: { source: 'meowtv', label: '🐱 MeowTv' },
    cinemaplus: { source: 'cinemaplus', label: '🎬 CinemaPlus' },
    viola: { source: 'viola', label: '🎭 VioLa' },
    egywatch: { source: 'egywatch', label: '📺 Egywatch' },
    okru: { source: 'okru', label: '📺 ok.ru' },
    myseed: { source: 'myseed', label: '🌱 MySeed' }
};

// ---------- akwam: أفلام ومسلسلات ----------
function extractAkwamMovies(html) {
    const results = [];
    const regex = /href="(https?:\/\/akwam\.ss\/movie\/[^"#?]+)"/g;
    let m;
    while ((m = regex.exec(html)) !== null) {
        const url = m[1].split('?')[0];
        if (!results.some(r => r.url === url)) {
            const slug = url.replace(/.*\/movie\//, '').replace(/\/$/, '');
            results.push({ url, name: decodeURIComponent(slug).replace(/-/g, ' ') });
        }
    }
    return results;
}

// بحث akwam: الاسم الكامل أولاً، ولو صفر نتائج جرّب أطول كلمة (بحث الموقع ضعيف مع الكلمات المتعددة)
async function akwamSearch(query, kind) {
    const tryOnce = async (q) => {
        const html = await akwamFetch(`https://akwam.ss/search?q=${encodeURIComponent(q)}`);
        return kind === 'movie' ? extractAkwamMovies(html) : extractAkwamSeries(html);
    };
    let results = await tryOnce(query);
    if (!results.length) {
        const words = String(query).split(/\s+/).filter(w => w.length >= 4).sort((a, b) => b.length - a.length);
        if (words.length) results = await tryOnce(words[0]);
    }
    return results.map(r => ({ id: r.url, title: r.name, type: kind === 'movie' ? 'movie' : 'series' }));
}

function akwamQualityName(url) {
    const u = String(url || '').toLowerCase();
    if (u.includes('1080') || u.includes('fhd')) return '🔵 FHD 1080p';
    if (u.includes('720') || u.includes('hd')) return '🟢 HD 720p';
    if (u.includes('480') || u.includes('sd')) return '🟡 SD 480p';
    if (u.includes('360')) return '🟠 360p';
    return `⚪ جودة ${String(url).match(/(\d{3,4}p)/i)?.[1] || 'غير معروفة'}`;
}

// ---------- MySeed / ArabSeed (arabseed.show ← m.myseed.tv): أفلام ومسلسلات مترجمة، mp4 مباشر ----------
const MYSEED_BASE = 'https://m.myseed.tv';
const MYSEED_HEADERS = {
    'User-Agent': WEB_UA,
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    'Accept-Language': 'ar,en;q=0.5'
};

async function myseedFetch(url, referer) {
    const res = await axios.get(url, {
        headers: { ...MYSEED_HEADERS, ...(referer ? { 'Referer': referer } : {}) },
        timeout: 20000,
        validateStatus: s => s < 500
    });
    return typeof res.data === 'string' ? res.data : '';
}

// بحث MySeed: نتائج البحث روابط class="movie__block" مع title — أفلام (فيلم-) ومسلسلات/أنمي (مسلسل-/انمي-)؛ صفحات "سلسلة-" فهارس بلا مشغّل فتُستبعد
async function myseedSearch(query, kind) {
    const html = await myseedFetch(`${MYSEED_BASE}/find/?word=${encodeURIComponent(query)}`);
    const results = [];
    const regex = /<a href="(https:\/\/m\.myseed\.tv\/[^"]+)" title="([^"]+)" class="movie__block[^"]*"/g;
    let m;
    while ((m = regex.exec(html)) !== null) {
        const url = m[1];
        const title = (m[2] || '').replace(/&amp;/g, '&').replace(/&quot;/g, '"').replace(/&#039;/g, "'").trim();
        if (!title || results.some(r => r.id === url)) continue;
        let slug = '';
        try { slug = decodeURIComponent(url.replace(MYSEED_BASE + '/', '').replace(/\/$/, '')); } catch (_) { slug = url; }
        if (slug.startsWith('سلسلة-')) continue; // فهرس مجموعة أفلام — بلا زر مشاهدة
        if (kind === 'movie' && !slug.startsWith('فيلم-')) continue;
        if (kind === 'series' && !(slug.startsWith('مسلسل-') || slug.startsWith('انمي-'))) continue;
        results.push({ id: url, title, type: kind === 'movie' ? 'movie' : 'series' });
    }
    return results;
}

// حل روابط MySeed: صفحة الفيلم/الحلقة ← /watch/ ← vids.php ← player-gateway ← mp4 مباشر (جودة واحدة، الترجمة مدمجة في الصورة)
async function myseedResolveLinks(pageUrl) {
    const pageHtml = await myseedFetch(pageUrl);
    const watchMatch = pageHtml.match(/href="((?:https:\/\/m\.myseed\.tv)?\/[^"]*\/watch\/)"/);
    if (!watchMatch) throw new Error('MySeed: لا رابط مشاهدة في الصفحة.');
    const watchUrl = watchMatch[1].startsWith('http') ? watchMatch[1] : MYSEED_BASE + watchMatch[1];
    const watchHtml = await myseedFetch(watchUrl, pageUrl);
    const tokenMatch = watchHtml.match(/\/vids\.php\?t=([a-f0-9]+)/);
    if (!tokenMatch) throw new Error('MySeed: لا توكن vids.php.');
    const token = tokenMatch[1];
    const vidsUrl = `${MYSEED_BASE}/vids.php?t=${token}`;
    const vidsHtml = await myseedFetch(vidsUrl, watchUrl);
    const gwMatch = vidsHtml.match(/https:\/\/d\.myseed\.tv\/player-gateway\.php\?[^"'\s]+/);
    if (!gwMatch) throw new Error('MySeed: لا رابط player-gateway.');
    const gatewayUrl = gwMatch[0].replace(/&amp;/g, '&');
    const gwHtml = await myseedFetch(gatewayUrl, vidsUrl);
    const mp4Match = gwHtml.match(/https:\/\/[^"'\s]+\/video\.mp4/);
    if (!mp4Match) throw new Error('MySeed: لا رابط mp4 في المشغّل.');
    return [{ url: mp4Match[0], label: '🎬 HD (mp4)', referer: gatewayUrl }];
}

// ---------- MeowTv (api.meowtv.ru + TMDB) ----------
const MEOW_API = 'https://api.meowtv.ru';
const MEOW_TMDB = 'https://api.themoviedb.org/3';
const MEOW_TMDB_KEY = '06f120992cfacd7c118f6e7086d23544'; // مفتاح TMDB عام مضمّن في كود مزوّد CloudStream
const MEOW_STATIC_KEY = '10eE3wyyhkF38rwLFwisRYgwP2bbTL_Y';
const MEOW_SERVERS = ['dcloud', 'doppler', 'acme', 'tik', 'ipcloud', 'turkce', 'hindi', 'english', 'febbox'];
const MEOW_UA = 'Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/153.0.0.0 Mobile Safari/537.36';
const MEOW_HEADERS = { 'Origin': 'https://meowtv.ru', 'Referer': 'https://meowtv.ru/', 'User-Agent': MEOW_UA };

// توكن جديد لكل سيرفر (سلوك التطبيق نفسه — التوكن يعيش ~58 ثانية)
async function meowTicket() {
    const res = await axios.post(`${MEOW_API}/streams/ticket`, {}, { headers: { ...MEOW_HEADERS, 'Content-Type': 'application/json' }, timeout: 15000 });
    const ticket = res.data && res.data.ticket;
    if (!ticket) throw new Error('MeowTv: لا توكن.');
    return ticket;
}

// فك تشفير MeowTv: sha = SHA-256(المفتاح الثابت + n) ثم XOR دوري 32 بايت
function meowDecrypt(n, d) {
    try {
        const sha = crypto.createHash('sha256').update(MEOW_STATIC_KEY + n, 'utf8').digest();
        const cipher = Buffer.from(d, 'base64');
        const plain = Buffer.alloc(cipher.length);
        for (let i = 0; i < cipher.length; i++) plain[i] = cipher[i] ^ sha[i % 32];
        const text = plain.toString('utf8');
        if (!text.includes('{')) return null;
        return JSON.parse(text);
    } catch (_) { return null; }
}

async function meowSearch(query, kind) {
    const res = await axios.get(`${MEOW_TMDB}/search/multi`, {
        params: { api_key: MEOW_TMDB_KEY, language: 'en-US', query, page: 1 },
        headers: { 'User-Agent': MEOW_UA }, timeout: 20000
    });
    const list = Array.isArray(res.data && res.data.results) ? res.data.results : [];
    const want = kind === 'movie' ? 'movie' : 'tv';
    return list.filter(r => r.media_type === want).slice(0, 10).map(r => ({
        id: String(r.id),
        title: `${r.title || r.name || ''}${r.release_date || r.first_air_date ? ` (${String(r.release_date || r.first_air_date).slice(0, 4)})` : ''}`.trim(),
        type: want === 'movie' ? 'movie' : 'series'
    }));
}

async function meowEpisodes(tmdbId) {
    const res = await axios.get(`${MEOW_TMDB}/tv/${tmdbId}`, {
        params: { api_key: MEOW_TMDB_KEY, language: 'en-US' },
        headers: { 'User-Agent': MEOW_UA }, timeout: 20000
    });
    const seasons = (res.data && res.data.seasons || []).filter(s => s.season_number > 0 && s.episode_count > 0);
    const eps = [];
    const seasonLists = await Promise.allSettled(seasons.map(s =>
        axios.get(`${MEOW_TMDB}/tv/${tmdbId}/season/${s.season_number}`, {
            params: { api_key: MEOW_TMDB_KEY, language: 'en-US' },
            headers: { 'User-Agent': MEOW_UA }, timeout: 20000
        }).then(r => ({ season: s.season_number, list: (r.data && r.data.episodes) || [] }))
    ));
    for (const sl of seasonLists) {
        if (sl.status !== 'fulfilled') continue;
        for (const e of sl.value.list) {
            eps.push({
                id: `${tmdbId}:${sl.value.season}:${e.episode_number}`,
                number: eps.length + 1,
                season: sl.value.season,
                episode: e.episode_number,
                title: `الموسم ${sl.value.season} — الحلقة ${e.episode_number}`
            });
        }
    }
    return eps;
}

// ترجمة عربية VTT لـ MeowTv (ملف منفصل يُدمج في الـ mp4 عند التحميل)
async function meowSubs(tmdbId, kind, season, episode) {
    try {
        const path = kind === 'movie' ? `/subs/movie/${tmdbId}` : `/subs/tv/${tmdbId}/${season}/${episode}`;
        const res = await axios.get(`${MEOW_API}${path}`, { headers: MEOW_HEADERS, timeout: 15000 });
        const arr = Array.isArray(res.data) ? res.data : [];
        const ar = arr.find(s => /arabic/i.test(s.label || '')) || arr.find(s => /^ar$/i.test((s.label || '').trim()));
        return ar && ar.file ? ar.file : null;
    } catch (_) { return null; }
}

// سيرفرات MeowTv → روابط m3u8 (بحد أقصى 3 روابط شغالة — الـ API يحظر عند الإفراط)
async function meowStreams(tmdbId, kind, season, episode) {
    const streamPath = kind === 'movie' ? `/streams/movie/${tmdbId}` : `/streams/tv/${tmdbId}/${season}/${episode}`;
    const out = [];
    for (const server of MEOW_SERVERS) {
        if (out.length >= 3) break;
        try {
            const ticket = await meowTicket();
            const res = await axios.get(`${MEOW_API}${streamPath}?s=${server}`, {
                headers: { ...MEOW_HEADERS, 'x-stream-ticket': ticket },
                timeout: 20000, validateStatus: s => s < 500
            });
            if (res.status !== 200 || !res.data || !res.data.n || !res.data.d) continue;
            const stream = meowDecrypt(res.data.n, res.data.d);
            if (!stream) continue;
            const urls = [];
            if (typeof stream.url === 'string' && /^https?:\/\//i.test(stream.url)) urls.push(stream.url);
            if (Array.isArray(stream.streams)) {
                for (const s of stream.streams) {
                    if (s && typeof s.url === 'string' && /^https?:\/\//i.test(s.url)) urls.push(s.url);
                }
            }
            for (const u of urls) {
                out.push({ url: u, label: `MeowTv — ${server}`, referer: 'https://meowtv.ru/' });
            }
        } catch (_) {}
    }
    return out.slice(0, 3);
}

// ---------- CinemaPlus (e-droid) ----------
const CPLUS_CONFIG_URL = 'https://config.e-droid.net/srv/config.php?v=211&vname=3.0&idapp=3796813&idusu=0&cod_g=&gp=0&am=0&idl=en&pa_env=1&pa=GB&pn=cinema.plus&fus=010100000000&aid=7db3574f7ef4288a';
const CPLUS_UA = 'Android Vinebre Software';
const CPLUS_GET_HTML = 'https://html.e-droid.net/html/get_html.php?ida=3796813&ids=%s';
let cplusConfigCache = { at: 0, items: [] };

async function cinemaPlusConfig() {
    if (cplusConfigCache.items.length && Date.now() - cplusConfigCache.at < 3600000) return cplusConfigCache.items;
    const res = await axios.get(CPLUS_CONFIG_URL, { headers: { 'User-Agent': CPLUS_UA }, timeout: 25000 });
    const body = String(res.data || '');
    const sections = {};
    const re = /\[s(\d+)_(\w+)=([^\]]*)\]/g;
    let m;
    while ((m = re.exec(body)) !== null) {
        (sections[m[1]] = sections[m[1]] || {})[m[2]] = m[3];
    }
    const items = [];
    for (const [pageId, d] of Object.entries(sections)) {
        if (d.tipo !== '2') continue;
        const title = String(d.tit || '').replace(/\s*logo$/i, '').trim();
        if (!title || ['الرئيسية', 'الرئيسيه', 'اكتشف'].some(x => title.includes(x))) continue;
        const tmdbId = parseInt(d.idgo, 10);
        if (!tmdbId) continue;
        items.push({ pageId, title, tmdbId });
    }
    if (items.length) cplusConfigCache = { at: Date.now(), items };
    return items;
}

async function cinemaPlusSearch(query) {
    const items = await cinemaPlusConfig();
    const q = String(query).trim().toLowerCase();
    if (!q) return [];
    return items.filter(it => it.title.toLowerCase().includes(q)).slice(0, 10)
        .map(it => ({ id: it.pageId, title: it.title }));
}

async function cinemaPlusPage(pageId) {
    const res = await axios.get(CPLUS_GET_HTML.replace('%s', pageId), { headers: { 'User-Agent': CPLUS_UA }, timeout: 25000 });
    const html = String(res.data || '');
    const epM = html.match(/const\s+episodeLinks\s*=\s*\{(.*?)\}/s);
    const episodeLinks = {};
    if (epM) {
        for (const mm of epM[1].matchAll(/"(\d+-\d+)":\s*"([^"]*)"/g)) episodeLinks[mm[1]] = mm[2];
    }
    const vsM = html.match(/const\s+videoSources\s*=\s*\{(.*?)\}/s);
    const videoSources = {};
    if (vsM) {
        for (const mm of vsM[1].matchAll(/"([^"]+)":\s*"([^"]*)"/g)) {
            if (mm[2] && mm[2].trim()) videoSources[mm[1]] = mm[2];
        }
    }
    const isSeries = html.includes('const SERIES_ID') && Object.keys(episodeLinks).length > 0;
    return { isSeries, episodeLinks, videoSources };
}

function cplusStreamUrl(src) {
    if (!src) return null;
    return /^https?:\/\//i.test(src) ? src : `https://stream.mux.com/${src}.m3u8`;
}

async function cinemaPlusEpisodes(pageId) {
    const page = await cinemaPlusPage(pageId);
    if (!page.isSeries) return [];
    const keys = Object.keys(page.episodeLinks)
        .filter(k => page.episodeLinks[k] && page.episodeLinks[k] !== '#')
        .sort((a, b) => {
            const [sa, ea] = a.split('-').map(Number);
            const [sb, eb] = b.split('-').map(Number);
            return (sa - sb) || (ea - eb);
        });
    return keys.map((k, i) => {
        const [s, e] = k.split('-').map(Number);
        return { id: `${pageId}:${k}`, number: i + 1, season: s, episode: e, title: `الموسم ${s} — الحلقة ${e}` };
    });
}

async function cinemaPlusEpisodeLinks(pageId, key) {
    const page = await cinemaPlusPage(pageId);
    const src = page.episodeLinks[key];
    const url = cplusStreamUrl(src);
    if (!url) return [];
    return [{ url, label: /m3u8/i.test(url) ? 'CinemaPlus — HLS' : 'CinemaPlus — MP4' }];
}

async function cinemaPlusMovieLinks(pageId) {
    const page = await cinemaPlusPage(pageId);
    const entries = Object.entries(page.videoSources);
    if (!entries.length) return [];
    const out = [];
    // Mux أولاً (الأكثر ثباتاً)، ثم الروابط المباشرة
    const sorted = entries.sort((a, b) => {
        const aMux = !/^https?:\/\//i.test(a[1]) ? 0 : 1;
        const bMux = !/^https?:\/\//i.test(b[1]) ? 0 : 1;
        return aMux - bMux;
    });
    for (const [q, src] of sorted) {
        const url = cplusStreamUrl(src);
        if (!url) continue;
        out.push({ url, label: `CinemaPlus — ${q}` });
        if (out.length >= 6) break;
    }
    return out;
}

// ---------- VioLa (hq.vio-la.com) ----------
const VIOLA_BASE = 'https://hq.vio-la.com';
const VIOLA_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/141.0.0.0 Safari/537.36';
const VIOLA_HEADERS = { 'User-Agent': VIOLA_UA };
const VK_CLIENT_ID = '52461373';
const VK_SECRET = 'o557NLIkAErNhakXrQ7A';
const VK_APP_ID = '6287487';
let vkTokenCache = null;

async function violaSearch(query) {
    const html = await fetchText(`${VIOLA_BASE}/search.php?keywords=${encodeURIComponent(query)}&video-id=`, { headers: VIOLA_HEADERS });
    const out = []; const seen = new Set();
    const re = /<a[^>]+href="[^"]*watch\.php\?vid=([a-z0-9]+)[^"]*"[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) {
        const vid = m[1];
        if (seen.has(vid)) continue;
        seen.add(vid);
        const tag = m[0];
        let title = (tag.match(/title="([^"]+)"/) || [])[1] || '';
        title = decodeHtmlEntities(title.trim());
        if (!title) continue;
        out.push({ id: vid, title });
        if (out.length >= 10) break;
    }
    return out;
}

async function violaEpisodes(vid) {
    const html = await fetchText(`${VIOLA_BASE}/watch.php?vid=${vid}`, { headers: VIOLA_HEADERS });
    const eps = [];
    // أقسام المواسم: div[id^=Season] — نقطّع الـ HTML بين بداية كل موسم والذي يليه (الـ div متداخلة)
    const starts = [];
    const re = /<div[^>]+id=["']?Season\d+["']?[^>]*>/gi;
    let m;
    while ((m = re.exec(html)) !== null) starts.push(m.index);
    for (let s = 0; s < starts.length; s++) {
        const block = html.slice(starts[s], s + 1 < starts.length ? starts[s + 1] : undefined);
        const aRe = /<a[^>]+href="[^"]*watch\.php\?vid=([a-z0-9]+)[^"]*"[^>]*>/gi;
        let am; let countInSeason = 0;
        while ((am = aRe.exec(block)) !== null) {
            const epid = am[1];
            const tag = am[0];
            let t = (tag.match(/title="([^"]+)"/) || [])[1] || '';
            t = decodeHtmlEntities(t.trim());
            const numM = t.match(/الحلقة\s*([0-9\u0660-\u0669]+)/);
            let epNum = null;
            if (numM) epNum = parseInt(String(numM[1]).replace(/[\u0660-\u0669]/g, ch => String(ch.charCodeAt(0) - 0x660)), 10);
            if (!epNum) epNum = ++countInSeason;
            else countInSeason = epNum;
            eps.push({ id: epid, number: eps.length + 1, season: s + 1, episode: epNum, title: t || `الموسم ${s + 1} — الحلقة ${epNum}` });
        }
    }
    return eps;
}

// VK Video: توكن مجهول → video.get → ملفات mp4 + hls
async function violaResolveVk(link) {
    const oid = (String(link).match(/oid=(-?\d+)/) || [])[1];
    const id = (String(link).match(/[?&]id=(\d+)/) || [])[1];
    if (!oid || !id) return [];
    if (!vkTokenCache) {
        try {
            const res = await axios.post('https://login.vk.ru?act=get_anonym_token',
                new URLSearchParams({
                    client_secret: VK_SECRET, client_id: VK_CLIENT_ID,
                    scopes: 'audio_anonymous,video_anonymous,photos_anonymous,profile_anonymous',
                    isApiOauthAnonymEnabled: 'false', version: '1', app_id: VK_APP_ID
                }).toString(),
                { headers: { 'User-Agent': VIOLA_UA, 'Content-Type': 'application/x-www-form-urlencoded', 'Origin': 'https://vkvideo.ru', 'Referer': 'https://vkvideo.ru/' }, timeout: 20000 });
            vkTokenCache = res.data && res.data.data && res.data.data.access_token;
        } catch (_) { vkTokenCache = null; }
        if (!vkTokenCache) return [];
    }
    try {
        const res = await axios.post(`https://api.vkvideo.ru/method/video.get?v=5.289&client_id=${VK_CLIENT_ID}`,
            new URLSearchParams({
                owner_id: '', videos: `${oid}_${id}`, extended: '0', is_embed: 'true',
                track_code: '', ref_domain: 'hq.vio-la.com', partner_name: '', access_token: vkTokenCache
            }).toString(),
            { headers: { 'User-Agent': VIOLA_UA, 'Content-Type': 'application/x-www-form-urlencoded', 'Origin': 'https://vkvideo.ru', 'Referer': 'https://vkvideo.ru/' }, timeout: 20000, responseType: 'text' });
        const dec = (typeof res.data === 'string' ? res.data : JSON.stringify(res.data || '')).replace(/\\\//g, '/').replace(/\\u0026/g, '&');
        const out = [];
        const seenLabels = new Set();
        for (const mm of dec.matchAll(/"(mp4_\d+|hls)"\s*:\s*"(https?[^"]+)"/g)) {
            const q = mm[1] === 'hls' ? 'HLS' : mm[1].replace('mp4_', '') + 'p';
            if (seenLabels.has(q)) continue;
            seenLabels.add(q);
            out.push({ url: mm[2], label: `VK — ${q}` });
        }
        // mp4 أولاً (روابط مباشرة)، ثم HLS
        out.sort((a, b) => (a.label.includes('HLS') ? 1 : 0) - (b.label.includes('HLS') ? 1 : 0));
        return out;
    } catch (_) { return []; }
}

// سكريبر mawdhou3: GET {endpoint}?api={embed} → file:"url" (,label:"q")
async function violaScrape(endpoint, link) {
    try {
        const res = await axios.get(endpoint + encodeURIComponent(link), { headers: { 'User-Agent': VIOLA_UA }, timeout: 20000 });
        const out = [];
        for (const mm of String(res.data || '').matchAll(/file:"(https[^"]+)"(?:\s*,\s*label:"([^"]*)")?/g)) {
            out.push({ url: mm[1], label: mm[2] ? `Ult4vid — ${mm[2]}` : 'Ult4vid — MP4' });
        }
        return out;
    } catch (_) { return []; }
}

async function violaEpisodeLinks(vid) {
    const html = await fetchText(`${VIOLA_BASE}/play.php?vid=${vid}`, { headers: VIOLA_HEADERS });
    const servers = [];
    const seen = new Set();
    for (const m of String(html).matchAll(/<li[^>]+data-embed[^>]*>/gi)) {
        const srcM = m[0].match(/src='([^']+)'/);
        if (!srcM || seen.has(srcM[1])) continue;
        seen.add(srcM[1]);
        servers.push({ link: srcM[1] });
    }
    const out = [];
    for (const s of servers) {
        try {
            if (/youtube\.com/i.test(s.link)) continue;
            if (/ok\.ru/i.test(s.link)) continue; // مشغّل JS حالياً — لا JSON ثابت
            if (/vkvideo\.ru|vk\.com\/video_ext/i.test(s.link)) {
                for (const r of await violaResolveVk(s.link)) out.push({ ...r, referer: 'https://hq.vio-la.com/' });
            } else if (/71stream/i.test(s.link)) {
                for (const r of await violaScrape('https://mawdhou3.com/scrapefinal/71stream.php?api=', s.link)) out.push({ ...r, referer: 'https://hq.vio-la.com/' });
            } else if (/ultra?4vid/i.test(s.link)) {
                for (const r of await violaScrape('https://mawdhou3.com/scrapefinal/ult4vid.php?api=', s.link)) out.push({ ...r, referer: 'https://hq.vio-la.com/' });
            } else {
                // محاولة أخيرة: mp4/m3u8 مباشر في صفحة الـ embed
                try {
                    const page = await fetchText(s.link, { headers: { ...VIOLA_HEADERS, Referer: 'https://hq.vio-la.com/' } });
                    const mm = String(page).match(/https?:\/\/[^\s"'<>]+\.(mp4|m3u8)[^\s"'<>]*/i);
                    if (mm) out.push({ url: mm[0], label: 'سيرفر — مباشر', referer: 'https://hq.vio-la.com/' });
                } catch (_) {}
            }
        } catch (_) {}
        if (out.length >= 6) break;
    }
    return out.slice(0, 6);
}

// ---------- حل روابط حلقة/فيلم من أي مصدر (أفلام ومسلسلات) ----------
// ترجع {links: [{url, label, referer?}], subtitleUrl?: string}
// ---------- Egywatch (gateway.egywatch.live — API بلا auth، مفتاح ثابت) ----------
// بحث ← عرض المسلسل (المواسم) ← حلقات الموسم ← فيديوهات (Uqload شغال، Server Egy ميت)
// ملحوظة: بلا ترجمة عربية في الستريم نفسه (الـ API يقول lang Arabic بلا ملف ترجمة فعلي)
const EGYWATCH_BASES = ['https://gateway.egywatch.live/egywatchapp/public/api', 'https://rn62mwg.com/egywatchapp/public/api'];
const EGYWATCH_CODE = 'p2lbgWkFrykA4QyUmpHihzmc5BNzIABq';
const EGYWATCH_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

async function egywatchGet(path) {
    let lastErr;
    for (const base of EGYWATCH_BASES) {
        try {
            const res = await axios.get(base + path, { headers: { 'User-Agent': EGYWATCH_UA }, timeout: 20000 });
            return res.data;
        } catch (e) { lastErr = e; }
    }
    throw lastErr || new Error('فشل الاتصال بـ Egywatch.');
}

async function egywatchSearch(query) {
    const data = await egywatchGet(`/search/${encodeURIComponent(query)}/${EGYWATCH_CODE}`);
    const list = (data && data.search) || [];
    return list
        .filter(x => /serie/i.test(String(x.type || '')))
        .map(x => ({ id: String(x.id), title: x.name, type: 'series' }))
        .slice(0, 5);
}

async function egywatchEpisodes(seriesId) {
    const show = await egywatchGet(`/series/show/${seriesId}/${EGYWATCH_CODE}`);
    const seasons = (show && show.seasons) || [];
    if (!seasons.length) throw new Error('لا توجد مواسم.');
    const lists = await Promise.allSettled(seasons.map(s => egywatchGet(`/series/season/${s.id}/${EGYWATCH_CODE}`)));
    const eps = [];
    seasons.forEach((s, i) => {
        if (lists[i].status !== 'fulfilled') return;
        const sNum = s.season_number || (i + 1);
        for (const e of (lists[i].value.episodes || [])) {
            eps.push({
                id: `${seriesId}:${s.id}:${e.episode_number}`,
                number: 0,
                title: `الموسم ${sNum} — الحلقة ${e.episode_number}`,
                season: sNum,
                epNum: e.episode_number,
                videos: e.videos || []
            });
        }
    });
    eps.sort((a, b) => (a.season - b.season) || (a.epNum - b.epNum));
    eps.forEach((e, i) => { e.number = i + 1; });
    return eps;
}

async function egywatchEpisodeLinks(ep) {
    const videos = ep.videos || [];
    const tryUq = async (url) => {
        const m3u8 = await extractUqloadM3u8(url);
        const plRes = await axios.get(m3u8, { headers: { 'User-Agent': 'Mozilla/5.0', 'Referer': 'https://uqload.com/' }, timeout: 20000, responseType: 'text' });
        const variants = parseM3u8Variants(String(plRes.data || ''), m3u8);
        if (variants.length) {
            const out = [];
            const seen = new Set();
            for (const v of variants) {
                const label = `Egywatch — ${v.label} (Uqload)`;
                if (seen.has(label)) continue;
                seen.add(label);
                out.push({ url: v.url, label, referer: 'https://uqload.com/' });
            }
            return out;
        }
        return [{ url: m3u8, label: 'Egywatch — HLS (Uqload)', referer: 'https://uqload.com/' }];
    };
    const uq = videos.find(v => /uqload/i.test(v.server || v.name || '') || /uqload/i.test(v.url || v.link || ''));
    if (uq) {
        try { return await tryUq(uq.url || uq.link); } catch (_) {}
    }
    for (const v of videos) {
        const url = v.url || v.link || '';
        if (/\.mp4(\?|$)/i.test(url)) return [{ url, label: `Egywatch — MP4 (${v.server || 'server'})`, referer: '' }];
        if (/uqload/i.test(url)) {
            try { return await tryUq(url); } catch (_) {}
        }
    }
    throw new Error('لا توجد سيرفرات شغالة لهذه الحلقة.');
}

// ---------- ok.ru في .series (احتياطي — فيديوهات منفردة بلا مواسم) ----------
// نتائج البحث فيديوهات (حلقات) مباشرة — الاختيار يذهب للجودات فوراً بلا قائمة حلقات
async function okruVideoLinks(id) {
    const { videos } = await extractOkruVideo(`https://ok.ru/video/${id}`);
    return videos.map(v => ({ url: v.url, label: 'ok.ru — ' + (OKRU_QUALITY_LABELS[v.name] || v.name), referer: '' }));
}

async function resolveMvEpisodeLinks(source, cdSource, id, ep) {
    if (source === 'akwam') {
        const mp4s = await extractAkwamMp4Links(ep.id);
        return { links: mp4s.map(u => ({ url: u, label: akwamQualityName(u), referer: 'https://akwam.ss/' })) };
    }
    if (source === 'cloudday') {
        const base = await cloudDayResolveBase(CLOUDDAY_SOURCES.find(s => s.name === cdSource));
        const links = await cloudDayServers(base, 'episode', ep.id);
        return { links: await cloudDayResolveLinks(links) };
    }
    if (source === 'meowtv') {
        const [tmdbId, s, e] = String(ep.id).split(':');
        const links = await meowStreams(tmdbId, 'tv', s, e);
        const subtitleUrl = await meowSubs(tmdbId, 'tv', s, e);
        return { links, subtitleUrl };
    }
    if (source === 'cinemaplus') {
        const [pageId, key] = String(ep.id).split(':');
        return { links: await cinemaPlusEpisodeLinks(pageId, key) };
    }
    if (source === 'viola') return { links: await violaEpisodeLinks(ep.id) };
    if (source === 'egywatch') return { links: await egywatchEpisodeLinks(ep) };
    if (source === 'myseed') return { links: await myseedResolveLinks(ep.id) };
    if (source === 'dramaworld') return { links: await dramaWorldEpisodeLinks(ep) };
    if (source === 'lodynet') return { links: await lodynetEpisodeLinks(ep.id) };
    return { links: [] };
}

async function resolveMvMovieLinks(source, cdSource, id) {
    if (source === 'akwam') {
        const mp4s = await extractAkwamMp4Links(id);
        return { links: mp4s.map(u => ({ url: u, label: akwamQualityName(u), referer: 'https://akwam.ss/' })) };
    }
    if (source === 'meowtv') {
        const links = await meowStreams(id, 'movie');
        const subtitleUrl = await meowSubs(id, 'movie');
        return { links, subtitleUrl };
    }
    if (source === 'cinemaplus') return { links: await cinemaPlusMovieLinks(id) };
    if (source === 'viola') return { links: await violaEpisodeLinks(id) };
    if (source === 'okru') return { links: await okruVideoLinks(id) };
    if (source === 'myseed') return { links: await myseedResolveLinks(id) };
    return { links: [] };
}

// بحث مصدر واحد بالاسم (نفس دوال البحث — بلا تكرار كود)
async function mvSearchOne(name, query, kind) {
    const e = MV_SOURCE_NAMES[name];
    if (!e) return [];
    if (e.source === 'akwam') return await akwamSearch(query, kind);
    if (e.source === 'cloudday') {
        if (kind !== 'series') return []; // أفلام CloudDay فاشلة — لا تُعرض
        return await cloudDaySearch(query, e.cdSource, '2');
    }
    if (e.source === 'meowtv') return await meowSearch(query, kind);
    if (e.source === 'cinemaplus') return await cinemaPlusSearch(query);
    if (e.source === 'viola') return await violaSearch(query);
    if (e.source === 'egywatch') {
        if (kind !== 'series') return []; // أفلام Egywatch لم تُفحص — مسلسلات فقط
        return await egywatchSearch(query);
    }
    if (e.source === 'okru') {
        if (kind !== 'series') return []; // ok.ru في .series فقط (حلقات منفردة)
        return await okruSearchRaw(query);
    }
    if (e.source === 'myseed') return await myseedSearch(query, kind);
    return [];
}

// دمج ترجمة VTT عربية في ملف mp4 (مسار ترجمة قابل للاختيار) — best-effort، الفيديو يُرسل حتى لو فشل الدمج
async function muxSubtitleIntoMp4(videoPath, vttUrl) {
    try {
        const tmpDir = path.join(process.cwd(), 'dltmp');
        const vttPath = path.join(tmpDir, `sub_${randomBytes(4).toString('hex')}.vtt`);
        const outPath = path.join(tmpDir, `vidsub_${randomBytes(4).toString('hex')}.mp4`);
        const res = await axios.get(vttUrl, { responseType: 'arraybuffer', timeout: 30000, headers: { 'User-Agent': 'Mozilla/5.0', 'Origin': 'https://meowtv.ru', 'Referer': 'https://meowtv.ru/' } });
        fs.writeFileSync(vttPath, Buffer.from(res.data));
        const r = await runFfmpeg(['-y', '-i', videoPath, '-i', vttPath, '-c', 'copy', '-c:s', 'mov_text', '-metadata:s:s:0', 'language=ar', outPath], null);
        try { if (fs.existsSync(vttPath)) fs.unlinkSync(vttPath); } catch (_) {}
        if (r && r.code === 0 && fs.existsSync(outPath) && fs.statSync(outPath).size > 0) {
            try { if (fs.existsSync(videoPath)) fs.unlinkSync(videoPath); } catch (_) {}
            return outPath;
        }
        try { if (fs.existsSync(outPath)) fs.unlinkSync(outPath); } catch (_) {}
        return videoPath;
    } catch (_) { return videoPath; }
}

const buildZip = (files, outPath) => {
    const entries    = [];
    const centralDir = [];
    let offset       = 0;

    for (const { data, name } of files) {
        const nameBytes = Buffer.from(name, 'utf8');

        let crc = 0xFFFFFFFF;
        for (let i = 0; i < data.length; i++) {
            let b = (crc ^ data[i]) & 0xFF;
            for (let j = 0; j < 8; j++) b = (b & 1) ? (b >>> 1) ^ 0xEDB88320 : b >>> 1;
            crc = (crc >>> 8) ^ b;
        }
        crc = (crc ^ 0xFFFFFFFF) >>> 0;

        const lh = Buffer.alloc(30 + nameBytes.length);
        lh.writeUInt32LE(0x04034b50, 0);
        lh.writeUInt16LE(20, 4);
        lh.writeUInt16LE(0, 6);
        lh.writeUInt16LE(0, 8);
        lh.writeUInt16LE(0, 10);
        lh.writeUInt16LE(0x5360, 12);
        lh.writeUInt32LE(crc, 14);
        lh.writeUInt32LE(data.length, 18);
        lh.writeUInt32LE(data.length, 22);
        lh.writeUInt16LE(nameBytes.length, 26);
        lh.writeUInt16LE(0, 28);
        nameBytes.copy(lh, 30);
        entries.push(Buffer.concat([lh, data]));

        const cd = Buffer.alloc(46 + nameBytes.length);
        cd.writeUInt32LE(0x02014b50, 0);
        cd.writeUInt16LE(20, 4); cd.writeUInt16LE(20, 6);
        cd.writeUInt16LE(0, 8);  cd.writeUInt16LE(0, 10);
        cd.writeUInt16LE(0, 12); cd.writeUInt16LE(0x5360, 14);
        cd.writeUInt32LE(crc, 16);
        cd.writeUInt32LE(data.length, 20);
        cd.writeUInt32LE(data.length, 24);
        cd.writeUInt16LE(nameBytes.length, 28);
        cd.writeUInt16LE(0, 30); cd.writeUInt16LE(0, 32);
        cd.writeUInt16LE(0, 34); cd.writeUInt16LE(0, 36);
        cd.writeUInt32LE(0, 38); cd.writeUInt32LE(offset, 42);
        nameBytes.copy(cd, 46);
        centralDir.push(cd);

        offset += lh.length + data.length;
    }

    const cdBuf = Buffer.concat(centralDir);
    const eocd  = Buffer.alloc(22);
    eocd.writeUInt32LE(0x06054b50, 0);
    eocd.writeUInt16LE(0, 4); eocd.writeUInt16LE(0, 6);
    eocd.writeUInt16LE(files.length, 8);
    eocd.writeUInt16LE(files.length, 10);
    eocd.writeUInt32LE(cdBuf.length, 12);
    eocd.writeUInt32LE(offset, 16);
    eocd.writeUInt16LE(0, 20);

    fs.writeFileSync(outPath, Buffer.concat([...entries, cdBuf, eocd]));
};

// ============================================================
// أدوات تحميل عامة (روابط مباشرة + Google Drive) — قابلة لإعادة الاستخدام
// تُستخدم من أوامر .download و .batchdl و .remotedl
// ============================================================
const DOWNLOAD_MIME_MAP = {
    '.mp4': 'video/mp4', '.mkv': 'video/x-matroska',
    '.webm': 'video/webm', '.avi': 'video/x-msvideo',
    '.zip': 'application/zip', '.rar': 'application/x-rar-compressed',
    '.pdf': 'application/pdf', '.apk': 'application/vnd.android.package-archive',
    '.mp3': 'audio/mpeg', '.ogg': 'audio/ogg',
    '.jpg': 'image/jpeg', '.png': 'image/png',
    '.bin': 'application/octet-stream'
};

function detectDownloadExt(url, contentType = '', contentDisposition = '') {
    const cdMatch = contentDisposition.match(/filename[^;=\n]*=\s*["']?([^"'\n;]+)/i);
    if (cdMatch) {
        const ext = path.extname(cdMatch[1].trim().replace(/["']/g, ''));
        if (ext.length >= 2 && ext.length <= 5) return ext.toLowerCase();
    }
    const urlExt = path.extname(url.split('?')[0]);
    if (urlExt.length >= 2 && urlExt.length <= 5) return urlExt.toLowerCase();
    const ctMap = {
        'video/mp4': '.mp4', 'video/x-matroska': '.mkv',
        'video/webm': '.webm', 'video/avi': '.avi',
        'application/zip': '.zip', 'application/x-rar-compressed': '.rar',
        'application/x-rar': '.rar', 'application/pdf': '.pdf',
        'application/vnd.android.package-archive': '.apk',
        'audio/mpeg': '.mp3', 'audio/ogg': '.ogg',
        'image/jpeg': '.jpg', 'image/png': '.png',
    };
    for (const [ct, ext] of Object.entries(ctMap)) {
        if (contentType.includes(ct)) return ext;
    }
    return '.bin';
}

// استخراج رابط تحميل مباشر من رابط Google Drive (يدعم الملفات الكبيرة التي تحتاج تأكيد "فحص الفيروسات")
async function resolveGoogleDriveUrl(inputUrl) {
    const idMatch = inputUrl.match(/\/d\/([a-zA-Z0-9_-]+)/) || inputUrl.match(/[?&]id=([a-zA-Z0-9_-]+)/);
    if (!idMatch) return null; // ليس رابط Google Drive
    const fileId = idMatch[1];

    const GD_HEADERS = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
    };

    let cookieHeader = '';
    const mergeCookies = (setCookieArr) => {
        if (!setCookieArr) return;
        const parts = setCookieArr.map(c => c.split(';')[0]);
        cookieHeader = cookieHeader ? `${cookieHeader}; ${parts.join('; ')}` : parts.join('; ');
    };

    let url = `https://drive.google.com/uc?export=download&confirm=t&id=${fileId}`;
    let res = await axios.get(url, {
        headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) },
        responseType: 'text',
        maxRedirects: 5,
        validateStatus: () => true
    });
    mergeCookies(res.headers['set-cookie']);

    const contentType = res.headers['content-type'] || '';
    if (!contentType.includes('text/html')) {
        return { url, headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) } };
    }

    // صفحة HTML (تحذير فحص فيروسات لملف كبير) — استخرج نموذج التأكيد
    const html = String(res.data);
    const actionMatch  = html.match(/action="([^"]+)"/);
    const idInput      = html.match(/name="id"\s+value="([^"]+)"/);
    const confirmInput = html.match(/name="confirm"\s+value="([^"]+)"/);
    const uuidInput    = html.match(/name="uuid"\s+value="([^"]+)"/);

    if (actionMatch && confirmInput) {
        const params = new URLSearchParams();
        params.set('id', idInput ? idInput[1] : fileId);
        params.set('export', 'download');
        params.set('confirm', confirmInput[1]);
        if (uuidInput) params.set('uuid', uuidInput[1]);
        const finalUrl = `${actionMatch[1].replace(/&amp;/g, '&')}?${params.toString()}`;
        return { url: finalUrl, headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) } };
    }

    const oldConfirmMatch = html.match(/confirm=([0-9A-Za-z_-]+)&(?:amp;)?id=/);
    if (oldConfirmMatch) {
        const finalUrl = `https://drive.google.com/uc?export=download&confirm=${oldConfirmMatch[1]}&id=${fileId}`;
        return { url: finalUrl, headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) } };
    }

    throw new Error('تعذر استخراج رابط Google Drive المباشر. تأكد أن الملف "متاح لأي شخص لديه الرابط".');
}

// ── رؤوس افتراضية أقرب لمتصفح حقيقي (تقلل رفض السيرفرات) ──
const DL_BASE_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Accept': '*/*',
    'Accept-Language': 'ar,en-US;q=0.9,en;q=0.8',
    'Accept-Encoding': 'identity',
    'Connection': 'keep-alive'
};

const sleepMs = (ms) => new Promise(r => setTimeout(r, ms));

// طلب مع إعادة محاولة تلقائية عند 5xx / 429 / أخطاء الشبكة المؤقتة
async function requestWithRetry(config, { retries = 4, baseDelay = 3000 } = {}) {
    let lastErr;
    for (let attempt = 1; attempt <= retries; attempt++) {
        try {
            const res = await axios({ ...config, validateStatus: () => true });

            if (res.status >= 500 || res.status === 429) {
                const retryAfter = parseInt(res.headers?.['retry-after']);
                lastErr = new Error(`السيرفر رد بالحالة ${res.status} (مؤقتًا غير متاح)`);
                if (attempt < retries) {
                    const wait = Math.min(retryAfter ? retryAfter * 1000 : baseDelay * attempt, 30000);
                    await sleepMs(wait);
                    continue;
                }
                throw lastErr;
            }
            return res;
        } catch (e) {
            lastErr = e;
            if (attempt < retries) await sleepMs(baseDelay * attempt);
            else throw lastErr;
        }
    }
    throw lastErr;
}

// فحص الرابط: HEAD أولاً، وعند فشله نستخدم GET بنطاق صغير (bytes=0-0)
// لأن سيرفرات كثيرة ترفض HEAD وترجع 503/405/403 رغم أن GET يعمل
async function resolveDirectUrl(url, headers) {
    try {
        const res = await requestWithRetry(
            { method: 'HEAD', url, headers, timeout: 20000, maxRedirects: 10 },
            { retries: 2, baseDelay: 2000 }
        );
        if (res.status < 400) {
            return { finalUrl: res.request?.res?.responseUrl || url, headRes: res };
        }
    } catch (_) { /* نتجاهل ونجرّب GET */ }

    const res = await requestWithRetry({
        method: 'GET', url,
        headers: { ...headers, 'Range': 'bytes=0-0' },
        timeout: 20000, maxRedirects: 10, responseType: 'stream'
    });

    try { res.data.destroy(); } catch (_) {}

    if (res.status >= 400 && res.status !== 416) {
        throw new Error(`تعذر الوصول للرابط (HTTP ${res.status}) — قد يكون السيرفر مطفأ أو الرابط منتهي الصلاحية.`);
    }

    // استخراج الحجم الكلي من content-range لأن content-length هنا = 1 بايت
    const cr = res.headers['content-range'];
    if (cr) {
        const total = parseInt(String(cr).split('/')[1]);
        if (total && !isNaN(total)) res.headers['content-length'] = String(total);
        res.headers['accept-ranges'] = 'bytes';
    } else {
        res.headers['accept-ranges'] = res.headers['accept-ranges'] || 'none';
    }

    return { finalUrl: res.request?.res?.responseUrl || url, headRes: res };
}

// ── عرض تقدم التحميل في السجل (كل 5 ثوانٍ) ──
function progressBar(pct, width = 20) {
    const p = Math.max(0, Math.min(100, pct));
    const filled = Math.round(p / 100 * width);
    return '[' + '#'.repeat(filled) + '-'.repeat(width - filled) + ']';
}
function makeProgress(label, total) {
    const t = { label, total: total || 0, bytes: 0, start: Date.now(), timer: null };
    t.timer = setInterval(() => {
        const mb = t.bytes / 1048576;
        const sec = Math.max((Date.now() - t.start) / 1000, 0.1);
        const speed = mb / sec;
        if (t.total) {
            const pct = t.bytes / t.total * 100;
            const remain = Math.max(t.total / 1048576 - mb, 0);
            const eta = speed > 0 ? Math.round(remain / speed) : 0;
            console.log(`[PROGRESS] ${t.label}\n   ${progressBar(pct)} ${pct.toFixed(1)}% | ${mb.toFixed(1)}/${(t.total / 1048576).toFixed(1)} MB | ${speed.toFixed(2)} MB/s | ETA ${eta}s`);
        } else {
            console.log(`[PROGRESS] ${t.label}\n   ${mb.toFixed(1)} MB | ${speed.toFixed(2)} MB/s | ${sec.toFixed(0)}s`);
        }
    }, 5000);
    t.add = (n) => { t.bytes += n; };
    t.stop = () => clearInterval(t.timer);
    return t;
}
function trackStream(stream, label, total) {
    const t = makeProgress(label, parseInt(total) || 0);
    stream.on('data', (c) => t.add(c.length));
    const end = () => t.stop();
    stream.on('end', end); stream.on('error', end); stream.on('close', end);
    return t;
}

function downloadChunkToFile(url, start, end, destPath, headers, tracker) {
    return new Promise(async (resolve, reject) => {
        try {
            const res = await requestWithRetry({
                method: 'GET', url, responseType: 'stream', timeout: 1800000,
                maxRedirects: 10, headers: { ...headers, 'Range': `bytes=${start}-${end}` }
            }, { retries: 4, baseDelay: 4000 });

            if (res.status >= 400) return reject(new Error(`فشل تحميل الجزء (HTTP ${res.status})`));

            const writer = fs.createWriteStream(destPath);
            if (tracker) res.data.on('data', (c) => tracker.add(c.length));
            res.data.pipe(writer);
            res.data.on('error', reject);
            writer.on('finish', resolve);
            writer.on('error', reject);
        } catch (e) { reject(e); }
    });
}

function mergeChunkFiles(chunkPaths, outputPath) {
    return new Promise((resolve, reject) => {
        const out = fs.createWriteStream(outputPath, { flags: 'a' });
        const writeNext = (i) => {
            if (i >= chunkPaths.length) { out.end(); return resolve(); }
            const src = fs.createReadStream(chunkPaths[i]);
            src.pipe(out, { end: false });
            src.on('end', () => {
                try { fs.unlinkSync(chunkPaths[i]); } catch (_) {}
                writeNext(i + 1);
            });
            src.on('error', reject);
        };
        writeNext(0);
        out.on('error', reject);
    });
}

// تحميل بخيط واحد مع إعادة محاولة — يُستخدم كخطة بديلة عند فشل التحميل المتوازي
async function singleStreamDownload(url, headers, outputPath, tracker) {
    const res = await requestWithRetry({
        method: 'GET', url, responseType: 'stream',
        timeout: 1800000, maxRedirects: 10, headers
    }, { retries: 4, baseDelay: 4000 });

    if (res.status >= 400) throw new Error(`فشل التحميل (HTTP ${res.status})`);

    const writer = fs.createWriteStream(outputPath);
    if (tracker) res.data.on('data', (c) => tracker.add(c.length));
    res.data.pipe(writer);
    await new Promise((resolve, reject) => {
        res.data.on('error', reject);
        writer.on('finish', resolve);
        writer.on('error', reject);
    });
}

// الدالة الموحّدة: تُحمّل رابطاً مباشراً أو رابط Google Drive إلى ملف على القرص
// وتُرجع مساره ونوعه وحجمه — يستخدمها كل من .download و .batchdl و .remotedl
async function smartDownloadUrl(rawUrl, tmpDir, fileTag) {
    let finalUrl, headRes, headersToUse = { ...DL_BASE_HEADERS };

    const gdrive = /drive\.google\.com|docs\.google\.com/i.test(rawUrl)
        ? await resolveGoogleDriveUrl(rawUrl)
        : null;

    if (gdrive) {
        finalUrl = gdrive.url;
        headersToUse = gdrive.headers;
        headRes = await axios({
            method: 'HEAD', url: finalUrl, headers: headersToUse,
            timeout: 20000, maxRedirects: 10, validateStatus: () => true
        }).catch(err => err.response || {});
    } else {
        try {
            headersToUse = { ...DL_BASE_HEADERS, 'Referer': new URL(rawUrl).origin + '/' };
        } catch (_) {}
        const resolved = await resolveDirectUrl(rawUrl, headersToUse);
        finalUrl = resolved.finalUrl;
        headRes = resolved.headRes;
        try {
            headersToUse = { ...headersToUse, 'Referer': new URL(finalUrl).origin + '/' };
        } catch (_) {}
    }

    const contentType  = headRes?.headers?.['content-type'] || '';
    const contentDisp  = headRes?.headers?.['content-disposition'] || '';
    const totalSize    = parseInt(headRes?.headers?.['content-length'] || '0');
    const acceptRanges = headRes?.headers?.['accept-ranges'] === 'bytes';

    const fileExt  = detectDownloadExt(finalUrl, contentType, contentDisp);
    const mimeType = DOWNLOAD_MIME_MAP[fileExt] || 'application/octet-stream';

    const fileId = randomBytes(4).toString('hex');
    const outputPath = path.join(tmpDir, `${fileTag || 'DL'}_${fileId}${fileExt}`);
    const chunkPaths = [];
    const THREADS = 8;

    let _dlName = (String(contentDisp).match(/filename\*?=(?:UTF-8'')?"?([^";]+)/i) || [])[1];
    if (!_dlName) { try { _dlName = decodeURIComponent(path.basename(new URL(finalUrl).pathname)) || '?'; } catch (_) { _dlName = '?'; } }
    const _parallel = !gdrive && acceptRanges && totalSize > 1024 * 1024;
    console.log(`[DOWNLOAD] info: name=${_dlName} | type=${contentType || '?'} | size=${totalSize ? (totalSize / 1048576).toFixed(1) + ' MB' : 'unknown'} | mode=${gdrive ? 'gdrive' : (_parallel ? 'parallel x' + THREADS : 'single')}`);
    const tracker = makeProgress(`${fileTag || 'DL'} ${_dlName}`.slice(0, 80), totalSize);

    const cleanupChunks = () => {
        for (const cp of chunkPaths) { try { if (fs.existsSync(cp)) fs.unlinkSync(cp); } catch (_) {} }
        chunkPaths.length = 0;
    };

    try {
        // Google Drive لا يدعم التقسيم المتوازي بشكل موثوق (روابط التأكيد أحادية الاستخدام أحياناً)
        if (!gdrive && acceptRanges && totalSize > 1024 * 1024) {
            try {
                const chunkSize = Math.ceil(totalSize / THREADS);
                const promises = [];
                for (let i = 0; i < THREADS; i++) {
                    const start = i * chunkSize;
                    const end = Math.min(start + chunkSize - 1, totalSize - 1);
                    const chunkPath = path.join(tmpDir, `chunk_${fileId}_${i}`);
                    chunkPaths.push(chunkPath);
                    promises.push(downloadChunkToFile(finalUrl, start, end, chunkPath, headersToUse, tracker));
                }
                await Promise.all(promises);
                await mergeChunkFiles(chunkPaths, outputPath);
            } catch (parallelErr) {
                // خطة بديلة: بعض السيرفرات تخنق الاتصالات المتوازية وترد 503
                cleanupChunks();
                try { if (fs.existsSync(outputPath)) fs.unlinkSync(outputPath); } catch (_) {}
                console.log('[DOWNLOAD] parallel failed, retrying single stream...');
                tracker.bytes = 0; tracker.start = Date.now();
                await sleepMs(3000);
                await singleStreamDownload(finalUrl, headersToUse, outputPath, tracker);
            }
        } else {
            await singleStreamDownload(finalUrl, headersToUse, outputPath, tracker);
        }
        tracker.stop();
    } catch (err) {
        tracker.stop();
        cleanupChunks();
        try { if (fs.existsSync(outputPath)) fs.unlinkSync(outputPath); } catch (_) {}
        throw err;
    }

    const stat = fs.statSync(outputPath);
    if (stat.size === 0) {
        try { fs.unlinkSync(outputPath); } catch (_) {}
        throw new Error('الملف الناتج فارغ (0 بايت) — السيرفر رفض التحميل.');
    }

    const finalSizeMB = (stat.size / 1024 / 1024).toFixed(2);
    return { outputPath, fileExt, mimeType, sizeMB: finalSizeMB, isGoogleDrive: !!gdrive };
}

// ── تشغيل yt-dlp وإرجاع مخرجاته (مع تمرير كل سطر لدالة onLine) ──
const ytPending = new Map(); // طلبات .ytdl بانتظار التأكيد
const ytActive = new Map();  // تحميلات ytdl الجارية
function fmtCount(n) {
    if (!n && n !== 0) return null;
    if (n >= 1e9) return (n / 1e9).toFixed(1).replace(/\.0$/, '') + 'B';
    if (n >= 1e6) return (n / 1e6).toFixed(1).replace(/\.0$/, '') + 'M';
    if (n >= 1e3) return (n / 1e3).toFixed(1).replace(/\.0$/, '') + 'K';
    return String(n);
}
function fmtBytes(n) {
    if (!n) return 'غير معروف';
    return n >= 1073741824 ? (n / 1073741824).toFixed(2) + ' GB' : (n / 1048576).toFixed(1) + ' MB';
}
function runFfmpeg(args, onLine, holder = null, timeoutMs = 5 * 60 * 60 * 1000) {
    return new Promise((resolve, reject) => {
        const proc = spawn('ffmpeg', args);
        if (holder) holder.proc = proc;
        let err = '';
        const killer = setTimeout(() => { try { proc.kill('SIGINT'); } catch (_) {} }, timeoutMs);
        proc.stdout.on('data', c => { if (onLine) c.toString().split(/\r?\n/).forEach(l => { if (l.trim()) onLine(l.trim()); }); });
        proc.stderr.on('data', c => { err += c.toString(); });
        proc.on('error', e => { clearTimeout(killer); reject(new Error(e.code === 'ENOENT' ? 'ffmpeg غير مثبت على السيرفر' : e.message)); });
        proc.on('close', code => { clearTimeout(killer); resolve({ code, err: err.trim() }); });
    });
}
function runYtDlp(args, onLine, timeoutMs = 60 * 60 * 1000, holder = null) {
    return new Promise((resolve, reject) => {
        const proc = spawn('yt-dlp', args);
        if (holder) holder.proc = proc;
        let out = '', err = '';
        const killer = setTimeout(() => { try { proc.kill('SIGKILL'); } catch (_) {} }, timeoutMs);
        const handle = (chunk, isErr) => {
            const t = chunk.toString();
            if (isErr) err += t; else out += t;
            if (onLine) t.split(/\r?\n/).forEach(l => { if (l.trim()) onLine(l.trim()); });
        };
        proc.stdout.on('data', c => handle(c, false));
        proc.stderr.on('data', c => handle(c, true));
        proc.on('error', e => { clearTimeout(killer); reject(new Error(e.code === 'ENOENT' ? 'yt-dlp غير مثبت على السيرفر' : e.message)); });
        proc.on('close', code => {
            clearTimeout(killer);
            if (code === 0) return resolve(out.trim());
            const errLine = err.split('\n').filter(l => /ERROR/.test(l)).pop();
            reject(new Error((errLine || err.trim().slice(-300) || `yt-dlp exit ${code}`).replace(/^ERROR:\s*/, '')));
        });
    });
}

// ── تسجيل بث yt-dlp المباشر على أجزاء متتابعة (ffmpeg واحد، نسخ مباشر -c copy بلا إعادة ترميز) ──
// تُكتب الأجزاء بصيغة mpegts (تقبل أي كودك) ثم يُستدعى onSegmentReady لكل جزء فور اكتماله
// أثناء استمرار التسجيل. عند تجاوز الجزء الحالي حد الأمان يُوقف التسجيل كاملاً.
async function recordLiveSegments(urls, segDir, prefix, totalSec, segSec, audioOnly, onSegmentReady, state) {
    const pattern = path.join(segDir, `${prefix}_%03d.ts`);
    const inArgs = urls.flatMap(u => ['-reconnect', '1', '-reconnect_streamed', '1', '-reconnect_delay_max', '5', '-i', u]);
    const mapArgs = audioOnly
        ? (urls.length > 1 ? ['-map', '1:a:0'] : ['-map', '0:a:0'])
        : (urls.length > 1 ? ['-map', '0:v:0', '-map', '1:a:0'] : ['-map', '0:v:0?', '-map', '0:a:0?']);
    const args = [
        '-y', '-hide_banner', '-loglevel', 'error',
        ...inArgs,
        '-t', String(totalSec),
        ...mapArgs,
        '-c', 'copy',
        '-f', 'segment', '-segment_format', 'mpegts',
        '-segment_time', String(segSec),
        '-reset_timestamps', '1',
        pattern
    ];

    const proc = spawn('ffmpeg', args);
    state.holder.proc = proc; // لأمر .stopytdl
    let stderr = '';
    proc.stderr.on('data', (d) => { stderr += d.toString(); });

    let finished = false;
    let abortedBySize = false;
    let spawnErr = null;
    proc.on('close', () => { finished = true; });
    proc.on('error', (e) => { spawnErr = e; finished = true; });

    const getSegFiles = () => {
        try {
            return fs.readdirSync(segDir)
                .filter(f => f.startsWith(prefix + '_') && f.endsWith('.ts'))
                .map(f => ({ file: f, idx: parseInt(f.match(/_(\d+)\.ts$/)?.[1] || '-1') }))
                .filter(x => x.idx >= 0)
                .sort((a, b) => a.idx - b.idx);
        } catch (_) { return []; }
    };

    let lastSentIndex = -1;
    let sentCount = 0;

    while (!finished) {
        if (state.early) { try { proc.kill('SIGINT'); } catch (_) {} break; }

        const files = getSegFiles();
        // أي ملف غير الأخير (قيد الكتابة) يكون قد اكتمل
        for (let i = 0; i < files.length - 1; i++) {
            if (files[i].idx > lastSentIndex) {
                lastSentIndex = files[i].idx;
                sentCount++;
                await onSegmentReady(path.join(segDir, files[i].file));
            }
        }

        if (!abortedBySize && files.length > 0) {
            const active = files[files.length - 1];
            try {
                if (fs.statSync(path.join(segDir, active.file)).size >= RECORD_SEGMENT_SAFETY_BYTES) {
                    abortedBySize = true;
                    proc.kill('SIGINT');
                }
            } catch (_) {}
        }
        await new Promise(r => setTimeout(r, 3000));
    }

    if (!finished) {
        await new Promise((resolve) => {
            if (proc.exitCode !== null || proc.killed) return resolve();
            proc.once('close', resolve);
            proc.once('error', resolve);
        });
    }

    if (spawnErr) throw new Error(spawnErr.code === 'ENOENT' ? 'ffmpeg غير مثبت على السيرفر' : spawnErr.message);

    // إرسال ما تبقى (بما فيه الجزء الأخير) — حتى عند الإيقاف المبكر نرسل كل ما سُجّل
    for (const item of getSegFiles()) {
        if (item.idx > lastSentIndex) {
            lastSentIndex = item.idx;
            try { if (fs.statSync(path.join(segDir, item.file)).size === 0) continue; } catch (_) { continue; }
            sentCount++;
            await onSegmentReady(path.join(segDir, item.file));
        }
    }
    return { stderr, sentCount, abortedBySize };
}

// ── الطرفية (Shell) عبر واتساب: تحقق صارم من المالك + تنفيذ أوامر لينكس ──
const SHELL_CWD = new Map();      // chatId -> مجلد العمل الحالي
const SHELL_ACTIVE = new Map();   // chatId -> { proc, cmd, startedAt }
const SHELL_HOME = process.env.HOME || process.cwd();
const SHELL_OUTPUT_LIMIT = 3500;  // أحرف قبل تحويل الناتج إلى ملف
const SHELL_DEFAULT_TIMEOUT_MS = 60 * 1000;
const SHELL_MAX_TIMEOUT_MS = 10 * 60 * 1000;

// تحقق صارم: فقط مالك البوت (رقم مطابق تماماً) أو رسالة أرسلها حساب البوت نفسه (fromMe).
// لا سودو، ولا مطابقة جزئية، ولا اعتماد على عضوية المجموعات — لتفادي أي التفاف على التحقق.
function isStrictOwner(mek, chatId) {
    try {
        if (mek.key.fromMe) return true; // البوت نفسه مسجَّل برقم صاحبه
        const senderId = mek.key.participant || mek.key.remoteJid || '';
        const senderClean = String(senderId).split(':')[0].split('@')[0];
        const ownerClean = String(settings.ownerNumber || '').split(':')[0].split('@')[0];
        if (!ownerClean) return false;
        if (senderClean !== ownerClean) return false;
        // نقبل تطابق الرقم فقط في محادثة خاصة (ليس داخل مجموعة) تفادياً لأي التباس بمعرّفات @lid الجماعية
        return !String(chatId).endsWith('@g.us');
    } catch (_) { return false; }
}

function shellResolveCwd(chatId) {
    return SHELL_CWD.get(chatId) || SHELL_HOME;
}

// ينفّذ سطر أوامر واحداً عبر bash -c، مع دعم `cd` التراكمي، ومهلة قابلة للإيقاف المبكر
async function runShellCommand(chatId, rawCmd, timeoutMs) {
    const cwd = shellResolveCwd(chatId);
    // نلتقط cwd الناتج فعلياً بعد التنفيذ (يدعم `cd dir && ...` ويحدّث الجلسة)
    const marker = `__SHELL_CWD_MARK_${randomBytes(4).toString('hex')}__`;
    const wrapped = `${rawCmd}\nprintf '\\n${marker}%s\\n' "$PWD"`;

    return await new Promise((resolve) => {
        const proc = spawn('bash', ['-c', wrapped], {
            cwd,
            env: { ...process.env, DEBIAN_FRONTEND: 'noninteractive' },
            detached: true // يجعل proc.pid رئيس مجموعة عمليات مستقلة، فنقدر نقتل كل العمليات الفرعية (sleep, apt..) دفعة واحدة
        });
        // قتل مجموعة العمليات كاملة لا bash وحده، وإلا تبقى عملية فرعية جارية تُبقي stdout/stderr مفتوحين
        // فيتأخر حدث 'close' حتى تنتهي هي بنفسها (مثال: `sleep 5 && ...` مع مهلة ثانية واحدة كان ينتظر 5 ثوانٍ كاملة)
        const killGroup = (sig) => {
            try { process.kill(-proc.pid, sig); } catch (_) { try { proc.kill(sig); } catch (_) {} }
        };
        SHELL_ACTIVE.set(chatId, { proc, cmd: rawCmd, startedAt: Date.now(), kill: killGroup });

        let out = '';
        let truncated = false;
        const MAX_BUF = 6 * 1024 * 1024; // سقف داخلي لمنع استهلاك الذاكرة من مخرجات ضخمة
        const onData = (d) => {
            if (out.length < MAX_BUF) out += d.toString();
            else truncated = true;
        };
        proc.stdout.on('data', onData);
        proc.stderr.on('data', onData);

        const timer = setTimeout(() => killGroup('SIGKILL'), timeoutMs);

        proc.on('close', (code, signal) => {
            clearTimeout(timer);
            SHELL_ACTIVE.delete(chatId);
            let newCwd = cwd;
            const idx = out.lastIndexOf(marker);
            if (idx !== -1) {
                newCwd = out.slice(idx + marker.length).trim().split('\n')[0] || cwd;
                out = out.slice(0, idx);
            }
            SHELL_CWD.set(chatId, newCwd);
            resolve({
                output: out.replace(/\s+$/, ''),
                code,
                signal,
                timedOut: signal === 'SIGKILL' && code === null,
                truncated,
                cwd: newCwd
            });
        });
        proc.on('error', (e) => {
            clearTimeout(timer);
            SHELL_ACTIVE.delete(chatId);
            resolve({ output: `تعذر تشغيل bash: ${e.message}`, code: -1, signal: null, timedOut: false, truncated: false, cwd });
        });
    });
}

// ── تجزئة فلاغات yt-dlp إضافية يمررها المستخدم بعد `--` (تدعم الاقتباس بـ " أو ') ──
function parseYtExtraFlags(str) {
    if (!str) return [];
    const out = [];
    const re = /"([^"]*)"|'([^']*)'|(\S+)/g;
    let m;
    while ((m = re.exec(str)) !== null) {
        out.push(m[1] !== undefined ? m[1] : (m[2] !== undefined ? m[2] : m[3]));
    }
    return out;
}

// يفصل سطر الأمر عند ` -- ` الأولى: ما قبلها وسيطات الأمر العادية، وما بعدها فلاغات yt-dlp خام تُمرَّر كما هي
function splitYtExtraFlags(query) {
    const sepIdx = query.indexOf(' -- ');
    if (sepIdx === -1) return { main: query, extra: [] };
    return { main: query.slice(0, sepIdx), extra: parseYtExtraFlags(query.slice(sepIdx + 4)) };
}

// ── تحميل فيديو عادي عبر yt-dlp وإرساله كملف (مشتركة بين .ytdl وحالة الرابط غير المباشر في .ytlive) ──
async function ytDownloadAndSendJob(XeonBotInc, chatId, mek, ytUrl, ytMode, ytExtraFlags, ytUsedImpersonate, ytTitle) {
    const ytTmpDir = path.join(process.cwd(), 'dltmp');
    if (!fs.existsSync(ytTmpDir)) fs.mkdirSync(ytTmpDir, { recursive: true });
    const ytId = randomBytes(4).toString('hex');
    const ytBase = ['--no-playlist', '--no-warnings', '--no-colors', '--newline', '--js-runtimes', 'node'];
    const ytCookies = path.join(process.cwd(), 'cookies.txt');
    if (fs.existsSync(ytCookies)) ytBase.push('--cookies', ytCookies);
    const ytFmt = ytMode === 'audio'
        ? ['-x', '--audio-format', 'mp3', '--audio-quality', '0']
        : ['-f', `bv*[height<=${ytMode}][vcodec^=avc1]+ba[acodec^=mp4a]/b[height<=${ytMode}][ext=mp4]/bv*[height<=${ytMode}]+ba/b`, '--merge-output-format', 'mp4'];

    const state = { holder: {}, cancelled: false };
    ytActive.set(chatId, state);
    try {
        await XeonBotInc.sendMessage(chatId, { text: `⚡ *بدأ التحميل...*\n🎬 ${ytTitle}\n⛔ للإيقاف: \`.stopytdl\`` }, { quoted: mek });
        const ytStart = Date.now();
        let ytLast = 0;
        await runYtDlp(
            [...ytBase, ...ytUsedImpersonate, ...ytFmt, ...ytExtraFlags, '-o', path.join(ytTmpDir, `ytdl_${ytId}.%(ext)s`), ytUrl],
            (l) => {
                if (l.startsWith('[download]') && l.includes('%') && Date.now() - ytLast > 5000) {
                    ytLast = Date.now();
                    const _m = l.match(/([\d.]+)%/);
                    const _bar = _m ? progressBar(parseFloat(_m[1])) + ' ' : '';
                    console.log(`[PROGRESS] ytdl ${ytTitle}\n   ${_bar}${l.replace('[download]', '').trim()}`);
                }
            },
            60 * 60 * 1000,
            state.holder
        );

        const ytFiles = fs.readdirSync(ytTmpDir)
            .filter(f => f.startsWith(`ytdl_${ytId}.`) && !/\.(part|ytdl|temp)$/i.test(f))
            .map(f => ({ f, size: fs.statSync(path.join(ytTmpDir, f)).size }))
            .sort((a, b) => b.size - a.size);
        if (!ytFiles.length || ytFiles[0].size === 0) throw new Error('لم يتم العثور على الملف الناتج.');

        const ytFile = path.join(ytTmpDir, ytFiles[0].f);
        const ytExt = path.extname(ytFile);
        const ytSizeMB = (ytFiles[0].size / 1048576).toFixed(2);
        console.log(`[YTDL] done: ${ytSizeMB} MB | ${ytExt} | ${((Date.now() - ytStart) / 1000).toFixed(1)}s`);
        if (ytFiles[0].size > 2000 * 1048576) throw new Error(`الملف (${ytSizeMB} MB) يتجاوز حد واتساب 2 جيجا. جرّب جودة أقل.`);

        const ytSafeName = String(ytTitle || 'video').replace(/[\\/:*?"<>|]+/g, '').slice(0, 80).trim() || 'video';
        await XeonBotInc.sendMessage(chatId, {
            document: { url: ytFile },
            mimetype: ytExt === '.mp3' ? 'audio/mpeg' : 'video/mp4',
            fileName: `${ytSafeName}${ytExt}`,
            caption: `✅ *اكتمل التحميل!*\n🎬 ${ytTitle}\n⚖️ *الحجم:* ${ytSizeMB} MB`
        }, { quoted: mek });
        console.log('[YTDL] sent');
    } catch (err) {
        if (state.cancelled) {
            await XeonBotInc.sendMessage(chatId, { text: '⛔ تم إيقاف التحميل.' }, { quoted: mek });
        } else {
            console.log(`[YTDL] failed: ${err.message}`);
            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل التحميل:\n\`${err.message}\`` }, { quoted: mek });
        }
    } finally {
        ytActive.delete(chatId);
        try {
            for (const f of fs.readdirSync(ytTmpDir)) {
                if (f.startsWith(`ytdl_${ytId}.`)) { try { fs.unlinkSync(path.join(ytTmpDir, f)); } catch (_) {} }
            }
        } catch (_) {}
    }
}

// ============================================================
// البوت الرئيسي
// ============================================================
async function startXeonBotInc() {
    try {
        let { version, isLatest } = await fetchLatestBaileysVersion()
        const { state, saveCreds } = await useMultiFileAuthState(`./session`)
        const msgRetryCounterCache = new NodeCache()

        const XeonBotInc = makeWASocket({
            version,
            logger: pino({ level: 'silent' }),
            printQRInTerminal: !usePairing,
            browser: ["Ubuntu", "Chrome", "20.0.04"],
            auth: {
                creds: state.creds,
                keys: makeCacheableSignalKeyStore(state.keys, pino({ level: "fatal" }).child({ level: "fatal" })),
            },
            markOnlineOnConnect: false,
            generateHighQualityLinkPreview: true,
            syncFullHistory: false,
            getMessage: async (key) => {
                let jid = jidNormalizedUser(key.remoteJid)
                let msg = await store.loadMessage(jid, key.id)
                return msg?.message || ""
            },
            msgRetryCounterCache,
            defaultQueryTimeoutMs: 60000,
            connectTimeoutMs: 60000,
            keepAliveIntervalMs: 10000,
        })

        XeonBotInc.ev.on('creds.update', saveCreds)
        store.bind(XeonBotInc.ev)

        // ── طلب Pairing Code تلقائياً (لتشغيل GitHub Actions) ──
        if (usePairing && !XeonBotInc.authState.creds.registered) {
            global.__pairTries = (global.__pairTries || 0) + 1
            if (global.__pairTries <= 3) {
                let num = String(require('./settings').ownerNumber || (owner && owner[0]) || '').replace(/[^0-9]/g, '')
                setTimeout(async () => {
                    try {
                        let code = await XeonBotInc.requestPairingCode(num)
                        code = code?.match(/.{1,4}/g)?.join('-') || code
                        console.log('Your Pairing Code : ' + code)
                        console.log('Enter it now: WhatsApp > Linked Devices > Link with phone number')
                    } catch (e) { console.error('Pairing code error:', e.message) }
                }, 3000)
            }
        }

        // ============================================================
        // معالجة الرسائل
        // ============================================================
        XeonBotInc.ev.on('messages.upsert', async chatUpdate => {
            try {
                const mek = chatUpdate.messages[0]
                if (!mek.message) return
                mek.message = (Object.keys(mek.message)[0] === 'ephemeralMessage')
                    ? mek.message.ephemeralMessage.message
                    : mek.message

                const msgType = Object.keys(mek.message || {})[0];
                let text = '';
                if (msgType === 'conversation') text = mek.message.conversation;
                else if (msgType === 'extendedTextMessage') text = mek.message.extendedTextMessage.text;
                else if (mek.message?.[msgType]?.caption) text = mek.message[msgType].caption;

                const chatId = mek.key.remoteJid;
                // ── سجل الأوامر (يظهر في Actions) ──
                if (text && text.trim().startsWith('.')) {
                    const _who = String(mek.key.participant || chatId || '').split('@')[0];
                    const _masked = _who.length > 4 ? '***' + _who.slice(-4) : _who;
                    const _where = String(chatId).endsWith('@g.us') ? 'group' : 'private';
                    console.log(`[CMD] ${new Date().toISOString()} | ${_where} | from:${mek.key.fromMe ? 'me' : _masked} | ${text.trim().slice(0, 200)}`);
                }
                const isReply = msgType === 'extendedTextMessage' &&
                    mek.message.extendedTextMessage.contextInfo?.quotedMessage;

                // ============================================================
                // معالجة الردود (Reply)
                // ============================================================
                if (isReply && text) {
                    const quotedId = mek.message.extendedTextMessage.contextInfo.stanzaId;
                    const replyText = text.trim();

                    // ── المرحلة 4: اختيار الجودة ──
                    if (qualityCache.has(quotedId)) {
                        const cached = qualityCache.get(quotedId);
                        const idx = parseInt(replyText) - 1;
                        if (!cached.links[idx]) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        const qName = cached.names[idx];
                        qualityCache.delete(quotedId);

                        // ── حجم أكبر من 2GB → لا تحميل مباشر ولا تمرير تلقائي؛ نطبع الرابط والحجم فقط والمستخدم يمرّره بنفسه لـ .remotedl ──
                        if (cached.sizes && cached.sizes[idx] && cached.sizes[idx] > FOOTBALL_MAX_DIRECT_BYTES) {
                            const bigUrl = cached.links[idx];
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ *الحجم كبير جداً للتحميل المباشر!*\n📌 *العنوان:* ${cached.title || '-'}\n⚙️ *الجودة:* ${qName}\n⚖️ *الحجم:* ${fmtBytes(cached.sizes[idx])} (حد واتساب 2GB)\n\n🔗 *رابط التحميل المباشر:*\n${bigUrl}\n\n💡 مرّر الرابط بنفسك لأمر \`.remotedl\` مع حجم الجزء اللي تختاره (مثلاً 500 لأجزاء 500MB — ولازم يفضل أقل من 2000 لأن واتساب أقصى ملف 2GB).`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });


                        // ── تحميل مدى حلقات (نفس منطق الحلقة الواحدة، في حلقة تكرار) ──
                        if (cached.batch && cached.batch.length) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `📥 جودة [${qName}] — جاري تحميل ${cached.batch.length} حلقة، يرجى الانتظار...`
                            }, { quoted: mek });
                            let ok = 0; const failedNums = [];
                            for (const item of cached.batch) {
                                const link = item.links[Math.min(idx, item.links.length - 1)];
                                let outPath = path.join(tmpDir, `vid_${randomBytes(4).toString('hex')}.mp4`);
                                try {
                                    await downloadVideoSmart(link.url, outPath, {
                                        'User-Agent': WEB_UA,
                                        'Referer': item.referer || cached.referer || 'https://akwam.ss/',
                                        ...(cached.headers || {})
                                    });
                                    if (item.subtitleUrl) outPath = await muxSubtitleIntoMp4(outPath, item.subtitleUrl);
                                    const finalSizeMB = (fs.statSync(outPath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: outPath },
                                        mimetype: 'video/mp4',
                                        fileName: `${cached.title || 'video'} - الحلقة ${item.number}.mp4`,
                                        caption:
                        `✅ *تم التحميل بنجاح!*
                        📌 *العنوان:* ${cached.title || '-'}
                        🎬 *الحلقة:* ${item.number}
                        ⚙️ *الجودة:* ${qName}
                        ⚖️ *الحجم:* ${finalSizeMB} MB`
                                    }, { quoted: mek });
                                    ok++;
                                } catch (err) {
                                    failedNums.push(item.number);
                                } finally {
                                    try { if (fs.existsSync(outPath)) fs.unlinkSync(outPath); } catch (_) {}
                                }
                            }
                            await XeonBotInc.sendMessage(chatId, {
                                text: ok === cached.batch.length
                                    ? `✅ تم تحميل كل الحلقات (${ok}/${cached.batch.length}).`
                                    : `⚠️ تم تحميل ${ok} من ${cached.batch.length} حلقة.${failedNums.length ? `\n❌ فشلت الحلقات: ${failedNums.join('، ')}` : ''}`
                            }, { quoted: mek });
                            return;
                        }


                        // ── تحميل رابط/حلقة واحدة (السلوك الأصلي) ──
                        const finalUrl = cached.links[idx];

                        await XeonBotInc.sendMessage(chatId, {
                            text: `📥 جودة [${qName}] — جاري التحميل، يرجى الانتظار...`
                        }, { quoted: mek });

                        let outPath;

                        // ── تقدّم تحميل .football في لوج GitHub Actions فقط (v117.4) — رسالة واتساب بدون أي تعديل ──
                        const footballProgress = !!cached.football;
                        const footballDlStartAt = Date.now();
                        const footballKnownTotal = (cached.sizes && cached.sizes[idx]) || null;
                        let footballLastLogPct = -1;
                        let footballLastLogAt = Date.now();
                        const footballFmtMB = (n) => n >= 1073741824 ? (n / 1073741824).toFixed(2) + ' GB' : (n / 1048576).toFixed(1) + ' MB';
                        const footballOnProgress = footballProgress ? (p) => {
                            const now = Date.now();
                            const total = p.total || footballKnownTotal || null;
                            const pct = total ? Math.min(100, Math.floor((p.downloaded || 0) / total * 100)) : null;
                            const isFinal = pct === 100;
                            if (!isFinal && pct !== null && pct - footballLastLogPct < 10 && now - footballLastLogAt < 15000) return;
                            if (!isFinal && pct === null && now - footballLastLogAt < 15000) return;
                            footballLastLogPct = pct === null ? footballLastLogPct : pct;
                            footballLastLogAt = now;
                            const speed = (p.elapsedMs > 0 && p.downloaded) ? footballFmtMB(Math.round(p.downloaded / (p.elapsedMs / 1000))) + '/s' : '—';
                            if (pct === null) console.log(`[FOOTBALL-DOWNLOAD] ⏳ ${footballFmtMB(p.downloaded || 0)} / ${total ? footballFmtMB(total) : '؟'} — ${speed}`);
                            else console.log(`[FOOTBALL-DOWNLOAD] ${pct}% — ${footballFmtMB(p.downloaded || 0)} / ${footballFmtMB(total)} — ${speed}`);
                        } : null;

                        try {

                            outPath = path.join(
                                tmpDir,
                                `vid_${randomBytes(4).toString('hex')}.mp4`
                            );

                            await downloadVideoSmart(finalUrl, outPath, {
                                'User-Agent': WEB_UA,
                                'Referer': (cached.referers && cached.referers[idx]) || cached.referer || 'https://akwam.ss/',
                                ...((cached.headerSets && cached.headerSets[idx]) || cached.headers || {})
                            }, footballOnProgress);
                            if (cached.subtitleUrl) outPath = await muxSubtitleIntoMp4(outPath, cached.subtitleUrl);

                            const finalSizeMB =
                            (fs.statSync(outPath).size / 1024 / 1024).toFixed(2);

                            if (footballProgress) console.log(`[FOOTBALL-DOWNLOAD] ✅ اكتمل التحميل — ${cached.title || ''} — ${qName} — ${finalSizeMB} MB — ${((Date.now() - footballDlStartAt) / 1000).toFixed(0)}s`);

                        await XeonBotInc.sendMessage(chatId, {
                            document: { url: outPath },
                            mimetype: 'video/mp4',
                            fileName: `${cached.title || 'video'}.mp4`,
                            caption:
                        `✅ *تم التحميل بنجاح!*
                        📌 *العنوان:* ${cached.title || '-'}
                        ⚙️ *الجودة:* ${qName}
                        ⚖️ *الحجم:* ${finalSizeMB} MB`
                        }, { quoted: mek });

                        } catch (err) {

                            if (footballProgress) console.log(`[FOOTBALL-DOWNLOAD] ❌ فشل التحميل — ${cached.title || ''} — ${qName}: ${err.message}`);

                            try {
                                if (outPath && fs.existsSync(outPath))
                                    fs.unlinkSync(outPath);
                            } catch (_) {}

                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل التحميل:\n\`${err.message}\``
                            }, { quoted: mek });

                        } finally {

                            try {
                                if (outPath && fs.existsSync(outPath))
                                    fs.unlinkSync(outPath);
                            } catch (_) {}

                        }

                        return;
                    }

                    // ── اختيار جودة فيديو ok.ru (okruCache) ──
                    if (okruCache.has(quotedId)) {
                        const cached = okruCache.get(quotedId);
                        const idx = parseInt(replyText) - 1;
                        const chosen = cached.videos[idx];

                        if (!chosen) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        okruCache.delete(quotedId);

                        const qualityLabels = {
                            ultra: '2160p (Ultra HD)',
                            quad: '1440p (Quad HD)',
                            full: '1080p (Full HD)',
                            hd: '720p (HD)',
                            sd: '480p (SD)',
                            low: '360p',
                            lowest: '240p',
                            mobile: '144p (Mobile)'
                        };
                        const qLabel = qualityLabels[chosen.name] || chosen.name || 'غير معروفة';

                        await XeonBotInc.sendMessage(chatId, {
                            text: `⬇️ *جاري تحميل الفيديو...*\n📺 الجودة: ${qLabel}`
                        }, { quoted: mek });

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });
                        const tmpPath = path.join(tmpDir, `okru_${randomBytes(4).toString('hex')}.mp4`);

                        try {
                            const videoUrl = String(chosen.url).replace(/\\u0026/g, '&').replace(/\\\//g, '/');

                            const videoRes = await axios({
                                method: 'GET',
                                url: videoUrl,
                                responseType: 'stream',
                                timeout: 1800000,
                                headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36' }
                            });

                            const writer = fs.createWriteStream(tmpPath);
                            trackStream(videoRes.data, 'ok.ru video', videoRes.headers['content-length']);
                            videoRes.data.pipe(writer);
                            await new Promise((resolve, reject) => {
                                writer.on('finish', resolve);
                                writer.on('error', reject);
                            });

                            const sizeMB = (fs.statSync(tmpPath).size / 1024 / 1024).toFixed(2);

                            await XeonBotInc.sendMessage(chatId, {
                                video: { url: tmpPath },
                                mimetype: 'video/mp4',
                                caption: `✅ *${cached.title}*\n⚖️ الحجم: ${sizeMB} MB\n📺 الجودة: ${qLabel}`
                            }, { quoted: mek });

                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل تحميل الفيديو من ok.ru:\n\`${err.message}\``
                            }, { quoted: mek });
                        } finally {
                            if (fs.existsSync(tmpPath)) {
                                try { fs.unlinkSync(tmpPath); } catch (_) {}
                            }
                        }
                        return;
                    }

                    // ── مراحل المانجا (mangaCache) ──
                    if (mangaCache.has(quotedId)) {
                        const cached = mangaCache.get(quotedId);

                        // المرحلة 1: اختيار المانجا
                        if (cached.stage === 'manga_list') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.results[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            const selected = cached.results[idx];
                            mangaCache.delete(quotedId);

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب قائمة فصول *${selected.name}*...`
                            }, { quoted: mek });

                            try {
                                const MANGA_HEADERS = {
                                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                                    'Accept': 'text/html,*/*;q=0.9',
                                    'Accept-Language': 'ar,en;q=0.9',
                                    'Referer': 'https://3asq.online/'
                                };

                                const pageRes = await axios.get(selected.url, {
                                    headers: MANGA_HEADERS, timeout: 15000
                                });
                                const pageHtml = pageRes.data;
                                const mangaSlug = selected.url.replace(/.*\/manga\//, '').replace(/\/$/, '');

                                const chapterRegex = new RegExp(
                                    'href="(https?://3asq\\.online/manga/' + mangaSlug.replace(/-/g, '-') + '/([\\d]+(?:\\.[\\d]+)?)/?)(?:[^"]*)"',
                                    'gi'
                                );

                                const chapters = [];
                                let cm;
                                while ((cm = chapterRegex.exec(pageHtml)) !== null) {
                                    const url = cm[1].endsWith('/') ? cm[1] : cm[1] + '/';
                                    const num = parseFloat(cm[2]);
                                    if (!isNaN(num) && !chapters.some(c => c.num === num)) {
                                        chapters.push({ url, num });
                                    }
                                }

                                if (chapters.length <= 2) {
                                    const nonceMatch = pageHtml.match(/["']nonce["']\s*:\s*["']([a-f0-9]+)["']/);
                                    const idMatch    = pageHtml.match(/postid-([0-9]+)|manga_id[^0-9]+([0-9]+)|data-id="([0-9]+)"/);
                                    const mangaId    = idMatch ? (idMatch[1] || idMatch[2] || idMatch[3]) : null;
                                    const nonce      = nonceMatch ? nonceMatch[1] : '';

                                    if (mangaId) {
                                        try {
                                            const ajaxRes = await axios.post(
                                                'https://3asq.online/wp-admin/admin-ajax.php',
                                                `action=manga_get_chapters&manga=${mangaId}${nonce ? '&nonce=' + nonce : ''}`,
                                                {
                                                    headers: {
                                                        'User-Agent': 'Mozilla/5.0',
                                                        'Referer': selected.url,
                                                        'Content-Type': 'application/x-www-form-urlencoded',
                                                        'X-Requested-With': 'XMLHttpRequest',
                                                        'Origin': 'https://3asq.online'
                                                    },
                                                    timeout: 20000,
                                                    validateStatus: () => true
                                                }
                                            );

                                            const ajaxHtml = typeof ajaxRes.data === 'string'
                                                ? ajaxRes.data
                                                : (ajaxRes.data?.data || '');

                                            const ajaxRegex = /href="(https?:\/\/3asq\.online\/manga\/[^\/]+\/([\d]+(?:\.[\d]+)?)\/?)"/gi;
                                            let am;
                                            while ((am = ajaxRegex.exec(ajaxHtml)) !== null) {
                                                const url = am[1].endsWith('/') ? am[1] : am[1] + '/';
                                                const num = parseFloat(am[2]);
                                                if (!isNaN(num) && !chapters.some(c => c.num === num)) {
                                                    chapters.push({ url, num });
                                                }
                                            }
                                        } catch (_) {}
                                    }

                                    if (chapters.length <= 2 && chapters.length > 0) {
                                        const minCh = Math.min(...chapters.map(c => c.num));
                                        const maxCh = Math.max(...chapters.map(c => c.num));
                                        for (let n = minCh; n <= maxCh; n++) {
                                            if (!chapters.some(c => c.num === n)) {
                                                chapters.push({
                                                    url: `https://3asq.online/manga/${mangaSlug}/${n}/`,
                                                    num: n
                                                });
                                            }
                                        }
                                    }
                                }

                                chapters.sort((a, b) => a.num - b.num);
                                if (chapters.length === 0) throw new Error('تعذر جلب الفصول. تأكد من اسم المانجا.');

                                const first = chapters[0].num;
                                const last  = chapters[chapters.length - 1].num;

                                let chText = `📚 *${selected.name}*\n\n`;
                                chText += `📖 الفصول المتاحة: *${first}* → *${last}*\n`;
                                chText += `📊 العدد الكلي: *${chapters.length}* فصل\n\n`;
                                chText += `💡 **رد (Reply)** بأرقام الفصول المطلوبة:\n`;
                                chText += `مثال: \`1 5\` (من فصل 1 إلى 5)\n`;
                                chText += `أو: \`10\` (فصل واحد فقط)\n\n`;
                                chText += `⚠️ الحد الأقصى 10 فصول في طلب واحد.\n`;
                                chText += `📦 سيتم إرسال كل فصل كملف ZIP منفصل.`;

                                const sentCh = await XeonBotInc.sendMessage(chatId, { text: chText }, { quoted: mek });
                                mangaCache.set(sentCh.key.id, {
                                    stage: 'chapter_select',
                                    mangaName: selected.name,
                                    mangaUrl: selected.url,
                                    chapters,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => mangaCache.delete(sentCh.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ ${err.message}` }, { quoted: mek });
                            }
                            return;
                        }

                        // المرحلة 2: اختيار الفصول → إرسال كل فصل ZIP منفصل
                        if (cached.stage === 'chapter_select') {
                            const parts   = replyText.trim().split(/\s+/);
                            const fromNum = parseFloat(parts[0]);
                            const toNum   = parts[1] ? parseFloat(parts[1]) : fromNum;
                            mangaCache.delete(quotedId);

                            if (isNaN(fromNum)) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ صيغة غير صحيحة. مثال: `1 5` أو `10`' }, { quoted: mek });
                                return;
                            }

                            const selectedChapters = cached.chapters.filter(
                                c => c.num >= fromNum && c.num <= toNum
                            ).slice(0, 10);

                            if (selectedChapters.length === 0) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ لم يتم العثور على الفصول المطلوبة.' }, { quoted: mek });
                                return;
                            }

                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                            const mangaNameClean = cached.mangaName.replace(/[^\w\s-]/g, '').trim();

                            await XeonBotInc.sendMessage(chatId, {
                                text: `📥 *سيتم إرسال ${selectedChapters.length} فصل — كل فصل كملف ZIP منفصل*\n📚 ${cached.mangaName}\n⏳ جاري البدء...`
                            }, { quoted: mek });

                            // دالة استخراج صور فصل واحد
                            const fetchChapterImgs = async (ch) => {
                                const chRes = await axios.get(ch.url, {
                                    headers: {
                                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                                        'Referer': 'https://3asq.online/'
                                    },
                                    timeout: 15000
                                });

                                const imgUrls = [];
                                const wpMangaRegex = /(https?:\/\/3asq\.online\/wp-content\/uploads\/WP-manga\/data\/[^"'\s<>]+\.(?:png|jpg|jpeg|webp))/gi;
                                let im;
                                while ((im = wpMangaRegex.exec(chRes.data)) !== null) {
                                    const u = im[1].replace(/&amp;/g, '&').trim();
                                    if (!imgUrls.includes(u)) imgUrls.push(u);
                                }
                                if (imgUrls.length === 0) {
                                    const lazySrcRegex = /data-src="(https?:\/\/3asq\.online\/wp-content\/uploads\/WP-manga\/data\/[^"]+\.(?:png|jpg|jpeg|webp))"/gi;
                                    while ((im = lazySrcRegex.exec(chRes.data)) !== null) {
                                        const u = im[1].replace(/&amp;/g, '&').trim();
                                        if (!imgUrls.includes(u)) imgUrls.push(u);
                                    }
                                }
                                if (imgUrls.length === 0) {
                                    const classRegex = /class="wp-manga-chapter-img"[^>]*(?:src|data-src)="([^"]+\.(?:png|jpg|jpeg|webp))"/gi;
                                    while ((im = classRegex.exec(chRes.data)) !== null) {
                                        const u = im[1].replace(/&amp;/g, '&').trim();
                                        if (u.startsWith('http') && !imgUrls.includes(u)) imgUrls.push(u);
                                    }
                                }
                                return imgUrls;
                            };

                            // ── معالجة كل فصل بشكل منفصل ──
                            for (const ch of selectedChapters) {
                                const batchId    = randomBytes(3).toString('hex');
                                const chZipPath  = path.join(tmpDir, `${mangaNameClean}_Ch${ch.num}_${batchId}.zip`);

                                try {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `📖 جاري تحميل الفصل *${ch.num}*...`
                                    }, { quoted: mek });

                                    const imgUrls = await fetchChapterImgs(ch);
                                    if (imgUrls.length === 0) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ الفصل ${ch.num}: لم يتم العثور على صور، تم التخطي.`
                                        }, { quoted: mek });
                                        continue;
                                    }

                                    // تحميل صور الفصل بالتوازي
                                    const dlPromises = imgUrls.map(async (imgUrl, i) => {
                                        const ext = imgUrl.match(/\.(jpg|jpeg|png|webp)/i)?.[1] || 'jpg';
                                        try {
                                            const imgRes = await axios({
                                                method: 'GET', url: imgUrl,
                                                responseType: 'arraybuffer', timeout: 30000,
                                                headers: {
                                                    'User-Agent': 'Mozilla/5.0',
                                                    'Referer': 'https://3asq.online/'
                                                }
                                            });
                                            return {
                                                data: Buffer.from(imgRes.data),
                                                name: `page_${String(i).padStart(3, '0')}.${ext}`
                                            };
                                        } catch (_) { return null; }
                                    });

                                    const downloaded = (await Promise.all(dlPromises))
                                        .filter(Boolean)
                                        .sort((a, b) => a.name.localeCompare(b.name));

                                    if (downloaded.length === 0) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ الفصل ${ch.num}: فشل تحميل الصور، تم التخطي.`
                                        }, { quoted: mek });
                                        continue;
                                    }

                                    // بناء ZIP لهذا الفصل فقط
                                    buildZip(downloaded, chZipPath);

                                    const sizeMB = (fs.statSync(chZipPath).size / 1024 / 1024).toFixed(2);

                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: chZipPath },
                                        mimetype: 'application/zip',
                                        fileName: `${mangaNameClean}_Ch${ch.num}.zip`,
                                        caption: `📚 *${cached.mangaName}*\n🔖 الفصل: ${ch.num}\n🖼️ الصفحات: ${downloaded.length}\n⚖️ الحجم: ${sizeMB} MB`
                                    }, { quoted: mek });

                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل الفصل ${ch.num}: ${err.message}`
                                    }, { quoted: mek });
                                } finally {
                                    // تنظيف فوري بعد كل فصل
                                    try { if (fs.existsSync(chZipPath)) fs.unlinkSync(chZipPath); } catch (_) {}
                                }
                            }

                            // رسالة اكتمال
                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *اكتمل الإرسال!*\n📚 ${cached.mangaName}\n🔖 الفصول: ${selectedChapters[0].num} → ${selectedChapters[selectedChapters.length - 1].num}\n📦 تم إرسال ${selectedChapters.length} ملف ZIP`
                            }, { quoted: mek });

                            return;
                        }
                    }

                    // ── المرحلة 3 (akwam): اختيار الحلقة → جلب الجودات ──
                    if (akwamCache.has(quotedId)) {
                        const cached = akwamCache.get(quotedId);

                        if (cached.stage === 'series_list') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.results[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            const selected = cached.results[idx];
                            akwamCache.delete(quotedId);

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب حلقات *${selected.name}*...`
                            }, { quoted: mek });

                            try {
                                const html = await akwamFetch(selected.url);
                                const episodes = extractAkwamEpisodes(html);
                                if (episodes.length === 0) throw new Error('لم يتم العثور على حلقات.');

                                let epText = `🎬 *حلقات ${selected.name}:*\n\n`;
                                episodes.slice(0, 40).forEach((ep, i) => {
                                    const label = ep.replace(/.*\/episode\//, '').replace(/-/g, ' ').replace(/\/$/, '');
                                    epText += `*${i + 1}* - ${label}\n`;
                                });
                                epText += `\n💡 **رد (Reply)** برقم الحلقة لاستخراج الجودات.`;

                                const sentEp = await XeonBotInc.sendMessage(chatId, { text: epText }, { quoted: mek });
                                akwamCache.set(sentEp.key.id, {
                                    stage: 'episode_list',
                                    results: episodes.slice(0, 40),
                                    seriesName: selected.name,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => akwamCache.delete(sentEp.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ ${err.message}` }, { quoted: mek });
                            }
                            return;
                        }

                        if (cached.stage === 'episode_list') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.results[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            const epUrl = cached.results[idx];
                            const seriesName = cached.seriesName;
                            akwamCache.delete(quotedId);

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري استخراج الجودات المتاحة...`
                            }, { quoted: mek });

                            try {
                                const mp4Links = await extractAkwamMp4Links(epUrl);
                                if (mp4Links.length === 0) throw new Error('لم يتم العثور على روابط تحميل مباشرة.');

                                const getQualityName = (url) => {
                                    const u = url.toLowerCase();
                                    if (u.includes('1080') || u.includes('fhd')) return '🔵 FHD 1080p';
                                    if (u.includes('720') || u.includes('hd'))  return '🟢 HD 720p';
                                    if (u.includes('480') || u.includes('sd'))  return '🟡 SD 480p';
                                    if (u.includes('360'))                       return '🟠 360p';
                                    return `⚪ جودة ${url.match(/(\d{3,4}p)/i)?.[1] || 'غير معروفة'}`;
                                };

                                const getWeight = (url) => {
                                    const u = url.toLowerCase();
                                    if (u.includes('1080') || u.includes('fhd')) return 4;
                                    if (u.includes('720') || u.includes('hd'))  return 3;
                                    if (u.includes('480') || u.includes('sd'))  return 2;
                                    if (u.includes('360'))                       return 1;
                                    return 0;
                                };
                                mp4Links.sort((a, b) => getWeight(b) - getWeight(a));

                                const names = mp4Links.map(l => getQualityName(l));

                                let qText = `⚙️ *الجودات المتاحة لـ ${seriesName}:*\n\n`;
                                names.forEach((n, i) => { qText += `*${i + 1}* - ${n}\n`; });
                                qText += `\n💡 **رد (Reply)** برقم الجودة لبدء التحميل الفوري.`;

                                const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                qualityCache.set(sentQ.key.id, {
                                    links: mp4Links,
                                    names,
                                    title: seriesName,
                                    referer: 'https://akwam.ss/',
                                    timestamp: Date.now()
                                });
                                setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ ${err.message}` }, { quoted: mek });
                            }
                            return;
                        }
                    }

                    // ── خطوات .livefootball التفاعلية بالرد: جودة ← مدة التسجيل ← دقائق الجزء ──
                    if (liveFootballQualityCache.has(quotedId)) {
                        const cached = liveFootballQualityCache.get(quotedId);
                        const stage = cached.stage || 'quality';
                        const job = { ...cached };
                        delete job.variants;
                        delete job.stage;
                        if (stage === 'quality') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.variants || !cached.variants[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من قائمة الجودات.' }, { quoted: mek });
                                return;
                            }
                            const chosen = cached.variants[idx];
                            liveFootballQualityCache.delete(quotedId);
                            job.streamUrl = chosen.url;
                            job.qualityHeight = chosen.height || null;
                            job.qualityLabel = chosen.height ? `${chosen.height}p` : 'غير معروفة';
                            await lfWizardNext(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        if (stage === 'duration') {
                            const mins = parseInt(String(replyText).trim());
                            if (isNaN(mins) || mins < 1 || mins > 360) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ اكتب عدد دقائق التسجيل برقم بين 1 و 360.' }, { quoted: mek });
                                return;
                            }
                            liveFootballQualityCache.delete(quotedId);
                            job.duration = mins;
                            // إن كانت دقائق الجزء المعطاة بالأمر أكبر من المدة الجديدة، نرجع للتقطيع التلقائي
                            if (job.manualSegmentMinutes && job.manualSegmentMinutes > mins) job.manualSegmentMinutes = null;
                            await lfWizardNext(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        if (stage === 'segment') {
                            const seg = parseInt(String(replyText).trim());
                            if (isNaN(seg) || seg < 0 || seg > job.duration) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ اكتب رقماً بين 0 و ${job.duration} (0 = تقطيع تلقائي).` }, { quoted: mek });
                                return;
                            }
                            liveFootballQualityCache.delete(quotedId);
                            job.segDecided = true;
                            job.manualSegmentMinutes = seg === 0 ? null : seg;
                            await lfWizardNext(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        return;
                    }

                    // ── خطوات .tflix التفاعلية بالرد: قناة ← جودة ← مدة التسجيل ← دقائق الجزء ──
                    if (tflixWizardCache.has(quotedId)) {
                        const cached = tflixWizardCache.get(quotedId);
                        const stage = cached.stage || 'quality';
                        const job = { ...cached };
                        delete job.variants;
                        delete job.stage;
                        if (stage === 'channel') {
                            const idx = parseInt(String(replyText).trim()) - 1;
                            if (!cached.channels || !cached.channels[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من قائمة القنوات.' }, { quoted: mek });
                                return;
                            }
                            tflixWizardCache.delete(quotedId);
                            job.channelId = cached.channels[idx].id;
                            job.channelName = cached.channels[idx].name;
                            await tflixBeginFlow(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        if (stage === 'quality') {
                            const idx = parseInt(String(replyText).trim()) - 1;
                            if (!cached.variants || !cached.variants[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من قائمة الجودات.' }, { quoted: mek });
                                return;
                            }
                            const chosen = cached.variants[idx];
                            tflixWizardCache.delete(quotedId);
                            job.videoRep = chosen;
                            job.qualityLabel = chosen.height ? `${chosen.height}p` : 'غير معروفة';
                            await tflixWizardNext(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        if (stage === 'duration') {
                            const mins = parseInt(String(replyText).trim());
                            if (isNaN(mins) || mins < 1 || mins > 360) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ اكتب عدد دقائق التسجيل برقم بين 1 و 360.' }, { quoted: mek });
                                return;
                            }
                            tflixWizardCache.delete(quotedId);
                            job.duration = mins;
                            if (job.manualSegmentMinutes && job.manualSegmentMinutes > mins) job.manualSegmentMinutes = null;
                            await tflixWizardNext(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        if (stage === 'segment') {
                            const seg = parseInt(String(replyText).trim());
                            if (isNaN(seg) || seg < 0 || seg > job.duration) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ اكتب رقماً بين 0 و ${job.duration} (0 = تقطيع تلقائي).` }, { quoted: mek });
                                return;
                            }
                            tflixWizardCache.delete(quotedId);
                            job.segDecided = true;
                            job.manualSegmentMinutes = seg === 0 ? null : seg;
                            await tflixWizardNext(XeonBotInc, chatId, mek, job);
                            return;
                        }
                        return;
                    }

                    // ── اختيار مباراة من قايمة .football recent ──
                    if (footballCache.has(quotedId)) {
                        const cached = footballCache.get(quotedId);
                        const num = parseInt(String(replyText).trim());
                        if (isNaN(num) || num < 1) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }
                        const match = cached.matches[num - 1];
                        if (!match) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }
                        footballCache.delete(quotedId);
                        const matchTitle = `${match.home} vs ${match.away}`;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `⏳ جاري البحث عن المباراة الكاملة لـ\n*${matchTitle}*...`
                        }, { quoted: mek });
                        try {
                            const [sf, ok, md] = await Promise.allSettled([
                                footballResolveSoccerFull(match),
                                footballResolveOkruFull(match.home, match.away),
                                footballResolveMixDrop(match)
                            ]);
                            const soccerFull = sf.status === 'fulfilled' ? sf.value : null;
                            const okFull = ok.status === 'fulfilled' ? ok.value.full : null;
                            const okHl = ok.status === 'fulfilled' ? ok.value.highlights : null;
                            const mixDrop = md.status === 'fulfilled' ? md.value : null;

                            const options = [];
                            if (soccerFull) {
                                options.push({
                                    label: `⚽ SoccerFull — ${soccerFull.label} (${footballFmtDuration(soccerFull.durationSec)})`,
                                    url: soccerFull.m3u8Url, sizeBytes: soccerFull.sizeBytes,
                                    referer: soccerFull.matchUrl
                                });
                            }
                            if (mixDrop) {
                                options.push({
                                    label: `💾 MixDrop — MP4${mixDrop.durationSec ? ` (${footballFmtDuration(mixDrop.durationSec)})` : ''}`,
                                    url: mixDrop.mp4Url, sizeBytes: mixDrop.sizeBytes,
                                    referer: mixDrop.eUrl,
                                    headers: { ...(mixDrop.cookie ? { Cookie: mixDrop.cookie } : {}), Referer: mixDrop.eUrl }
                                });
                            }
                            if (okFull) {
                                for (const q of okFull.qualities) {
                                    options.push({
                                        label: `📺 ok.ru — ${q.label}`,
                                        url: q.url, sizeBytes: q.sizeBytes,
                                        referer: 'https://ok.ru/'
                                    });
                                }
                            }

                            if (!options.length) {
                                // لا تحميل مباشر للمباراة الكاملة — لينك مشاهدة + ملخص إن وُجد
                                let msg = `⚠️ *المباراة الكاملة لسه مش متاحة للتحميل المباشر.*\n⚽ ${matchTitle}\n\n🎬 *شاهدها هنا:*\n${match.url}`;
                                if (okHl) {
                                    try {
                                        const { title, videos } = await extractOkruVideo(`https://ok.ru/video/${okHl.id}`);
                                        const qOpts = [];
                                        const sized = await Promise.allSettled(videos.map(async v => {
                                            const url = String(v.url).replace(/\\u0026/g, '&').replace(/\\\//g, '/');
                                            return { name: v.name, label: OKRU_QUALITY_LABELS[v.name] || v.name || 'غير معروفة', url, sizeBytes: await footballHeadSize(url) };
                                        }));
                                        for (const s of sized) if (s.status === 'fulfilled') qOpts.push(s.value);
                                        if (qOpts.length) {
                                            let qText = `${msg}\n\n🎞️ *الملخص متاح للتحميل (${footballFmtDuration(okHl.durationSec)}):*\n\n`;
                                            qOpts.forEach((o, i) => { qText += `*${i + 1}* - 📺 ok.ru — ${o.label} — ${o.sizeBytes ? fmtBytes(o.sizeBytes) : 'الحجم غير معروف'}\n`; });
                                            qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة المطلوبة.`;
                                            const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                            qualityCache.set(sentQ.key.id, {
                                                links: qOpts.map(o => o.url),
                                                names: qOpts.map(o => `📺 ok.ru — ${o.label}`),
                                                sizes: qOpts.map(o => o.sizeBytes),
                                                referers: qOpts.map(() => 'https://ok.ru/'),
                                                title: `${matchTitle} — ملخص`,
                                                referer: 'https://ok.ru/',
                                                headers: {},
                                                football: true, // تقدّم .football في لوج Actions (v117.4)
                                                timestamp: Date.now()
                                            });
                                            setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                            return;
                                        }
                                    } catch (_) {}
                                }
                                msg += `\n\n💡 جرّب تاني بعد شوية — الرفوعات الكاملة بتنزل بعد المباراة بساعات.`;
                                await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                                return;
                            }

                            let qText = `🍿 *اختر جودة التحميل:*\n⚽ ${matchTitle}\n🎬 مباراة كاملة\n\n`;
                            options.forEach((o, i) => {
                                const sizeStr = o.sizeBytes ? fmtBytes(o.sizeBytes) : 'الحجم غير معروف';
                                const big = o.sizeBytes && o.sizeBytes > FOOTBALL_MAX_DIRECT_BYTES ? ' ⚠️ فوق 2GB — تحميل عن بُعد' : '';
                                qText += `*${i + 1}* - ${o.label} — ${sizeStr}${big}\n`;
                            });
                            qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة المطلوبة.`;
                            const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                            qualityCache.set(sentQ.key.id, {
                                links: options.map(o => o.url),
                                names: options.map(o => o.label),
                                sizes: options.map(o => o.sizeBytes),
                                referers: options.map(o => o.referer),
                                headerSets: options.map(o => o.headers || null), // هيدرز مخصصة لكل خيار (MixDrop: كوكيز + Referer) — v117
                                title: `${matchTitle} — Full Match`,
                                referer: options[0].referer || 'https://footballzzz.com/',
                                headers: {},
                                football: true, // تقدّم .football في لوج Actions (v117.4)
                                timestamp: Date.now()
                            });
                            setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل جلب المباراة:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── اختيار أنمي/حلقة من نتائج .anime (متعدد المصادر) ──
                    if (animeCache.has(quotedId)) {
                        const cachedData = animeCache.get(quotedId);
                        const num = parseInt(String(replyText).trim());
                        if (isNaN(num) || num < 1) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        // ── المرحلة 1: اختيار أنمي من نتائج البحث ──
                        if (cachedData.stage === 'search') {
                            const selected = cachedData.results[num - 1];
                            if (!selected) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                                return;
                            }
                            animeCache.delete(quotedId);

                            // ok.ru → استخراج الجودات مباشرة (المنطق السابق)
                            if (selected.source === 'okru') {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري استخراج الجودات لـ\n*${selected.title}*...`
                                }, { quoted: mek });
                                try {
                                    const { title, videos } = await extractOkruVideo(`https://ok.ru/video/${selected.id}`);
                                    const links = videos.map(v => v.url);
                                    const names = videos.map(v => OKRU_QUALITY_LABELS[v.name] || v.name || 'غير معروفة');
                                    let qualityResponseText = `🍿 *اختر جودة التحميل:*\n🎬 ${title}\n\n`;
                                    names.forEach((qName, i) => {
                                        qualityResponseText += `*${i + 1}* - ${qName}\n`;
                                    });
                                    qualityResponseText += `\n💡 قم **بالرد (Reply)** على هذه الرسالة برقم الجودة المطلوبة.`;
                                    const sentQualityMsg = await XeonBotInc.sendMessage(chatId, { text: qualityResponseText }, { quoted: mek });
                                    qualityCache.set(sentQualityMsg.key.id, {
                                        links, names, title,
                                        referer: 'https://ok.ru/',
                                        headers: {},
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQualityMsg.key.id), 300000);
                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ ${err.message}`
                                    }, { quoted: mek });
                                }
                                return;
                            }

                            // EgyAflam → نتائج البحث حلقات منفردة، الجودات مباشرة (مثل ok.ru)
                            if (selected.source === 'egyaflam') {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري استخراج الجودات لـ\n*${selected.title}*...`
                                }, { quoted: mek });
                                try {
                                    const links = await egyaflamEpisodeLinks(selected.id);
                                    if (!links.length) throw new Error('لا توجد روابط تحميل متاحة.');
                                    let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${selected.title}\n\n`;
                                    links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                    qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                                    const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                    qualityCache.set(sentQ.key.id, {
                                        links: links.map(r => r.url),
                                        names: links.map(r => r.label),
                                        title: selected.title,
                                        referer: (links[0] && links[0].referer) || '',
                                        headers: {},
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ ${err.message}`
                                    }, { quoted: mek });
                                }
                                return;
                            }

                            // CloudDay / AnimeRift → جلب الحلقات
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب حلقات *${selected.title}*...`
                            }, { quoted: mek });
                            try {
                                // الفيلم في CloudDay: السيرفرات مباشرة بدون حلقات
                                if (selected.source === 'cloudday' && selected.type === 'movie') {
                                    const base = await cloudDayResolveBase(CLOUDDAY_SOURCES.find(s => s.name === selected.cdSource));
                                    const links = await cloudDayServers(base, 'movie', selected.id);
                                    const resolved = await cloudDayResolveLinks(links);
                                    if (!resolved.length) throw new Error('لا توجد روابط تحميل متاحة لهذا الفيلم.');
                                    let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${selected.title}\n\n`;
                                    resolved.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                    qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                                    const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                    qualityCache.set(sentQ.key.id, {
                                        links: resolved.map(r => r.url),
                                        names: resolved.map(r => r.label),
                                        title: selected.title,
                                        referer: '', headers: {},
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                    return;
                                }

                                let episodes = [];
                                if (selected.source === 'cloudday') {
                                    const base = await cloudDayResolveBase(CLOUDDAY_SOURCES.find(s => s.name === selected.cdSource));
                                    episodes = await cloudDayEpisodes(base, selected.id);
                                } else if (selected.source === 'rift') {
                                    episodes = await riftEpisodes(selected.id);
                                } else if (selected.source === 'witcher') {
                                    episodes = await witcherEpisodes(selected.id);
                                } else if (selected.source === 'shahiid') {
                                    episodes = await shahiidEpisodes(selected.id);
                                } else if (selected.source === 'anime4up') {
                                    episodes = await anime4upEpisodes(selected.id);
                                } else if (selected.source === 'animedar') {
                                    episodes = await animedarEpisodes(selected.id);
                                } else if (selected.source === 'kartoney') {
                                    episodes = await kartoneyEpisodes(selected.id);
                                } else if (selected.source === 'animerco') {
                                    episodes = await animercoEpisodes(selected.id);
                                } else if (selected.source === 'hianime') {
                                    episodes = await hianimeEpisodes(selected.id);
                                } else if (selected.source === 'arabanime') {
                                    episodes = await arabanimeEpisodes(selected.id);
                                } else if (selected.source === 'animezid') {
                                    episodes = await animezidEpisodes(selected.id);
                                } else if (selected.source === 'okanime') {
                                    episodes = await okanimeEpisodes(selected.id);
                                }
                                if (!episodes.length) throw new Error('لا توجد حلقات.');
                                let epText = `📺 *${selected.title}*\n🔢 عدد الحلقات: ${episodes.length}\n\n`;
                                episodes.slice(0, 10).forEach(e => {
                                    epText += `*${e.number}* - ${e.title || ('الحلقة ' + e.number)}\n`;
                                });
                                if (episodes.length > 10) epText += `…\n`;
                                epText += `\n💡 رد (Reply) على هذه الرسالة برقم الحلقة، أو بمدى مثل 1-15 لتحميل عدة حلقات دفعة واحدة.`;
                                const sentEp = await XeonBotInc.sendMessage(chatId, { text: epText }, { quoted: mek });
                                animeCache.set(sentEp.key.id, {
                                    stage: 'episodes', source: selected.source, cdSource: selected.cdSource,
                                    animeId: selected.id, title: selected.title, episodes,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => animeCache.delete(sentEp.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل جلب الحلقات:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // ── المرحلة 2: اختيار الحلقة (أو مدى حلقات مثل 1-15) ──
                        if (cachedData.stage === 'episodes') {
                            // ── تحميل مدى حلقات ──
                            const rangeMatch = String(replyText).trim().match(/^(\d+)\s*-\s*(\d+)$/);
                            if (rangeMatch) {
                                const start = parseInt(rangeMatch[1], 10);
                                const end = parseInt(rangeMatch[2], 10);
                                const total = cachedData.episodes.length;
                                if (start < 1 || end < start || end > total || (end - start + 1) > 20) {
                                    await XeonBotInc.sendMessage(chatId, { text: `❌ مدى غير صحيح. اكتب مدى مثل 1-15 (بحد أقصى 20 حلقة، والأنمي فيه ${total} حلقة).` }, { quoted: mek });
                                    return;
                                }
                                const wanted = cachedData.episodes.filter(e => e.number >= start && e.number <= end).sort((a, b) => a.number - b.number);
                                if (!wanted.length) {
                                    await XeonBotInc.sendMessage(chatId, { text: '❌ لا توجد حلقات في هذا المدى.' }, { quoted: mek });
                                    return;
                                }
                                animeCache.delete(quotedId);
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري جلب سيرفرات الحلقات ${start}-${end} (${wanted.length} حلقة)...`
                                }, { quoted: mek });
                                try {
                                    const batch = [];
                                    const failedNums = [];
                                    for (const ep of wanted) {
                                        try {
                                            const resolved = await resolveAnimeEpisodeLinks(cachedData.source, cachedData.cdSource, cachedData.animeId, ep);
                                            if (resolved.length) batch.push({ number: ep.number, links: resolved, referer: (resolved[0] && resolved[0].referer) || '' });
                                            else failedNums.push(ep.number);
                                        } catch (_) { failedNums.push(ep.number); }
                                    }
                                    if (!batch.length) throw new Error('لا توجد روابط تحميل متاحة لأي حلقة في هذا المدى.');
                                    let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.title} — الحلقات ${start}-${end} (${batch.length} حلقة جاهزة${failedNums.length ? `، فشلت: ${failedNums.join('، ')}` : ''})\n\n`;
                                    batch[0].links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                    qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة، وسيتم تحميل كل الحلقات بنفس الجودة.`;
                                    const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                    qualityCache.set(sentQ.key.id, {
                                        links: batch[0].links.map(r => r.url),
                                        names: batch[0].links.map(r => r.label),
                                        title: `${cachedData.title} - الحلقات ${start}-${end}`,
                                        referer: batch[0].referer, headers: {},
                                        batch: batch.map(b => ({ number: b.number, links: b.links, referer: b.referer })),
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل جلب السيرفرات:\n\`${err.message}\``
                                    }, { quoted: mek });
                                }
                                return;
                            }
                            const ep = cachedData.episodes.find(e => e.number === num);
                            if (!ep) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم حلقة غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            animeCache.delete(quotedId);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب سيرفرات الحلقة ${ep.number}...`
                            }, { quoted: mek });
                            try {
                                const resolved = await resolveAnimeEpisodeLinks(cachedData.source, cachedData.cdSource, cachedData.animeId, ep);
                                if (!resolved.length) throw new Error('لا توجد روابط تحميل متاحة لهذه الحلقة.');
                                let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.title} — الحلقة ${ep.number}\n\n`;
                                resolved.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                                const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                qualityCache.set(sentQ.key.id, {
                                    links: resolved.map(r => r.url),
                                    names: resolved.map(r => r.label),
                                    title: `${cachedData.title} - الحلقة ${ep.number}`,
                                    referer: (resolved[0] && resolved[0].referer) || '', headers: {},
                                    timestamp: Date.now()
                                });
                                setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل جلب السيرفرات:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }
                    }

                    // ── اختيار كرتون/حلقة من نتائج .cartoon (متعدد المصادر) ──
                    if (cartoonCache.has(quotedId)) {
                        const cachedData = cartoonCache.get(quotedId);
                        const num = parseInt(String(replyText).trim());
                        if (isNaN(num) || num < 1) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        // ── المرحلة 1: اختيار كرتون من نتائج البحث ──
                        if (cachedData.stage === 'search') {
                            const selected = cachedData.results[num - 1];
                            if (!selected) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                                return;
                            }
                            cartoonCache.delete(quotedId);

                            // ok.ru → استخراج الجودات مباشرة
                            if (selected.source === 'okru') {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري استخراج الجودات لـ\n*${selected.title}*...`
                                }, { quoted: mek });
                                try {
                                    const { title, videos } = await extractOkruVideo(`https://ok.ru/video/${selected.id}`);
                                    const links = videos.map(v => v.url);
                                    const names = videos.map(v => OKRU_QUALITY_LABELS[v.name] || v.name || 'غير معروفة');
                                    let qualityResponseText = `🍿 *اختر جودة التحميل:*\n🎬 ${title}\n\n`;
                                    names.forEach((qName, i) => {
                                        qualityResponseText += `*${i + 1}* - ${qName}\n`;
                                    });
                                    qualityResponseText += `\n💡 قم **بالرد (Reply)** على هذه الرسالة برقم الجودة المطلوبة.`;
                                    const sentQualityMsg = await XeonBotInc.sendMessage(chatId, { text: qualityResponseText }, { quoted: mek });
                                    qualityCache.set(sentQualityMsg.key.id, {
                                        links, names, title,
                                        referer: 'https://ok.ru/',
                                        headers: {},
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQualityMsg.key.id), 300000);
                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ ${err.message}`
                                    }, { quoted: mek });
                                }
                                return;
                            }

                            // باقي المصادر → جلب الحلقات
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب حلقات *${selected.title}*...`
                            }, { quoted: mek });
                            try {
                                let episodes = [];
                                if (selected.source === 'cartoondub') {
                                    episodes = await cartoonDubEpisodes(selected.id);
                                } else if (selected.source === 'carateen') {
                                    episodes = await carateenEpisodes(selected);
                                } else if (selected.source === 'kartoney') {
                                    episodes = await kartoneyEpisodes(selected.id);
                                } else if (selected.source === 'dimakids') {
                                    episodes = await dimaEpisodes(selected);
                                } else if (selected.source === 'animezid') {
                                    episodes = await animezidEpisodes(selected.id);
                                } else if (selected.source === 'stardima') {
                                    episodes = await stardimaEpisodes(selected.id);
                                }
                                if (!episodes.length) throw new Error('لا توجد حلقات.');
                                let epText = `📺 *${selected.title}*\n🔢 عدد الحلقات: ${episodes.length}\n\n`;
                                episodes.slice(0, 10).forEach(e => {
                                    epText += `*${e.number}* - ${e.title || ('الحلقة ' + e.number)}\n`;
                                });
                                if (episodes.length > 10) epText += `…\n`;
                                epText += `\n💡 رد (Reply) على هذه الرسالة برقم الحلقة، أو بمدى مثل 1-15 لتحميل عدة حلقات دفعة واحدة.`;
                                const sentEp = await XeonBotInc.sendMessage(chatId, { text: epText }, { quoted: mek });
                                cartoonCache.set(sentEp.key.id, {
                                    stage: 'episodes', source: selected.source, cdSource: null,
                                    cartoonId: selected.id, kind: selected.kind || null, title: selected.title, episodes,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => cartoonCache.delete(sentEp.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل جلب الحلقات:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // ── المرحلة 2: اختيار الحلقة (أو مدى حلقات مثل 1-15) ──
                        if (cachedData.stage === 'episodes') {
                            // ── تحميل مدى حلقات ──
                            const rangeMatch = String(replyText).trim().match(/^(\d+)\s*-\s*(\d+)$/);
                            if (rangeMatch) {
                                const start = parseInt(rangeMatch[1], 10);
                                const end = parseInt(rangeMatch[2], 10);
                                const total = cachedData.episodes.length;
                                if (start < 1 || end < start || end > total || (end - start + 1) > 20) {
                                    await XeonBotInc.sendMessage(chatId, { text: `❌ مدى غير صحيح. اكتب مدى مثل 1-15 (بحد أقصى 20 حلقة، والكرتون فيه ${total} حلقة).` }, { quoted: mek });
                                    return;
                                }
                                const wanted = cachedData.episodes.filter(e => e.number >= start && e.number <= end).sort((a, b) => a.number - b.number);
                                if (!wanted.length) {
                                    await XeonBotInc.sendMessage(chatId, { text: '❌ لا توجد حلقات في هذا المدى.' }, { quoted: mek });
                                    return;
                                }
                                cartoonCache.delete(quotedId);
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري جلب سيرفرات الحلقات ${start}-${end} (${wanted.length} حلقة)...`
                                }, { quoted: mek });
                                try {
                                    const batch = [];
                                    const failedNums = [];
                                    for (const ep of wanted) {
                                        try {
                                            const resolved = await resolveAnimeEpisodeLinks(cachedData.source, cachedData.cdSource, cachedData.cartoonId, ep);
                                            if (resolved.length) batch.push({ number: ep.number, links: resolved, referer: (resolved[0] && resolved[0].referer) || '' });
                                            else failedNums.push(ep.number);
                                        } catch (_) { failedNums.push(ep.number); }
                                    }
                                    if (!batch.length) throw new Error('لا توجد روابط تحميل متاحة لأي حلقة في هذا المدى.');
                                    let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.title} — الحلقات ${start}-${end} (${batch.length} حلقة جاهزة${failedNums.length ? `، فشلت: ${failedNums.join('، ')}` : ''})\n\n`;
                                    batch[0].links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                    qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة، وسيتم تحميل كل الحلقات بنفس الجودة.`;
                                    const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                    qualityCache.set(sentQ.key.id, {
                                        links: batch[0].links.map(r => r.url),
                                        names: batch[0].links.map(r => r.label),
                                        title: `${cachedData.title} - الحلقات ${start}-${end}`,
                                        referer: batch[0].referer, headers: {},
                                        batch: batch.map(b => ({ number: b.number, links: b.links, referer: b.referer })),
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل جلب السيرفرات:\n\`${err.message}\``
                                    }, { quoted: mek });
                                }
                                return;
                            }
                            const ep = cachedData.episodes.find(e => e.number === num);
                            if (!ep) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم حلقة غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            cartoonCache.delete(quotedId);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب سيرفرات الحلقة ${ep.number}...`
                            }, { quoted: mek });
                            try {
                                const resolved = await resolveAnimeEpisodeLinks(cachedData.source, cachedData.cdSource, cachedData.cartoonId, ep);
                                if (!resolved.length) throw new Error('لا توجد روابط تحميل متاحة لهذه الحلقة.');
                                let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.title} — الحلقة ${ep.number}\n\n`;
                                resolved.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                                const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                qualityCache.set(sentQ.key.id, {
                                    links: resolved.map(r => r.url),
                                    names: resolved.map(r => r.label),
                                    title: `${cachedData.title} - الحلقة ${ep.number}`,
                                    referer: (resolved[0] && resolved[0].referer) || '', headers: {},
                                    timestamp: Date.now()
                                });
                                setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل جلب السيرفرات:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }
                    }

                    // ── اختيار شورت من نتائج .cartoon-en (مصادر إنجليزية — مباشرة للجودات) ──
                    if (cartoonEnCache.has(quotedId)) {
                        const cachedData = cartoonEnCache.get(quotedId);
                        const replyTrim = String(replyText).trim();
                        // ── تحميل مدى شورتات مثل 1-15 ──
                        const rangeMatch = replyTrim.match(/^(\d+)\s*-\s*(\d+)$/);
                        if (rangeMatch) {
                            const start = parseInt(rangeMatch[1], 10);
                            const end = parseInt(rangeMatch[2], 10);
                            const total = cachedData.results.length;
                            if (start < 1 || end < start || end > total || (end - start + 1) > 20) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ مدى غير صحيح. اكتب مدى مثل 1-15 (بحد أقصى 20، والقائمة فيها ${total}).` }, { quoted: mek });
                                return;
                            }
                            const wanted = cachedData.results.slice(start - 1, end);
                            cartoonEnCache.delete(quotedId);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب روابط الشورتات ${start}-${end} (${wanted.length} شورت)...`
                            }, { quoted: mek });
                            try {
                                const batch = [];
                                const failedNums = [];
                                for (let i = 0; i < wanted.length; i++) {
                                    const item = wanted[i];
                                    try {
                                        const resolved = await cartoonEnResolveLinks(item.source, item);
                                        if (resolved.length) batch.push({ number: start + i, links: resolved, referer: (resolved[0] && resolved[0].referer) || '' });
                                        else failedNums.push(start + i);
                                    } catch (_) { failedNums.push(start + i); }
                                }
                                if (!batch.length) throw new Error('لا توجد روابط تحميل متاحة لأي شورت في هذا المدى.');
                                let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.query} — الشورتات ${start}-${end} (${batch.length} جاهز${failedNums.length ? `، فشل: ${failedNums.join('، ')}` : ''})\n\n`;
                                batch[0].links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة، وسيتم تحميل كل الشورتات بنفس الجودة.`;
                                const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                qualityCache.set(sentQ.key.id, {
                                    links: batch[0].links.map(r => r.url),
                                    names: batch[0].links.map(r => r.label),
                                    title: `${cachedData.query} - الشورتات ${start}-${end}`,
                                    referer: batch[0].referer, headers: {},
                                    batch: batch.map(b => ({ number: b.number, links: b.links, referer: b.referer })),
                                    timestamp: Date.now()
                                });
                                setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل جلب الروابط:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }
                        const num = parseInt(replyTrim);
                        if (isNaN(num) || num < 1) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }
                        const selected = cachedData.results[num - 1];
                        if (!selected) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }
                        cartoonEnCache.delete(quotedId);
                        await XeonBotInc.sendMessage(chatId, {
                            text: `⏳ جاري استخراج رابط *${selected.title}*...`
                        }, { quoted: mek });
                        try {
                            const resolved = await cartoonEnResolveLinks(selected.source, selected);
                            if (!resolved.length) throw new Error('لا توجد روابط تحميل متاحة.');
                            let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${selected.title}\n\n`;
                            resolved.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                            qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                            const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                            qualityCache.set(sentQ.key.id, {
                                links: resolved.map(r => r.url),
                                names: resolved.map(r => r.label),
                                title: selected.title,
                                referer: (resolved[0] && resolved[0].referer) || '', headers: {},
                                timestamp: Date.now()
                            });
                            setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استخراج الرابط:\n\`${err.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── اختيار فيلم/مسلسل/حلقة من نتائج .movie / .series (متعدد المصادر) ──
                    if (mvCache.has(quotedId)) {
                        const cachedData = mvCache.get(quotedId);
                        const num = parseInt(String(replyText).trim());
                        if (isNaN(num) || num < 1) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        // ── المرحلة 1: اختيار فيلم/مسلسل من نتائج البحث ──
                        if (cachedData.stage === 'search') {
                            const selected = cachedData.results[num - 1];
                            if (!selected) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                                return;
                            }
                            mvCache.delete(quotedId);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب ${selected.type === 'movie' ? 'سيرفرات' : 'حلقات'} *${selected.title}*...`
                            }, { quoted: mek });
                            try {
                                // فيلم مباشر (أو فيديو واحد) → الجودات مباشرة
                                const direct = async () => {
                                    const resolved = await resolveMvMovieLinks(selected.source, selected.cdSource, selected.id);
                                    if (!resolved.links.length) throw new Error('لا توجد روابط تحميل متاحة.');
                                    let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${selected.title}\n\n`;
                                    resolved.links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                    qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                                    const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                    qualityCache.set(sentQ.key.id, {
                                        links: resolved.links.map(r => r.url),
                                        names: resolved.links.map(r => r.label),
                                        title: selected.title,
                                        referer: (resolved.links[0] && resolved.links[0].referer) || '',
                                        headers: selected.source === 'meowtv' ? { 'Origin': 'https://meowtv.ru' } : {},
                                        subtitleUrl: resolved.subtitleUrl || null,
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                };

                                // مسلسل → قائمة الحلقات
                                const showEpisodes = async (episodes) => {
                                    if (!episodes.length) throw new Error('لا توجد حلقات.');
                                    let epText = `📺 *${selected.title}*\n🔢 عدد الحلقات: ${episodes.length}\n\n`;
                                    episodes.slice(0, 10).forEach(e => {
                                        epText += `*${e.number}* - ${e.title || ('الحلقة ' + e.number)}\n`;
                                    });
                                    if (episodes.length > 10) epText += `…\n`;
                                    epText += `\n💡 رد (Reply) على هذه الرسالة برقم الحلقة، أو بمدى مثل 1-15 لتحميل عدة حلقات دفعة واحدة.`;
                                    const sentEp = await XeonBotInc.sendMessage(chatId, { text: epText }, { quoted: mek });
                                    mvCache.set(sentEp.key.id, {
                                        stage: 'episodes', source: selected.source, cdSource: selected.cdSource,
                                        mvId: selected.id, title: selected.title, episodes,
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => mvCache.delete(sentEp.key.id), 300000);
                                };

                                if (selected.source === 'akwam') {
                                    if (String(selected.id).includes('/movie/')) await direct();
                                    else {
                                        const html = await akwamFetch(selected.id);
                                        await showEpisodes(extractAkwamEpisodes(html).map((u, i) => ({ id: u, number: i + 1, title: u.replace(/.*\/episode\//, '').replace(/-/g, ' ').replace(/\/$/, '') })));
                                    }
                                } else if (selected.source === 'cloudday') {
                                    if (selected.type === 'movie') await direct();
                                    else {
                                        const base = await cloudDayResolveBase(CLOUDDAY_SOURCES.find(s => s.name === selected.cdSource));
                                        await showEpisodes(await cloudDayEpisodes(base, selected.id));
                                    }
                                } else if (selected.source === 'meowtv') {
                                    if (selected.type === 'movie') await direct();
                                    else await showEpisodes(await meowEpisodes(selected.id));
                                } else if (selected.source === 'cinemaplus') {
                                    const page = await cinemaPlusPage(selected.id);
                                    if (page.isSeries) await showEpisodes(await cinemaPlusEpisodes(selected.id));
                                    else await direct();
                                } else if (selected.source === 'viola') {
                                    const eps = await violaEpisodes(selected.id);
                                    if (eps.length) await showEpisodes(eps);
                                    else await direct();
                                } else if (selected.source === 'egywatch') {
                                    await showEpisodes(await egywatchEpisodes(selected.id));
                                } else if (selected.source === 'dramaworld') {
                                    await showEpisodes(await dramaWorldEpisodes(selected.id));
                                } else if (selected.source === 'lodynet') {
                                    await showEpisodes(await lodynetEpisodes(selected.id));
                                } else if (selected.source === 'okru') {
                                    await direct();
                                } else if (selected.source === 'myseed') {
                                    await direct(); // بحث MySeed يرجع صفحات أفلام/حلقات جاهزة مباشرة (بلا قائمة حلقات)
                                } else {
                                    throw new Error('مصدر غير معروف.');
                                }
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل الجلب:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // ── المرحلة 2: اختيار الحلقة (أو مدى حلقات مثل 1-15) ──
                        if (cachedData.stage === 'episodes') {
                            // ── تحميل مدى حلقات ──
                            const rangeMatch = String(replyText).trim().match(/^(\d+)\s*-\s*(\d+)$/);
                            if (rangeMatch) {
                                const start = parseInt(rangeMatch[1], 10);
                                const end = parseInt(rangeMatch[2], 10);
                                const total = cachedData.episodes.length;
                                if (start < 1 || end < start || end > total || (end - start + 1) > 20) {
                                    await XeonBotInc.sendMessage(chatId, { text: `❌ مدى غير صحيح. اكتب مدى مثل 1-15 (بحد أقصى 20 حلقة، والمسلسل فيه ${total} حلقة).` }, { quoted: mek });
                                    return;
                                }
                                const wanted = cachedData.episodes.filter(e => e.number >= start && e.number <= end).sort((a, b) => a.number - b.number);
                                if (!wanted.length) {
                                    await XeonBotInc.sendMessage(chatId, { text: '❌ لا توجد حلقات في هذا المدى.' }, { quoted: mek });
                                    return;
                                }
                                mvCache.delete(quotedId);
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري جلب سيرفرات الحلقات ${start}-${end} (${wanted.length} حلقة)...`
                                }, { quoted: mek });
                                try {
                                    const batch = [];
                                    const failedNums = [];
                                    for (const ep of wanted) {
                                        try {
                                            const resolved = await resolveMvEpisodeLinks(cachedData.source, cachedData.cdSource, cachedData.mvId, ep);
                                            if (resolved.links.length) batch.push({ number: ep.number, links: resolved.links, referer: (resolved.links[0] && resolved.links[0].referer) || '', subtitleUrl: resolved.subtitleUrl || null });
                                            else failedNums.push(ep.number);
                                        } catch (_) { failedNums.push(ep.number); }
                                    }
                                    if (!batch.length) throw new Error('لا توجد روابط تحميل متاحة لأي حلقة في هذا المدى.');
                                    let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.title} — الحلقات ${start}-${end} (${batch.length} حلقة جاهزة${failedNums.length ? `، فشلت: ${failedNums.join('، ')}` : ''})\n\n`;
                                    batch[0].links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                    qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة، وسيتم تحميل كل الحلقات بنفس الجودة.`;
                                    const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                    qualityCache.set(sentQ.key.id, {
                                        links: batch[0].links.map(r => r.url),
                                        names: batch[0].links.map(r => r.label),
                                        title: `${cachedData.title} - الحلقات ${start}-${end}`,
                                        referer: batch[0].referer,
                                        headers: cachedData.source === 'meowtv' ? { 'Origin': 'https://meowtv.ru' } : {},
                                        batch: batch.map(b => ({ number: b.number, links: b.links, referer: b.referer, subtitleUrl: b.subtitleUrl })),
                                        timestamp: Date.now()
                                    });
                                    setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل جلب السيرفرات:\n\`${err.message}\``
                                    }, { quoted: mek });
                                }
                                return;
                            }
                            const ep = cachedData.episodes.find(e => e.number === num);
                            if (!ep) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم حلقة غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            mvCache.delete(quotedId);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب سيرفرات الحلقة ${ep.number}...`
                            }, { quoted: mek });
                            try {
                                const resolved = await resolveMvEpisodeLinks(cachedData.source, cachedData.cdSource, cachedData.mvId, ep);
                                if (!resolved.links.length) throw new Error('لا توجد روابط تحميل متاحة لهذه الحلقة.');
                                let qText = `🍿 *اختر جودة التحميل:*\n🎬 ${cachedData.title} — الحلقة ${ep.number}\n\n`;
                                resolved.links.forEach((r, i) => { qText += `*${i + 1}* - ${r.label}\n`; });
                                qText += `\n💡 رد (Reply) على هذه الرسالة برقم الجودة.`;
                                const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                qualityCache.set(sentQ.key.id, {
                                    links: resolved.links.map(r => r.url),
                                    names: resolved.links.map(r => r.label),
                                    title: `${cachedData.title} - الحلقة ${ep.number}`,
                                    referer: (resolved.links[0] && resolved.links[0].referer) || '',
                                    headers: cachedData.source === 'meowtv' ? { 'Origin': 'https://meowtv.ru' } : {},
                                    subtitleUrl: resolved.subtitleUrl || null,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل جلب السيرفرات:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }
                    }
                }

                // ============================================================
                // الأوامر الرئيسية
                // ============================================================
                if (text && (
                    text.startsWith('.help') ||
                    text.startsWith('.ping') ||
                    text.startsWith('.download') ||
                    text.startsWith('.ytdl') ||
                    text.startsWith('.ytlive') ||
                    text.startsWith('.ytsearch') ||
                    text.startsWith('.yts') ||
                    text.startsWith('.$') ||
                    text.startsWith('.sh') ||
                    text.startsWith('.killcmd') ||
                    text.startsWith('.cwd') ||
                    text.startsWith('.ytgo') ||
                    text.startsWith('.ytno') ||
                    text.startsWith('.stopytdl') ||
                    text.startsWith('.batchdl') ||
                    text.startsWith('.apk') ||
                    text.startsWith('.anime') ||
                    text.startsWith('.football') ||
                    text.startsWith('.setanime') ||
                    text.startsWith('.animeset') ||
                    text.startsWith('.cartoon') ||
                    text.startsWith('.setcartoon') ||
                    text.startsWith('.cartoonapi') ||
                    text.startsWith('.cartoon-en') ||
                    text.startsWith('.catoon-en') ||
                    text.startsWith('.setcartoon-en') ||
                    text.startsWith('.cartoon-enapi') ||
                    text.startsWith('.kdrama') ||
                    text.startsWith('.setkdrama') ||
                    text.startsWith('.kdramaapi') ||
                    text.startsWith('.series') ||
                    text.startsWith('.manga') ||
                    text.startsWith('.movie') ||
                    text.startsWith('.setmv') ||
                    text.startsWith('.mvapi') ||
                    text.startsWith('.test') ||
                    text.startsWith('.seturl') ||
                    text.startsWith('.channels') ||
                    text.startsWith('.iptv') ||
                    text.startsWith('.recordiptv') ||
                    text.startsWith('.stoprecordiptv') ||
                    text.startsWith('.livefootball') ||
                    text.startsWith('.livechannel') ||
                    text.startsWith('.stoplivechannel') ||
                    text.startsWith('.stoplivefootball') ||
                    text.startsWith('.tflix') ||
                    text.startsWith('.stoptflix') ||
                    text.startsWith('.settflix') ||
                    text.startsWith('.m3u') ||
                    text.startsWith('.record') ||
                    text.startsWith('.stoprecord') ||
                    text.startsWith('.okru') ||
                    text.startsWith('.playm3u') ||
                    text.startsWith('.stopplaym3u') ||
                    text.startsWith('.setm3u') ||
                    text.startsWith('.m3usource') ||
                    text.startsWith('.remotedl') ||
                    text.startsWith('.stopremotedl') ||
                    text.startsWith('.setremotedl') ||
                    text.startsWith('.cleanremote')
                )) {
                    const args = text.split(' ');
                    const command = args[0].toLowerCase();
                    let query = args.slice(1).join(' ').trim();

                    // ── أمر .ping ──
                    if (command === '.ping') {
                        const t0 = Date.now();
                        await XeonBotInc.sendMessage(chatId, { text: `🏓 Pong!\n⏱️ ${Date.now() - t0}ms` }, { quoted: mek });
                        return;
                    }

                    // ── أمر .help — عرض كل أوامر البوت مع الشرح ──
                    if (command === '.help') {
                        await XeonBotInc.sendMessage(chatId, { text: `🤖 *بوت صادق — كل الأوامر*

✨ *ازاي تستخدم البوت؟ (4 خطوات)*
1️⃣ اكتب أمر بحث — مثال: \`.anime ناروتو\`
2️⃣ البوت هيبعتلك قائمة مرقّمة — *رد (Reply)* على رسالته برقم اللي عايزه
3️⃣ لو أنمي/مسلسل: رد برقم الحلقة، أو بمدى زي \`1-15\` لتحميل كذا حلقة مرة واحدة
4️⃣ رد برقم الجودة اللي عايزها — والبوت هيحمّل ويبعتلك الفيديو
⏰ *مهم:* الرد لازم يكون خلال *5 دقايق* من رسالة البوت، وإلا عيد البحث من الأول

🎬 *أنمي — عربي ومترجم (15 مصدر)*
• \`.anime <اسم>\` — ابحث وحمّل أي أنمي
  ↳ مثال: \`.anime ناروتو\` أو \`.anime Naruto\`
• \`.setanime <مصدر>\` — ثبّت مصدر واحد يبحث فيه بس، وبدّله لما يقع
  ↳ مثال: \`.setanime okru\` — وارجع للكل بـ \`.setanime all\`
• \`.animeapi\` — شوف حالة مصادر الأنمي (شغال ولا واقع)

📺 *كرتون مدبلج عربي (7 مصادر)*
• \`.cartoon <اسم>\` — ابحث وحمّل كرتون مدبلج
  ↳ مثال: \`.cartoon بن تن\` أو \`.cartoon سيف النار\`
• \`.setcartoon <مصدر>\` — ثبّت مصدر واحد للكرتون
  ↳ مثال: \`.setcartoon stardima\` — وارجع للكل بـ \`.setcartoon all\`
• \`.cartoonapi\` — شوف حالة مصادر الكرتون

🌍 *كرتون إنجليزي (4 مصادر)*
• \`.cartoon-en <اسم>\` — كرتون إنجليزي كلاسيكي
  ↳ مثال: \`.cartoon-en Tom and Jerry\` أو \`.cartoon-en Ben 10\`
• \`.setcartoon-en <مصدر>\` — ثبّت مصدر واحد للكرتون الإنجليزي
• \`.cartoon-enapi\` — شوف حالة مصادر الكرتون الإنجليزي

🇰🇷 *دراما كورية (6 مصادر)*
• \`.kdrama <اسم>\` — مسلسلات كورية مدبلجة/مترجمة
  ↳ مثال: \`.kdrama لعبة الحبار\` أو \`.kdrama squid game\`
• \`.setkdrama <مصدر>\` — ثبّت مصدر واحد للدراما
• \`.kdramaapi\` — شوف حالة مصادر الدراما

🎥 *أفلام ومسلسلات (8 مصادر)*
• \`.movie <اسم>\` — ابحث وحمّل فيلم مترجم
  ↳ مثال: \`.movie breaking bad\`
• \`.series <اسم>\` — ابحث وحمّل مسلسل (حلقات + مدى حلقات)
  ↳ مثال: \`.series breaking bad\`
• \`.setmv <مصدر>\` — ثبّت مصدر واحد للأفلام والمسلسلات
• \`.mvapi\` — شوف حالة مصادر الأفلام والمسلسلات

⚽ *كورة — إعادة مباريات*
• \`.football recent\` — مباريات اليوم من كل الدوريات (من غير حرق)
  ↳ مثال: \`.football recent\` — رد برقم المباراة لعرض الجودات والحجم قبل التحميل
• \`.football <فريق>\` — ابحث عن مباريات فريق من آخر 14 يوم (مثال: \`.football liverpool\`)
  ↳ لو الحجم فوق 2GB البوت هيطبع لك الرابط والحجم، وتمرّره بنفسك لـ \`.remotedl\` مع حجم الجزء اللي تختاره

📖 *مانجا وفيديو*
• \`.manga <اسم>\` — ابحث وحمّل مانجا (رد برقم الفصل، أو بمدى زي \`1 5\`)
  ↳ مثال: \`.manga naruto\` أو \`.manga بلاك كلوفر\`
• \`.okru <رابط>\` — حمّل فيديو من ok.ru
  ↳ مثال: \`.okru https://ok.ru/video/123456789\`
• \`.m3u8 <رابط>\` — حمّل فيديو من رابط m3u8/HLS (بأجزاء إن كان كبيراً)
  ↳ مثال: \`.m3u8 https://example.com/playlist.m3u8\`

⬇️ *تحميل*
• \`.download <رابط>\` — تحميل مباشر (يدعم Google Drive)
  ↳ مثال: \`.download <رابط الفيديو المباشر>\`
• \`.batchdl\` — حمّل عدة روابط مرة واحدة: أرفق ملف txt (رابط في كل سطر) واكتب \`.batchdl\` كتعليق عليه
• \`.remotedl <رابط> [حجم الجزء]\` — تحميل عن بُعد عبر GitHub Actions (للملفات الكبيرة)
• \`.setremotedl <owner/repo> <توكن>\` — ضبط مستودع ورمز التحميل عن بُعد
• \`.stopremotedl\` — إلغاء تحميل عن بُعد شغال
• \`.cleanremote\` — حذف إصدارات التحميل عن بُعد من GitHub

▶️ *يوتيوب*
• \`.ytdl <رابط> [جودة]\` — حمّل فيديو يوتيوب (الجودة: audio أو 360/480/720/1080)
  ↳ مثال: \`.ytdl https://youtu.be/xxxx 480\`
• \`.ytlive <رابط> [دقائق] [جودة]\` — سجّل بث مباشر من يوتيوب (مقاطع متواصلة)
  ↳ مثال: \`.ytlive https://youtube.com/watch?v=xxxx 120 480\`
• \`.ytsearch [عدد] <كلمات>\` — ابحث في يوتيوب من غير تحميل
  ↳ مثال: \`.ytsearch 8 شرح البرمجة بايثون\`
• \`.ytgo\` — تأكيد التحميل / بدء التسجيل بعد ما البوت يسألك
• \`.ytno\` — إلغاء الطلب
• \`.stopytdl\` — إيقاف تحميل أو تسجيل يوتيوب شغال

📺 *قنوات IPTV*
• \`.setm3u <رابط>\` — عيّن قائمة M3U الخاصة بيك
  ↳ مثال: \`.setm3u https://example.com/playlist.m3u\`
• \`.m3usource\` — اعرض قنوات مصدر M3U الحالي
• \`.seturl <رابط>\` — حدّث رابط M3U بعد التجديد
• \`.channels <اسم>\` — ابحث عن قناة في قائمتك (وهات الـ ID بتاعها)
  ↳ مثال: \`.channels الجزيرة\`
• \`.iptv <اسم>\` — ابحث في قائمة iptv-org الثابتة
• \`.test\` — اختبر سيرفر IPTV شغال ولا لأ
• \`.playm3u <رابط> [المدة]\` — شغّل قناة من رابط m3u/m3u8
  ↳ مثال: \`.playm3u https://example.com/stream.m3u8 60\`
• \`.stopplaym3u\` — إيقاف التشغيل
• \`.record <ID> [دقائق]\` — سجّل قناة من قائمتك (مقاطع متواصلة)
  ↳ مثال: \`.record 1234 120\` — هات الـ ID من \`.channels\`
• \`.stoprecord\` — إيقاف التسجيل
• \`.recordiptv <ID> [دقائق]\` — سجّل من قائمة iptv-org
  ↳ مثال: \`.recordiptv 1234 120\` — هات الـ ID من \`.iptv\`
• \`.stoprecordiptv\` — إيقاف تسجيل IPTV
• \`.livefootball\` — مباريات مباشرة/قادمة من مصادر البث الرياضي (DaddyLive, DamiTV, PPV.ST...)
  ↳ \`.livefootball <فريق>\` للبحث، ثم \`.livefootball <رقم> [دقائق]\` للتسجيل بنفس منطق \`.record\`
  ↳ بعد اختيار المباراة يعرض البوت *قائمة الجودات* المتاحة (360p/480p/720p/1080p...) — رد برقم الجودة ليبدأ التسجيل
  ↳ أو حدّد الجودة مباشرة واختصر الخطوة: \`.livefootball 1 120 720p\`
  ↳ أو \`.livefootball <رابط صفحة مباراة أو m3u8> [دقائق]\` — و \`.livefootball sources\` لعرض المصادر
  ↳ \`.livefootball <رقم> link\` لطباعة رابط البث فقط للتشغيل — و \`.livefootballapi\` لفحص حالة المصادر
• \`.livechannel\` — قنوات 24/7 من كل المواقع ذات القنوات (DamiTV، DaddyLive، PPV.ST وغيرها)، بنفس خطوات التسجيل — و \`.stoplivechannel\` للإيقاف — و \`.livechannelapi\` لفحص حالة مصادر القنوات
• \`.stoplivefootball\` — إيقاف تسجيل مباراة مباشرة
• \`.tflix\` — مباريات موقع tflix (بث مشفّر ClearKey يفكّه البوت ويسجّله): قائمة/بحث، ثم اختيار برقم وخطوات كالمعتاد (قناة ← جودة ← مدة ← جزء)
  ↳ \`.tflix <رابط صفحة مباراة tflix>\` للتسجيل من رابط مباشر — و \`.tflix [رقم] link\` لطباعة رابط MPD ومفتاح فك التشفير — و \`.stoptflix\` للإيقاف
  ↳ الدومين قابل للتبديل إن تغيّر عنوان الموقع: \`.tflix -domain <الدومين الجديد>\` (مثال: \`.tflix -domain tflix.su\`) — و \`.tflix -domain\` وحده يعرض الحالي

📱 *أدوات*
• \`.apk <اسم>\` — ابحث وحمّل تطبيق APK
  ↳ مثال: \`.apk mt manager\`
• \`.sh <أمر>\` — نفّذ أمر شل (للمالك فقط)
• \`.cwd\` — اعرض مجلد العمل الحالي
• \`.killcmd\` — أوقف الأمر الجاري
• \`.ping\` — افحص إن البوت شغال (بيرد Pong + زمن الرد)
• \`.help\` — اعرض هذه القائمة` }, { quoted: mek });
                        return;
                    }

                    // ============================================================
                    // ── أوامر مشغّل m3u المستقل (.playm3u / .stopplaym3u) ──
                    // مستقلة بالكامل عن .record/.recordiptv وتعتمد على lib/m3uplayer.js
                    // ============================================================

                    // ── أمر .stopplaym3u ──
                    if (command === '.stopplaym3u') {
                        const stopped = m3uPlayer.stopM3UPlayer(chatId);
                        if (!stopped) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تشغيل m3u نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تشغيل m3u... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .playm3u [رابط] [المدة بالدقائق] [مدة الجزء - اختياري] ──
                    if (command === '.playm3u') {
                        const parts = query.split(' ').filter(Boolean);
                        const streamUrl = parts[0];
                        const durationMin = parseInt(parts[1]);
                        const manualSegmentMin = parts[2] && !isNaN(parseInt(parts[2])) ? parseInt(parts[2]) : null;

                        if (!streamUrl || !m3uPlayer.isValidM3UUrl(streamUrl) || isNaN(durationMin)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ الصيغة الصحيحة:\n\`.playm3u [رابط m3u/m3u8] [المدة الكلية بالدقائق] [مدة الجزء بالدقائق - اختياري]\`\n\n💡 مثال: \`.playm3u https://example.com/stream.m3u8 60\`\nأو: \`.playm3u https://example.com/stream.m3u8 60 10\` (كل جزء 10 دقائق بالضبط)`
                            }, { quoted: mek });
                            return;
                        }

                        if (durationMin < 1 || durationMin > m3uPlayer.M3U_MAX_DURATION_MIN) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و ${m3uPlayer.M3U_MAX_DURATION_MIN} دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMin !== null && (manualSegmentMin < 1 || manualSegmentMin > durationMin)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        if (m3uPlayer.hasActiveM3UPlayer(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تشغيل m3u نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stopplaym3u\` قبل بدء تشغيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        // لا ننتظر (fire-and-forget) — تماماً مثل .record — حتى لا يتوقف معالج الرسائل
                        m3uPlayer.startM3UPlayer({
                            sock: XeonBotInc,
                            chatId,
                            mek,
                            streamUrl,
                            durationMin,
                            manualSegmentMin,
                            tmpRootDir: tmpDir
                        }).catch(async (err) => {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ غير متوقع في مشغّل m3u: ${err.message}`
                            }, { quoted: mek });
                        });
                        return;
                    }

                    // ============================================================
                    // ── أمر .setm3u (استبدال/تحديث رابط مصدر M3U — مستقل عن UGEEN) ──
                    // ============================================================
                    if (command === '.setm3u') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ يرجى إرسال رابط M3U الجديد بعد الأمر.\n💡 مثال:\n\`.setm3u https://example.com/playlist.m3u\`\n\nهذا الأمر مستقل تماماً عن \`.seturl\` (الخاص بـ UGEEN) — يضبط مصدر M3U منفصل خاصاً به، يُستخدم مع \`.m3usource\` للبحث عن قنواته.`
                            }, { quoted: mek });
                            return;
                        }

                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري التحقق من الرابط الجديد...`
                            }, { quoted: mek });

                            const result = await replaceM3USource(query.trim());

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *تم استبدال مصدر M3U بنجاح وحُفظ بشكل دائم!*\n🔗 الرابط: ${result.url}\n📺 عدد القنوات المتاحة: ${result.channelCount}\n\n💡 استخدم \`.m3usource [اسم]\` للبحث ضمن هذا المصدر، أو استخدم أي رابط قناة مباشرة مع \`.playm3u\`.`
                            }, { quoted: mek });

                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استبدال الرابط:\n\`${e.message}\`\n\n⚠️ تم إبقاء المصدر القديم كما هو (لم يُحفظ الرابط الجديد).`
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .m3usource (عرض/بحث قنوات مصدر M3U المستقل الحالي) ──
                    if (command === '.m3usource') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: query
                                    ? `🔍 جاري البحث عن قنوات تحتوي على *${query}* في مصدر M3U الحالي...`
                                    : `📡 جاري جلب قائمة قنوات مصدر M3U الحالي...`
                            }, { quoted: mek });

                            const channels = await fetchM3USourceChannels();

                            let filtered = query
                                ? channels.filter(ch => ch.name.toLowerCase().includes(query.toLowerCase()))
                                : channels;

                            if (filtered.length === 0) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لم يتم العثور على قنوات تطابق: *${query}*`
                                }, { quoted: mek });
                                return;
                            }

                            let msg = `📺 *نتائج مصدر M3U المستبدل (${filtered.length} قناة):*\n\n`;
                            filtered.slice(0, 20).forEach((ch) => {
                                msg += `${ch.name}\n🆔 ID: \`${ch.id}\`\n🔗 ${ch.url}\n\n`;
                            });
                            if (filtered.length > 20) msg += `💡 _عرض أول 20 نتيجة فقط من ${filtered.length}._\n`;
                            msg += `\n▶️ للتشغيل استخدم: \`.playm3u [الرابط] [المدة بالدقائق]\``;

                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ ${e.message}`
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .seturl (تحديث رابط M3U بعد كل تجديد بدون تعديل الكود) ──
                    if (command === '.seturl') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إرسال رابط M3U الجديد بعد الأمر.\n💡 مثال:\n`.seturl https://ugeen.live/get.php?username=USER&password=PASS&type=m3u&output=ts`'
                            }, { quoted: mek });
                            return;
                        }

                        let oldConfig;
                        try {
                            const parsed = new URL(query.trim());
                            const newUser = parsed.searchParams.get('username');
                            const newPass = parsed.searchParams.get('password');

                            if (!newUser || !newPass) {
                                throw new Error('لم أتمكن من استخراج اليوزر أو الباسورد من هذا الرابط. تأكد أن الرابط يحتوي على username= و password=');
                            }

                            oldConfig = { ...UGEEN_CONFIG };

                            UGEEN_CONFIG.host = parsed.origin;
                            UGEEN_CONFIG.user = newUser;
                            UGEEN_CONFIG.pass = newPass;

                            // مسح الكاش لإجبار إعادة الجلب بالبيانات الجديدة فوراً
                            ugeenChannelsCache = [];
                            ugeenChannelsCacheTime = 0;

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري التحقق من الرابط الجديد...`
                            }, { quoted: mek });

                            // تحقق فعلي قبل الحفظ الدائم — لتفادي حفظ رابط لا يعمل
                            const channels = await fetchUgeenChannels(true);

                            // الحفظ الدائم لا يتم إلا بعد نجاح التحقق
                            const dataDir = path.dirname(UGEEN_CONFIG_PATH);
                            if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
                            fs.writeFileSync(UGEEN_CONFIG_PATH, JSON.stringify(UGEEN_CONFIG, null, 2));

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *تم تحديث الرابط بنجاح وحُفظ بشكل دائم!*\n🌐 Host: ${UGEEN_CONFIG.host}\n👤 User: ${UGEEN_CONFIG.user}\n📺 عدد القنوات المتاحة: ${channels.length}\n\n💡 سيبقى هذا الرابط فعّالاً حتى بعد إعادة تشغيل البوت.`
                            }, { quoted: mek });

                        } catch (e) {
                            // فشل التحقق → استرجاع الإعدادات القديمة لتفادي كسر البوت برابط لا يعمل
                            if (typeof oldConfig !== 'undefined') {
                                UGEEN_CONFIG.host = oldConfig.host;
                                UGEEN_CONFIG.user = oldConfig.user;
                                UGEEN_CONFIG.pass = oldConfig.pass;
                                ugeenChannelsCache = [];
                                ugeenChannelsCacheTime = 0;
                            }
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل تحديث الرابط:\n\`${e.message}\`\n\n⚠️ تم إبقاء الإعدادات القديمة كما هي (لم يُحفظ الرابط الجديد).`
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .test ──
                    if (command === '.test') {
                        try {
                            const res = await axios.get(
                                `${UGEEN_CONFIG.host}/get.php?username=${UGEEN_CONFIG.user}&password=${UGEEN_CONFIG.pass}&type=m3u&output=ts`,
                                { timeout: 30000 }
                            );
                            const channelCount = (String(res.data).match(/#EXTINF/g) || []).length;
                            if (channelCount === 0) throw new Error('لم يتم العثور على أي قنوات في الرد (تحقق من صحة الحساب).');
                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *سيرفر IPTV يعمل بنجاح!*\n📺 إجمالي القنوات المتاحة: *${channelCount}*`
                            }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل الاتصال بالسيرفر:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .channels ──
                    if (command === '.channels') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: query
                                    ? `🔍 جاري البحث عن قنوات تحتوي على *${query}*...`
                                    : `📡 جاري جلب قائمة جميع القنوات...`
                            }, { quoted: mek });

                            const channels = await fetchUgeenChannels();

                            let filtered = query
                                ? channels.filter(ch => ch.name.toLowerCase().includes(query.toLowerCase()))
                                : channels;

                            if (filtered.length === 0) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لم يتم العثور على قنوات تطابق: *${query}*`
                                }, { quoted: mek });
                                return;
                            }

                            let msg = `📺 *نتائج البحث (${filtered.length} قناة):*\n\n`;
                            filtered.slice(0, 20).forEach((ch) => {
                                msg += `${ch.name}\n🆔 ID: \`${ch.id}\`\n\n`;
                            });
                            if (filtered.length > 20) msg += `💡 _عرض أول 20 نتيجة فقط من ${filtered.length}._\n`;
                            msg += `\n▶️ للتسجيل استخدم: \`.record [ID] [المدة بالدقائق]\``;

                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ في جلب القنوات:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .iptv (قائمة ثابتة من iptv-org، منفصلة عن UGEEN) ──
                    if (command === '.iptv') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: query
                                    ? `🔍 جاري البحث عن قنوات تحتوي على *${query}* في القائمة الثابتة...`
                                    : `📡 جاري جلب قائمة القنوات الثابتة (iptv-org)...`
                            }, { quoted: mek });

                            const channels = await fetchFixedIptvChannels();

                            let filtered = query
                                ? channels.filter(ch => ch.name.toLowerCase().includes(query.toLowerCase()))
                                : channels;

                            if (filtered.length === 0) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لم يتم العثور على قنوات تطابق: *${query}*`
                                }, { quoted: mek });
                                return;
                            }

                            let msg = `📺 *نتائج قائمة IPTV الثابتة (${filtered.length} قناة):*\n\n`;
                            filtered.slice(0, 20).forEach((ch) => {
                                msg += `${ch.name}\n🆔 ID: \`${ch.id}\`\n🔗 ${ch.url}\n\n`;
                            });
                            if (filtered.length > 20) msg += `💡 _عرض أول 20 نتيجة فقط من ${filtered.length}._\n`;
                            msg += `\n▶️ للتسجيل استخدم: \`.recordiptv [ID] [المدة بالدقائق]\``;

                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ في جلب القائمة الثابتة:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .stoprecord ──
                    if (command === '.stoprecord') {
                        const control = activeRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء التسجيل... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .stopremotedl (إلغاء تحميل عن بُعد نشط: يلغي الـ workflow على GitHub إن كان لسه شغال، أو يوقف إرسال الأجزاء المتبقية) ──
                    if (command === '.stopremotedl') {
                        const control = activeRemoteDl.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تحميل عن بُعد نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء التحميل عن بُعد... (سيتم إلغاء تشغيل GitHub Actions إن كان لا يزال يعمل، أو إيقاف إرسال الأجزاء المتبقية)`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .stoprecordiptv (خاص بتسجيلات القائمة الثابتة فقط) ──
                    if (command === '.stoprecordiptv') {
                        const control = activeIptvRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل IPTV (ثابت) نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تسجيل IPTV الثابت... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .record ──
                    if (command === '.record') {
                        if (args.length < 3 || isNaN(parseInt(args[2]))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ الصيغة الصحيحة:\n\`.record [ID القناة] [المدة الكلية بالدقائق] [مدة الجزء بالدقائق - اختياري]\`\n\n💡 مثال: \`.record 1234 120\` (تسجيل متواصل 120 دقيقة، كل جزء ~${RECORD_TARGET_MB} MB تلقائياً عبر فحص معدل البت)\nأو: \`.record 1234 120 10\` (كل جزء 10 دقائق بالضبط، بدون فحص)\n\n🔍 للحصول على ID القناة استخدم: \`.channels [اسم القناة]\``
                            }, { quoted: mek });
                            return;
                        }

                        const streamId = args[1];
                        const duration = parseInt(args[2]);
                        const manualSegmentMinutes = args[3] && !isNaN(parseInt(args[3])) ? parseInt(args[3]) : null;

                        if (duration < 1 || duration > 360) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || manualSegmentMinutes > duration)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        let channel;
                        try {
                            const channels = await fetchUgeenChannels();
                            channel = channels.find(ch => ch.id === streamId);
                            if (!channel) throw new Error('لم يتم العثور على قناة بهذا الـ ID. تأكد منه عبر أمر .channels');
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ ${e.message}`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        if (activeRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoprecord\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const streamUrl = channel.url;
                        const totalDurationSec = duration * 60;

                        let segmentTimeSec;
                        let segmentMinutes;
                        let bitrateNote = '';

                        if (manualSegmentMinutes !== null) {
                            segmentMinutes = manualSegmentMinutes;
                            segmentTimeSec = manualSegmentMinutes * 60;
                        } else {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري فحص معدل بت القناة لتقدير حجم الجزء بدقة (~${RECORD_TARGET_MB} MB)...`
                            }, { quoted: mek });

                            const bitrate = await probeStreamBitrate(streamUrl);
                            segmentTimeSec = computeSegmentTimeSec(bitrate);
                            segmentMinutes = Math.round(segmentTimeSec / 60);

                            bitrateNote = bitrate
                                ? `\n📊 معدل البت المُقاس: ~${(bitrate / 1000000).toFixed(2)} Mbps`
                                : `\n⚠️ تعذر قياس معدل البت، تم استخدام تقدير احتياطي (${RECORD_DEFAULT_SEGMENT_MIN} دقائق)`;
                        }

                        const segDir = path.join(tmpDir, `rec_${streamId}_${Date.now()}`);
                        fs.mkdirSync(segDir, { recursive: true });

                        await XeonBotInc.sendMessage(chatId, {
                            text: `🎙️ *بدأ التسجيل المتواصل!*\n📺 القناة: ${channel.name}\n🆔 ID: \`${streamId}\`\n⏱️ المدة الكلية: *${duration} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${RECORD_TARGET_MB} MB)${bitrateNote}\n🔗 اتصال واحد متواصل بالبث — بدون أي انقطاع بين الأجزاء\n\n🛑 لإلغاء التسجيل في أي وقت: \`.stoprecord\``
                        }, { quoted: mek });

                        const control = { proc: null, cancelled: false };
                        activeRecordings.set(chatId, control);

                        const MAX_RECONNECT_ATTEMPTS = 15; // مع التأخير التصاعدي (backoff)، هذا يكفي لتغطية ساعات من الانقطاعات المتكررة بدون إغراق السيرفر

                        (async () => {
                            let segmentIndex = 0;
                            let abortedBySize = false;
                            let wasCancelled = false;
                            let remainingSec = totalDurationSec;
                            let attempt = 0;
                            let reconnectedCount = 0;

                            const onSegmentReady = async (filePath) => {
                                segmentIndex++;
                                try {
                                    const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: filePath },
                                        mimetype: 'video/mp4',
                                        fileName: `Match_${streamId}_part${segmentIndex}.mp4`,
                                        caption: `📦 *الجزء ${segmentIndex}*\n📺 ${channel.name}\n⚖️ ${sizeMB} MB`
                                    }, { quoted: mek });
                                } catch (e) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ فشل إرسال الجزء ${segmentIndex}: ${e.message}`
                                    }, { quoted: mek });
                                } finally {
                                    try { fs.unlinkSync(filePath); } catch (_) {}
                                }
                            };

                            try {
                                while (remainingSec > 60 && attempt < MAX_RECONNECT_ATTEMPTS && !control.cancelled) {
                                    attempt++;
                                    const startTs = Date.now();

                                    const result = await recordContinuousSegmented(
                                        streamUrl, segDir, `part_a${attempt}`, remainingSec, segmentTimeSec,
                                        onSegmentReady, control
                                    );

                                    const elapsedSec = Math.floor((Date.now() - startTs) / 1000);
                                    remainingSec -= elapsedSec;

                                    abortedBySize = result.abortedBySize;
                                    wasCancelled = result.cancelled;

                                    if (wasCancelled || abortedBySize) break;
                                    if (remainingSec <= 60) break; // اكتملت المدة فعلياً (بهامش بسيط)

                                    // توقف مبكر غير متوقع (انقطاع بث/شبكة) وما زال هناك وقت متبقٍ → أعد الاتصال
                                    reconnectedCount++;
                                    // تأخير تصاعدي: 3، 6، 12، 24، 48 ثانية، ثم يثبت عند 60 ثانية
                                    // لتفادي إغراق السيرفر بطلبات متكررة سريعة (قد يُفسَّر كإساءة استخدام ويؤدي لحظر الـIP)
                                    const backoffMs = Math.min(3000 * Math.pow(2, Math.min(reconnectedCount - 1, 5)), 60000);
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ *انقطع الاتصال بالبث بشكل غير متوقع.*\n⏱️ الوقت المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🔄 جاري إعادة الاتصال بعد ${Math.round(backoffMs / 1000)} ثانية... (محاولة ${attempt + 1}/${MAX_RECONNECT_ATTEMPTS})`
                                    }, { quoted: mek });
                                    await new Promise(r => setTimeout(r, backoffMs));
                                }

                                if (!wasCancelled && !abortedBySize && attempt >= MAX_RECONNECT_ATTEMPTS && remainingSec > 60) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ تعذر إكمال التسجيل بعد ${MAX_RECONNECT_ATTEMPTS} محاولات إعادة اتصال. قد تكون القناة غير مستقرة حالياً.`
                                    }, { quoted: mek });
                                }
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في التسجيل: ${err.message}`
                                }, { quoted: mek });
                            } finally {
                                activeRecordings.delete(chatId);
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }

                            if (wasCancelled) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إلغاء التسجيل بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${segmentIndex}`
                                }, { quoted: mek });
                            } else if (abortedBySize) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إيقاف التسجيل مبكراً!*\nجودة البث كانت أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن للتخزين المتاح.\n📦 عدد الأجزاء المُرسلة قبل التوقف: ${segmentIndex}\n\n💡 جرّب تقليل مدة الجزء (مثال: \`.record ${streamId} ${duration} 3\`) للحصول على أجزاء أصغر تلائم جودة هذا البث.`
                                }, { quoted: mek });
                            } else {
                                const reconnectNote = reconnectedCount > 0 ? `\n🔄 حدثت ${reconnectedCount} إعادة اتصال بسبب انقطاعات مؤقتة في البث.` : '';
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `✅ *اكتمل التسجيل الكامل!*\n📺 القناة: ${channel.name}\n📦 عدد الأجزاء المُرسلة: ${segmentIndex}${reconnectNote}`
                                }, { quoted: mek });
                            }
                        })();
                        return;
                    }

                    // ── أمر .livefootballapi (فحص حالة مصادر كرة القدم المباشرة) ──
                    if (command === '.livefootballapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر كرة القدم المباشرة...'
                            }, { quoted: mek });
                            const autoNames = ['📺 DamiTV', '🎬 DaddyLive', '🎟️ PPV.ST', '🐶 SportsBite', '📡 FCTV33', '🏟️ WatchSports', '🎥 RoxieStreams', '🆓 StreamFree', '📱 TheTVApp'];
                            const settled = await Promise.allSettled(LF_FETCHERS.map(async (f, i) => {
                                const t = Date.now();
                                const r = await f();
                                return { name: autoNames[i], ms: Date.now() - t, n: r.length };
                            }));
                            let out = `📊 *حالة مصادر كرة القدم المباشرة:*\n\n⚽ *مصادر تلقائية (بحث عن المباريات):*\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    if (s.value.n > 0) out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} مباراة)\n`;
                                    else out += `🟡 *${s.value.name}* — يرد، لكن بلا مباريات الآن (${s.value.ms}ms)\n`;
                                } else {
                                    out += `🔴 *${autoNames[i]}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            // مصادر الرابط المباشر: فحص وصول لموقع المصدر نفسه
                            const linkSources = LF_SOURCES.filter(x => !x.auto && x.url);
                            const linkSettled = await Promise.allSettled(linkSources.map(async s => {
                                const t = Date.now();
                                await axios.get(s.url, { timeout: 8000, maxRedirects: 3, validateStatus: () => true, headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)' } });
                                return { name: s.name, ms: Date.now() - t };
                            }));
                            out += `\n🔗 *مصادر بالرابط المباشر (وجود الموقع):*\n`;
                            linkSettled.forEach((s, i) => {
                                if (s.status === 'fulfilled') out += `🟢 *${s.value.name}* — يرد (${s.value.ms}ms)\n`;
                                else out += `🔴 *${linkSources[i].name}* — لا يرد\n`;
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .livechannelapi (فحص حالة مصادر القنوات المباشرة) ──
                    if (command === '.livechannelapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر القنوات المباشرة...'
                            }, { quoted: mek });
                            const settled = await Promise.allSettled(LF_CHANNEL_FETCHERS.map(async f => {
                                const t = Date.now();
                                const r = await f.fn();
                                return { name: f.name, ms: Date.now() - t, n: r.length };
                            }));
                            let out = `📊 *حالة مصادر القنوات المباشرة:*\n\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    if (s.value.n > 0) out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} قناة)\n`;
                                    else out += `🟡 *${LF_CHANNEL_FETCHERS[i].name}* — يرد، لكن بلا قنوات مكتشفة الآن (${s.value ? s.value.ms : 0}ms)\n`;
                                } else {
                                    out += `🔴 *${LF_CHANNEL_FETCHERS[i].name}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .stoplivefootball ──
                    if (command === '.stoplivefootball') {
                        const control = activeLiveFootballRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل مباراة مباشرة نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تسجيل المباراة... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .stoplivechannel ──
                    if (command === '.stoplivechannel') {
                        const control = activeLiveChannelRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل قناة مباشرة نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تسجيل القناة... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .livefootball — مباريات مباشرة من مصادر البث الرياضي، بنفس منطق .record ──
                    // .livefootball                      → قائمة المباريات من المصادر التلقائية
                    // .livefootball <فريق>               → بحث داخل القائمة
                    // .livefootball <رقم> [دقائق] [جزء]  → تسجيل مباراة من آخر قائمة
                    // .livefootball <رابط> [دقائق] [جزء] → تسجيل من صفحة مباراة/رابط m3u8 مباشر (لأي مصدر)
                    // .livefootball sources              → عرض سجل المصادر
                    if (command === '.livefootball') {
                        if ((args[1] || '').toLowerCase() === 'sources') {
                            let msg = `📡 *مصادر .livefootball (${LF_SOURCES.length} مصدر):*\n\n✅ *بحث تلقائي عن المباريات:*\n`;
                            for (const s of LF_SOURCES.filter(x => x.auto)) msg += `• ${s.name}\n`;
                            msg += `\n🔗 *تعمل بالرابط المباشر* (\`.livefootball <رابط صفحة المباراة>\`):\n`;
                            for (const s of LF_SOURCES.filter(x => !x.auto)) msg += `• ${s.name}\n`;
                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                            return;
                        }

                        const isUrlArg = !!args[1] && /^https?:\/\//i.test(args[1]);
                        const isPickArg = !!args[1] && /^\d+$/.test(args[1]) && liveFootballLists.has(chatId);

                        // وضع القائمة/البحث (بدون رقم اختيار وبدون رابط)
                        if (!isUrlArg && !isPickArg) {
                            if (!!args[1] && /^\d+$/.test(args[1])) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `ℹ️ اعرض قائمة المباريات أولاً بأمر \`.livefootball\` ثم اختر برقم: \`.livefootball <رقم> [دقائق]\``
                                }, { quoted: mek });
                                return;
                            }
                            try {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: query ? `🔍 جاري البحث عن مباريات *${query}* في مصادر البث المباشر...` : `📡 جاري جلب مباريات كرة القدم من مصادر البث المباشر...`
                                }, { quoted: mek });
                                const { matches, failed } = await lfFetchAllEvents();
                                // طلب المستخدم: لا عرض لمباريات لم تبدأ (ولا التي انتهت) —
                                // يُطبق على المصادر ذات التوقيت الموثوق (DamiTV)، وما بلا توقيت يبقى كما هو
                                const nowMs = Date.now();
                                const startedOnly = matches.filter(mt => {
                                    if (mt.startsAtTs && mt.startsAtTs * 1000 > nowMs) return false;
                                    if (mt.endsAtTs && mt.endsAtTs * 1000 < nowMs) return false;
                                    return true;
                                });
                                let filtered = query
                                    ? startedOnly.filter(mt => footballHasTeam(mt.title, query) || footballNorm(mt.title).includes(footballNorm(query)))
                                    : startedOnly;
                                filtered = filtered.slice(0, 20);
                                if (!filtered.length) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: query ? `❌ لم يتم العثور على مباريات تطابق: *${query}* في المصادر حالياً.` : `❌ لم يتم العثور على مباريات متاحة في المصادر حالياً.`
                                    }, { quoted: mek });
                                    return;
                                }
                                liveFootballLists.set(chatId, { matches: filtered, at: Date.now() });
                                let msg = `⚽ *مباريات كرة القدم (${filtered.length}):*\n\n`;
                                filtered.forEach((mt, i) => {
                                    const meta = [mt.source, mt.league, mt.status, mt.startsAt].filter(Boolean).join(' • ');
                                    msg += `*${i + 1}.* ${mt.title}\n📡 ${meta}\n\n`;
                                });
                                if (failed.length) msg += `⚠️ تعذر جلب: ${failed.join('، ')}\n\n`;
                                msg += `▶️ للتسجيل: \`.livefootball [رقم]\` — وبعدها يسألك البوت خطوة بخطوة: الجودة، ثم كم دقيقة يسجّل، ثم كل كم دقيقة يبعث جزءاً\n⚡ أو اختصر كل الخطوات: \`.livefootball 1 100 1\` = مباراة 1، تسجيل 100 دقيقة، جزء كل دقيقة\n🔗 للرابط المباشر فقط (تشغيل بدون تسجيل): \`.livefootball [رقم] link\``;
                                await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                            } catch (e) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في جلب المباريات:\n\`${e.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // وضع التسجيل (اختيار من قائمة أو رابط مباشر) — نفس منطق .record
                        // وسيط جودة اختياري على نمط 720p قد يأتي في أي موضع بعد الرقم/الرابط
                        // وكلمة link (أو رابط) تعني: اطبع رابط البث فقط للتشغيل، بدون تسجيل
                        let requestedQuality = null;
                        let lfLinkOnly = false;
                        const lfTail = [];
                        for (const a of args.slice(2)) {
                            if (/^link$/i.test(String(a)) || a === 'رابط') { lfLinkOnly = true; continue; }
                            const qm = String(a).match(/^(\d{3,4})p$/i);
                            if (qm && !requestedQuality) requestedQuality = parseInt(qm[1]);
                            else lfTail.push(a);
                        }
                        let lfTitle, lfSource, lfPageUrl;
                        let lfDurationArg, lfSegArg;
                        let lfStartsAtTs = null, lfStartsAtLabel = null, lfStatus = null;
                        if (isPickArg) {
                            const list = liveFootballLists.get(chatId).matches;
                            const pick = parseInt(args[1]);
                            if (pick < 1 || pick > list.length) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ الرقم يجب أن يكون بين 1 و ${list.length}.`
                                }, { quoted: mek });
                                return;
                            }
                            const chosen = list[pick - 1];
                            lfTitle = chosen.title; lfSource = chosen.source; lfPageUrl = chosen.pageUrl;
                            lfDurationArg = lfTail[0]; lfSegArg = lfTail[1];
                            lfStartsAtTs = chosen.startsAtTs || null;
                            lfStartsAtLabel = chosen.startsAt || null;
                            lfStatus = chosen.status || null;
                        } else {
                            lfPageUrl = args[1];
                            lfTitle = 'مباراة مباشرة';
                            try { lfSource = new URL(lfPageUrl).hostname; } catch (_) { lfSource = 'رابط مباشر'; }
                            lfDurationArg = lfTail[0]; lfSegArg = lfTail[1];
                        }

                        // المدة ودقائق الجزء اختياريان في الأمر: إن غابا سأل عنهما البوت خطوة بخطوة بالردود
                        const duration = lfDurationArg && !isNaN(parseInt(lfDurationArg)) ? parseInt(lfDurationArg) : null;
                        const manualSegmentMinutes = lfSegArg && !isNaN(parseInt(lfSegArg)) ? parseInt(lfSegArg) : null;

                        if (duration !== null && (duration < 1 || duration > 360)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || (duration !== null && manualSegmentMinutes > duration))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        // مباراة لم تبدأ بعد: لا يوجد بث أصلاً قبل الانطلاق، فلا نحاول الاستخراج عبثاً
                        if (lfStartsAtTs && lfStatus !== 'live' && (lfStartsAtTs * 1000 - Date.now() > 10 * 60 * 1000)) {
                            const minsLeft = Math.ceil((lfStartsAtTs * 1000 - Date.now()) / 60000);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ *هذه المباراة لم تبدأ بعد.*\n⚽ ${lfTitle}\n🕐 تبدأ: ${lfStartsAtLabel || ''} (بعد ~${minsLeft} دقيقة)\n\nبث هذه المصادر يظهر عادة قبل الانطلاق بدقائق فقط. أعد المحاولة عند بداية المباراة وسيعمل الاستخراج.`
                            }, { quoted: mek });
                            return;
                        }

                        if (!lfLinkOnly && activeLiveFootballRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل مباراة نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoplivefootball\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        let streamUrl, streamHeaders;
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔎 جاري استخراج رابط البث من *${lfSource}*...`
                            }, { quoted: mek });
                            const resolved = await lfResolveStream(lfPageUrl);
                            streamUrl = resolved.streamUrl;
                            streamHeaders = resolved.headers;
                            var lfSealedInfo = resolved.sealedInfo || null;
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استخراج البث:\n\`${e.message}\``
                            }, { quoted: mek });
                            return;
                        }

                        await lfBeginRecording(XeonBotInc, chatId, mek, {
                            title: lfTitle, source: lfSource, pageUrl: lfPageUrl,
                            streamUrl, headers: streamHeaders, sealedInfo: lfSealedInfo,
                            duration, manualSegmentMinutes, requestedQuality,
                            segDecided: manualSegmentMinutes !== null,
                            linkOnly: lfLinkOnly
                        });
                        return;
                    }

                    // ── أمر .stoptflix ──
                    if (command === '.stoptflix') {
                        const control = activeTflixRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل tflix نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.stopped = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تسجيل tflix... سيتم إنهاء الجزء الحالي ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .settflix — تبديل دومين tflix (صيغة بديلة عن .tflix -domain) ──
                    if (command === '.settflix') {
                        await tflixDomainCommand(XeonBotInc, chatId, mek, args[1] || '');
                        return;
                    }

                    // ── أمر .tflix — مباريات tflix (بث DASH مشفّر ClearKey يفكّه البوت) ──
                    // .tflix                            → قائمة المباريات (المباشرة أولاً ثم القادمة)
                    // .tflix <فريق>                     → بحث داخل القائمة
                    // .tflix <رقم> [دقائق] [جزء] [جودة] → تسجيل بخطوات تفاعلية أو باختصار كامل
                    // .tflix <رابط مشاهدة> [دقائق]      → تسجيل من رابط صفحة مباراة tflix مباشر
                    // .tflix [رقم|رابط] link            → طباعة رابط MPD + مفتاح ClearKey فقط
                    // .tflix -domain <دومين>            → تبديل دومين الموقع (يُحفظ دائماً)
                    if (command === '.tflix') {
                        const flag1 = (args[1] || '').toLowerCase();
                        if (flag1 === '-domain' || flag1 === '--domain' || flag1 === 'domain') {
                            await tflixDomainCommand(XeonBotInc, chatId, mek, args[2] || '');
                            return;
                        }
                        const domain = TFLIX_CONFIG.domain;
                        const isUrlArg = !!args[1] && /^https?:\/\//i.test(args[1]);
                        const isPickArg = !!args[1] && /^\d+$/.test(args[1]) && tflixLists.has(chatId);

                        // وضع القائمة/البحث
                        if (!isUrlArg && !isPickArg) {
                            if (!!args[1] && /^\d+$/.test(args[1])) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `ℹ️ اعرض قائمة المباريات أولاً بأمر \`.tflix\` ثم اختر برقم: \`.tflix <رقم> [دقائق]\``
                                }, { quoted: mek });
                                return;
                            }
                            try {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: query ? `🔍 جاري البحث عن مباريات *${query}* في tflix...` : `📡 جاري جلب مباريات كرة القدم من tflix (${domain})...`
                                }, { quoted: mek });
                                const events = await tflixListEvents(domain);
                                const nowMs = Date.now();
                                let filtered = events.filter(e => e.live || (e.startsAt > nowMs && e.startsAt < nowMs + 48 * 3600 * 1000));
                                if (query) {
                                    const nq = footballNorm(query);
                                    filtered = filtered.filter(e => footballNorm(e.title).includes(nq) || footballNorm(e.competition || '').includes(nq));
                                }
                                filtered = filtered.slice(0, 20);
                                if (!filtered.length) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: query ? `❌ لم يتم العثور على مباريات تطابق: *${query}* في tflix حالياً.` : `❌ لا توجد مباريات مباشرة أو قادمة قريباً على tflix حالياً.`
                                    }, { quoted: mek });
                                    return;
                                }
                                tflixLists.set(chatId, { events: filtered, at: Date.now() });
                                let msg = `⚽ *مباريات tflix (${filtered.length}):*\n\n`;
                                filtered.forEach((e, i) => {
                                    const when = e.live
                                        ? '🔴 مباشرة الآن'
                                        : '🗓️ ' + new Date(e.startsAt).toLocaleString('ar-EG', { timeZone: 'Africa/Casablanca', weekday: 'short', day: 'numeric', month: 'numeric', hour: '2-digit', minute: '2-digit' });
                                    msg += `*${i + 1}.* ${e.title}\n🏆 ${e.competition || '—'} • ${when}\n📺 ${e.channels.length} قناة\n\n`;
                                });
                                msg += `▶️ للتسجيل: \`.tflix [رقم]\` — وبعدها يسألك البوت خطوة بخطوة: القناة (إن تعددت)، الجودة، المدة، دقائق الجزء\n⚡ أو اختصر كل الخطوات: \`.tflix 1 100 1\` = مباراة 1، تسجيل 100 دقيقة، جزء كل دقيقة\n🔗 للرابط فقط: \`.tflix [رقم] link\`\n🌐 الدومين الحالي: ${domain} — لتبديله: \`.tflix -domain <الدومين الجديد>\``;
                                await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                            } catch (e) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في جلب مباريات tflix:\n\`${e.message}\`\n\n💡 إن كان الموقع غيّر عنوانه، بدّل الدومين: \`.tflix -domain <الدومين الجديد>\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // تحليل الذيل: link / جودة مثل 720p / أرقام المدة والجزء
                        let requestedQuality = null;
                        let tfLinkOnly = false;
                        const tfTail = [];
                        for (const a of args.slice(2)) {
                            if (/^link$/i.test(String(a)) || a === 'رابط') { tfLinkOnly = true; continue; }
                            const qm = String(a).match(/^(\d{3,4})p$/i);
                            if (qm && !requestedQuality) requestedQuality = parseInt(qm[1]);
                            else tfTail.push(a);
                        }

                        let ev, jobDomain = domain;
                        if (isPickArg) {
                            const list = tflixLists.get(chatId).events;
                            const pick = parseInt(args[1]);
                            if (pick < 1 || pick > list.length) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ الرقم يجب أن يكون بين 1 و ${list.length}.`
                                }, { quoted: mek });
                                return;
                            }
                            ev = list[pick - 1];
                        } else {
                            let u;
                            try { u = new URL(args[1]); } catch (_) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ رابط غير صحيح.` }, { quoted: mek });
                                return;
                            }
                            jobDomain = u.hostname.replace(/^www\./, '').toLowerCase();
                            const watchPath = u.pathname;
                            if (!/\/watch\//.test(watchPath)) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ هذا ليس رابط صفحة مباراة tflix — يجب أن يكون رابط مشاهدة يحتوي على /watch/ (انسخه من صفحة المباراة في الموقع).`
                                }, { quoted: mek });
                                return;
                            }
                            try {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🔎 جاري قراءة بيانات المباراة من الرابط...`
                                }, { quoted: mek });
                                const boot = await tflixGetWatchEvent(jobDomain, watchPath);
                                ev = { title: boot.title || 'مباراة tflix', competition: '', feedId: boot.feedId, watchPath, channels: boot.channels, live: true, startsAt: 0 };
                                if (jobDomain !== domain) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `🌐 ملحوظة: دومين هذا الرابط (${jobDomain}) يختلف عن الدومين المضبوط (${domain}) — سأستعمل دومين الرابط لهذه المباراة. لاعتماده دائماً: \`.tflix -domain ${jobDomain}\``
                                    }, { quoted: mek });
                                }
                            } catch (e) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ تعذر قراءة المباراة من الرابط:\n\`${e.message}\``
                                }, { quoted: mek });
                                return;
                            }
                        }

                        const duration = tfTail[0] && !isNaN(parseInt(tfTail[0])) ? parseInt(tfTail[0]) : null;
                        let manualSegmentMinutes = tfTail[1] && !isNaN(parseInt(tfTail[1])) ? parseInt(tfTail[1]) : null;
                        const segDecided = manualSegmentMinutes !== null;
                        if (manualSegmentMinutes === 0) manualSegmentMinutes = null; // 0 في الأمر = تقطيع تلقائي محسوم

                        if (duration !== null && (duration < 1 || duration > 360)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || (duration !== null && manualSegmentMinutes > duration))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        // مباراة لم تبدأ بعد: القنوات والبث يظهران عند الانطلاق فقط
                        if (ev.startsAt && !ev.live && (ev.startsAt - Date.now() > 10 * 60 * 1000)) {
                            const minsLeft = Math.ceil((ev.startsAt - Date.now()) / 60000);
                            const whenStr = new Date(ev.startsAt).toLocaleString('ar-EG', { timeZone: 'Africa/Casablanca', weekday: 'long', hour: '2-digit', minute: '2-digit' });
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ *هذه المباراة لم تبدأ بعد.*\n⚽ ${ev.title}\n🕐 تبدأ: ${whenStr} (بعد ~${minsLeft} دقيقة)\n\nبث tflix يظهر عند الانطلاق. أعد المحاولة عند بداية المباراة وسيعمل الاستخراج.`
                            }, { quoted: mek });
                            return;
                        }

                        if (!tfLinkOnly && activeTflixRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل tflix نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoptflix\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        // وضع الرابط فقط: استخراج وطباعة MPD + مفتاح ClearKey لكل قناة (حتى 3)
                        if (tfLinkOnly) {
                            const chans = (ev.channels || []).slice(0, 3);
                            if (!chans.length) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لا توجد قنوات بث لهذه المباراة على tflix حالياً (تظهر القنوات عند الانطلاق).`
                                }, { quoted: mek });
                                return;
                            }
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔎 جاري استخراج روابط البث من tflix...`
                            }, { quoted: mek });
                            for (const c of chans) {
                                try {
                                    const cfg = await tflixExtractConfig(jobDomain, ev.watchPath, ev.feedId, c.id);
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `🔗 *${ev.title}*\n📺 القناة: ${c.name}\n\nرابط MPD:\n${cfg.mpdUrl}\n\n🔑 مفتاح ClearKey:\n\`${cfg.kid}:${cfg.key}\`\n\nℹ️ البث مشفّر: الرابط وحده لا يكفي في المشغّلات العادية — استعمل مشغّلاً يدعم ClearKey مع هذا المفتاح، أو سجّل من البوت مباشرة بنفس الأمر بدون كلمة link.`
                                    }, { quoted: mek });
                                } catch (e) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ القناة ${c.name}: ${e.message}`
                                    }, { quoted: mek });
                                }
                            }
                            return;
                        }

                        await tflixBeginFlow(XeonBotInc, chatId, mek, {
                            title: ev.title, competition: ev.competition || '',
                            watchPath: ev.watchPath, feedId: ev.feedId,
                            channels: ev.channels || [], domain: jobDomain,
                            duration, manualSegmentMinutes, segDecided,
                            requestedQuality, fastPath: duration !== null
                        });
                        return;
                    }

                    // ── أمر .livechannel — قنوات 24/7 من كل المواقع ذات القنوات (DamiTV، DaddyLive، PPV.ST، وبقية السجل) ──
                    // .livechannel                 → قائمة القنوات من كل المواقع
                    // .livechannel <اسم>           → بحث في القنوات
                    // .livechannel <رقم> [دقائق] [جزء] → تسجيل قناة (أو خطوات تفاعلية إن غابت الأرقام)
                    // .livechannel <رابط>          → تسجيل من صفحة قناة/رابط m3u8 مباشر
                    if (command === '.livechannel') {
                        const isUrlArg = !!args[1] && /^https?:\/\//i.test(args[1]);
                        const isPickArg = !!args[1] && /^\d+$/.test(args[1]) && liveChannelLists.has(chatId);

                        if (!isUrlArg && !isPickArg) {
                            if (!!args[1] && /^\d+$/.test(args[1])) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `ℹ️ اعرض قائمة القنوات أولاً بأمر \`.livechannel\` ثم اختر برقم: \`.livechannel <رقم> [دقائق]\``
                                }, { quoted: mek });
                                return;
                            }
                            const query = (args.slice(1).join(' ') || '').trim();
                            try {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: query ? `🔍 جاري البحث عن قنوات *${query}* في المواقع ذات القنوات...` : `📡 جاري جلب القنوات من كل المواقع ذات القنوات...`
                                }, { quoted: mek });
                                const { channels, failed } = await lfFetchAllChannels();
                                let filtered = query
                                    ? channels.filter(ch => footballNorm(ch.title).includes(footballNorm(query)))
                                    : channels;
                                filtered = filtered.slice(0, 30);
                                if (!filtered.length) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: query ? `❌ لم يتم العثور على قنوات تطابق: *${query}* حالياً.` : `❌ لم يتم العثور على قنوات متاحة حالياً.`
                                    }, { quoted: mek });
                                    return;
                                }
                                liveChannelLists.set(chatId, { channels: filtered, at: Date.now() });
                                let msg = `📺 *قنوات مباشرة (${filtered.length}):*\n\n`;
                                filtered.forEach((ch, i) => {
                                    msg += `*${i + 1}.* ${ch.title}\n📡 ${ch.source}\n\n`;
                                });
                                if (failed.length) msg += `⚠️ تعذر جلب: ${failed.join('، ')}\n\n`;
                                msg += `▶️ للتسجيل: \`.livechannel [رقم]\` — وبعدها يسألك البوت خطوة بخطوة: الجودة، ثم كم دقيقة يسجّل، ثم كل كم دقيقة يبعث جزءاً\n⚡ أو اختصر كل الخطوات: \`.livechannel 1 100 1\` = قناة 1، تسجيل 100 دقيقة، جزء كل دقيقة\n🔗 للرابط المباشر فقط (تشغيل بدون تسجيل): \`.livechannel [رقم] link\``;
                                await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                            } catch (e) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في جلب القنوات:\n\`${e.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // وضع التسجيل (اختيار من قائمة أو رابط مباشر) — نفس منطق .livefootball
                        let requestedQuality = null;
                        let lcLinkOnly = false;
                        const lcTail = [];
                        for (const a of args.slice(2)) {
                            if (/^link$/i.test(String(a)) || a === 'رابط') { lcLinkOnly = true; continue; }
                            const qm = String(a).match(/^(\d{3,4})p$/i);
                            if (qm && !requestedQuality) requestedQuality = parseInt(qm[1]);
                            else lcTail.push(a);
                        }
                        let lcTitle, lcSource, lcPageUrl;
                        let lcDurationArg, lcSegArg;
                        if (isPickArg) {
                            const list = liveChannelLists.get(chatId).channels;
                            const pick = parseInt(args[1]);
                            if (pick < 1 || pick > list.length) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ الرقم يجب أن يكون بين 1 و ${list.length}.`
                                }, { quoted: mek });
                                return;
                            }
                            const chosen = list[pick - 1];
                            lcTitle = chosen.title; lcSource = chosen.source; lcPageUrl = chosen.pageUrl;
                            lcDurationArg = lcTail[0]; lcSegArg = lcTail[1];
                        } else {
                            lcPageUrl = args[1];
                            lcTitle = 'قناة مباشرة';
                            try { lcSource = new URL(lcPageUrl).hostname; } catch (_) { lcSource = 'رابط مباشر'; }
                            lcDurationArg = lcTail[0]; lcSegArg = lcTail[1];
                        }

                        const duration = lcDurationArg && !isNaN(parseInt(lcDurationArg)) ? parseInt(lcDurationArg) : null;
                        const manualSegmentMinutes = lcSegArg && !isNaN(parseInt(lcSegArg)) ? parseInt(lcSegArg) : null;

                        if (duration !== null && (duration < 1 || duration > 360)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || (duration !== null && manualSegmentMinutes > duration))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        if (!lcLinkOnly && activeLiveChannelRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل قناة نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoplivechannel\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        let streamUrl, streamHeaders;
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔎 جاري استخراج رابط بث القناة من *${lcSource}*...`
                            }, { quoted: mek });
                            const resolved = await lfResolveStream(lcPageUrl);
                            streamUrl = resolved.streamUrl;
                            streamHeaders = resolved.headers;
                            var lcSealedInfo = resolved.sealedInfo || null;
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استخراج البث:\n\`${e.message}\``
                            }, { quoted: mek });
                            return;
                        }

                        await lfBeginRecording(XeonBotInc, chatId, mek, {
                            title: lcTitle, source: lcSource, pageUrl: lcPageUrl,
                            streamUrl, headers: streamHeaders, sealedInfo: lcSealedInfo,
                            duration, manualSegmentMinutes, requestedQuality,
                            segDecided: manualSegmentMinutes !== null,
                            linkOnly: lcLinkOnly, isChannel: true
                        });
                        return;
                    }

                    // ── أمر .recordiptv (تسجيل من القائمة الثابتة iptv-org فقط) ──
                    if (command === '.recordiptv') {
                        if (args.length < 3 || isNaN(parseInt(args[2]))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ الصيغة الصحيحة:\n\`.recordiptv [ID القناة] [المدة الكلية بالدقائق] [مدة الجزء بالدقائق - اختياري]\`\n\n💡 مثال: \`.recordiptv 1234 120\` (تسجيل متواصل 120 دقيقة، كل جزء ~${RECORD_TARGET_MB} MB تلقائياً عبر فحص معدل البت)\nأو: \`.recordiptv 1234 120 10\` (كل جزء 10 دقائق بالضبط، بدون فحص)\n\n🔍 للحصول على ID القناة استخدم: \`.iptv [اسم القناة]\``
                            }, { quoted: mek });
                            return;
                        }

                        const streamId = args[1];
                        const duration = parseInt(args[2]);
                        const manualSegmentMinutes = args[3] && !isNaN(parseInt(args[3])) ? parseInt(args[3]) : null;

                        if (duration < 1 || duration > 360) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || manualSegmentMinutes > duration)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        let channel;
                        try {
                            const channels = await fetchFixedIptvChannels();
                            channel = channels.find(ch => ch.id === streamId);
                            if (!channel) throw new Error('لم يتم العثور على قناة بهذا الـ ID. تأكد منه عبر أمر .iptv');
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ ${e.message}`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        if (activeIptvRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل IPTV ثابت نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoprecordiptv\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const streamUrl = channel.url;
                        const totalDurationSec = duration * 60;

                        let segmentTimeSec;
                        let segmentMinutes;
                        let bitrateNote = '';

                        if (manualSegmentMinutes !== null) {
                            segmentMinutes = manualSegmentMinutes;
                            segmentTimeSec = manualSegmentMinutes * 60;
                        } else {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري فحص معدل بت القناة لتقدير حجم الجزء بدقة (~${RECORD_TARGET_MB} MB)...`
                            }, { quoted: mek });

                            const bitrate = await probeStreamBitrate(streamUrl);
                            segmentTimeSec = computeSegmentTimeSec(bitrate);
                            segmentMinutes = Math.round(segmentTimeSec / 60);

                            bitrateNote = bitrate
                                ? `\n📊 معدل البت المُقاس: ~${(bitrate / 1000000).toFixed(2)} Mbps`
                                : `\n⚠️ تعذر قياس معدل البت، تم استخدام تقدير احتياطي (${RECORD_DEFAULT_SEGMENT_MIN} دقائق)`;
                        }

                        const segDir = path.join(tmpDir, `rec_iptv_${streamId}_${Date.now()}`);
                        fs.mkdirSync(segDir, { recursive: true });

                        await XeonBotInc.sendMessage(chatId, {
                            text: `🎙️ *بدأ تسجيل IPTV الثابت!*\n📺 القناة: ${channel.name}\n🆔 ID: \`${streamId}\`\n⏱️ المدة الكلية: *${duration} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${RECORD_TARGET_MB} MB)${bitrateNote}\n🔗 اتصال واحد متواصل بالبث — بدون أي انقطاع بين الأجزاء\n\n🛑 لإلغاء التسجيل في أي وقت: \`.stoprecordiptv\``
                        }, { quoted: mek });

                        const control = { proc: null, cancelled: false };
                        activeIptvRecordings.set(chatId, control);

                        const MAX_RECONNECT_ATTEMPTS = 15;

                        (async () => {
                            let segmentIndex = 0;
                            let abortedBySize = false;
                            let wasCancelled = false;
                            let remainingSec = totalDurationSec;
                            let attempt = 0;
                            let reconnectedCount = 0;

                            const onSegmentReady = async (filePath) => {
                                segmentIndex++;
                                try {
                                    const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: filePath },
                                        mimetype: 'video/mp4',
                                        fileName: `IptvMatch_${streamId}_part${segmentIndex}.mp4`,
                                        caption: `📦 *الجزء ${segmentIndex}*\n📺 ${channel.name}\n⚖️ ${sizeMB} MB`
                                    }, { quoted: mek });
                                } catch (e) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ فشل إرسال الجزء ${segmentIndex}: ${e.message}`
                                    }, { quoted: mek });
                                } finally {
                                    try { fs.unlinkSync(filePath); } catch (_) {}
                                }
                            };

                            try {
                                while (remainingSec > 60 && attempt < MAX_RECONNECT_ATTEMPTS && !control.cancelled) {
                                    attempt++;
                                    const startTs = Date.now();

                                    const result = await recordContinuousSegmented(
                                        streamUrl, segDir, `iptv_part_a${attempt}`, remainingSec, segmentTimeSec,
                                        onSegmentReady, control
                                    );

                                    const elapsedSec = Math.floor((Date.now() - startTs) / 1000);
                                    remainingSec -= elapsedSec;

                                    abortedBySize = result.abortedBySize;
                                    wasCancelled = result.cancelled;

                                    if (wasCancelled || abortedBySize) break;
                                    if (remainingSec <= 60) break;

                                    reconnectedCount++;
                                    const backoffMs = Math.min(3000 * Math.pow(2, Math.min(reconnectedCount - 1, 5)), 60000);
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ *انقطع الاتصال بالبث بشكل غير متوقع.*\n⏱️ الوقت المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🔄 جاري إعادة الاتصال بعد ${Math.round(backoffMs / 1000)} ثانية... (محاولة ${attempt + 1}/${MAX_RECONNECT_ATTEMPTS})`
                                    }, { quoted: mek });
                                    await new Promise(r => setTimeout(r, backoffMs));
                                }

                                if (!wasCancelled && !abortedBySize && attempt >= MAX_RECONNECT_ATTEMPTS && remainingSec > 60) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ تعذر إكمال التسجيل بعد ${MAX_RECONNECT_ATTEMPTS} محاولات إعادة اتصال. قد تكون القناة غير مستقرة حالياً.`
                                    }, { quoted: mek });
                                }
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في التسجيل: ${err.message}`
                                }, { quoted: mek });
                            } finally {
                                activeIptvRecordings.delete(chatId);
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }

                            if (wasCancelled) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إلغاء تسجيل IPTV الثابت بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${segmentIndex}`
                                }, { quoted: mek });
                            } else if (abortedBySize) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إيقاف التسجيل مبكراً!*\nجودة البث كانت أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن للتخزين المتاح.\n📦 عدد الأجزاء المُرسلة قبل التوقف: ${segmentIndex}\n\n💡 جرّب تقليل مدة الجزء (مثال: \`.recordiptv ${streamId} ${duration} 3\`) للحصول على أجزاء أصغر تلائم جودة هذا البث.`
                                }, { quoted: mek });
                            } else {
                                const reconnectNote = reconnectedCount > 0 ? `\n🔄 حدثت ${reconnectedCount} إعادة اتصال بسبب انقطاعات مؤقتة في البث.` : '';
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `✅ *اكتمل التسجيل الكامل!*\n📺 القناة: ${channel.name}\n📦 عدد الأجزاء المُرسلة: ${segmentIndex}${reconnectNote}`
                                }, { quoted: mek });
                            }
                        })();
                        return;
                    }

                    // ── أوامر الطرفية: .$ (تنفيذ) / .killcmd (إيقاف) / .cwd (عرض مجلد العمل الحالي) — للمالك فقط، في الخاص فقط ──
                    if (command === '.$' || command === '.sh' || command === '.killcmd' || command === '.cwd') {
                        if (!isStrictOwner(mek, chatId)) {
                            // لا نكشف وجود الأمر: صمت تام لغير المالك يمنع الاستكشاف
                            return;
                        }

                        if (command === '.cwd') {
                            await XeonBotInc.sendMessage(chatId, { text: `📁 مجلد العمل الحالي:\n\`${shellResolveCwd(chatId)}\`` }, { quoted: mek });
                            return;
                        }

                        if (command === '.killcmd') {
                            const active = SHELL_ACTIVE.get(chatId);
                            if (!active) {
                                await XeonBotInc.sendMessage(chatId, { text: 'ℹ️ لا يوجد أمر قيد التنفيذ حالياً.' }, { quoted: mek });
                            } else {
                                active.kill('SIGKILL');
                                await XeonBotInc.sendMessage(chatId, { text: `🛑 أُوقف الأمر:\n\`${active.cmd}\`` }, { quoted: mek });
                            }
                            return;
                        }

                        // .$ أو .sh
                        if (!query.trim()) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة: `.$ [أمر لينكس]`\n💡 أمثلة:\n`.$ ls -la`\n`.$ cd /var/log && tail -n 50 syslog`\n`.$ apt install -y htop`  (تُضاف `-y` تلقائياً عند الحاجة)\n⏱️ مهلة افتراضية 60 ثانية. لمهلة مخصصة: `.$ --t=180 أمر طويل`\n⏹️ لإيقاف أمر قيد التنفيذ: `.killcmd`'
                            }, { quoted: mek });
                            return;
                        }
                        if (SHELL_ACTIVE.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, { text: '⏳ يوجد أمر قيد التنفيذ بالفعل. استخدم `.killcmd` لإيقافه أولاً.' }, { quoted: mek });
                            return;
                        }

                        let cmdText = query;
                        let timeoutMs = SHELL_DEFAULT_TIMEOUT_MS;
                        const tMatch = cmdText.match(/^--t=(\d+)\s+/);
                        if (tMatch) {
                            timeoutMs = Math.min(parseInt(tMatch[1]) * 1000, SHELL_MAX_TIMEOUT_MS);
                            cmdText = cmdText.slice(tMatch[0].length);
                        }

                        // تثبيت الحزم: نضيف -y تلقائياً إن لم تكن موجودة، لتفادي تعليق التنفيذ بسؤال تفاعلي
                        if (/^\s*(sudo\s+)?(apt|apt-get)\s+(install|remove|purge|upgrade|dist-upgrade|full-upgrade)\b/.test(cmdText) && !/\s-y\b|\s--yes\b/.test(cmdText)) {
                            cmdText = cmdText.replace(/(apt|apt-get)(\s+)(install|remove|purge|upgrade|dist-upgrade|full-upgrade)/, '$1$2$3 -y');
                        }
                        if (/^\s*(sudo\s+)?(yum|dnf)\s+(install|remove|update)\b/.test(cmdText) && !/\s-y\b/.test(cmdText)) {
                            cmdText = cmdText.replace(/(yum|dnf)(\s+)(install|remove|update)/, '$1$2$3 -y');
                        }
                        if (/^\s*(sudo\s+)?apk\s+add\b/.test(cmdText)) {
                            // apk add لا تطلب تأكيداً أصلاً
                        }

                        const startedAt = Date.now();
                        const safeCmdForCaption = cmdText.length > 150 ? cmdText.slice(0, 150) + '…' : cmdText;
                        const result = await runShellCommand(chatId, cmdText, timeoutMs);
                        const elapsed = ((Date.now() - startedAt) / 1000).toFixed(1);

                        let statusLine;
                        if (result.timedOut) statusLine = `⏱️ انتهت المهلة (${(timeoutMs / 1000).toFixed(0)}s) وأُوقف الأمر`;
                        else if (result.code === 0) statusLine = `✅ انتهى بنجاح`;
                        else statusLine = `❌ رمز الخروج: ${result.code}${result.signal ? ` (إشارة ${result.signal})` : ''}`;

                        const header = `💻 \`${safeCmdForCaption}\`\n📁 ${result.cwd}\n${statusLine} | ⏱️ ${elapsed}s${result.truncated ? '\n⚠️ الناتج أكبر من الحد الداخلي وقُصَّ' : ''}`;
                        const body = result.output || '(لا يوجد ناتج)';

                        if (body.length <= SHELL_OUTPUT_LIMIT) {
                            await XeonBotInc.sendMessage(chatId, { text: `${header}\n\n\`\`\`\n${body}\n\`\`\`` }, { quoted: mek });
                        } else {
                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });
                            const outFile = path.join(tmpDir, `sh_${randomBytes(4).toString('hex')}.txt`);
                            fs.writeFileSync(outFile, result.output);
                            await XeonBotInc.sendMessage(chatId, {
                                document: { url: outFile },
                                mimetype: 'text/plain',
                                fileName: 'output.txt',
                                caption: header
                            }, { quoted: mek });
                            try { fs.unlinkSync(outFile); } catch (_) {}
                        }
                        return;
                    }

                    // ── أمر .ytlive [رابط] [الدقائق] [الجودة] [مدة الجزء] [-y] : تسجيل بث مباشر على أجزاء (نسخ مباشر بلا إعادة ترميز) ──
                    if (command === '.ytlive') {
                        const { main: lMainQuery, extra: lExtraFlags } = splitYtExtraFlags(query);
                        const lp = lMainQuery.split(' ').filter(Boolean);
                        const lSkip = lp.includes('-y');
                        const la = lp.filter(x => x !== '-y');
                        const lUrl = la[0];
                        const lMin = parseInt(la[1]);
                        const lMode = (la[2] || '720').toLowerCase();
                        const lSegMin = la[3] !== undefined ? parseInt(la[3]) : null;
                        if (!lUrl || !/^https?:\/\//i.test(lUrl) || !lMin || lMin < 1 || lMin > 360 || !/^(audio|\d{3,4})$/.test(lMode) || (lSegMin !== null && (!(lSegMin >= 1) || lSegMin > lMin))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.ytlive [رابط البث] [عدد الدقائق] [الجودة] [مدة الجزء بالدقائق]`\n💡 الدقائق من 1 إلى 360. الجودة اختيارية: `audio` أو `360` أو `480` أو `720` (الافتراضي) أو `1080`\n📦 مدة الجزء اختيارية؛ إن لم تحددها يُحسب تلقائياً (~' + RECORD_TARGET_MB + ' MB لكل جزء).\n🎞️ التسجيل نسخ مباشر بدون أي ضغط أو إعادة ترميز.\n🔧 فلاغات yt-dlp إضافية: `.ytlive رابط 60 720 -- --proxy http://x`\nأضف `-y` لتخطي سؤال التأكيد.\nمثال: `.ytlive https://youtube.com/watch?v=xxxx 120 480` أو `.ytlive https://youtube.com/watch?v=xxxx 120 480 10`\n⏹️ للإيقاف وإرسال ما سُجّل: `.stopytdl`'
                            }, { quoted: mek });
                            return;
                        }
                        if (ytActive.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, { text: '⏳ يوجد تحميل أو تسجيل جارٍ بالفعل. استخدم `.stopytdl`.' }, { quoted: mek });
                            return;
                        }

                        const lTmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(lTmpDir)) fs.mkdirSync(lTmpDir, { recursive: true });
                        const lId = randomBytes(4).toString('hex');
                        const lBase = ['--no-playlist', '--no-warnings', '--no-colors', '--newline', '--js-runtimes', 'node'];
                        const lCookies = path.join(process.cwd(), 'cookies.txt');
                        if (fs.existsSync(lCookies)) lBase.push('--cookies', lCookies);
                        const lFmt = lMode === 'audio'
                            ? ['-f', 'ba/b']
                            : ['-f', `b[height<=${lMode}]/bv*[height<=${lMode}]+ba/b`];
                        const lAudio = lMode === 'audio';

                        const lTry = async (fn) => {
                            try { return await fn([]); }
                            catch (e) {
                                if (!/403|Forbidden/i.test(e.message)) throw e;
                                console.log('[YTLIVE] 403 -> retry with --impersonate chrome');
                                let origin = '';
                                try { origin = new URL(lUrl).origin + '/'; } catch (_) {}
                                return await fn(['--impersonate', 'chrome', ...(origin ? ['--referer', origin] : [])]);
                            }
                        };
                        // معلومات البث + روابط التسجيل الحالية (تُجدَّد عند كل إعادة اتصال لأن الروابط تنتهي صلاحيتها)
                        const lGetLive = async (holder = null) => {
                            const raw = await lTry((ex) => runYtDlp([...lBase, ...ex, ...lFmt, ...lExtraFlags, '--dump-single-json', lUrl], null, 120000, holder));
                            const j = JSON.parse(raw.slice(raw.indexOf('{')));
                            const fl = j.requested_formats || [j];
                            const urls = fl.map(f => f.url).filter(u => /^https?:\/\//i.test(u || ''));
                            return { j, urls };
                        };

                        let lTitle = 'live';
                        let lSegSec = RECORD_DEFAULT_SEGMENT_MIN * 60;

                        const lRunJob = async () => {
                            const state = { holder: {}, cancelled: false, early: false, kind: 'live' };
                            ytActive.set(chatId, state);
                            const segDir = path.join(lTmpDir, `ytlive_${lId}`);
                            fs.mkdirSync(segDir, { recursive: true });
                            let partNo = 0, abortedBySize = false, endedLive = false, reconnects = 0, lastErr = '';
                            try {
                                const lSafe = String(lTitle || 'live').replace(/[\\/:*?"<>|]+/g, '').slice(0, 80).trim() || 'live';

                                // يُستدعى لكل جزء فور اكتماله: remux بنسخ مباشر إلى mp4/m4a (بدون إعادة ترميز) ثم الإرسال
                                const onSegmentReady = async (filePath) => {
                                    partNo++;
                                    const myNo = partNo;
                                    const outExt = lAudio ? '.m4a' : '.mp4';
                                    const outPath = filePath.replace(/\.ts$/, outExt);
                                    let sendPath = filePath, mime = 'video/mp2t', ext = '.ts';
                                    try {
                                        const mx = await runFfmpeg(['-y', '-hide_banner', '-loglevel', 'error', '-i', filePath, '-c', 'copy', ...(lAudio ? [] : ['-movflags', '+faststart']), outPath], null, null, 10 * 60 * 1000);
                                        if (mx.code === 0 && fs.existsSync(outPath) && fs.statSync(outPath).size > 0) {
                                            sendPath = outPath; ext = outExt; mime = lAudio ? 'audio/mp4' : 'video/mp4';
                                        } else {
                                            console.log(`[YTLIVE] remux failed (part ${myNo}), sending .ts: ${mx.err.split('\n').pop()}`);
                                        }
                                        const size = fs.statSync(sendPath).size;
                                        const sizeMB = (size / 1048576).toFixed(2);
                                        if (size > 2000 * 1048576) throw new Error(`الجزء (${sizeMB} MB) يتجاوز حد واتساب 2 جيجا.`);
                                        await XeonBotInc.sendMessage(chatId, {
                                            document: { url: sendPath },
                                            mimetype: mime,
                                            fileName: `${lSafe}_part${myNo}${ext}`,
                                            caption: `📦 *الجزء ${myNo}*\n🔴 ${lTitle}\n⚖️ ${sizeMB} MB`
                                        }, { quoted: mek });
                                        console.log(`[YTLIVE] part ${myNo} sent | ${sizeMB} MB`);
                                    } catch (e) {
                                        await XeonBotInc.sendMessage(chatId, { text: `⚠️ فشل إرسال الجزء ${myNo}: ${e.message}` }, { quoted: mek });
                                    } finally {
                                        try { fs.unlinkSync(filePath); } catch (_) {}
                                        try { fs.unlinkSync(outPath); } catch (_) {}
                                    }
                                };

                                await XeonBotInc.sendMessage(chatId, { text: `🔴 *بدأ تسجيل البث لمدة ${lMin} دقيقة...*\n🎬 ${lTitle}\n📦 كل جزء: ~${Math.max(1, Math.round(lSegSec / 60))} دقيقة\n⏹️ للإيقاف المبكر وإرسال ما سُجّل: \`.stopytdl\`` }, { quoted: mek });

                                const MAX_ATTEMPTS = 8;
                                let remainingSec = lMin * 60;
                                let attempt = 0;
                                while (remainingSec > 60 && attempt < MAX_ATTEMPTS && !state.early) {
                                    attempt++;
                                    const startTs = Date.now();

                                    let info;
                                    try {
                                        info = await lGetLive(state.holder);
                                    } catch (e) {
                                        if (state.early) break;
                                        if (attempt === 1) throw e;
                                        lastErr = e.message;
                                        console.log(`[YTLIVE] refresh failed: ${e.message}`);
                                        await new Promise(r => setTimeout(r, 10000));
                                        remainingSec -= Math.floor((Date.now() - startTs) / 1000);
                                        continue;
                                    }
                                    if (state.early) break;
                                    if (!info.j.is_live) { endedLive = true; break; } // انتهى البث، لا نسجّل الإعادة
                                    if (!info.urls.length) throw new Error('تعذر الحصول على رابط البث.');

                                    console.log(`[YTLIVE] recording attempt ${attempt} | remaining ${remainingSec}s | seg ${lSegSec}s | ${lTitle}`);
                                    const result = await recordLiveSegments(info.urls, segDir, `a${attempt}`, remainingSec, lSegSec, lAudio, onSegmentReady, state);
                                    if (result.stderr) lastErr = result.stderr.split('\n').filter(Boolean).pop() || lastErr;

                                    remainingSec -= Math.floor((Date.now() - startTs) / 1000);
                                    abortedBySize = result.abortedBySize;
                                    if (state.early || abortedBySize || remainingSec <= 60) break;

                                    // توقف غير متوقع مع بقاء وقت → أعد الاتصال بتأخير تصاعدي
                                    reconnects++;
                                    const backoffMs = Math.min(3000 * Math.pow(2, Math.min(reconnects - 1, 5)), 60000);
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ *انقطع الاتصال بالبث.*\n⏱️ المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🔄 إعادة الاتصال بعد ${Math.round(backoffMs / 1000)} ثانية... (محاولة ${attempt + 1}/${MAX_ATTEMPTS})`
                                    }, { quoted: mek });
                                    await new Promise(r => setTimeout(r, backoffMs));
                                }

                                if (partNo === 0 && !state.early) {
                                    throw new Error(lastErr || (endedLive ? 'انتهى البث قبل أن يبدأ التسجيل.' : 'لم يتم تسجيل أي بيانات (قد يكون البث غير متاح).'));
                                }

                                if (state.early) {
                                    await XeonBotInc.sendMessage(chatId, { text: `⏹️ *تم إيقاف التسجيل بطلبك.*\n🎬 ${lTitle}\n📦 عدد الأجزاء المُرسلة: ${partNo}` }, { quoted: mek });
                                } else if (abortedBySize) {
                                    await XeonBotInc.sendMessage(chatId, { text: `🛑 *تم إيقاف التسجيل مبكراً!*\nجودة البث أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن.\n📦 عدد الأجزاء المُرسلة: ${partNo}\n\n💡 جرّب جودة أقل أو مدة جزء أقصر (مثال: \`.ytlive ${lUrl} ${lMin} ${lMode} 3\`).` }, { quoted: mek });
                                } else if (endedLive) {
                                    await XeonBotInc.sendMessage(chatId, { text: `📴 *انتهى البث قبل اكتمال المدة المطلوبة.*\n🎬 ${lTitle}\n📦 عدد الأجزاء المُرسلة: ${partNo}` }, { quoted: mek });
                                } else {
                                    const rn = reconnects > 0 ? `\n🔄 حدثت ${reconnects} إعادة اتصال.` : '';
                                    await XeonBotInc.sendMessage(chatId, { text: `✅ *اكتمل تسجيل البث!*\n🎬 ${lTitle}\n📦 عدد الأجزاء المُرسلة: ${partNo}${rn}` }, { quoted: mek });
                                }
                                console.log(`[YTLIVE] done | parts=${partNo}`);
                            } catch (err) {
                                console.log(`[YTLIVE] failed: ${err.message}`);
                                await XeonBotInc.sendMessage(chatId, { text: `❌ فشل تسجيل البث:\n\`${err.message}\`${partNo ? `\n📦 الأجزاء المُرسلة قبل الفشل: ${partNo}` : ''}` }, { quoted: mek });
                            } finally {
                                ytActive.delete(chatId);
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }
                        };

                        // ── فحص الرابط والتأكد أنه بث مباشر ──
                        try {
                            await XeonBotInc.sendMessage(chatId, { text: '🔎 جاري فحص البث...' }, { quoted: mek });
                            const { j } = await lGetLive();
                            lTitle = j.title || 'live';
                            const fl = j.requested_formats || [j];
                            const tbr = fl.reduce((a, f) => a + (f.tbr || 0), 0);
                            const estBytes = tbr ? tbr * 1000 / 8 * lMin * 60 : 0;
                            const res = j.resolution || (j.height ? `${j.width || '?'}x${j.height}` : (lAudio ? 'صوت' : '?'));
                            lSegSec = lSegMin !== null ? lSegMin * 60 : computeSegmentTimeSec(tbr ? tbr * 1000 : null);
                            console.log(`[YTLIVE] info: ${lTitle} | live=${!!j.is_live} | ${res} | est ~${fmtBytes(estBytes)} for ${lMin}min | seg ${lSegSec}s`);

                            if (!j.is_live) {
                                // ليس بثاً مباشراً الآن: نحمّله كفيديو عادي ونرسله (بدل رفض الطلب)
                                const lDlFiles = j.requested_formats || [j];
                                let lDlTotal = 0, lDlApprox = false;
                                for (const f of lDlFiles) {
                                    const sz = f.filesize || f.filesize_approx;
                                    if (sz) { lDlTotal += sz; if (!f.filesize) lDlApprox = true; } else lDlApprox = true;
                                }
                                if (!lDlTotal) {
                                    const lDlTbr = lDlFiles.reduce((a, f) => a + (f.tbr || 0), 0);
                                    if (lDlTbr && j.duration) { lDlTotal = lDlTbr * 1000 / 8 * j.duration; lDlApprox = true; }
                                }
                                if (lDlTotal > 2000 * 1048576) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `🎬 *${lTitle}*\n\nℹ️ هذا الرابط ليس بثاً مباشراً، وحجمه كفيديو عادي يتجاوز حد واتساب (2 جيجا) ولن يمكن إرساله.\n⚖️ الحجم التقريبي: ${fmtBytes(lDlTotal)}\n💡 جرّب جودة أقل، مثل: \`.ytlive ${lUrl} ${lMin} 480\``
                                    }, { quoted: mek });
                                    return;
                                }
                                const lDlInfoText = `🎬 *${lTitle}*\nℹ️ هذا الرابط ليس بثاً مباشراً الآن، سيُحمَّل كفيديو عادي ويُرسل.\n📐 الدقة: ${res} (${lMode})\n⚖️ الحجم${lDlApprox ? ' التقريبي' : ''}: *${fmtBytes(lDlTotal)}*`;
                                const lDlRunJob = async () => {
                                    if (ytActive.has(chatId)) {
                                        await XeonBotInc.sendMessage(chatId, { text: '⏳ يوجد تحميل أو تسجيل جارٍ بالفعل. استخدم `.stopytdl`.' }, { quoted: mek });
                                        return;
                                    }
                                    await ytDownloadAndSendJob(XeonBotInc, chatId, mek, lUrl, lMode, lExtraFlags, [], lTitle);
                                };
                                if (lSkip) {
                                    await XeonBotInc.sendMessage(chatId, { text: lDlInfoText }, { quoted: mek });
                                    await lDlRunJob();
                                } else {
                                    ytPending.set(chatId, { run: lDlRunJob, expires: Date.now() + 2 * 60 * 1000 });
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `${lDlInfoText}\n\n❓ هل تريد التحميل؟\n✅ للتحميل: \`.ytgo\`\n🚫 للإلغاء: \`.ytno\`\n_(ينتهي الطلب بعد دقيقتين)_`
                                    }, { quoted: mek });
                                }
                                return;
                            }

                            const infoText = `🔴 *${lTitle}*\n📐 الدقة: ${res} (${lMode})\n🎞️ نسخ مباشر بدون ضغط أو إعادة ترميز\n⏱️ مدة التسجيل: ${lMin} دقيقة\n📦 كل جزء: ~${Math.max(1, Math.round(lSegSec / 60))} دقيقة\n⚖️ الحجم الكلي المتوقع${estBytes ? ' (تقريبي)' : ''}: *${fmtBytes(estBytes)}*`;

                            if (lSkip) {
                                await XeonBotInc.sendMessage(chatId, { text: infoText }, { quoted: mek });
                                await lRunJob();
                            } else {
                                ytPending.set(chatId, { run: lRunJob, expires: Date.now() + 2 * 60 * 1000 });
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `${infoText}\n\n❓ هل تريد بدء التسجيل؟\n✅ للبدء: \`.ytgo\`\n🚫 للإلغاء: \`.ytno\`\n_(ينتهي الطلب بعد دقيقتين)_`
                                }, { quoted: mek });
                            }
                        } catch (err) {
                            console.log(`[YTLIVE] failed: ${err.message}`);
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل فحص البث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .ytsearch [عدد النتائج] [كلمات البحث] : بحث في يوتيوب بدون تحميل ──
                    if (command === '.ytsearch' || command === '.yts') {
                        const sParts = query.split(' ').filter(Boolean);
                        let sCount = 5;
                        let sQueryWords = sParts;
                        if (sParts[0] && /^\d+$/.test(sParts[0])) {
                            sCount = Math.min(Math.max(parseInt(sParts[0]), 1), 15);
                            sQueryWords = sParts.slice(1);
                        }
                        const sQuery = sQueryWords.join(' ').trim();
                        if (!sQuery) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.ytsearch [عدد النتائج] [كلمات البحث]`\n💡 عدد النتائج اختياري (1 إلى 15، الافتراضي 5).\nمثال: `.ytsearch 8 شرح البرمجة بايثون`'
                            }, { quoted: mek });
                            return;
                        }

                        await XeonBotInc.sendMessage(chatId, { text: `🔎 جاري البحث عن: *${sQuery}*...` }, { quoted: mek });
                        try {
                            const sBase = ['--no-warnings', '--no-colors', '--flat-playlist', '--js-runtimes', 'node'];
                            const sCookies = path.join(process.cwd(), 'cookies.txt');
                            if (fs.existsSync(sCookies)) sBase.push('--cookies', sCookies);
                            const raw = await runYtDlp(
                                [...sBase, '--dump-single-json', `ytsearch${sCount}:${sQuery}`],
                                null, 60000
                            );
                            const data = JSON.parse(raw.slice(raw.indexOf('{')));
                            const entries = (data.entries || []).filter(Boolean);
                            if (!entries.length) {
                                await XeonBotInc.sendMessage(chatId, { text: `😕 لا توجد نتائج لـ: *${sQuery}*` }, { quoted: mek });
                                return;
                            }

                            const fmtDur = (secs) => {
                                if (!secs && secs !== 0) return '؟';
                                secs = Math.round(secs);
                                const h = Math.floor(secs / 3600), m = Math.floor((secs % 3600) / 60), s = secs % 60;
                                return h > 0 ? `${h}:${String(m).padStart(2, '0')}:${String(s).padStart(2, '0')}` : `${m}:${String(s).padStart(2, '0')}`;
                            };

                            const lines = entries.map((e, i) => {
                                const url = e.webpage_url || e.url || (e.id ? `https://youtube.com/watch?v=${e.id}` : '');
                                const viewsFmt = fmtCount(e.view_count);
                                const views = viewsFmt ? `👁️ ${viewsFmt}` : '';
                                return `*${i + 1}.* ${e.title || 'بدون عنوان'}\n📺 ${e.channel || e.uploader || '؟'} | ⏱️ ${fmtDur(e.duration)}${views ? ' | ' + views : ''}\n🔗 ${url}`;
                            });
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔎 *نتائج البحث عن:* ${sQuery}\n\n${lines.join('\n\n')}\n\n💡 لتحميل أي نتيجة: \`.ytdl [الرابط]\` أو \`.ytlive [الرابط]\` إن كان بثاً مباشراً.`
                            }, { quoted: mek });
                        } catch (err) {
                            console.log(`[YTSEARCH] failed: ${err.message}`);
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أوامر yt-dlp: .ytdl / .ytgo / .ytno / .stopytdl ──
                    if (command === '.stopytdl') {
                        const st = ytActive.get(chatId);
                        if (!st) {
                            await XeonBotInc.sendMessage(chatId, { text: 'ℹ️ لا يوجد تحميل ytdl نشط في هذه المحادثة.' }, { quoted: mek });
                            return;
                        }
                        if (st.kind === 'live') {
                            st.early = true;
                            try { if (st.holder.proc) st.holder.proc.kill('SIGINT'); } catch (_) {}
                            console.log('[YTLIVE] stop requested (will send what was recorded)');
                            await XeonBotInc.sendMessage(chatId, { text: '⏹️ جاري إيقاف التسجيل وإرسال ما تم تسجيله...' }, { quoted: mek });
                            return;
                        }
                        st.cancelled = true;
                        try { if (st.holder.proc) st.holder.proc.kill('SIGKILL'); } catch (_) {}
                        console.log('[YTDL] stopped by user');
                        return;
                    }

                    if (command === '.ytno') {
                        const had = ytPending.delete(chatId);
                        await XeonBotInc.sendMessage(chatId, { text: had ? '🚫 تم إلغاء طلب التحميل.' : 'ℹ️ لا يوجد طلب معلّق.' }, { quoted: mek });
                        return;
                    }

                    if (command === '.ytgo') {
                        const pd = ytPending.get(chatId);
                        if (!pd || Date.now() > pd.expires) {
                            ytPending.delete(chatId);
                            await XeonBotInc.sendMessage(chatId, { text: '⌛ لا يوجد طلب معلّق أو انتهت صلاحيته. أعد إرسال `.ytdl [رابط]`.' }, { quoted: mek });
                            return;
                        }
                        if (ytActive.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, { text: '⏳ يوجد تحميل جارٍ بالفعل. استخدم `.stopytdl` لإيقافه.' }, { quoted: mek });
                            return;
                        }
                        ytPending.delete(chatId);
                        await pd.run();
                        return;
                    }

                    // ── أمر .ytdl [رابط] [audio|360|480|720|1080] [-y] ──
                    if (command === '.ytdl') {
                        const { main: ytMainQuery, extra: ytExtraFlags } = splitYtExtraFlags(query);
                        const ytParts = ytMainQuery.split(' ').filter(Boolean);
                        const ytSkipConfirm = ytParts.includes('-y');
                        const ytArgs = ytParts.filter(x => x !== '-y');
                        const ytUrl = ytArgs[0];
                        const ytMode = (ytArgs[1] || '720').toLowerCase();
                        if (!ytUrl || !/^https?:\/\//i.test(ytUrl) || !/^(audio|\d{3,4})$/.test(ytMode)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.ytdl [رابط] [الجودة]`\n💡 الجودة اختيارية: `audio` أو `360` أو `480` أو `720` (الافتراضي) أو `1080`\nأضف `-y` لتخطي سؤال التأكيد.\n🔧 فلاغات yt-dlp إضافية: `.ytdl رابط 720 -- --proxy http://x --limit-rate 2M`\nمثال: `.ytdl https://youtu.be/xxxx 480`\n⛔ لإيقاف تحميل جارٍ: `.stopytdl`'
                            }, { quoted: mek });
                            return;
                        }
                        if (ytActive.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, { text: '⏳ يوجد تحميل جارٍ بالفعل. استخدم `.stopytdl` لإيقافه.' }, { quoted: mek });
                            return;
                        }

                        const ytTmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(ytTmpDir)) fs.mkdirSync(ytTmpDir, { recursive: true });
                        const ytId = randomBytes(4).toString('hex');
                        const ytBase = ['--no-playlist', '--no-warnings', '--no-colors', '--newline', '--js-runtimes', 'node'];
                        const ytCookies = path.join(process.cwd(), 'cookies.txt');
                        if (fs.existsSync(ytCookies)) ytBase.push('--cookies', ytCookies);

                        const ytFmt = ytMode === 'audio'
                            ? ['-x', '--audio-format', 'mp3', '--audio-quality', '0']
                            : ['-f', `bv*[height<=${ytMode}][vcodec^=avc1]+ba[acodec^=mp4a]/b[height<=${ytMode}][ext=mp4]/bv*[height<=${ytMode}]+ba/b`, '--merge-output-format', 'mp4'];

                        let ytUsed = [];
                        // عند خطأ 403 نعيد المحاولة تلقائياً بمحاكاة متصفح Chrome و Referer
                        const ytTry = async (fn) => {
                            try { ytUsed = []; return await fn([]); }
                            catch (e) {
                                if (!/403|Forbidden/i.test(e.message)) throw e;
                                console.log('[YTDL] 403 -> retry with --impersonate chrome');
                                let origin = '';
                                try { origin = new URL(ytUrl).origin + '/'; } catch (_) {}
                                ytUsed = ['--impersonate', 'chrome', ...(origin ? ['--referer', origin] : [])];
                                return await fn(ytUsed);
                            }
                        };

                        let ytTitle = 'video';
                        // ── تنفيذ التحميل الفعلي (بعد التأكيد) ──
                        const ytRunJob = async () => {
                            if (ytActive.has(chatId)) {
                                await XeonBotInc.sendMessage(chatId, { text: '⏳ يوجد تحميل أو تسجيل جارٍ بالفعل. استخدم `.stopytdl`.' }, { quoted: mek });
                                return;
                            }
                            await ytDownloadAndSendJob(XeonBotInc, chatId, mek, ytUrl, ytMode, ytExtraFlags, ytUsed, ytTitle);
                        };

                        // ── فحص الرابط وعرض الحجم قبل التحميل ──
                        try {
                            await XeonBotInc.sendMessage(chatId, { text: '🔎 جاري فحص الرابط...' }, { quoted: mek });
                            const raw = await ytTry((ex) => runYtDlp([...ytBase, ...ex, ...ytFmt, ...ytExtraFlags, '--dump-single-json', ytUrl], null, 120000));
                            const j = JSON.parse(raw.slice(raw.indexOf('{')));
                            ytTitle = j.title || 'video';
                            const fl = j.requested_formats || [j];
                            let total = 0, approx = false;
                            for (const f of fl) {
                                const sz = f.filesize || f.filesize_approx;
                                if (sz) { total += sz; if (!f.filesize) approx = true; } else approx = true;
                            }
                            if (!total) {
                                const tbr = fl.reduce((a, f) => a + (f.tbr || 0), 0);
                                if (tbr && j.duration) { total = tbr * 1000 / 8 * j.duration; approx = true; }
                            }
                            const res = j.resolution || (j.height ? `${j.width || '?'}x${j.height}` : (ytMode === 'audio' ? 'صوت' : '?'));
                            console.log(`[YTDL] info: ${ytTitle} | ${j.duration_string || '?'} | ${res} | ~${fmtBytes(total)} | mode=${ytMode} | live=${!!j.is_live}`);

                            const infoText = `🎬 *${ytTitle}*\n⏱️ المدة: ${j.duration_string || 'غير معروفة'}\n📐 الدقة: ${res} (${ytMode})\n⚖️ الحجم${approx ? ' التقريبي' : ''}: *${fmtBytes(total)}*`;

                            if (j.is_live) {
                                await XeonBotInc.sendMessage(chatId, { text: `${infoText}\n\n🔴 هذا بث مباشر ولا يُحمّل بهذا الأمر.` }, { quoted: mek });
                                return;
                            }
                            if (total > 2000 * 1048576) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `${infoText}\n\n⚠️ الحجم يتجاوز حد واتساب (2 جيجا) ولن يمكن إرساله.\n💡 جرّب جودة أقل مثل: \`.ytdl ${ytUrl} 480\` أو \`audio\``
                                }, { quoted: mek });
                                return;
                            }

                            if (ytSkipConfirm) {
                                await XeonBotInc.sendMessage(chatId, { text: infoText }, { quoted: mek });
                                await ytRunJob();
                            } else {
                                ytPending.set(chatId, { run: ytRunJob, expires: Date.now() + 2 * 60 * 1000 });
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `${infoText}\n\n❓ هل تريد التحميل؟\n✅ للتحميل: \`.ytgo\`\n🚫 للإلغاء: \`.ytno\`\n_(ينتهي الطلب بعد دقيقتين)_`
                                }, { quoted: mek });
                            }
                        } catch (err) {
                            console.log(`[YTDL] failed: ${err.message}`);
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل فحص الرابط:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .download (يدعم الروابط المباشرة و Google Drive تلقائياً) ──
                    if (command === '.download') {
                        if (!query || (!query.startsWith('http://') && !query.startsWith('https://'))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة خاطئة!\n`.download [رابط مباشر أو رابط Google Drive]`'
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        let result;
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚡ *بدأ التحميل...*`
                            }, { quoted: mek });

                            const _dlUrl = query.split(' ')[0];
                            const _dlStart = Date.now();
                            console.log(`[DOWNLOAD] start: ${_dlUrl}`);
                            result = await smartDownloadUrl(_dlUrl, tmpDir, 'File');
                            console.log(`[DOWNLOAD] done: ${result.sizeMB} MB | ${result.fileExt} | ${((Date.now() - _dlStart) / 1000).toFixed(1)}s`);

                            await XeonBotInc.sendMessage(chatId, {
                                document: { url: result.outputPath },
                                mimetype: result.mimeType,
                                fileName: `File${result.fileExt}`,
                                caption: `✅ *اكتمل التحميل!*\n⚖️ *الحجم:* ${result.sizeMB} MB${result.isGoogleDrive ? '\n☁️ المصدر: Google Drive' : ''}`
                            }, { quoted: mek });

                        } catch (err) {
                            console.log(`[DOWNLOAD] failed: ${err.message}`);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل التحميل:\n\`${err.message}\`\n\n💡 إذا كان الخطأ 503/502: السيرفر مزدحم أو مطفأ مؤقتاً — جرّب بعد قليل أو تأكد أن الرابط يعمل في المتصفح.`
                            }, { quoted: mek });
                        } finally {
                            if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                try { fs.unlinkSync(result.outputPath); } catch (_) {}
                            }
                        }
                        return;
                    }

                    // ── أمر .cleanremote : حذف إصدارات split-* المتراكمة على GitHub (للمالك فقط، فهو حذف فعلي لا رجعة فيه) ──
                    if (command === '.cleanremote') {
                        if (!isStrictOwner(mek, chatId)) return; // صمت تام: حذف فعلي خطير، لا نكشف وجود الأمر لغير المالك
                        if (!REMOTE_DL_CONFIG.token || !REMOTE_DL_CONFIG.owner || !REMOTE_DL_CONFIG.repo) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ لم يتم ضبط إعدادات Remote Downloader بعد. استخدم `.setremotedl` أولاً.'
                            }, { quoted: mek });
                            return;
                        }

                        const arg = query.trim();
                        try {
                            const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/releases?per_page=100`;
                            const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
                            const releases = res.data || [];
                            const matching = releases.filter(r => isSplitReleaseTag(r.tag_name));
                            const sizeOf = (r) => (r.assets || []).reduce((s, a) => s + (a.size || 0), 0);

                            // حذف إصدار واحد محدد بالاسم (يجب أن يطابق نمط split-* حتى لا يُحذف أي إصدار حقيقي آخر بالخطأ)
                            if (arg && arg !== 'confirm') {
                                if (!isSplitReleaseTag(arg)) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ \`${arg}\` لا يطابق نمط إصدارات split_upload.py، فلن يُحذف تفادياً لحذف إصدار حقيقي بالخطأ.`
                                    }, { quoted: mek });
                                    return;
                                }
                                const target = matching.find(r => r.tag_name === arg);
                                if (!target) {
                                    await XeonBotInc.sendMessage(chatId, { text: `ℹ️ لا يوجد إصدار بالاسم \`${arg}\` حالياً.` }, { quoted: mek });
                                    return;
                                }
                                await cleanupRemoteDlRelease(target);
                                await XeonBotInc.sendMessage(chatId, { text: `✅ حُذف الإصدار \`${arg}\` (${target.assets?.length || 0} ملف، ${fmtBytes(sizeOf(target))}).` }, { quoted: mek });
                                return;
                            }

                            if (!matching.length) {
                                await XeonBotInc.sendMessage(chatId, { text: '✨ لا توجد إصدارات split متراكمة تحتاج تنظيفاً.' }, { quoted: mek });
                                return;
                            }

                            // وضع العرض المسبق: بدون `confirm` فقط نعرض القائمة دون حذف
                            if (arg !== 'confirm') {
                                const totalSize = matching.reduce((s, r) => s + sizeOf(r), 0);
                                const lines = matching.map((r, i) => `${i + 1}. \`${r.tag_name}\` — ${r.assets?.length || 0} ملف، ${fmtBytes(sizeOf(r))}`);
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🗂️ *إصدارات split متراكمة: ${matching.length}*\n⚖️ الحجم الإجمالي: ${fmtBytes(totalSize)}\n\n${lines.join('\n')}\n\n⚠️ هذا عرض فقط ولم يُحذف شيء بعد.\n✅ لحذف الكل فعلياً: \`.cleanremote confirm\`\n🎯 لحذف واحد محدد: \`.cleanremote ${matching[0].tag_name}\``
                                }, { quoted: mek });
                                return;
                            }

                            // التنفيذ الفعلي: حذف الكل مع تأخير بسيط بين كل حذف تجنباً لحدود معدل GitHub
                            let ok = 0, fail = 0;
                            for (const r of matching) {
                                try { await cleanupRemoteDlRelease(r); ok++; } catch (_) { fail++; }
                                await new Promise(res2 => setTimeout(res2, 500));
                            }
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🧹 *اكتمل التنظيف!*\n✅ حُذف: ${ok}\n${fail ? `❌ فشل: ${fail}\n` : ''}💾 تم تحرير نحو ${fmtBytes(matching.reduce((s, r) => s + sizeOf(r), 0))}`
                            }, { quoted: mek });
                        } catch (err) {
                            console.log(`[CLEANREMOTE] failed: ${err.message}`);
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل التنظيف:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .setremotedl (ضبط مستودع/رمز GitHub الخاص بالتحميل عن بُعد) ──
                    if (command === '.setremotedl') {
                        const partsArr = query.split(' ').filter(Boolean);
                        const [ownerRepo, token, workflowFile] = partsArr;

                        if (!ownerRepo || !ownerRepo.includes('/') || !token) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.setremotedl [owner/repo] [GitHub Token] [اسم ملف workflow - اختياري]`\n💡 مثال:\n`.setremotedl myuser/file-splitter ghp_xxx remote-download.yml`'
                            }, { quoted: mek });
                            return;
                        }

                        const [rdOwner, rdRepo] = ownerRepo.split('/');
                        const oldRemoteDlConfig = { ...REMOTE_DL_CONFIG };

                        try {
                            await axios.get(`https://api.github.com/repos/${rdOwner}/${rdRepo}`, {
                                headers: { Authorization: `Bearer ${token}`, 'User-Agent': 'Sadek-RemoteDL' },
                                timeout: 15000
                            });

                            REMOTE_DL_CONFIG.owner = rdOwner;
                            REMOTE_DL_CONFIG.repo = rdRepo;
                            REMOTE_DL_CONFIG.token = token;
                            if (workflowFile) REMOTE_DL_CONFIG.workflowFile = workflowFile;
                            saveRemoteDlConfig();

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ تم ضبط إعدادات Remote Downloader بنجاح!\n📁 المستودع: ${rdOwner}/${rdRepo}\n⚙️ ملف الـ workflow: ${REMOTE_DL_CONFIG.workflowFile}`
                            }, { quoted: mek });
                        } catch (e) {
                            Object.assign(REMOTE_DL_CONFIG, oldRemoteDlConfig);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل التحقق من المستودع/الرمز:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .remotedl (تحميل عن بُعد عبر GitHub Actions ثم إعادة إرسال الأجزاء) ──
                    // يدعم: إلغاء (.stopremotedl)، إعادة محاولة تلقائية لكل جزء فاشل، وتنظيف الـ Release بعد الانتهاء.
                    if (command === '.remotedl') {
                        if (!query || (!query.startsWith('http://') && !query.startsWith('https://'))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.remotedl [رابط مباشر] [حجم الجزء بالميجا - اختياري]`'
                            }, { quoted: mek });
                            return;
                        }

                        if (activeRemoteDl.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تحميل عن بُعد نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stopremotedl\` قبل بدء تحميل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const rdParts = query.split(' ').filter(Boolean);
                        const fileUrl = rdParts[0];
                        const chunkSizeMb = rdParts[1] && !isNaN(parseInt(rdParts[1])) ? parseInt(rdParts[1]) : 100;

                        const control = { cancelled: false, runId: null };
                        activeRemoteDl.set(chatId, control);

                        let dispatchTime, run, release, links;
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🚀 *جاري تشغيل التحميل عن بُعد على GitHub Actions...*\n📦 حجم الجزء: ${chunkSizeMb} MB\n\n🛑 لإلغاء التحميل في أي وقت: \`.stopremotedl\``
                            }, { quoted: mek });

                            console.log(`[REMOTEDL] start: ${fileUrl} | chunk:${chunkSizeMb}MB`);
                            dispatchTime = await triggerRemoteDownload(fileUrl, chunkSizeMb);
                            run = await findTriggeredRun(dispatchTime);
                            control.runId = run.id;

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ بدأ التشغيل بنجاح.\n🔗 السجل: ${run.html_url}\nجاري الانتظار حتى الاكتمال (قد يستغرق عدة دقائق حسب حجم الملف)...`
                            }, { quoted: mek });

                            const completedRun = await waitForRunCompletion(run.id, 55 * 60 * 1000, async (r) => {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ لا يزال التحميل عن بُعد قيد التشغيل...\n🔗 ${r.html_url}`
                                }, { quoted: mek });
                            }, control);

                            if (completedRun.conclusion !== 'success') {
                                throw new Error(`فشل تشغيل الـ workflow (${completedRun.conclusion}).\n🔗 راجع السجل: ${completedRun.html_url}`);
                            }

                            const result = await fetchRemoteDlResult();
                            release = result.release;
                            links = result.links;

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *اكتمل التحميل عن بُعد!*\n📦 عدد الأجزاء: ${links.length}\n⬇️ جاري تحميل الأجزاء وإرسالها...`
                            }, { quoted: mek });

                        } catch (err) {
                            activeRemoteDl.delete(chatId);
                            if (err.isCancelled) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إلغاء التحميل عن بُعد بطلبك.*`
                                }, { quoted: mek });
                            } else {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل التحميل عن بُعد:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // ── مرحلة تحميل وإرسال الأجزاء: مع إعادة محاولة تلقائية ودعم الإلغاء ──
                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        const PART_MAX_RETRIES = 3;      // عدد محاولات تحميل كل جزء قبل اعتباره فشل نهائياً
                        const PART_RETRY_BASE_MS = 4000; // أساس التأخير التصاعدي بين المحاولات

                        let successCount = 0, failCount = 0, wasCancelledMidway = false;
                        const failedParts = [];

                        for (let i = 0; i < links.length; i++) {
                            if (control.cancelled) {
                                wasCancelledMidway = true;
                                break;
                            }

                            let result, lastErr, succeeded = false;

                            for (let attempt = 1; attempt <= PART_MAX_RETRIES; attempt++) {
                                if (control.cancelled) { wasCancelledMidway = true; break; }
                                try {
                                    if (attempt > 1) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `🔁 إعادة محاولة تحميل الجزء ${i + 1}/${links.length} — المحاولة ${attempt}/${PART_MAX_RETRIES}...`
                                        }, { quoted: mek });
                                    }

                                    result = await smartDownloadUrl(links[i], tmpDir, `remote${i + 1}`);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: result.outputPath },
                                        mimetype: result.mimeType,
                                        fileName: `Part_${i + 1}${result.fileExt}`,
                                        caption: `✅ *الجزء ${i + 1}/${links.length}*\n⚖️ الحجم: ${result.sizeMB} MB${attempt > 1 ? `\n🔁 نجح بعد ${attempt} محاولات` : ''}`
                                    }, { quoted: mek });

                                    succeeded = true;
                                    break;
                                } catch (err) {
                                    lastErr = err;
                                    if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                        try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                    }
                                    if (attempt < PART_MAX_RETRIES) {
                                        const backoffMs = PART_RETRY_BASE_MS * attempt;
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ فشلت المحاولة ${attempt}/${PART_MAX_RETRIES} للجزء ${i + 1}:\n\`${err.message}\`\n🔄 إعادة المحاولة بعد ${Math.round(backoffMs / 1000)} ثانية...`
                                        }, { quoted: mek });
                                        await new Promise(r => setTimeout(r, backoffMs));
                                    }
                                } finally {
                                    if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                        try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                    }
                                }
                            }

                            if (wasCancelledMidway) break;

                            if (succeeded) {
                                successCount++;
                            } else {
                                failCount++;
                                failedParts.push({ index: i + 1, url: links[i], error: lastErr?.message || 'خطأ غير معروف' });
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل تحميل/إرسال الجزء ${i + 1} نهائياً بعد ${PART_MAX_RETRIES} محاولات:\n\`${lastErr?.message || 'خطأ غير معروف'}\`\n🔗 الرابط المباشر: ${links[i]}`
                                }, { quoted: mek });
                            }

                            if (i < links.length - 1) await new Promise(r => setTimeout(r, 2000));
                        }

                        activeRemoteDl.delete(chatId);

                        if (wasCancelledMidway) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🛑 *تم إلغاء إرسال الأجزاء بطلبك.*\n✅ تم إرسال: ${successCount}/${links.length} قبل الإلغاء`
                            }, { quoted: mek });
                        } else {
                            let summaryText = `🏁 *اكتمل!*\n✅ نجح: ${successCount}\n❌ فشل: ${failCount}`;
                            if (failedParts.length > 0) {
                                summaryText += `\n\n📋 *الأجزاء التي فشلت نهائياً:*\n`;
                                failedParts.forEach(f => {
                                    summaryText += `${f.index}. \`${f.error}\`\n🔗 ${f.url}\n`;
                                });
                            }
                            await XeonBotInc.sendMessage(chatId, { text: summaryText }, { quoted: mek });
                        }

                        if (release) cleanupRemoteDlRelease(release).catch(() => {});
                        return;
                    }

                    // ── أمر .batchdl: تحميل عدة روابط دفعة واحدة من ملف txt مرفق (رابط لكل سطر) ──
                    // الاستخدام: أرسل ملف .txt واجعل التعليق عليه .batchdl (أو .batchdl Part لتحديد بادئة التسمية)
                    // أو أرسل .batchdl كرد (Reply) على ملف txt أرسلته سابقاً
                    // صيغة كل سطر داخل الملف: رابط | اسم مخصص  (أو رابط فقط وسيُسمّى تلقائياً)
                    if (command === '.batchdl') {
                        let docMessage = mek.message?.documentMessage;

                        if (!docMessage && isReply) {
                            const quoted = mek.message.extendedTextMessage.contextInfo.quotedMessage;
                            if (quoted?.documentMessage) docMessage = quoted.documentMessage;
                        }

                        if (!docMessage || !(docMessage.fileName || '').toLowerCase().endsWith('.txt')) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ أرفق ملف نصي (.txt) يحتوي على رابط في كل سطر، ثم استخدم `.batchdl` كتعليق على الملف أو كرد عليه.\n\n💡 صيغة كل سطر:\n`رابط | اسم مخصص`\nأو رابط فقط (سيُسمّى تلقائياً Part 1, Part 2 ...)\n\n📌 مثال: `.batchdl Part` لتحديد بادئة التسمية.'
                            }, { quoted: mek });
                            return;
                        }

                        // ── إعدادات إعادة المحاولة والفاصل الزمني ──
                        const BATCHDL_SLEEP_MS = 5000;      // فاصل 5 ثوانٍ بين كل رابط والذي يليه
                        const BATCHDL_MAX_RETRIES = 3;       // عدد محاولات التحميل لكل رابط قبل اعتباره فشل نهائياً
                        const BATCHDL_RETRY_BASE_MS = 4000;  // أساس التأخير بين المحاولات (تصاعدي)

                        try {
                            const stream = await downloadContentFromMessage(docMessage, 'document');
                            let buffer = Buffer.from([]);
                            for await (const chunk of stream) buffer = Buffer.concat([buffer, chunk]);

                            const lines = buffer.toString('utf8').split(/\r?\n/).map(l => l.trim()).filter(Boolean);
                            if (lines.length === 0) throw new Error('الملف فارغ.');

                            const namePrefix = query || 'Part';
                            const jobs = lines.map((line, i) => {
                                const [rawUrl, customName] = line.split('|').map(s => s?.trim());
                                return { url: rawUrl, name: customName || `${namePrefix} ${i + 1}` };
                            }).filter(j => /^https?:\/\//i.test(j.url));

                            if (jobs.length === 0) throw new Error('لم يتم العثور على أي روابط صحيحة في الملف.');

                            await XeonBotInc.sendMessage(chatId, {
                                text: `📦 *بدء التحميل المجمّع!*\n🔗 عدد الروابط: ${jobs.length}\n⏱️ فاصل ${BATCHDL_SLEEP_MS / 1000} ثوانٍ بين كل رابط\n🔁 حتى ${BATCHDL_MAX_RETRIES} محاولات لكل رابط عند الفشل\n⏳ سيتم إرسال كل ملف فور اكتمال تحميله...`
                            }, { quoted: mek });

                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                            let successCount = 0, failCount = 0;
                            const failedJobs = []; // لتقرير نهائي بالروابط التي فشلت بعد كل المحاولات

                            for (let i = 0; i < jobs.length; i++) {
                                const { url, name } = jobs[i];
                                let result;
                                let lastErr;
                                let succeeded = false;

                                // ── حلقة إعادة المحاولة لهذا الرابط ──
                                for (let attempt = 1; attempt <= BATCHDL_MAX_RETRIES; attempt++) {
                                    try {
                                        if (attempt === 1) {
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `⬇️ (${i + 1}/${jobs.length}) جاري تحميل: *${name}*...`
                                            }, { quoted: mek });
                                        } else {
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `🔁 (${i + 1}/${jobs.length}) إعادة محاولة تحميل *${name}* — المحاولة ${attempt}/${BATCHDL_MAX_RETRIES}...`
                                            }, { quoted: mek });
                                        }

                                        result = await smartDownloadUrl(url, tmpDir, `batch${i + 1}`);
                                        const cleanName = name.replace(/[^\w\s\u0600-\u06FF-]/g, '').trim() || `Part_${i + 1}`;

                                        await XeonBotInc.sendMessage(chatId, {
                                            document: { url: result.outputPath },
                                            mimetype: result.mimeType,
                                            fileName: `${cleanName}${result.fileExt}`,
                                            caption: `✅ *${name}*\n⚖️ الحجم: ${result.sizeMB} MB${result.isGoogleDrive ? '\n☁️ المصدر: Google Drive' : ''}${attempt > 1 ? `\n🔁 نجح بعد ${attempt} محاولات` : ''}`
                                        }, { quoted: mek });

                                        succeeded = true;
                                        break; // نجح التحميل، لا داعي لمزيد من المحاولات

                                    } catch (err) {
                                        lastErr = err;
                                        if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                            try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                        }

                                        if (attempt < BATCHDL_MAX_RETRIES) {
                                            // تأخير تصاعدي بسيط قبل إعادة المحاولة: 4، 8، 12 ثانية...
                                            const backoffMs = BATCHDL_RETRY_BASE_MS * attempt;
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `⚠️ فشلت المحاولة ${attempt}/${BATCHDL_MAX_RETRIES} لـ *${name}*:\n\`${err.message}\`\n🔄 إعادة المحاولة بعد ${Math.round(backoffMs / 1000)} ثانية...`
                                            }, { quoted: mek });
                                            await new Promise(r => setTimeout(r, backoffMs));
                                        }
                                    } finally {
                                        if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                            try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                        }
                                    }
                                }

                                if (succeeded) {
                                    successCount++;
                                } else {
                                    failCount++;
                                    failedJobs.push({ name, url, error: lastErr?.message || 'خطأ غير معروف' });
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل تحميل *${name}* نهائياً بعد ${BATCHDL_MAX_RETRIES} محاولات:\n\`${lastErr?.message || 'خطأ غير معروف'}\``
                                    }, { quoted: mek });
                                }

                                // ── فاصل sleep 5 ثوانٍ قبل الانتقال للرابط التالي (إن وُجد رابط آخر) ──
                                if (i < jobs.length - 1) {
                                    await new Promise(r => setTimeout(r, BATCHDL_SLEEP_MS));
                                }
                            }

                            let summaryText = `🏁 *اكتمل التحميل المجمّع!*\n✅ نجح: ${successCount}\n❌ فشل: ${failCount}`;
                            if (failedJobs.length > 0) {
                                summaryText += `\n\n📋 *الروابط التي فشلت نهائياً:*\n`;
                                failedJobs.forEach((f, idx) => {
                                    summaryText += `${idx + 1}. ${f.name} — \`${f.error}\`\n`;
                                });
                            }

                            await XeonBotInc.sendMessage(chatId, {
                                text: summaryText
                            }, { quoted: mek });

                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ في معالجة ملف الروابط:\n\`${err.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .apk ──
                    if (command === '.apk') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إدخال اسم التطبيق.\nمثال: `.apk mt manager`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري البحث عن *${query}* في قاعدة البيانات...`
                            }, { quoted: mek });

                            const searchUrl = `https://ws75.aptoide.com/api/7/apps/search/query=${encodeURIComponent(query)}/limit=1`;
                            const searchResponse = await axios.get(searchUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } });
                            const appList = searchResponse.data?.datalist?.list;
                            if (!appList || appList.length === 0) throw new Error('لم يتم العثور على هذا التطبيق!');

                            const app = appList[0];
                            const apkUrl = app.file?.path;
                            const appName = app.name || query;
                            if (!apkUrl) throw new Error('رابط الحزمة المباشر غير متوفر حالياً.');

                            await XeonBotInc.sendMessage(chatId, {
                                text: `📦 *تم العثور على:* ${appName}\n🆔 *الحزمة:* ${app.package}\n\nجاري تحميل ملف الـ APK...`
                            }, { quoted: mek });

                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                            const cleanName = appName.replace(/[^\w\s-]/g, '').replace(/\s+/g, '_');
                            const outputPath = path.join(tmpDir, `${cleanName}_${randomBytes(2).toString('hex')}.apk`);

                            const response = await axios({
                                method: 'GET', url: apkUrl, responseType: 'stream',
                                timeout: 600000, headers: { 'User-Agent': 'Mozilla/5.0' }
                            });
                            const writer = fs.createWriteStream(outputPath);
                            trackStream(response.data, `APK ${cleanName}`, response.headers['content-length']);
                            response.data.pipe(writer);
                            await new Promise((resolve, reject) => { writer.on('finish', resolve); writer.on('error', reject); });

                            const sizeMB = (fs.statSync(outputPath).size / 1024 / 1024).toFixed(2);
                            await XeonBotInc.sendMessage(chatId, {
                                document: { url: outputPath },
                                mimetype: 'application/vnd.android.package-archive',
                                fileName: `${cleanName}.apk`,
                                caption: `🤖 *تم تحميل الـ APK بنجاح!*\n📱 *التطبيق:* ${appName}\n⚖ *الحجم:* ${sizeMB} MB`
                            }, { quoted: mek });

                            try { if (fs.existsSync(outputPath)) fs.unlinkSync(outputPath); } catch (_) {}
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ تعذر تحميل الـ APK:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .setanime / .animeset (تثبيت مصدر واحد لـ .anime) ──
                    if (command === '.setanime' || command === '.animeset') {
                        const name = query.toLowerCase().trim();
                        const namesList = ANIME_SOURCE_LIST.join('، ');
                        if (!name) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: animeLockedSource
                                    ? `📌 المصدر المثبّت حالياً: *${ANIME_SOURCE_NAMES[animeLockedSource].label}*\n\n💡 للتبديل: \`.setanime <اسم المصدر>\`\nللرجوع لكل المصادر: \`.setanime all\`\n\nالمصادر المتاحة: ${namesList}`
                                    : `📌 لا يوجد مصدر مثبّت — البحث في كل المصادر.\n\n💡 للتثبيت على مصدر واحد: \`.setanime <اسم المصدر>\`\n\nالمصادر المتاحة: ${namesList}`
                            }, { quoted: mek });
                            return;
                        }
                        if (name === 'all' || name === 'off' || name === 'none' || name === 'الكل') {
                            animeLockedSource = null;
                            await XeonBotInc.sendMessage(chatId, { text: '✅ تم الرجوع للبحث في كل المصادر.' }, { quoted: mek });
                            return;
                        }
                        if (!ANIME_SOURCE_NAMES[name]) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ مصدر غير معروف: *${name}*\n\nالمصادر المتاحة: ${namesList}` }, { quoted: mek });
                            return;
                        }
                        animeLockedSource = name;
                        await XeonBotInc.sendMessage(chatId, { text: `✅ تم تثبيت مصدر الأنمي على: *${ANIME_SOURCE_NAMES[name].label}*\n\n🔍 أمر .anime سيبحث فيه فقط الآن. عند وقوعه، بدّله بأمر \`.setanime <مصدر آخر>\` أو ارجع للكل بـ \`.setanime all\`.` }, { quoted: mek });
                        return;
                    }

                    // ── أمر .anime (بحث أنمي عربي عبر ok.ru) ──
                    if (command === '.anime') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم الأنمي.\n💡 *مثال:* `.anime Naruto` أو `.anime ناروتو`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            const locked = animeLockedSource ? ANIME_SOURCE_NAMES[animeLockedSource] : null;
                            await XeonBotInc.sendMessage(chatId, {
                                text: locked
                                    ? `🔍 جاري البحث عن *${query}* في مصدر ${locked.label} فقط...`
                                    : `🔍 جاري البحث عن *${query}* في 15 مصدراً...`
                            }, { quoted: mek });

                            const results = [];
                            const seenTitles = new Set();
                            const addResults = (source, cdSource, list, max) => {
                                for (const it of (Array.isArray(list) ? list : []).slice(0, max)) {
                                    const key = String(it.title || '').trim().toLowerCase();
                                    if (!key || seenTitles.has(key)) continue;
                                    seenTitles.add(key);
                                    results.push({ source, cdSource, id: it.id, type: it.type || 'series', title: it.title });
                                }
                            };
                            if (locked) {
                                // مصدر واحد مثبّت عبر .setanime — نفس الكود، مصدر واحد فقط
                                const list = await animeSearchOne(animeLockedSource, query);
                                addResults(locked.source, locked.cdSource, list, 10);
                            } else {
                                // بحث متوازي في المصادر الخمسة عشر — فشل مصدر لا يوقف الباقي
                                const [cdDay, cdCloud, rift, witcher, shahiid, a4up, animedar, kartoney, animerco, hianime, okru, arab, az, okan, egya] = await Promise.allSettled([
                                    cloudDaySearch(query, 'AnimeDay'),
                                    cloudDaySearch(query, 'CimaCloud'),
                                    riftSearch(query),
                                    witcherSearch(query),
                                    shahiidSearch(query),
                                    anime4upSearch(query),
                                    animedarSearch(query),
                                    kartoneySearch(query),
                                    animercoSearch(query),
                                    hianimeSearch(query),
                                    okruSearchAnime(query),
                                    arabanimeSearch(query),
                                    animezidSearch(query),
                                    okanimeSearch(query),
                                    egyaflamSearch(query)
                                ]);
                                if (cdDay.status === 'fulfilled') addResults('cloudday', 'AnimeDay', cdDay.value, 3);
                                if (cdCloud.status === 'fulfilled') addResults('cloudday', 'CimaCloud', cdCloud.value, 3);
                                if (rift.status === 'fulfilled') addResults('rift', null, rift.value, 3);
                                if (witcher.status === 'fulfilled') addResults('witcher', null, witcher.value, 2);
                                if (shahiid.status === 'fulfilled') addResults('shahiid', null, shahiid.value, 2);
                                if (a4up.status === 'fulfilled') addResults('anime4up', null, a4up.value, 2);
                                if (animedar.status === 'fulfilled') addResults('animedar', null, animedar.value, 2);
                                if (kartoney.status === 'fulfilled') addResults('kartoney', null, kartoney.value, 2);
                                if (animerco.status === 'fulfilled') addResults('animerco', null, animerco.value, 2);
                                if (hianime.status === 'fulfilled') addResults('hianime', null, hianime.value, 2);
                                if (okru.status === 'fulfilled') addResults('okru', null, okru.value.map(v => ({ id: v.id, title: v.title })), 2);
                                if (arab.status === 'fulfilled') addResults('arabanime', null, arab.value, 2);
                                if (az.status === 'fulfilled') addResults('animezid', null, az.value, 2);
                                if (okan.status === 'fulfilled') addResults('okanime', null, okan.value, 2);
                                if (egya.status === 'fulfilled') addResults('egyaflam', null, egya.value, 2);
                            }
                            if (results.length === 0) throw new Error(locked ? `لا نتائج في مصدر ${locked.label}. جرّب اسماً مختلفاً أو بدّل المصدر بـ \`.setanime <مصدر آخر>\`.` : 'لم يتم العثور على أي نتائج في المصادر الخمسة عشر. جرّب اسماً مختلفاً.');

                            const tagOf = s => s === 'cloudday' ? '☁️ CloudDay' : s === 'rift' ? '🌐 AnimeRift' : s === 'witcher' ? '🧙 AnimeWitcher' : s === 'shahiid' ? '🎬 شهيد' : s === 'anime4up' ? '📺 Anime4Up' : s === 'animedar' ? '🎞️ Animedar' : s === 'kartoney' ? '🧒 Kartoney' : s === 'animerco' ? '🎭 Animerco' : s === 'hianime' ? '🌍 HiAnime EN' : s === 'arabanime' ? '🌸 ArabAnime' : s === 'animezid' ? '🌟 AnimeZid' : s === 'okanime' ? '🎬 OkAnime' : s === 'egyaflam' ? '🎞️ EgyAflam' : '📺 ok.ru';
                            let responseText = `🎌 *نتائج البحث (أنمي عربي):*\n\n`;
                            results.slice(0, 15).forEach((r, index) => {
                                responseText += `*${index + 1}* - ${r.title} [${tagOf(r.source)}]\n`;
                            });
                            responseText += `\n💡 *طريقة الاختيار:*\nقم **بالرد (Reply)** على هذه الرسالة برقم الأنمي المطلوب.\n\n🍿 *مثال:* \`1\``;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            animeCache.set(sentMsg.key.id, {
                                stage: 'search',
                                results: results.slice(0, 15),
                                timestamp: Date.now()
                            });
                            setTimeout(() => animeCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .football — إعادة مباريات اليوم + بحث بالفريق (v117.2) ──
                    if (command === '.football') {
                        const sub = (query || '').split(/\s+/)[0].toLowerCase();
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '⚽ *أمر .football — إعادة مباريات كرة القدم*\n\n• `.football recent` — مباريات اليوم من كل الدوريات (من غير حرق: لا نتائج ولا أهداف)\n  ↳ رد برقم المباراة لعرض الجودات والحجم قبل التحميل\n• `.football <فريق>` — ابحث عن مباريات فريق (بالإنجليزية) من آخر 14 يوم، الأحدث أولاً\n  ↳ مثال: `.football liverpool`\n\n💡 *مثال:* `.football recent`'
                            }, { quoted: mek });
                            return;
                        }
                        if (sub !== 'recent') {
                            // ── بحث بالفريق ──
                            const team = query.trim();
                            try {
                                await XeonBotInc.sendMessage(chatId, { text: `🔍 جاري البحث عن مباريات *${team}*...` }, { quoted: mek });
                                const matches = await footballSearchTeam(team);
                                if (!matches.length) throw new Error(`لا توجد مباريات لـ "${team}" في آخر 14 يوم في المصادر المتاحة حالياً. جرّب اسم الفريق بالإنجليزية.`);
                                const shown = matches.slice(0, 20);
                                let responseText = `⚽ *مباريات ${team} — آخر 14 يوم*\n\n`;
                                let lastDate = null;
                                shown.forEach((mt, i) => {
                                    if (mt.date !== lastDate) {
                                        lastDate = mt.date;
                                        responseText += `📅 *${new Date(mt.date + 'T00:00:00Z').toLocaleDateString('ar-EG', { weekday: 'long', day: 'numeric', month: 'long', year: 'numeric', timeZone: 'Africa/Cairo' })}*\n`;
                                    }
                                    const listSrc = footballListLabel(mt);
                                    responseText += `*${i + 1}* - ${mt.home} 🆚 ${mt.away} ${mt.ready ? '✅' : '⏳'}${listSrc ? ` [${listSrc}]` : ''}\n`;
                                });
                                responseText += `\n✅ = الإعادة جاهزة • ⏳ = لسه منزلتش\n💡 رد (Reply) على هذه الرسالة برقم المباراة لعرض الجودات والحجم قبل التحميل.\n⏰ الرد لازم يكون خلال *5 دقايق*.`;
                                const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                                footballCache.set(sentMsg.key.id, { matches: shown, timestamp: Date.now() });
                                setTimeout(() => footballCache.delete(sentMsg.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث عن مباريات ${team}:\n\`${err.message}\`` }, { quoted: mek });
                            }
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, { text: '⏳ جاري جلب مباريات اليوم...' }, { quoted: mek });
                            const { matches, source } = await footballFetchTodayMatches();
                            if (!matches.length) throw new Error('لا توجد مباريات اليوم في المصادر المتاحة حالياً. جرّب لاحقاً.');
                            const shown = matches.slice(0, 30);
                            const dateStr = new Date().toLocaleDateString('ar-EG', { weekday: 'long', day: 'numeric', month: 'long', year: 'numeric', timeZone: 'Africa/Cairo' });
                            let responseText = `⚽ *مباريات اليوم — ${dateStr}*\n\n`;
                            let lastLeague = null;
                            shown.forEach((mt, i) => {
                                if (mt.league !== lastLeague) {
                                    lastLeague = mt.league;
                                    responseText += `🏆 *${mt.league}*\n`;
                                }
                                const listSrc = footballListLabel(mt);
                                responseText += `*${i + 1}* - ${mt.home} 🆚 ${mt.away} ${mt.ready ? '✅' : '⏳'}${listSrc ? ` [${listSrc}]` : ''}\n`;
                            });
                            responseText += `\n✅ = الإعادة جاهزة • ⏳ = لسه منزلتش\n💡 رد (Reply) على هذه الرسالة برقم المباراة لعرض الجودات والحجم قبل التحميل.\n⏰ الرد لازم يكون خلال *5 دقايق*.`;
                            if (matches.length > 30) responseText += `\n\n📌 عرض أول 30 مباراة من ${matches.length}.`;
                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            footballCache.set(sentMsg.key.id, { matches: shown, timestamp: Date.now() });
                            setTimeout(() => footballCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل جلب مباريات اليوم:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .animeapi (فحص حالة مصادر الأنمي) ──
                    if (command === '.animeapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر الأنمي...'
                            }, { quoted: mek });
                            const probes = [
                                { name: '☁️ CloudDay (AnimeDay)', fn: async () => { const r = await cloudDaySearch('naruto', 'AnimeDay'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '☁️ CloudDay (CimaCloud)', fn: async () => { const r = await cloudDaySearch('naruto', 'CimaCloud'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🌐 AnimeRift', fn: async () => { const r = await riftSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🧙 AnimeWitcher', fn: async () => { const r = await witcherSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎬 شهيد', fn: async () => { const r = await shahiidSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 Anime4Up', fn: async () => { const r = await anime4upSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎞️ Animedar', fn: async () => { const r = await animedarSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🧒 Kartoney', fn: async () => { const r = await kartoneySearch('pokemon'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎭 Animerco', fn: async () => { const r = await animercoSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🌍 HiAnime EN', fn: async () => { const r = await hianimeSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 ok.ru', fn: async () => { const r = await okruSearchAnime('ناروتو الحلقة 1'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🌸 ArabAnime', fn: async () => { const r = await arabanimeSearch('naruto shippuuden'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🌟 AnimeZid', fn: async () => { const r = await animezidSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎬 OkAnime', fn: async () => { const r = await okanimeSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎞️ EgyAflam', fn: async () => { const r = await egyaflamSearch('naruto'); if (!r.length) throw new Error('لا نتائج'); return r.length; } }
                            ];
                            const settled = await Promise.allSettled(probes.map(async p => {
                                const t = Date.now();
                                const n = await p.fn();
                                return { name: p.name, ms: Date.now() - t, n };
                            }));
                            let out = `📊 *حالة مصادر الأنمي:*\n\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} نتيجة)\n`;
                                } else {
                                    out += `🔴 *${probes[i].name}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .cartoon (كرتون قديم مدبلج — 7 مصادر) ──
                    if (command === '.cartoon') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم الكرتون.\n💡 *مثال:* `.cartoon سيف النار` أو `.cartoon بن تن`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            const locked = cartoonLockedSource ? CARTOON_SOURCE_NAMES[cartoonLockedSource] : null;
                            await XeonBotInc.sendMessage(chatId, {
                                text: locked
                                    ? `🔍 جاري البحث عن *${query}* في مصدر ${locked.label} فقط...`
                                    : `🔍 جاري البحث عن *${query}* في 7 مصادر...`
                            }, { quoted: mek });

                            const results = [];
                            const seenTitles = new Set();
                            const addResults = (source, list, max) => {
                                for (const it of (Array.isArray(list) ? list : []).slice(0, max)) {
                                    const key = String(it.title || '').trim().toLowerCase();
                                    if (!key || seenTitles.has(key)) continue;
                                    seenTitles.add(key);
                                    results.push({ source, id: it.id, kind: it.kind || null, title: it.title });
                                }
                            };
                            if (locked) {
                                // مصدر واحد مثبّت عبر .setcartoon — نفس الكود، مصدر واحد فقط
                                const list = await cartoonSearchOne(cartoonLockedSource, query);
                                addResults(locked.source, list, 10);
                            } else {
                                // بحث متوازي في المصادر السبعة — فشل مصدر لا يوقف الباقي
                                const [dub, carateen, kartoney, okru, dima, az, sd] = await Promise.allSettled([
                                    cartoonDubSearch(query),
                                    carateenSearch(query),
                                    kartoneySearch(query),
                                    okruSearchCartoon(query),
                                    dimaSearch(query),
                                    animezidSearch(query),
                                    stardimaSearch(query)
                                ]);
                                if (dub.status === 'fulfilled') addResults('cartoondub', dub.value, 3);
                                if (carateen.status === 'fulfilled') addResults('carateen', carateen.value, 3);
                                if (kartoney.status === 'fulfilled') addResults('kartoney', kartoney.value, 2);
                                if (okru.status === 'fulfilled') addResults('okru', okru.value.map(v => ({ id: v.id, title: v.title })), 2);
                                if (dima.status === 'fulfilled') addResults('dimakids', dima.value, 2);
                                if (az.status === 'fulfilled') addResults('animezid', az.value, 2);
                                if (sd.status === 'fulfilled') addResults('stardima', sd.value, 2);
                            }
                            if (results.length === 0) throw new Error(locked ? `لا نتائج في مصدر ${locked.label}. جرّب اسماً مختلفاً أو بدّل المصدر بـ \`.setcartoon <مصدر آخر>\`.` : 'لم يتم العثور على أي نتائج في المصادر السبعة. جرّب اسماً مختلفاً.');

                            const tagOf = s => s === 'cartoondub' ? '🎨 CartoonDub' : s === 'carateen' ? '📺 Carateen' : s === 'kartoney' ? '🧒 Kartoney' : s === 'okru' ? '📺 ok.ru' : s === 'dimakids' ? '🎬 DimaKids' : s === 'stardima' ? '⭐ Stardima' : '🌟 AnimeZid';
                            let responseText = `🎨 *نتائج البحث (كرتون قديم مدبلج):*\n\n`;
                            results.slice(0, 15).forEach((r, index) => {
                                responseText += `*${index + 1}* - ${r.title} [${tagOf(r.source)}]\n`;
                            });
                            responseText += `\n💡 *طريقة الاختيار:*\nقم **بالرد (Reply)** على هذه الرسالة برقم الكرتون المطلوب.\n\n🍿 *مثال:* \`1\``;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            cartoonCache.set(sentMsg.key.id, {
                                stage: 'search',
                                results: results.slice(0, 15),
                                timestamp: Date.now()
                            });
                            setTimeout(() => cartoonCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .cartoonapi (فحص حالة مصادر الكرتون) ──
                    if (command === '.cartoonapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر الكرتون...'
                            }, { quoted: mek });
                            const probes = [
                                { name: '🎨 CartoonDub', fn: async () => { const r = await cartoonDubSearch('بن تن'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 Carateen', fn: async () => { const r = await carateenSearch('سيف النار'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🧒 Kartoney', fn: async () => { const r = await kartoneySearch('الكابتن ماجد'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 ok.ru', fn: async () => { const r = await okruSearchCartoon('الرمية الملتهبة'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎬 DimaKids', fn: async () => { const r = await dimaSearch('سيف النار'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🌟 AnimeZid', fn: async () => { const r = await animezidSearch('سيف النار'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '⭐ Stardima', fn: async () => { const r = await stardimaSearch('بن تن'); if (!r.length) throw new Error('لا نتائج'); return r.length; } }
                            ];
                            const settled = await Promise.allSettled(probes.map(async p => {
                                const t = Date.now();
                                const n = await p.fn();
                                return { name: p.name, ms: Date.now() - t, n };
                            }));
                            let out = `📊 *حالة مصادر الكرتون:*\n\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} نتيجة)\n`;
                                } else {
                                    out += `🔴 *${probes[i].name}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .setcartoon (تثبيت مصدر واحد لـ .cartoon) ──
                    if (command === '.setcartoon') {
                        const name = query.toLowerCase().trim();
                        const namesList = CARTOON_SOURCE_LIST.join('، ');
                        if (!name) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: cartoonLockedSource
                                    ? `📌 المصدر المثبّت حالياً: *${CARTOON_SOURCE_NAMES[cartoonLockedSource].label}*\n\n💡 للتبديل: \`.setcartoon <اسم المصدر>\`\nللرجوع لكل المصادر: \`.setcartoon all\`\n\nالمصادر المتاحة: ${namesList}`
                                    : `📌 لا يوجد مصدر مثبّت — البحث في كل المصادر.\n\n💡 للتثبيت على مصدر واحد: \`.setcartoon <اسم المصدر>\`\n\nالمصادر المتاحة: ${namesList}`
                            }, { quoted: mek });
                            return;
                        }
                        if (name === 'all' || name === 'off' || name === 'none' || name === 'الكل') {
                            cartoonLockedSource = null;
                            await XeonBotInc.sendMessage(chatId, { text: '✅ تم الرجوع للبحث في كل المصادر.' }, { quoted: mek });
                            return;
                        }
                        if (!CARTOON_SOURCE_NAMES[name]) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ مصدر غير معروف: *${name}*\n\nالمصادر المتاحة: ${namesList}` }, { quoted: mek });
                            return;
                        }
                        cartoonLockedSource = name;
                        await XeonBotInc.sendMessage(chatId, { text: `✅ تم تثبيت مصدر الكرتون على: *${CARTOON_SOURCE_NAMES[name].label}*\n\n🔍 أمر .cartoon سيبحث فيه فقط الآن. عند وقوعه، بدّله بأمر \`.setcartoon <مصدر آخر>\` أو ارجع للكل بـ \`.setcartoon all\`.` }, { quoted: mek });
                        return;
                    }

                    // ── أمر .cartoon-en (كرتون إنجليزي — 4 مصادر) ──
                    if (command === '.cartoon-en' || command === '.catoon-en') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم الكرتون.\n💡 *مثال:* `.cartoon-en Tom and Jerry` أو `.cartoon-en Ben 10`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            const locked = cartoonEnLockedSource ? CARTOON_EN_SOURCE_NAMES[cartoonEnLockedSource] : null;
                            await XeonBotInc.sendMessage(chatId, {
                                text: locked
                                    ? `🔍 جاري البحث عن *${query}* في مصدر ${locked.label} فقط...`
                                    : `🔍 جاري البحث عن *${query}* في 4 مصادر إنجليزية...`
                            }, { quoted: mek });

                            const results = [];
                            const seenTitles = new Set();
                            const addResults = (source, list, max) => {
                                for (const it of (Array.isArray(list) ? list : []).slice(0, max)) {
                                    const key = String(it.title || '').trim().toLowerCase();
                                    if (!key || seenTitles.has(key)) continue;
                                    seenTitles.add(key);
                                    results.push({ source, id: it.id, title: it.title });
                                }
                            };
                            if (locked) {
                                // مصدر واحد مثبّت عبر .setcartoon-en — نفس الكود، مصدر واحد فقط
                                const list = await cartoonEnSearchOne(cartoonEnLockedSource, query);
                                addResults(locked.source, list, 10);
                            } else {
                                // بحث متوازي في المصادر الأربعة — فشل مصدر لا يوقف الباقي
                                const [tt, sc, fm, ia] = await Promise.allSettled([
                                    toontalesSearch(query),
                                    supercartoonsSearch(query),
                                    funniermomentsSearch(query),
                                    archiveorgSearch(query)
                                ]);
                                if (tt.status === 'fulfilled') addResults('toontales', tt.value, 4);
                                if (sc.status === 'fulfilled') addResults('supercartoons', sc.value, 4);
                                if (fm.status === 'fulfilled') addResults('funniermoments', fm.value, 4);
                                if (ia.status === 'fulfilled') addResults('archiveorg', ia.value, 3);
                            }
                            if (results.length === 0) throw new Error(locked ? `لا نتائج في مصدر ${locked.label}. جرّب اسماً مختلفاً أو بدّل المصدر بـ \`.setcartoon-en <مصدر آخر>\`.` : 'لم يتم العثور على أي نتائج في المصادر الأربعة. جرّب اسماً مختلفاً.');

                            const tagOf = s => s === 'toontales' ? '🎬 ToonTales' : s === 'supercartoons' ? '🐰 SuperCartoons' : s === 'funniermoments' ? '😂 FunnierMoments' : '📚 Archive.org';
                            let responseText = `🎬 *نتائج البحث (كرتون إنجليزي):*\n\n`;
                            results.slice(0, 15).forEach((r, index) => {
                                responseText += `*${index + 1}* - ${r.title} [${tagOf(r.source)}]\n`;
                            });
                            responseText += `\n💡 *طريقة الاختيار:*\nقم **بالرد (Reply)** على هذه الرسالة برقم الشورت المطلوب، أو بمدى مثل 1-5 لتحميل عدة شورتات دفعة واحدة.\n\n🍿 *مثال:* \`1\``;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            cartoonEnCache.set(sentMsg.key.id, {
                                stage: 'search',
                                query,
                                results: results.slice(0, 15),
                                timestamp: Date.now()
                            });
                            setTimeout(() => cartoonEnCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .cartoon-enapi (فحص حالة مصادر الكرتون الإنجليزي) ──
                    if (command === '.cartoon-enapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر الكرتون الإنجليزي...'
                            }, { quoted: mek });
                            const probes = [
                                { name: '🎬 ToonTales', fn: async () => { const r = await toontalesSearch('Tom and Jerry'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🐰 SuperCartoons', fn: async () => { const r = await supercartoonsSearch('Canned Feud'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '😂 FunnierMoments', fn: async () => { const r = await funniermomentsSearch('Courage'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📚 Archive.org', fn: async () => { const r = await archiveorgSearch('Tom and Jerry'); if (!r.length) throw new Error('لا نتائج'); return r.length; } }
                            ];
                            const settled = await Promise.allSettled(probes.map(async p => {
                                const t = Date.now();
                                const n = await p.fn();
                                return { name: p.name, ms: Date.now() - t, n };
                            }));
                            let out = `📊 *حالة مصادر الكرتون الإنجليزي:*\n\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} نتيجة)\n`;
                                } else {
                                    out += `🔴 *${probes[i].name}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .setcartoon-en (تثبيت مصدر واحد لـ .cartoon-en) ──
                    if (command === '.setcartoon-en') {
                        const name = query.toLowerCase().trim();
                        const namesList = CARTOON_EN_SOURCE_LIST.join('، ');
                        if (!name) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: cartoonEnLockedSource
                                    ? `📌 المصدر المثبّت حالياً: *${CARTOON_EN_SOURCE_NAMES[cartoonEnLockedSource].label}*\n\n💡 للتبديل: \`.setcartoon-en <اسم المصدر>\`\nللرجوع لكل المصادر: \`.setcartoon-en all\`\n\nالمصادر المتاحة: ${namesList}`
                                    : `📌 لا يوجد مصدر مثبّت — البحث في كل المصادر.\n\n💡 للتثبيت على مصدر واحد: \`.setcartoon-en <اسم المصدر>\`\n\nالمصادر المتاحة: ${namesList}`
                            }, { quoted: mek });
                            return;
                        }
                        if (name === 'all' || name === 'off' || name === 'none' || name === 'الكل') {
                            cartoonEnLockedSource = null;
                            await XeonBotInc.sendMessage(chatId, { text: '✅ تم الرجوع للبحث في كل المصادر.' }, { quoted: mek });
                            return;
                        }
                        if (!CARTOON_EN_SOURCE_NAMES[name]) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ مصدر غير معروف: *${name}*\n\nالمصادر المتاحة: ${namesList}` }, { quoted: mek });
                            return;
                        }
                        cartoonEnLockedSource = name;
                        await XeonBotInc.sendMessage(chatId, { text: `✅ تم تثبيت مصدر الكرتون الإنجليزي على: *${CARTOON_EN_SOURCE_NAMES[name].label}*\n\n🔍 أمر .cartoon-en سيبحث فيه فقط الآن. عند وقوعه، بدّله بأمر \`.setcartoon-en <مصدر آخر>\` أو ارجع للكل بـ \`.setcartoon-en all\`.` }, { quoted: mek });
                        return;
                    }

// ============================================================
// v108 — .kdrama: DramaWorld + Lodynet + قوائم المصادر
// ============================================================

// ── تثبيت مصدر واحد لـ .kdrama (عبر .setkdrama) ──
let kdLockedSource = null; // null = البحث في كل المصادر
const KD_SOURCE_LIST = ['akwam', 'meowtv', 'cloudday', 'dramaworld', 'lodynet', 'okru'];
const KD_SOURCE_NAMES = {
    akwam: { source: 'akwam', label: '📺 Akwam' },
    meowtv: { source: 'meowtv', label: '🐱 MeowTv' },
    cloudday: { source: 'cloudday', cdSource: 'CimaCloud', label: '☁️ CloudDay (CimaCloud)' },
    dramaworld: { source: 'dramaworld', label: '🎭 DramaWorld' },
    lodynet: { source: 'lodynet', label: '🎬 Lodynet' },
    okru: { source: 'okru', label: '📺 ok.ru' }
};

// بحث مصدر واحد بالاسم (نفس دوال البحث — بلا تكرار كود)
async function kdSearchOne(name, query) {
    const e = KD_SOURCE_NAMES[name];
    if (!e) return [];
    if (e.source === 'akwam') return await akwamSearch(query, 'series');
    if (e.source === 'meowtv') return await meowSearch(query, 'series');
    if (e.source === 'cloudday') return await cloudDaySearch(query, 'CimaCloud', '2');
    if (e.source === 'dramaworld') return await dramaWorldSearch(query);
    if (e.source === 'lodynet') return await lodynetSearch(query);
    if (e.source === 'okru') return (await okruSearchRaw(query)).map(v => ({ id: v.id, title: v.title }));
    return [];
}

// ---------- DramaWorld (API — مترجم، وبعض العناوين مدبلجة) ----------
// تم التحقق: لعبة الحبار id 6410 (S1 9/S2 7/S3 6)، ح1 242,470,740 بايت، 3582.42 ثانية
// ملحوظة: ستريمات 1vid/hanerix مشفّرة AES-128 — تُحمّل بـ ffmpeg المباشر (downloadVideoSmart)، لا بـ downloadHlsSegments
const DRAMAWORLD_BASES = ['https://dwapp.arabypros.com/api', 'https://test.arabypros.com/api'];
const DRAMAWORLD_KEY = '4F5A9C3D9A86FA54EACEDDD635185';
const DRAMAWORLD_UUID = 'd506abfd-9fe2-4b71-b979-feff21bcad13';
const DRAMAWORLD_UA = 'okhttp/4.12.0';

async function dramaWorldGet(path) {
    let lastErr;
    for (const base of DRAMAWORLD_BASES) {
        try {
            const res = await axios.get(`${base}/${path}/${DRAMAWORLD_KEY}/${DRAMAWORLD_UUID}/`, {
                headers: { 'User-Agent': DRAMAWORLD_UA }, timeout: 20000
            });
            return res.data;
        } catch (e) { lastErr = e; }
    }
    throw lastErr || new Error('فشل الاتصال بـ DramaWorld.');
}

async function dramaWorldSearch(query) {
    const data = await dramaWorldGet(`search/${encodeURIComponent(query)}/0`);
    const posters = (data && data.posters) || [];
    return posters
        .filter(p => /serie/i.test(String(p.type || '')))
        .map(p => {
            const label = String(p.label || '');
            const tag = /مدبلج|مترجم/.test(label) ? ` (${label})` : '';
            return { id: String(p.id), title: p.title + tag, type: 'series' };
        })
        .slice(0, 5);
}

async function dramaWorldEpisodes(seriesId) {
    const seasons = await dramaWorldGet(`season/by/serie/${seriesId}`);
    if (!Array.isArray(seasons) || !seasons.length) throw new Error('لا توجد مواسم.');
    const eps = [];
    seasons.forEach((s, i) => {
        const m = String(s.title || '').match(/(\d+)/);
        const sNum = m ? parseInt(m[1], 10) : (seasons.length - i);
        for (const e of (s.episodes || [])) {
            eps.push({
                id: String(e.id),
                number: 0,
                title: `الموسم ${sNum} — الحلقة ${e.title || ''}`.trim(),
                season: sNum,
                epNum: 0
            });
        }
    });
    // ترقيم الحلقات بالترتيب داخل كل موسم (عنوان الحلقة غالباً "الحلقة N")
    const perSeason = {};
    eps.forEach(e => {
        const n = (String(e.title).match(/الحلقة\s*(\d+)/) || [])[1];
        e.epNum = n ? parseInt(n, 10) : ((perSeason[e.season] = (perSeason[e.season] || 0) + 1));
    });
    eps.sort((a, b) => (a.season - b.season) || (a.epNum - b.epNum));
    eps.forEach((e, i) => { e.number = i + 1; });
    if (!eps.length) throw new Error('لا توجد حلقات.');
    return eps;
}

async function dramaWorldEpisodeLinks(ep) {
    const res = await axios.get(`${DRAMAWORLD_BASES[0]}/episode/source/by/${ep.id}/${DRAMAWORLD_KEY}/${DRAMAWORLD_UUID}/`, {
        headers: { 'User-Agent': DRAMAWORLD_UA }, timeout: 20000, responseType: 'text'
    });
    const text = String(res.data || '');
    const idx = text.indexOf('W3s');
    if (idx < 0) throw new Error('لم يتم العثور على قائمة السيرفرات.');
    let servers;
    try { servers = JSON.parse(Buffer.from(text.slice(idx), 'base64').toString('utf-8')); }
    catch (_) { throw new Error('فشل تحليل قائمة السيرفرات.'); }
    if (!Array.isArray(servers) || !servers.length) throw new Error('لا توجد سيرفرات.');
    const links = [];
    // Uqload أولاً (المضمون) — ثم أي تضمين فيه mp4/m3u8 مباشر
    const uq = servers.filter(s => /uqload/i.test(s.title || '') || /uqload/i.test(s.url || ''));
    for (const s of uq) {
        try {
            const m3u8 = await extractUqloadM3u8(s.url);
            const plRes = await axios.get(m3u8, { headers: { 'User-Agent': 'Mozilla/5.0', 'Referer': 'https://uqload.com/' }, timeout: 20000, responseType: 'text' });
            const variants = parseM3u8Variants(String(plRes.data || ''), m3u8);
            if (variants.length) {
                for (const v of variants) links.push({ url: v.url, label: `DramaWorld — ${v.label} (Uqload)`, referer: 'https://uqload.com/' });
            } else {
                links.push({ url: m3u8, label: 'DramaWorld — HLS (Uqload)', referer: 'https://uqload.com/' });
            }
        } catch (_) {}
    }
    if (links.length) return [...new Map(links.map(l => [l.label, l])).values()];
    for (const s of servers) {
        const url = s.url || '';
        if (/\.mp4(\?|$)/i.test(url)) return [{ url, label: `DramaWorld — MP4 (${s.title || 'server'})`, referer: '' }];
        if (/\.m3u8(\?|$)/i.test(url)) return [{ url, label: `DramaWorld — HLS (${s.title || 'server'})`, referer: '' }];
    }
    throw new Error('لا توجد سيرفرات شغالة لهذه الحلقة.');
}

// ---------- Lodynet (lodynet.top — مترجم + أقسام مدبلجة) ----------
// تم التحقق: لعبة الحبار ح1 198,262,204 بايت، 3582.30 ثانية، 13 سيرفر
const LODYNET_BASE = 'https://lodynet.top';
const LODYNET_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

async function lodynetSearch(query) {
    const res = await axios.get(`${LODYNET_BASE}/`, {
        params: { s: query },
        headers: { 'User-Agent': LODYNET_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const out = []; const seen = new Set();
    // نتائج البحث: روابط نسبية category/... والعنوان في خاصية title (تسبق href في الوسم)
    for (const m of html.matchAll(/<a[^>]*href="(category\/[^"]+)"[^>]*>/g)) {
        const tag = m[0];
        const t = (tag.match(/title="([^"]{3,160})"/) || [])[1];
        if (!t) continue; // روابط القائمة بلا title تُتجاهل
        const url = LODYNET_BASE + '/' + m[1];
        if (seen.has(url)) continue;
        seen.add(url);
        const title = decodeHtmlEntities(t.replace(/\s+/g, ' ').trim());
        if (!title) continue;
        out.push({ id: url, title });
    }
    return out.slice(0, 5);
}

async function lodynetEpisodes(categoryUrl) {
    const res = await axios.get(categoryUrl, {
        headers: { 'User-Agent': LODYNET_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const eps = []; const seen = new Set();
    const normNum = s2 => parseInt(String(s2).replace(/[٠-٩]/g, d => '٠١٢٣٤٥٦٧٨٩'.indexOf(d)), 10);
    const add = (url, num) => {
        if (!url || !num || seen.has(num)) return;
        seen.add(num);
        eps.push({ id: url, number: num, title: `الحلقة ${num}` });
    };
    // الطريقة الأساسية: بطاقات ItemNewly — الرقم من title أو من نص البطاقة
    // (تغطي صيغتي الروابط: /slug-ep{N} و /slug-الموسم-الث-N)
    for (const b of html.matchAll(/<div class="ItemNewly">([\s\S]{0,900}?)<\/a>/g)) {
        const block = b[1];
        const hrefAbs = (block.match(/href="(https?:\/\/lodynet\.top\/[^"]+)"/) || [])[1];
        const hrefRel = (block.match(/href="(\/[^"]+)"/) || [])[1];
        const href = hrefAbs || (hrefRel ? LODYNET_BASE + hrefRel : null);
        const t = (block.match(/title="([^"]+)"/) || [])[1] || (block.match(/NewlyTitle">([^<]+)</) || [])[1] || '';
        const n = (t.match(/الحلقة\s*([٠-٩0-9]+)/) || [])[1];
        if (href && n) add(href, normNum(n));
    }
    // احتياطي: روابط /slug-ep{N} في الصفحة كلها
    if (!eps.length) {
        for (const m of html.matchAll(/<a[^>]*href="(?:https?:\/\/lodynet\.top)?\/([a-z0-9\-]+-ep(\d+))[^"]*"[^>]*>/g)) {
            add(`${LODYNET_BASE}/${m[1]}`, parseInt(m[2], 10));
        }
    }
    eps.sort((a, b) => a.number - b.number);
    if (!eps.length) throw new Error('لا توجد حلقات.');
    return eps;
}

async function lodynetEpisodeLinks(episodeUrl) {
    const res = await axios.get(episodeUrl, {
        headers: { 'User-Agent': LODYNET_UA }, timeout: 20000, responseType: 'text'
    });
    const html = String(res.data || '');
    const servers = [];
    for (const m of html.matchAll(/"Name"\s*:\s*"([^"]+)"\s*,\s*"Embed"\s*:\s*"([^"]+)"/g)) {
        try {
            const url = Buffer.from(m[2], 'base64').toString('utf-8').trim();
            if (url) servers.push({ name: m[1], url });
        } catch (_) {}
    }
    if (!servers.length) throw new Error('لم يتم العثور على سيرفرات.');
    const links = [];
    const uq = servers.filter(s => /uqload/i.test(s.name) || /uqload/i.test(s.url));
    for (const s of uq) {
        try {
            const m3u8 = await extractUqloadM3u8(s.url);
            const plRes = await axios.get(m3u8, { headers: { 'User-Agent': 'Mozilla/5.0', 'Referer': 'https://uqload.com/' }, timeout: 20000, responseType: 'text' });
            const variants = parseM3u8Variants(String(plRes.data || ''), m3u8);
            if (variants.length) {
                for (const v of variants) links.push({ url: v.url, label: `Lodynet — ${v.label} (Uqload)`, referer: 'https://uqload.com/' });
            } else {
                links.push({ url: m3u8, label: 'Lodynet — HLS (Uqload)', referer: 'https://uqload.com/' });
            }
        } catch (_) {}
    }
    if (links.length) return [...new Map(links.map(l => [l.label, l])).values()];
    for (const s of servers) {
        if (/\.mp4(\?|$)/i.test(s.url)) return [{ url: s.url, label: `Lodynet — MP4 (${s.name})`, referer: '' }];
        if (/\.m3u8(\?|$)/i.test(s.url)) return [{ url: s.url, label: `Lodynet — HLS (${s.name})`, referer: '' }];
    }
    throw new Error('لا توجد سيرفرات شغالة لهذه الحلقة.');
}

                    // ── أمر .setmv (تثبيت مصدر واحد لـ .movie / .series) ──
                    if (command === '.setmv') {
                        const name = query.toLowerCase().trim();
                        const namesList = MV_SOURCE_LIST.join('، ');
                        if (!name) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: mvLockedSource
                                    ? `📌 المصدر المثبّت حالياً: *${MV_SOURCE_NAMES[mvLockedSource].label}*\n\n💡 للتبديل: \`.setmv <اسم المصدر>\`\nللرجوع لكل المصادر: \`.setmv all\`\n\nالمصادر المتاحة: ${namesList}`
                                    : `📌 لا يوجد مصدر مثبّت — البحث في كل المصادر.\n\n💡 للتثبيت على مصدر واحد: \`.setmv <اسم المصدر>\`\n\nالمصادر المتاحة: ${namesList}`
                            }, { quoted: mek });
                            return;
                        }
                        if (name === 'all' || name === 'off' || name === 'none' || name === 'الكل') {
                            mvLockedSource = null;
                            await XeonBotInc.sendMessage(chatId, { text: '✅ تم الرجوع للبحث في كل المصادر.' }, { quoted: mek });
                            return;
                        }
                        if (!MV_SOURCE_NAMES[name]) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ مصدر غير معروف: *${name}*\n\nالمصادر المتاحة: ${namesList}` }, { quoted: mek });
                            return;
                        }
                        mvLockedSource = name;
                        await XeonBotInc.sendMessage(chatId, { text: `✅ تم تثبيت مصدر الأفلام/المسلسلات على: *${MV_SOURCE_NAMES[name].label}*\n\n🔍 أمرا .movie و .series سيبحثان فيه فقط الآن. عند وقوعه، بدّله بأمر \`.setmv <مصدر آخر>\` أو ارجع للكل بـ \`.setmv all\`.` }, { quoted: mek });
                        return;
                    }

                    // ── أمر .movie / .series (بحث أفلام ومسلسلات — Egywatch + ok.ru للمسلسلات فقط) ──
                    if (command === '.movie' || command === '.series') {
                        const kind = command === '.movie' ? 'movie' : 'series';
                        const kindAr = kind === 'movie' ? 'الفيلم' : 'المسلسل';
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ يرجى كتابة اسم ${kindAr}.\n💡 *مثال:* \`${command} breaking bad\``
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            const locked = mvLockedSource ? MV_SOURCE_NAMES[mvLockedSource] : null;
                            await XeonBotInc.sendMessage(chatId, {
                                text: locked
                                    ? `🔍 جاري البحث عن *${query}* في مصدر ${locked.label} فقط...`
                                    : `🔍 جاري البحث عن *${query}* في ${kind === 'series' ? 8 : 7} مصادر...`
                            }, { quoted: mek });

                            const results = [];
                            const seenTitles = new Set();
                            const addResults = (source, cdSource, list, max) => {
                                for (const it of (Array.isArray(list) ? list : []).slice(0, max)) {
                                    const key = String(it.title || '').trim().toLowerCase();
                                    if (!key || seenTitles.has(key)) continue;
                                    seenTitles.add(key);
                                    results.push({ source, cdSource, id: it.id, type: it.type || 'series', title: it.title });
                                }
                            };
                            if (locked) {
                                // مصدر واحد مثبّت عبر .setmv — نفس الكود، مصدر واحد فقط
                                const list = await mvSearchOne(mvLockedSource, query, kind);
                                addResults(locked.source, locked.cdSource, list, 10);
                            } else {
                                // بحث متوازي في المصادر — فشل مصدر لا يوقف الباقي
                                const [akwam, cdCloud, meow, cplus, viola, egyw, okru, myseed] = await Promise.allSettled([
                                    akwamSearch(query, kind),
                                    kind === 'series' ? cloudDaySearch(query, 'CimaCloud', '2') : Promise.resolve([]),
                                    meowSearch(query, kind),
                                    cinemaPlusSearch(query),
                                    violaSearch(query),
                                    kind === 'series' ? egywatchSearch(query) : Promise.resolve([]),
                                    kind === 'series' ? okruSearchRaw(query) : Promise.resolve([]),
                                    myseedSearch(query, kind)
                                ]);
                                if (akwam.status === 'fulfilled') addResults('akwam', null, akwam.value, 3);
                                if (cdCloud.status === 'fulfilled') addResults('cloudday', 'CimaCloud', cdCloud.value, 3);
                                if (meow.status === 'fulfilled') addResults('meowtv', null, meow.value, 3);
                                if (cplus.status === 'fulfilled') addResults('cinemaplus', null, cplus.value, 2);
                                if (viola.status === 'fulfilled') addResults('viola', null, viola.value, 2);
                                if (egyw.status === 'fulfilled') addResults('egywatch', null, egyw.value, 2);
                                if (okru.status === 'fulfilled') addResults('okru', null, okru.value.map(v => ({ id: v.id, title: v.title })), 2);
                                if (myseed.status === 'fulfilled') addResults('myseed', null, myseed.value, 2);
                            }
                            if (results.length === 0) throw new Error(locked ? `لا نتائج في مصدر ${locked.label}. جرّب اسماً مختلفاً أو بدّل المصدر بـ \`.setmv <مصدر آخر>\`.` : `لم يتم العثور على أي نتائج في المصادر ${kind === 'series' ? 'الثمانية' : 'السبعة'}. جرّب اسماً مختلفاً.`);

                            const tagOf = s => s === 'akwam' ? '📺 Akwam' : s === 'cloudday' ? '☁️ CloudDay' : s === 'meowtv' ? '🐱 MeowTv' : s === 'cinemaplus' ? '🎬 CinemaPlus' : s === 'viola' ? '🎭 VioLa' : s === 'egywatch' ? '📺 Egywatch' : s === 'myseed' ? '🌱 MySeed' : '📺 ok.ru';
                            let responseText = kind === 'movie' ? `🎬 *نتائج البحث (أفلام):*\n\n` : `📺 *نتائج البحث (مسلسلات):*\n\n`;
                            results.slice(0, 15).forEach((r, index) => {
                                responseText += `*${index + 1}* - ${r.title} [${tagOf(r.source)}]\n`;
                            });
                            responseText += `\n💡 *طريقة الاختيار:*\nقم **بالرد (Reply)** على هذه الرسالة برقم ${kindAr} المطلوب.\n\n🍿 *مثال:* \`1\``;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            mvCache.set(sentMsg.key.id, {
                                stage: 'search',
                                results: results.slice(0, 15),
                                timestamp: Date.now()
                            });
                            setTimeout(() => mvCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .mvapi (فحص حالة مصادر الأفلام والمسلسلات) ──
                    if (command === '.mvapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر الأفلام والمسلسلات...'
                            }, { quoted: mek });
                            const probes = [
                                { name: '📺 Akwam', fn: async () => { const r = await akwamSearch('breaking', 'series'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '☁️ CloudDay (CimaCloud)', fn: async () => { const r = await cloudDaySearch('breaking bad', 'CimaCloud', '2'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🐱 MeowTv', fn: async () => { const r = await meowSearch('breaking bad', 'series'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎬 CinemaPlus', fn: async () => { const r = await cinemaPlusSearch('one piece'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎭 VioLa', fn: async () => { const r = await violaSearch('breaking bad'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 Egywatch', fn: async () => { const r = await egywatchSearch('star trek enterprise'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 ok.ru', fn: async () => { const r = await okruSearchRaw('star trek enterprise'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🌱 MySeed', fn: async () => { const r = await myseedSearch('john wick', 'movie'); if (!r.length) throw new Error('لا نتائج'); return r.length; } }
                            ];
                            const settled = await Promise.allSettled(probes.map(async p => {
                                const t = Date.now();
                                const n = await p.fn();
                                return { name: p.name, ms: Date.now() - t, n };
                            }));
                            let out = `📊 *حالة مصادر الأفلام والمسلسلات:*\n\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} نتيجة)\n`;
                                } else {
                                    out += `🔴 *${probes[i].name}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }


                    // ── أمر .setkdrama (تثبيت مصدر واحد لـ .kdrama) ──
                    if (command === '.setkdrama') {
                        const name = query.toLowerCase().trim();
                        const namesList = KD_SOURCE_LIST.join('، ');
                        if (!name) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: kdLockedSource
                                    ? `📌 المصدر المثبّت حالياً: *${KD_SOURCE_NAMES[kdLockedSource].label}*\n\n💡 للتبديل: \`.setkdrama <اسم المصدر>\`\nللرجوع لكل المصادر: \`.setkdrama all\`\n\nالمصادر المتاحة: ${namesList}`
                                    : `📌 لا يوجد مصدر مثبّت — البحث في كل المصادر.\n\n💡 للتثبيت على مصدر واحد: \`.setkdrama <اسم المصدر>\`\n\nالمصادر المتاحة: ${namesList}`
                            }, { quoted: mek });
                            return;
                        }
                        if (name === 'all' || name === 'off' || name === 'none' || name === 'الكل') {
                            kdLockedSource = null;
                            await XeonBotInc.sendMessage(chatId, { text: '✅ تم الرجوع للبحث في كل المصادر.' }, { quoted: mek });
                            return;
                        }
                        if (!KD_SOURCE_NAMES[name]) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ مصدر غير معروف: *${name}*\n\nالمصادر المتاحة: ${namesList}` }, { quoted: mek });
                            return;
                        }
                        kdLockedSource = name;
                        await XeonBotInc.sendMessage(chatId, { text: `✅ تم تثبيت مصدر الدراما الكورية على: *${KD_SOURCE_NAMES[name].label}*\n\n🔍 أمر .kdrama سيبحث فيه فقط الآن. عند وقوعه، بدّله بأمر \`.setkdrama <مصدر آخر>\` أو ارجع للكل بـ \`.setkdrama all\`.` }, { quoted: mek });
                        return;
                    }

                    // ── أمر .kdrama (دراما كورية مدبلجة/مترجمة — 6 مصادر) ──
                    if (command === '.kdrama') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم المسلسل الكوري.\n💡 *مثال:* `.kdrama لعبة الحبار` أو `.kdrama squid game`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            const locked = kdLockedSource ? KD_SOURCE_NAMES[kdLockedSource] : null;
                            await XeonBotInc.sendMessage(chatId, {
                                text: locked
                                    ? `🔍 جاري البحث عن *${query}* في مصدر ${locked.label} فقط...`
                                    : `🔍 جاري البحث عن *${query}* في 6 مصادر...`
                            }, { quoted: mek });

                            const results = [];
                            const seenTitles = new Set();
                            const addResults = (source, cdSource, list, max) => {
                                for (const it of (Array.isArray(list) ? list : []).slice(0, max)) {
                                    const key = String(it.title || '').trim().toLowerCase();
                                    if (!key || seenTitles.has(key)) continue;
                                    seenTitles.add(key);
                                    results.push({ source, cdSource, id: it.id, type: 'series', title: it.title });
                                }
                            };
                            if (locked) {
                                const list = await kdSearchOne(kdLockedSource, query);
                                addResults(locked.source, locked.cdSource, list, 10);
                            } else {
                                const [akwam, meow, cdCloud, dw, lody, okru] = await Promise.allSettled([
                                    akwamSearch(query, 'series'),
                                    meowSearch(query, 'series'),
                                    cloudDaySearch(query, 'CimaCloud', '2'),
                                    dramaWorldSearch(query),
                                    lodynetSearch(query),
                                    okruSearchRaw(query)
                                ]);
                                if (akwam.status === 'fulfilled') addResults('akwam', null, akwam.value, 2);
                                if (meow.status === 'fulfilled') addResults('meowtv', null, meow.value, 2);
                                if (cdCloud.status === 'fulfilled') addResults('cloudday', 'CimaCloud', cdCloud.value, 2);
                                if (dw.status === 'fulfilled') addResults('dramaworld', null, dw.value, 2);
                                if (lody.status === 'fulfilled') addResults('lodynet', null, lody.value, 2);
                                if (okru.status === 'fulfilled') addResults('okru', null, okru.value.map(v => ({ id: v.id, title: v.title })), 2);
                            }
                            if (results.length === 0) throw new Error(locked ? `لا نتائج في مصدر ${locked.label}. جرّب اسماً مختلفاً أو بدّل المصدر بـ \`.setkdrama <مصدر آخر>\`.` : 'لم يتم العثور على أي نتائج في المصادر الستة. جرّب اسماً مختلفاً.');

                            const tagOf = s => s === 'akwam' ? '📺 Akwam' : s === 'meowtv' ? '🐱 MeowTv' : s === 'cloudday' ? '☁️ CloudDay' : s === 'dramaworld' ? '🎭 DramaWorld' : s === 'lodynet' ? '🎬 Lodynet' : '📺 ok.ru';
                            let responseText = `🇰🇷 *نتائج البحث (دراما كورية):*\n\n`;
                            results.slice(0, 15).forEach((r, index) => {
                                responseText += `*${index + 1}* - ${r.title} [${tagOf(r.source)}]\n`;
                            });
                            responseText += `\n💡 *طريقة الاختيار:*\nقم **بالرد (Reply)** على هذه الرسالة برقم المسلسل المطلوب.\n\n🍿 *مثال:* \`1\``;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            mvCache.set(sentMsg.key.id, {
                                stage: 'search',
                                results: results.slice(0, 15),
                                timestamp: Date.now()
                            });
                            setTimeout(() => mvCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .kdramaapi (فحص حالة مصادر الدراما الكورية) ──
                    if (command === '.kdramaapi') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '🔍 جاري فحص مصادر الدراما الكورية...'
                            }, { quoted: mek });
                            const probes = [
                                { name: '📺 Akwam', fn: async () => { const r = await akwamSearch('الحبار', 'series'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🐱 MeowTv', fn: async () => { const r = await meowSearch('squid game', 'series'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '☁️ CloudDay (CimaCloud)', fn: async () => { const r = await cloudDaySearch('squid game', 'CimaCloud', '2'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎭 DramaWorld', fn: async () => { const r = await dramaWorldSearch('squid game'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '🎬 Lodynet', fn: async () => { const r = await lodynetSearch('squid game'); if (!r.length) throw new Error('لا نتائج'); return r.length; } },
                                { name: '📺 ok.ru', fn: async () => { const r = await okruSearchRaw('squid game'); if (!r.length) throw new Error('لا نتائج'); return r.length; } }
                            ];
                            const settled = await Promise.allSettled(probes.map(async p => {
                                const t = Date.now();
                                const n = await p.fn();
                                return { name: p.name, ms: Date.now() - t, n };
                            }));
                            let out = `📊 *حالة مصادر الدراما الكورية:*\n\n`;
                            settled.forEach((s, i) => {
                                if (s.status === 'fulfilled') {
                                    out += `🟢 *${s.value.name}* — شغال (${s.value.ms}ms، ${s.value.n} نتيجة)\n`;
                                } else {
                                    out += `🔴 *${probes[i].name}* — متوقف (${String((s.reason && s.reason.message) || 'خطأ').slice(0, 80)})\n`;
                                }
                            });
                            out += `\n🕐 ${new Date().toLocaleString('ar-EG', { timeZone: 'Africa/Cairo' })}`;
                            await XeonBotInc.sendMessage(chatId, { text: out }, { quoted: mek });
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل الفحص:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }


                    // ── أمر .manga (3asq.online) ──
                    if (command === '.manga') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم المانجا.\n💡 *مثال:* `.manga naruto`\nأو: `.manga بلاك كلوفر`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري البحث عن *${query}* في 3asq.org...`
                            }, { quoted: mek });

                            const searchSlug = query.trim().replace(/\s+/g, '+');
                            const searchRes  = await axios.get(
                                `https://3asq.online/?s=${encodeURIComponent(searchSlug)}&post_type=wp-manga`,
                                { headers: { 'User-Agent': 'Mozilla/5.0' }, timeout: 15000 }
                            );

                            const titleRegex = /<h3[^>]*class="[^"]*h4[^"]*"[^>]*>\s*<a[^>]*href="([^"]+)"[^>]*>([^<]+)<\/a>/gi;
                            const results = [];
                            let m;
                            while ((m = titleRegex.exec(searchRes.data)) !== null) {
                                const url  = m[1].trim();
                                const name = m[2].trim();
                                if (!results.some(r => r.url === url)) {
                                    results.push({ url, name });
                                }
                            }

                            if (results.length === 0) throw new Error('لم يتم العثور على نتائج. جرّب اسماً مختلفاً.');

                            let resText = `📚 *نتائج البحث في 3asq.org:*\n\n`;
                            results.slice(0, 12).forEach((r, i) => {
                                resText += `*${i + 1}* - ${r.name}\n`;
                            });
                            resText += `\n💡 **رد (Reply)** برقم المانجا المطلوبة.`;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: resText }, { quoted: mek });
                            mangaCache.set(sentMsg.key.id, {
                                stage: 'manga_list',
                                results: results.slice(0, 12),
                                timestamp: Date.now()
                            });
                            setTimeout(() => mangaCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .okru (تحميل فيديو من ok.ru وإرساله) ──
                    if (command === '.okru') {
                        if (!query || !/ok\.ru\//i.test(query)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إرسال رابط فيديو صحيح من ok.ru\n💡 *مثال:* `.okru https://ok.ru/video/123456789`'
                            }, { quoted: mek });
                            return;
                        }

                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري استخراج رابط الفيديو من ok.ru...`
                            }, { quoted: mek });

                            const pageUrl = query.trim();
                            const { title, videos } = await extractOkruVideo(pageUrl);

                            let listText = `🎬 *${title}*\n\n📺 *اختر الجودة المطلوبة (رد بالرقم):*\n\n`;
                            videos.forEach((v, i) => {
                                listText += `*${i + 1}* - ${OKRU_QUALITY_LABELS[v.name] || v.name || 'غير معروفة'}\n`;
                            });
                            listText += `\n💡 **رد (Reply)** على هذه الرسالة برقم الجودة.`;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: listText }, { quoted: mek });
                            okruCache.set(sentMsg.key.id, {
                                title,
                                videos,
                                timestamp: Date.now()
                            });
                            setTimeout(() => okruCache.delete(sentMsg.key.id), 300000);

                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استخراج روابط الفيديو من ok.ru:\n\`${err.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .m3u8 (تحميل فيديو من رابط m3u8/HLS وإرساله - بأجزاء إن تجاوز الحجم) ──
                    if (command === '.m3u8' || command === '.hls') {
                        if (!query || !/^https?:\/\//i.test(query)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إرسال رابط m3u8 صحيح\n💡 *مثال:* `.m3u8 https://example.com/playlist.m3u8`\n💡 *مع Referer مخصص (لو ظهر خطأ 403):* `.m3u8 https://example.com/playlist.m3u8 https://example.com`'
                            }, { quoted: mek });
                            return;
                        }

                        // args[1] = الرابط، args[2] (اختياري) = Referer مخصص لتفادي حظر 403
                        const m3u8Url = args[1];
                        const customReferer = args[2] && /^https?:\/\//i.test(args[2]) ? args[2] : null;
                        let refererToUse = customReferer;
                        if (!refererToUse) {
                            try { refererToUse = new URL(m3u8Url).origin + '/'; } catch (_) { refererToUse = null; }
                        }
                        const HLS_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';
                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        const fileId = randomBytes(4).toString('hex');
                        const outputPath = path.join(tmpDir, `M3U8_${fileId}.mp4`);
                        const segDir = path.join(tmpDir, `m3u8_${fileId}_parts`);

                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚡ *جاري تحميل فيديو m3u8...*\nقد يستغرق هذا بعض الوقت حسب طول الفيديو وسرعة السيرفر.`
                            }, { quoted: mek });

                            // تحميل ودمج الفيديو من رابط m3u8 (فيديو كامل VOD وليس بثاً مباشراً - بدون إعادة ترميز)
                            await new Promise((resolve, reject) => {
                                const args = ['-y'];
                                if (refererToUse) {
                                    args.push('-headers', `Referer: ${refererToUse}\r\nOrigin: ${refererToUse}\r\n`);
                                }
                                args.push(
                                    '-user_agent', HLS_USER_AGENT,
                                    '-reconnect', '1',
                                    '-reconnect_streamed', '1',
                                    '-reconnect_delay_max', '5',
                                    '-i', m3u8Url,
                                    '-c', 'copy',
                                    '-bsf:a', 'aac_adtstoasc',
                                    outputPath
                                );
                                const proc = spawn('ffmpeg', args);
                                let stderr = '';
                                proc.stderr.on('data', (d) => { stderr += d.toString(); });
                                proc.on('close', (code) => {
                                    if (code === 0 && fs.existsSync(outputPath)) resolve();
                                    else reject(new Error(`فشل تحميل الفيديو (ffmpeg code ${code}):\n${stderr.slice(-500)}`));
                                });
                                proc.on('error', reject);
                            });

                            const totalBytes = fs.statSync(outputPath).size;

                            if (totalBytes <= MAX_DOWNLOAD_BYTES) {
                                // الحجم ضمن الحد المسموح - إرسال كملف واحد
                                const sizeMB = (totalBytes / 1024 / 1024).toFixed(2);
                                await XeonBotInc.sendMessage(chatId, {
                                    document: { url: outputPath },
                                    mimetype: 'video/mp4',
                                    fileName: `Video_${fileId}.mp4`,
                                    caption: `✅ *اكتمل تحميل الفيديو!*\n⚖️ *الحجم:* ${sizeMB} MB`
                                }, { quoted: mek });
                            } else {
                                // الحجم أكبر من 200 ميجا - يتم تقسيمه لأجزاء وإرسالها مثل التسجيل
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `📦 حجم الفيديو *${(totalBytes / 1024 / 1024).toFixed(1)} MB* أكبر من ${MAX_DOWNLOAD_MB} MB — جاري تقسيمه وإرساله كأجزاء...`
                                }, { quoted: mek });

                                fs.mkdirSync(segDir, { recursive: true });

                                // فحص مدة الفيديو لحساب معدل البت الفعلي وبالتالي مدة كل جزء (~100 ميجا للجزء)
                                const durationSec = await new Promise((resolve) => {
                                    const p = spawn('ffprobe', [
                                        '-v', 'quiet', '-print_format', 'json', '-show_format', outputPath
                                    ]);
                                    let out = '';
                                    p.stdout.on('data', (d) => { out += d.toString(); });
                                    p.on('close', () => {
                                        try {
                                            const data = JSON.parse(out);
                                            const dur = parseFloat(data?.format?.duration);
                                            resolve(dur && dur > 0 ? dur : null);
                                        } catch (_) { resolve(null); }
                                    });
                                    p.on('error', () => resolve(null));
                                });

                                const bitrateBps = durationSec ? (totalBytes * 8) / durationSec : null;
                                const segmentTimeSec = computeSegmentTimeSec(bitrateBps);

                                const pattern = path.join(segDir, `part_%03d.mp4`);
                                await new Promise((resolve, reject) => {
                                    const args = [
                                        '-y', '-i', outputPath,
                                        '-c', 'copy',
                                        '-f', 'segment',
                                        '-segment_time', String(segmentTimeSec),
                                        '-reset_timestamps', '1',
                                        pattern
                                    ];
                                    const proc = spawn('ffmpeg', args);
                                    let stderr = '';
                                    proc.stderr.on('data', (d) => { stderr += d.toString(); });
                                    proc.on('close', (code) => {
                                        if (code === 0) resolve();
                                        else reject(new Error(`فشل تقسيم الفيديو (ffmpeg code ${code}):\n${stderr.slice(-500)}`));
                                    });
                                    proc.on('error', reject);
                                });

                                const parts = fs.readdirSync(segDir)
                                    .filter(f => f.startsWith('part_') && f.endsWith('.mp4'))
                                    .sort();
                                if (parts.length === 0) throw new Error('فشل إنشاء أجزاء الفيديو.');

                                for (let i = 0; i < parts.length; i++) {
                                    const partPath = path.join(segDir, parts[i]);
                                    const partSizeMB = (fs.statSync(partPath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: partPath },
                                        mimetype: 'video/mp4',
                                        fileName: `Video_${fileId}_part${i + 1}.mp4`,
                                        caption: `📦 *الجزء ${i + 1}/${parts.length}*\n⚖️ ${partSizeMB} MB`
                                    }, { quoted: mek });
                                    try { fs.unlinkSync(partPath); } catch (_) {}
                                }

                                await XeonBotInc.sendMessage(chatId, {
                                    text: `✅ *اكتمل إرسال الفيديو بالكامل!*\n📦 عدد الأجزاء: ${parts.length}`
                                }, { quoted: mek });
                            }
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل تحميل/إرسال فيديو m3u8:\n\`${err.message}\``
                            }, { quoted: mek });
                        } finally {
                            if (fs.existsSync(outputPath)) {
                                try { fs.unlinkSync(outputPath); } catch (_) {}
                            }
                            if (fs.existsSync(segDir)) {
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }
                        }
                        return;
                    }
                }

                // ============================================================
                // باقي معالجات البوت الأصلية
                // ============================================================
                if (mek.key && mek.key.remoteJid === 'status@broadcast') {
                    await handleStatus(XeonBotInc, chatUpdate);
                    return;
                }
                if (!XeonBotInc.public && !mek.key.fromMe && chatUpdate.type === 'notify') {
                    const isGroup = mek.key?.remoteJid?.endsWith('@g.us')
                    if (!isGroup) return
                }
                if (mek.key.id.startsWith('BAE5') && mek.key.id.length === 16) return

                if (XeonBotInc?.msgRetryCounterCache) {
                    XeonBotInc.msgRetryCounterCache.clear()
                }

                try {
                    await handleMessages(XeonBotInc, chatUpdate, true)
                } catch (err) {
                    console.error("Error in handleMessages:", err)
                }

            } catch (err) {
                console.error("Error in messages.upsert:", err)
            }
        })

        XeonBotInc.decodeJid = (jid) => {
            if (!jid) return jid
            if (/:\d+@/gi.test(jid)) {
                let decode = jidDecode(jid) || {}
                return decode.user && decode.server && decode.user + '@' + decode.server || jid
            } else return jid
        }

        XeonBotInc.ev.on('connection.update', async (s) => {
            const { connection, lastDisconnect, qr } = s
            if (qr) console.log(chalk.yellow('📱 QR Code generated.'))
            if (connection == "open") {
                console.log(chalk.green(`🤖 Bot Connected Successfully! ✅`));
            }
            if (connection === 'close') {
                const shouldReconnect = (lastDisconnect?.error)?.output?.statusCode !== DisconnectReason.loggedOut
                if (shouldReconnect) {
                    await delay(5000)
                    startXeonBotInc()
                }
            }
        })

        return XeonBotInc
    } catch (error) {
        console.error('Error in startXeonBotInc:', error)
        await delay(5000)
        startXeonBotInc()
    }
}

startXeonBotInc().catch(error => {
    process.exit(1)
})
