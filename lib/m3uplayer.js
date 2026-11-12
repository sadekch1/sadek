// ============================================================
// lib/m3uplayer.js — مشغّل m3u المستقل (أوامر .playm3u / .stopplaym3u)
// وحدة حقيقية كاملة: تسجيل متواصل مُجزّأ عبر ffmpeg (نسخ مباشر بلا
// إعادة ترميز) وإرسال كل جزء كملف فور اكتماله — نفس أسلوب .record.
// الواجهة المطلوبة من index.js:
//   isValidM3UUrl(url) -> boolean
//   hasActiveM3UPlayer(chatId) -> boolean
//   stopM3UPlayer(chatId) -> boolean (true إذا كان هناك تشغيل نشط)
//   startM3UPlayer({sock, chatId, mek, streamUrl, durationMin,
//                   manualSegmentMin, tmpRootDir}) -> Promise
//   M3U_MAX_DURATION_MIN -> number
// ============================================================
const { spawn } = require('child_process');
const fs = require('fs');
const path = require('path');

const M3U_MAX_DURATION_MIN = 360; // 6 ساعات كحد أقصى مثل باقي أوامر التسجيل
const TARGET_MB = 100;            // الحجم المستهدف لكل جزء عند التقسيم التلقائي
const SAFETY_BYTES = 180 * 1024 * 1024; // حد أمان لحجم الجزء الواحد
const BROWSER_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36';

// chatId -> { cancelled, proc }
const activeM3UPlayers = new Map();

// التحقق من رابط m3u/m3u8 (وأيضاً روابط بث Xtream المنتهية بـ .ts)
// + روابط Xtream بلا امتداد من قوائم مثل لوحة sadek (‏/live/user/pass/12345
// أو /user/pass/12345) وروابط get.php?type=m3u — كانت تُرفض سابقاً.
function isValidM3UUrl(url) {
    if (!url || typeof url !== 'string') return false;
    const u = url.trim();
    if (!/^https?:\/\/\S+$/i.test(u)) return false;
    const lower = u.toLowerCase();
    const pathPart = u.split(/[?#]/)[0].toLowerCase();
    if (pathPart.endsWith('.m3u') || pathPart.endsWith('.m3u8') ||
        pathPart.endsWith('.ts') || lower.includes('.m3u8')) return true;
    // Xtream: /live|movie|series/<user>/<pass>/<numeric-id> أو /<user>/<pass>/<numeric-id>
    if (/^\/(live|movie|series)\/[^\/]+\/[^\/]+\/\d+$/i.test(pathPart.replace(/^https?:\/\/[^\/]+/i, ''))) return true;
    if (/^\/[^\/]+\/[^\/]+\/\d+$/i.test(pathPart.replace(/^https?:\/\/[^\/]+/i, ''))) return true;
    // Xtream get.php: ?type=m3u أو type=m3u8 أو output=ts
    if (/get\.php/i.test(pathPart) && /(^|[?&])type=m3u8?([&#]|$)/i.test(lower)) return true;
    return false;
}

function hasActiveM3UPlayer(chatId) {
    return activeM3UPlayers.has(chatId);
}

function stopM3UPlayer(chatId) {
    const control = activeM3UPlayers.get(chatId);
    if (!control) return false;
    control.cancelled = true;
    if (control.proc) {
        try { control.proc.kill('SIGINT'); } catch (_) {}
    }
    return true;
}

// فحص معدل بت البث عبر ffprobe (لمعرفة مدة جزء تعطي ~100MB) — null عند الفشل
function probeBitrate(streamUrl) {
    return new Promise((resolve) => {
        let settled = false;
        const finish = (v) => { if (!settled) { settled = true; resolve(v); } };
        const proc = spawn('ffprobe', [
            '-v', 'quiet',
            '-print_format', 'json',
            '-show_format',
            '-user_agent', BROWSER_UA,
            '-analyzeduration', '4000000',
            '-probesize', '4000000',
            streamUrl
        ]);
        let out = '';
        proc.stdout.on('data', (d) => { out += d.toString(); });
        proc.on('close', () => {
            try {
                const data = JSON.parse(out);
                const br = parseInt(data?.format?.bit_rate);
                if (br && br > 0) return finish(br);
            } catch (_) {}
            finish(null);
        });
        proc.on('error', () => finish(null));
        setTimeout(() => { try { proc.kill(); } catch (_) {} finish(null); }, 12000);
    });
}

function computeSegmentTimeSec(bitrateBps) {
    if (!bitrateBps || bitrateBps <= 0) return 6 * 60; // احتياطي: 6 دقائق
    const seconds = Math.floor((TARGET_MB * 1024 * 1024 * 8) / bitrateBps);
    return Math.max(120, Math.min(20 * 60, seconds));
}

async function startM3UPlayer({ sock, chatId, mek, streamUrl, durationMin, manualSegmentMin, tmpRootDir }) {
    if (activeM3UPlayers.has(chatId)) {
        throw new Error('يوجد تشغيل m3u نشط بالفعل في هذه المحادثة.');
    }

    const control = { cancelled: false, proc: null };
    activeM3UPlayers.set(chatId, control);

    const safeChat = String(chatId).replace(/[^a-zA-Z0-9]/g, '_');
    const segDir = path.join(tmpRootDir, `m3u_${safeChat}_${Date.now()}`);
    fs.mkdirSync(segDir, { recursive: true });

    const totalDurationSec = durationMin * 60;
    let segmentIndex = 0;

    const sendPart = async (filePath) => {
        segmentIndex++;
        const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
        try {
            await sock.sendMessage(chatId, {
                document: { url: filePath },
                mimetype: 'video/mp4',
                fileName: `M3U_part${segmentIndex}.mp4`,
                caption: `📦 *الجزء ${segmentIndex}*\n📡 تشغيل m3u\n⚖️ ${sizeMB} MB`
            }, { quoted: mek });
        } finally {
            try { fs.unlinkSync(filePath); } catch (_) {}
        }
    };

    try {
        // مدة الجزء: يدوية إن حدّدها المستخدم، وإلا تلقائية (~100MB) بعد فحص معدل البت
        let segmentTimeSec;
        if (manualSegmentMin) {
            segmentTimeSec = manualSegmentMin * 60;
        } else {
            const bitrate = await probeBitrate(streamUrl);
            segmentTimeSec = computeSegmentTimeSec(bitrate);
            if (segmentTimeSec > totalDurationSec) segmentTimeSec = totalDurationSec;
        }

        await sock.sendMessage(chatId, {
            text: `▶️ *بدأ تشغيل m3u*\n⏱️ المدة الكلية: ${durationMin} دقيقة\n✂️ كل جزء: ${Math.round(segmentTimeSec / 60)} دقيقة تقريباً\n🛑 للإيقاف: \`.stopplaym3u\``
        }, { quoted: mek });

        const pattern = path.join(segDir, 'seg_%03d.mp4');
        const proc = spawn('ffmpeg', [
            '-y',
            '-user_agent', BROWSER_UA,
            '-i', streamUrl,
            '-t', String(totalDurationSec),
            '-c', 'copy',
            '-f', 'segment',
            '-segment_time', String(segmentTimeSec),
            '-reset_timestamps', '1',
            pattern
        ]);
        control.proc = proc;

        let stderrTail = '';
        proc.stderr.on('data', (d) => {
            stderrTail = (stderrTail + d.toString()).slice(-2000);
        });

        let finished = false;
        proc.on('close', () => { finished = true; });
        proc.on('error', () => { finished = true; });

        const listSegFiles = () => {
            try {
                return fs.readdirSync(segDir)
                    .filter(f => /^seg_\d+\.mp4$/.test(f))
                    .sort()
                    .map(f => path.join(segDir, f));
            } catch (_) { return []; }
        };

        let sentCount = 0;
        let abortedBySize = false;

        // أثناء التسجيل: كل الملفات عدا الأخير (قيد الكتابة) اكتملت فعلاً
        while (!finished) {
            if (control.cancelled) {
                try { proc.kill('SIGINT'); } catch (_) {}
                break;
            }
            const files = listSegFiles();
            // فحص أمان الحجم للجزء الحالي قيد الكتابة
            if (files.length > sentCount) {
                const current = files[files.length - 1];
                try {
                    if (fs.statSync(current).size > SAFETY_BYTES) {
                        abortedBySize = true;
                        try { proc.kill('SIGINT'); } catch (_) {}
                        break;
                    }
                } catch (_) {}
            }
            for (let i = sentCount; i < files.length - 1; i++) {
                await sendPart(files[i]);
                sentCount++;
            }
            await new Promise(r => setTimeout(r, 2000));
        }

        // انتظار انتهاء العملية فعلياً (بحد أقصى 10 ثوانٍ بعد SIGINT)
        for (let i = 0; i < 50 && !finished; i++) {
            await new Promise(r => setTimeout(r, 200));
        }
        if (!finished) { try { proc.kill('SIGKILL'); } catch (_) {} }

        // إرسال الأجزاء المتبقية (الأخير اكتمل الآن بخروج ffmpeg)
        const remaining = listSegFiles().slice(sentCount);
        for (const f of remaining) {
            try {
                if (fs.statSync(f).size > 0) { await sendPart(f); sentCount++; }
            } catch (_) {}
        }

        if (segmentIndex === 0) {
            const tail = stderrTail.trim().split('\n').slice(-3).join('\n');
            throw new Error(`لم يتم استلام أي جزء من البث. تأكد أن الرابط يعمل وأنه رابط بث مباشر (m3u8) لا رابط قائمة قنوات.${tail ? `\n${tail}` : ''}`);
        }

        if (abortedBySize) {
            await sock.sendMessage(chatId, {
                text: `⚠️ توقف تشغيل m3u: تجاوز الجزء الحالي حد الأمان (${Math.round(SAFETY_BYTES / 1024 / 1024)} MB). تم إرسال ${segmentIndex} جزء.`
            }, { quoted: mek });
        } else if (control.cancelled) {
            await sock.sendMessage(chatId, {
                text: `🛑 توقف تشغيل m3u بطلبك. تم إرسال ${segmentIndex} جزء.`
            }, { quoted: mek });
        } else {
            await sock.sendMessage(chatId, {
                text: `✅ انتهى تشغيل m3u — تم إرسال ${segmentIndex} جزء (${durationMin} دقيقة).`
            }, { quoted: mek });
        }
    } finally {
        activeM3UPlayers.delete(chatId);
        try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
    }
}

module.exports = {
    isValidM3UUrl,
    hasActiveM3UPlayer,
    stopM3UPlayer,
    startM3UPlayer,
    M3U_MAX_DURATION_MIN
};
