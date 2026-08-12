require('dotenv').config();

const {
  Client,
  GatewayIntentBits,
  Collection,
  ModalBuilder,
  TextInputBuilder,
  TextInputStyle,
  ActionRowBuilder,
  ButtonBuilder,
  ButtonStyle,
  PermissionsBitField,
  EmbedBuilder,
  Events
} = require('discord.js');

const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const net = require('net');

const LOCK_FILE_PATH = path.join(__dirname, 'bot.lock');

function processExists(pid) {
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

function cleanupLockFile() {
  if (!fs.existsSync(LOCK_FILE_PATH)) return;
  try {
    const raw = fs.readFileSync(LOCK_FILE_PATH, 'utf8');
    const data = JSON.parse(raw);
    if (data.pid === process.pid) {
      fs.unlinkSync(LOCK_FILE_PATH);
    }
  } catch {
    try {
      fs.unlinkSync(LOCK_FILE_PATH);
    } catch {
      // ignore
    }
  }
}

function ensureSingleInstance() {
  // First attempt a TCP bind on a configured port to enforce a single instance
  const port = Number(process.env.SINGLE_INSTANCE_PORT) || 54321;
  let server = null;
  try {
    server = net.createServer().listen(port, '127.0.0.1');
    server.on('error', (err) => {
      if (err && err.code === 'EADDRINUSE') {
        console.error(`Another bot instance is already running (port ${port} in use). Exiting to prevent duplicates.`);
        process.exit(1);
      }
    });
  } catch (err) {
    // If binding fails synchronously, fall back to lockfile check below
  }

  // Fallback/file based lock (keeps previous behavior for platforms where TCP binding may fail)
  if (fs.existsSync(LOCK_FILE_PATH)) {
    try {
      const raw = fs.readFileSync(LOCK_FILE_PATH, 'utf8');
      const data = JSON.parse(raw);
      if (data?.pid && processExists(data.pid)) {
        console.error('Another bot instance is already running. Exiting to prevent duplicates.');
        if (server) try { server.close(); } catch {};
        process.exit(1);
      }
      fs.unlinkSync(LOCK_FILE_PATH);
    } catch (error) {
      console.error('Failed to read or remove existing lock file:', error);
    }
  }

  try {
    fs.writeFileSync(LOCK_FILE_PATH, JSON.stringify({ pid: process.pid, cwd: process.cwd(), startedAt: new Date().toISOString() }), { flag: 'w' });
  } catch (error) {
    console.error('Failed to create bot lock file:', error);
  }

  process.on('exit', () => { cleanupLockFile(); if (server) try { server.close(); } catch {} });
  process.on('SIGINT', () => { cleanupLockFile(); if (server) try { server.close(); } catch {}; process.exit(0); });
  process.on('SIGTERM', () => { cleanupLockFile(); if (server) try { server.close(); } catch {}; process.exit(0); });
}

ensureSingleInstance();
console.log(`[BOOT] PID=${process.pid}`);

const client = new Client({
  intents: [
    GatewayIntentBits.Guilds,
    GatewayIntentBits.GuildMessages,
    GatewayIntentBits.MessageContent,
    GatewayIntentBits.GuildMembers,
    GatewayIntentBits.GuildVoiceStates,
    GatewayIntentBits.GuildPresences
  ]
});

client.commands = new Collection();
const processedInteractionIds = new Set();
const ROLELIST_PAGE_SIZE = 10;
// Recent interaction signature map to prevent near-duplicate processing (user double-clicks or duplicated events)
const recentInteractionSignatures = new Map(); // signature -> timestamp
const DUPLICATE_WINDOW_MS = 1000; // 1 second
// Recent outgoing send dedupe: prevent sending same content to same channel repeatedly
const recentSends = new Map(); // key -> timestamp
const SEND_DEDUPE_MS = 5000; // 5 seconds

const applyAttempts = new Map(); // userId -> timestamps
const BLACKLIST_FILE_PATH = path.join(__dirname, 'blacklist.json');
const APPLICATION_COUNTER_FILE_PATH = path.join(__dirname, 'application-counter.json');
const SUBMITTED_APPLICATIONS_FILE_PATH = path.join(__dirname, 'submitted-applications.json');
const SUBMISSION_LOCKS_DIR = path.join(__dirname, 'submission_locks');
const APPLICATIONS_CHANNEL_ID = process.env.APPLICATIONS_CHANNEL_ID || process.env.APPLY_CHANNEL_ID;
const APPLY_MESSAGE_CHANNEL_ID = process.env.APPLY_MESSAGE_CHANNEL_ID || process.env.APPLY_CHANNEL_ID;
const APPLY_LOG_CHANNEL_ID = process.env.APPLY_LOG_CHANNEL_ID;
const EVENT_APPLICATION_LOG_CHANNEL_ID = process.env.EVENT_APPLICATION_LOG_CHANNEL_ID || process.env.EVENT_APPLY_LOG_CHANNEL_ID || '1536969703329763358';
const CLAN_LEADER_ROLE_ID = process.env.CLAN_LEADER_ROLE_ID;
const AV_FAMILY_ROLE_ID = process.env.AV_FAMILY_ROLE_ID || process.env.ACCEPT_ROLE_ID;
const TEST_VOICE_CHANNEL_ID = process.env.TEST_VOICE_CHANNEL_ID;

const blacklistedUsers = loadBlacklistedUsers();
const submittedApplications = loadSubmittedApplications();
let nextApplicationNumber = loadNextApplicationNumber();
const MAX_ATTEMPTS = 5;
const WINDOW_MS = 60 * 1000;
const BLACKLIST_MS = 5 * 60 * 1000; // 5 minutes blacklist

function loadBlacklistedUsers() {
  try {
    if (!fs.existsSync(BLACKLIST_FILE_PATH)) return new Map();
    const raw = fs.readFileSync(BLACKLIST_FILE_PATH, 'utf8');
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') return new Map();
    return new Map(Object.entries(parsed).map(([userId, expiry]) => [userId, Number(expiry)]));
  } catch (err) {
    console.error('Failed to load blacklist:', err);
    return new Map();
  }
}

function saveBlacklistedUsers() {
  try {
    const data = Object.fromEntries(blacklistedUsers);
    fs.writeFileSync(BLACKLIST_FILE_PATH, JSON.stringify(data, null, 2));
  } catch (err) {
    console.error('Failed to save blacklist:', err);
  }
}

function loadNextApplicationNumber() {
  try {
    if (!fs.existsSync(APPLICATION_COUNTER_FILE_PATH)) return 1;
    const raw = fs.readFileSync(APPLICATION_COUNTER_FILE_PATH, 'utf8');
    const parsed = JSON.parse(raw);
    return Number(parsed?.nextApplicationNumber) || 1;
  } catch (err) {
    console.error('Failed to load application counter:', err);
    return 1;
  }
}

function saveNextApplicationNumber() {
  try {
    fs.writeFileSync(APPLICATION_COUNTER_FILE_PATH, JSON.stringify({ nextApplicationNumber }, null, 2));
  } catch (err) {
    console.error('Failed to save application counter:', err);
  }
}

function loadSubmittedApplications() {
  try {
    if (!fs.existsSync(SUBMITTED_APPLICATIONS_FILE_PATH)) {
      return {
        ids: new Set(),
        hashes: new Set(),
        byUser: new Map()
      };
    }

    const raw = fs.readFileSync(SUBMITTED_APPLICATIONS_FILE_PATH, 'utf8');
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') {
      return {
        ids: new Set(),
        hashes: new Set(),
        byUser: new Map()
      };
    }

    const byUser = new Map();
    const submissions = new Map();
    if (parsed.byUser && typeof parsed.byUser === 'object') {
      for (const [userId, hashes] of Object.entries(parsed.byUser)) {
        byUser.set(userId, new Set(Array.isArray(hashes) ? hashes : []));
      }
    }

    // load submissions map if present
    if (parsed.submissions && typeof parsed.submissions === 'object') {
      for (const [hash, meta] of Object.entries(parsed.submissions)) {
        submissions.set(hash, {
          applicationNumber: Number(meta.applicationNumber) || null,
          applicantId: meta.applicantId || null,
          messageId: meta.messageId || null
        });
      }
    }

    return {
      ids: new Set(Array.isArray(parsed.ids) ? parsed.ids : []),
      hashes: new Set(Array.isArray(parsed.hashes) ? parsed.hashes : []),
      byUser,
      submissions
    };
  } catch (err) {
    console.error('Failed to load submitted applications:', err);
    return {
      ids: new Set(),
      hashes: new Set(),
      byUser: new Map(),
      submissions: new Map()
    };
  }
}

function saveSubmittedApplications() {
  try {
    const byUserObj = {};
    for (const [userId, hashes] of submittedApplications.byUser.entries()) {
      byUserObj[userId] = [...hashes];
    }

    const submissionsObj = {};
    for (const [hash, meta] of (submittedApplications.submissions || new Map()).entries()) {
      submissionsObj[hash] = {
        applicationNumber: meta.applicationNumber,
        applicantId: meta.applicantId,
        messageId: meta.messageId || null
      };
    }

    fs.writeFileSync(SUBMITTED_APPLICATIONS_FILE_PATH, JSON.stringify({
      ids: [...submittedApplications.ids],
      hashes: [...submittedApplications.hashes],
      byUser: byUserObj,
      submissions: submissionsObj
    }, null, 2));
  } catch (err) {
    console.error('Failed to save submitted applications:', err);
  }
}

function removeUserSubmittedApplicationHashes(userId) {
  if (!submittedApplications.byUser.has(userId)) return 0;
  const userHashes = submittedApplications.byUser.get(userId);
  let removed = 0;
  for (const hash of userHashes) {
    if (submittedApplications.hashes.delete(hash)) {
      removed += 1;
      // remove any persistent lock file for this submission hash
      try {
        const lockPath = path.join(SUBMISSION_LOCKS_DIR, `${hash}.lock`);
        if (fs.existsSync(lockPath)) fs.unlinkSync(lockPath);
      } catch (e) {
        // ignore
      }
    }
  }
  submittedApplications.byUser.delete(userId);
  saveSubmittedApplications();
  return removed;
}

function createApplicationHash(payload) {
  const ordered = Object.keys(payload).sort().reduce((acc, key) => {
    acc[key] = payload[key];
    return acc;
  }, {});
  return crypto.createHash('sha256').update(JSON.stringify(ordered)).digest('hex');
}

function createSubmissionHash(applicantId, details) {
  return createApplicationHash({ applicantId, ...details });
}

async function hasDuplicateApplicationMessage(channel, applicantId, applicationNumber) {
  if (!channel || !channel.isTextBased()) return false;
  try {
    const messages = await fetchChannelMessages(channel, 500);
    return [...messages.values()].some(msg => {
      const embed = msg.embeds[0];
      if (!embed) return false;
      const titleMatch = embed.title?.match(/application\s*#(\d+)/i);
      const footerMatch = embed.footer?.text?.match(/(\d{17,19})/);
      const existingNumber = titleMatch ? Number(titleMatch[1]) : null;
      const existingApplicantId = footerMatch ? footerMatch[1] : null;
      return existingNumber === applicationNumber || existingApplicantId === applicantId;
    });
  } catch (err) {
    console.error('Failed to check duplicate application message:', err);
    return false;
  }
}

async function findExistingApplyMessage(channel) {
  if (!channel || !channel.isTextBased()) return null;
  try {
    const messages = await fetchChannelMessages(channel, 500);
    return [...messages.values()].find(msg => {
      if (msg.author?.id !== client.user.id) return false;
      if (msg.components.some(row => row.components.some(component => component.customId === 'apply' || component.customId === 'event_apply'))) return true;
      const embed = msg.embeds[0];
      return embed && embed.title === '🛡️ AVENGERS APPLICATION';
    }) || null;
  } catch (err) {
    console.error('Failed to find existing apply message:', err);
    return null;
  }
}

async function ensureApplyMessageButtons(message) {
  if (!message || !message.edit) return;
  try {
    const row = createApplyButtonRow();
    await message.edit({ components: [row] });
  } catch (err) {
    console.error('Failed to ensure apply message buttons:', err);
  }
}

function extractApplicationNumberFromCustomId(customId) {
  if (!customId) return null;
  const parts = customId.split('_');
  if (parts[0] === 'accept' || parts[0] === 'reject') {
    const value = Number(parts[2]);
    return Number.isFinite(value) ? value : null;
  }
  if (parts[0] === 'status') {
    const value = Number(parts[2]);
    return Number.isFinite(value) ? value : null;
  }
  if (parts[0] === 'move') {
    const value = Number(parts[2]);
    return Number.isFinite(value) ? value : null;
  }
  return null;
}

function extractApplicationNumberFromMessage(message) {
  const embed = message?.embeds?.[0];
  const title = embed?.title || '';
  const titleMatch = title.match(/application\s*#(\d+)/i);
  if (titleMatch) return Number(titleMatch[1]);
  const footerText = embed?.footer?.text || '';
  const footerMatch = footerText.match(/application\s*#(\d+)/i);
  if (footerMatch) return Number(footerMatch[1]);
  return null;
}

function extractApplicantIdFromCustomId(customId) {
  if (!customId) return null;
  const parts = customId.split('_');
  if (parts.length >= 2 && /^\d{17,19}$/.test(parts[1])) {
    return parts[1];
  }
  return null;
}

async function sendStaffLog({ action, applicantUser, applicantId, staffUser, details = null, applicationNumber = null, logChannelId = null }) {
  const channelId = logChannelId || APPLY_LOG_CHANNEL_ID;
  if (!channelId) return;
  const logChannel = await client.channels.fetch(channelId).catch(() => null);
  if (!logChannel || !logChannel.isTextBased()) return;

  const processingId = `${action}:${applicantId || 'unknown'}:${applicationNumber || 'none'}:${Date.now()}:${Math.random().toString(36).slice(2,8)}`;
  console.log('[ROLE LOG START]', `processingId=${processingId}`, `action=${action}`, `applicantId=${applicantId || 'unknown'}`, `applicationNumber=${applicationNumber || 'none'}`, `logChannelId=${channelId}`, `pid=${process.pid}`);

  const now = new Date();
  const date = now.toLocaleDateString('en-GB');
  const time = now.toLocaleTimeString('en-US', { hour: 'numeric', minute: '2-digit', hour12: true });

  const applicantName = applicantUser?.tag || applicantUser?.displayName || applicantUser?.username || 'Unknown';
  const staffName = staffUser?.tag || staffUser?.displayName || staffUser?.username || 'Unknown';
  const content = [
    `${action}`,
    ...(applicationNumber ? [`📄 Application #${applicationNumber}`] : []),
    `Applicant: ${applicantName}`,
    `Applicant ID: ${applicantId || 'Unknown'}`,
    `Staff: ${staffName}`,
    `Action: ${details || action}`,
    `Date: ${date}`,
    `Time: ${time}`
  ].join('\n');

  try {
    const recent = await logChannel.messages.fetch({ limit: 20 });
    const duplicate = recent.some(msg => msg.author?.id === client.user.id && msg.content === content);
    console.log('[ROLE LOG CHECK]', `processingId=${processingId}`, `duplicate=${duplicate}`);
    if (duplicate) {
      console.log('[ROLE LOG SKIP]', `processingId=${processingId}`, `reason=recent_duplicate_detected`);
      return;
    }
  } catch (err) {
    console.error('Failed to fetch recent log messages for dedupe:', err);
  }

  // Use safe send to avoid race conditions causing duplicate sends
  const dedupeKey = `staff:${applicantId || 'unknown'}:${applicationNumber || 'none'}:${action}`;
  console.log('[ROLE SEND START]', `processingId=${processingId}`, `dedupeKey=${dedupeKey}`);
  const sent = await safeChannelSend(logChannel, { content }, dedupeKey).catch(err => { console.error('safeChannelSend error in sendStaffLog:', err); return null; });
  if (sent && sent.id) {
    console.log('[ROLE SEND COMPLETE]', `processingId=${processingId}`, `messageId=${sent.id}`, `applicationNumber=${applicationNumber || 'none'}`, `pid=${process.pid}`);
  } else {
    console.log('[ROLE SEND FAILED]', `processingId=${processingId}`, `applicationNumber=${applicationNumber || 'none'}`, `pid=${process.pid}`);
  }
}

async function safeChannelSend(channel, payload, dedupeKey) {
  if (!channel || !channel.isTextBased()) return null;
  try {
    const key = `${channel.id}:${dedupeKey || JSON.stringify(payload).slice(0, 200)}`;
    const now = Date.now();
    const last = recentSends.get(key) || 0;
    if (now - last < SEND_DEDUPE_MS) {
      console.warn(`[SafeSend][SKIP] skipping duplicate send key=${key}`);
      return null;
    }
    recentSends.set(key, now);
    setTimeout(() => recentSends.delete(key), SEND_DEDUPE_MS + 100);
    // Single attempt only. Do NOT retry automatically — a retry may create duplicates if the first request succeeded on Discord's side.
    return await channel.send(payload);
  } catch (err) {
    console.error('safeChannelSend failed:', err);
    return null;
  }
}

function createApplyModal() {
  const modal = new ModalBuilder()
    .setCustomId('apply_form')
    .setTitle('تقديم للكلان');

  const nameInput = new TextInputBuilder()
    .setCustomId('apply_name')
    .setLabel('Name')
    .setStyle(TextInputStyle.Short)
    .setRequired(true);

  const ageInput = new TextInputBuilder()
    .setCustomId('apply_age')
    .setLabel('Age')
    .setStyle(TextInputStyle.Short)
    .setRequired(true);

  const playStyleInput = new TextInputBuilder()
    .setCustomId('apply_play_style')
    .setLabel('Apostado or eSports')
    .setStyle(TextInputStyle.Short)
    .setRequired(true);

  const gameIdInput = new TextInputBuilder()
    .setCustomId('apply_game_id')
    .setLabel('Game ID')
    .setStyle(TextInputStyle.Short)
    .setRequired(true);

  modal.addComponents(
    new ActionRowBuilder().addComponents(nameInput),
    new ActionRowBuilder().addComponents(ageInput),
    new ActionRowBuilder().addComponents(playStyleInput),
    new ActionRowBuilder().addComponents(gameIdInput)
  );

  return modal;
}

function createApplyEmbed() {
  return new EmbedBuilder()
    .setColor('Blue')
    .setTitle('🛡️ AVENGERS APPLICATION')
    .setDescription(
      'Click the Apply button below to submit your application.\n\n' +
      '⚠️ Warning\n' +
      'Submitting 5 applications within 1 minute will automatically blacklist you.\n\n' +
      '⏳ Your application will be reviewed by the staff.\n\n' +
      'While waiting, you can read the server rules and clan rules.\n\n' +
      'Good luck and thank you for choosing AVENGERS.'
    )
    .setFooter({ text: 'AVENGERS' });
}

function createApplyButtonRow() {
  return new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId('apply')
      .setLabel('تقديم')
      .setEmoji('📝')
      .setStyle(ButtonStyle.Success),
    new ButtonBuilder()
      .setCustomId('event_apply')
      .setLabel('Event Apply')
      .setEmoji('🎯')
      .setStyle(ButtonStyle.Primary)
  );
}

function createEventApplyModal() {
  const modal = new ModalBuilder()
    .setCustomId('event_apply_form')
    .setTitle('تقديم للـ Event');

  const sqNameInput = new TextInputBuilder()
    .setCustomId('event_sq_name')
    .setLabel('SQ Name')
    .setStyle(TextInputStyle.Short)
    .setRequired(true);

  const sqSizeInput = new TextInputBuilder()
    .setCustomId('event_sq_size')
    .setLabel('عدد أعضاء الـ SQ')
    .setStyle(TextInputStyle.Short)
    .setRequired(true);

  const detailsInput = new TextInputBuilder()
    .setCustomId('event_additional_info')
    .setLabel('معلومات إضافية للتقديم')
    .setStyle(TextInputStyle.Paragraph)
    .setRequired(false);

  modal.addComponents(
    new ActionRowBuilder().addComponents(sqNameInput),
    new ActionRowBuilder().addComponents(sqSizeInput),
    new ActionRowBuilder().addComponents(detailsInput)
  );

  return modal;
}

function extractApplicantInfo(customId, message) {
  const applicantId = extractApplicantIdFromCustomId(customId)
    || (message?.embeds?.[0]?.footer?.text || '').match(/(\d{17,19})/)?.[1] || null;

  const applicationNumber = extractApplicationNumberFromCustomId(customId)
    || extractApplicationNumberFromMessage(message);

  return { applicantId, applicationNumber };
}

function hasAdminPermissions(member) {
  return member && member.permissions.has(PermissionsBitField.Flags.Administrator);
}

function requireAdminPermission(message) {
  if (!hasAdminPermissions(message.member)) {
    message.reply('🚫 Only administrators can use this command.');
    return false;
  }
  return true;
}

function isUserTemporarilyBlacklisted(userId) {
  const expiry = blacklistedUsers.get(userId);
  if (!expiry || expiry === Number.MAX_SAFE_INTEGER) return false;
  if (expiry <= Date.now()) {
    blacklistedUsers.delete(userId);
    saveBlacklistedUsers();
    return false;
  }
  return true;
}

function clearUserTemporaryBlacklist(userId) {
  const expiry = blacklistedUsers.get(userId);
  if (!expiry) return null;
  if (expiry === Number.MAX_SAFE_INTEGER) return expiry;
  blacklistedUsers.delete(userId);
  saveBlacklistedUsers();
  applyAttempts.delete(userId);
  return expiry;
}

async function cleanOldApplyMessages(channel, keepMessageId = null) {
  if (!channel || !channel.isTextBased()) return 0;
  try {
    const messages = await fetchChannelMessages(channel, 500);
    const applyMessages = [...messages.values()].filter(msg => {
      if (msg.author?.id !== client.user.id) return false;
      if (msg.components.some(row => row.components.some(c => c.customId === 'apply' || c.customId === 'event_apply'))) {
        return true;
      }
      const embed = msg.embeds[0];
      return embed && embed.title === '🛡️ AVENGERS APPLICATION';
    });

    if (applyMessages.length === 0) return 0;

    let keepMessage = null;
    if (keepMessageId) {
      keepMessage = applyMessages.find(msg => msg.id === keepMessageId) || null;
    }

    if (!keepMessage) {
      keepMessage = applyMessages[0];
    }

    const duplicates = applyMessages.filter(msg => msg.id !== keepMessage.id);
    for (const msg of duplicates) {
      await msg.delete().catch(() => null);
    }
    return duplicates.length;
  } catch (err) {
    console.error('Failed to clean old apply messages:', err);
    return 0;
  }
}

async function removeDuplicateApplicationMessages(channel, targetUserId) {
  if (!channel || !channel.isTextBased()) return 0;
  try {
    const messages = await channel.messages.fetch({ limit: 200 });
    const seen = new Map();
    const duplicates = [];

    for (const msg of messages.values()) {
      if (msg.author?.id !== client.user.id) continue;
      const footerText = msg.embeds?.[0]?.footer?.text || '';
      const applicantId = footerText.match(/(\d{17,19})/)?.[1];
      if (!applicantId || applicantId !== targetUserId) continue;

      const body = `${msg.embeds?.[0]?.title || ''}\n${msg.embeds?.[0]?.description || ''}`;
      if (seen.has(body)) {
        duplicates.push(msg);
        continue;
      }
      seen.set(body, msg.id);
    }

    for (const duplicate of duplicates) {
      await duplicate.delete().catch(() => null);
    }

    return duplicates.length;
  } catch (err) {
    console.error('Failed to remove duplicate application messages:', err);
    return 0;
  }
}

async function fetchChannelMessages(channel, limit = 200) {
  if (!channel || !channel.isTextBased()) return new Map();
  let before = null;
  const collected = new Map();
  while (collected.size < limit) {
    const batchSize = Math.min(100, limit - collected.size);
    const options = { limit: batchSize };
    if (before) options.before = before;
    const batch = await channel.messages.fetch(options).catch(() => null);
    if (!batch || batch.size === 0) break;
    for (const [id, msg] of batch) {
      if (!collected.has(id)) collected.set(id, msg);
    }
    before = batch.last().id;
    if (batch.size < batchSize) break;
  }
  return collected;
}

async function removeUserApplicationMessages(channel, targetUserId) {
  if (!channel || !channel.isTextBased()) return 0;
  try {
    const messages = await fetchChannelMessages(channel, 500);
    const toDelete = Array.from(messages.values()).filter(msg => {
      if (msg.author?.id !== client.user.id) return false;
      const footerText = msg.embeds?.[0]?.footer?.text || '';
      const applicantId = footerText.match(/(\d{17,19})/)?.[1];
      return applicantId === targetUserId;
    });

    for (const msg of toDelete) {
      await msg.delete().catch(() => null);
    }

    return toDelete.size;
  } catch (err) {
    console.error('Failed to remove user application messages:', err);
    return 0;
  }
}

function getRoleListEmbed(roleName, onlineCount, offlineCount, members, page) {
  const total = members.length;
  const start = page * ROLELIST_PAGE_SIZE;
  const end = Math.min(start + ROLELIST_PAGE_SIZE, total);
  const pageMembers = members.slice(start, end);

  const description = pageMembers.length > 0
    ? pageMembers.map(member => {
      const status = member.presence?.status && member.presence.status !== 'offline' && member.presence.status !== 'invisible'
        ? '🟢'
        : '⚫';
      return `${status} <@${member.id}>`;
    }).join('\n')
    : 'لا يوجد أعضاء في هذه الصفحة.';

  return new EmbedBuilder()
    .setTitle(`Role Members: ${roleName}`)
    .setDescription(description)
    .addFields(
      { name: 'Total Members', value: `${total}`, inline: true },
      { name: 'Online Members', value: `${onlineCount}`, inline: true },
      { name: 'Offline Members', value: `${offlineCount}`, inline: true }
    )
    .setFooter({ text: `Page ${page + 1} / ${Math.max(1, Math.ceil(total / ROLELIST_PAGE_SIZE))}` });
}

function createRoleListButtons(roleId, currentPage, totalPages) {
  if (totalPages <= 1) return null;

  const row = new ActionRowBuilder();
  row.addComponents(
    new ButtonBuilder()
      .setCustomId(`rolelist_prev_${roleId}_${Math.max(0, currentPage - 1)}`)
      .setLabel('Previous')
      .setStyle(ButtonStyle.Secondary)
      .setDisabled(currentPage === 0),
    new ButtonBuilder()
      .setCustomId(`rolelist_next_${roleId}_${Math.min(totalPages - 1, currentPage + 1)}`)
      .setLabel('Next')
      .setStyle(ButtonStyle.Secondary)
      .setDisabled(currentPage === totalPages - 1)
  );
  return row;
}

function parseRoleListCustomId(customId) {
  if (!customId) return null;
  const match = customId.match(/^rolelist_(prev|next)_(\d+)_(\d+)$/);
  if (!match) return null;
  return {
    direction: match[1],
    roleId: match[2],
    page: Number(match[3])
  };
}

// Command files were migrated into this single file. No external
// `./commands` loader is necessary — keep `client.commands` as an
// empty Collection for compatibility with any code that expects it.

client.once(Events.ClientReady, () => {
  console.log(`${client.user.tag} is online!`);
  console.log(`[READY] PID=${process.pid}`);
  // Diagnostic: print listener counts to detect accidental multiple registrations
  try {
    console.log('[Startup] listenerCount interactionCreate =', client.listenerCount('interactionCreate'));
    console.log('[Startup] listenerCount messageCreate =', client.listenerCount('messageCreate'));
  } catch (e) {
    console.error('Failed to log listener counts:', e);
  }
  // Post the persistent apply message to a configured channel so users can apply without running /setup
  (async () => {
    try {
      const postChannelId = APPLY_MESSAGE_CHANNEL_ID;
      if (!postChannelId) return console.log('No apply post channel configured (APPLY_MESSAGE_CHANNEL_ID or APPLY_CHANNEL_ID)');
      const channel = await client.channels.fetch(postChannelId).catch(err => {
        console.error(`Failed to fetch apply post channel ${postChannelId}:`, err);
        return null;
      });
      if (!channel) {
        return console.log(`Apply post channel not found: ${postChannelId}`);
      }
      console.log(`Apply post channel fetched: id=${channel.id}, type=${channel.type}, name=${channel.name || 'unknown'}, guild=${channel.guild?.id || 'none'}`);
      if (!channel.isTextBased()) {
        return console.log(`Apply post channel is not text based: ${channel.type}`);
      }

      const existingApplyMessage = await findExistingApplyMessage(channel);
      if (existingApplyMessage) {
        const removed = await cleanOldApplyMessages(channel, existingApplyMessage.id);
        if (removed > 0) {
          console.log(`Found existing apply message; removed ${removed} duplicate(s).`);
        }
        await ensureApplyMessageButtons(existingApplyMessage);
        return console.log('Found existing apply message; skipping repost.');
      }

      const embed = createApplyEmbed();
      const row = createApplyButtonRow();

      // Remove any older bot apply messages before posting the latest one.
      await cleanOldApplyMessages(channel);
      await safeChannelSend(channel, { embeds: [embed], components: [row] }, 'apply_post');
      console.log('Posted apply message to', postChannelId);
    } catch (err) {
      console.error('Failed to post apply message:', err);
    }
  })();
});

client.on('error', console.error);

client.on('interactionCreate', async interaction => {
  // Global dedupe: ignore interactions that match the same signature within DUPLICATE_WINDOW_MS
  try {
    const sigParts = [interaction.user?.id || 'unknown', interaction.type, interaction.customId || interaction.commandName || 'none', interaction.channel?.id || 'dm'];
    const signature = sigParts.join(':');
    const now = Date.now();
    const last = recentInteractionSignatures.get(signature) || 0;
    if (now - last < DUPLICATE_WINDOW_MS) {
      console.warn(`[Interaction][DEDUPE] Ignoring near-duplicate interaction signature=${signature} id=${interaction.id}`);
      return;
    }
    recentInteractionSignatures.set(signature, now);
  } catch (e) {
    console.error('Failed to compute interaction signature:', e);
  }

  if (processedInteractionIds.has(interaction.id)) {
    return;
  }
  processedInteractionIds.add(interaction.id);
  // Wrap response methods to prevent duplicate replies/updates for the same interaction
  try {
    console.log(`[Interaction][RECV] ${new Date().toISOString()} id=${interaction.id} type=${interaction.type} customId=${interaction.customId || ''} user=${interaction.user?.id || 'unknown'} channel=${interaction.channel?.id || 'dm'}`);
    const stackPreview = (new Error().stack || '').split('\n').slice(2,6).map(s => s.trim()).join(' | ');
    console.log(`[Interaction][STACK] ${stackPreview}`);
    interaction.__respondedFlags = interaction.__respondedFlags || {};

    const wrapOnce = (obj, name, marker) => {
      if (!obj || typeof obj[name] !== 'function') return;
      const orig = obj[name].bind(obj);
      obj[name] = async function(...args) {
        const flags = interaction.__respondedFlags;
        if (flags[marker]) {
          console.warn(`[Interaction][SKIP] ${name} for interaction ${interaction.id} (already ${marker})`);
          return null;
        }
        flags[marker] = true;
        console.log(`[Interaction][HANDLING] ${name} for interaction ${interaction.id}`);
        try {
          return await orig(...args);
        } catch (err) {
          console.error(`Error during ${name}:`, err);
          throw err;
        }
      };
    };

    // deferReply/deferUpdate should be allowed once
    wrapOnce(interaction, 'deferReply', 'deferred');
    wrapOnce(interaction, 'deferUpdate', 'deferredUpdate');
    // reply/update/editReply/showModal/followUp should be allowed once each
    wrapOnce(interaction, 'reply', 'replied');
    wrapOnce(interaction, 'update', 'updated');
    wrapOnce(interaction, 'editReply', 'editedReply');
    wrapOnce(interaction, 'followUp', 'followedUp');
    wrapOnce(interaction, 'showModal', 'modalShown');
  } catch (err) {
    console.error('Failed to wrap interaction methods:', err);
  }
  try {
    if (interaction.isChatInputCommand()) {
      const command = client.commands.get(interaction.commandName);
      if (!command) return;
      return await command.execute(interaction);
    }

    if (interaction.isButton()) {
      const customId = interaction.customId;

      if (customId === 'apply' || customId === 'event_apply') {
        const userId = interaction.user.id;
        const now = Date.now();

        const blacklistExpiry = blacklistedUsers.get(userId);
        if (blacklistExpiry && (blacklistExpiry === Number.MAX_SAFE_INTEGER || blacklistExpiry > now)) {
          return await interaction.reply({
            content: '🚫 لقد تجاوزت الحد المسموح به من محاولات التقديم. حاول لاحقاً.',
            ephemeral: true
          });
        }

        const attempts = applyAttempts.get(userId) || [];
        const recent = attempts.filter(ts => now - ts < WINDOW_MS);
        recent.push(now);
        applyAttempts.set(userId, recent);

        if (recent.length > MAX_ATTEMPTS) {
          blacklistedUsers.set(userId, now + BLACKLIST_MS);
          saveBlacklistedUsers();
          return await interaction.reply({
            content: '🚫 تم حظرك مؤقتاً من التقديم لأنك حاولت أكثر من 5 مرات في دقيقة واحدة.',
            ephemeral: true
          });
        }

        if (customId === 'apply') {
          await interaction.showModal(createApplyModal());
        } else {
          await interaction.showModal(createEventApplyModal());
        }
        return;
      }

      if (customId.startsWith('rolelist_next_') || customId.startsWith('rolelist_prev_')) {
        const parsed = parseRoleListCustomId(customId);
        if (!parsed) {
          return interaction.reply({ content: '⚠️ تنسيق الزر غير صالح. حاول الأمر مرة أخرى.', ephemeral: true });
        }

        const { roleId, page } = parsed;
        if (!Number.isInteger(page) || page < 0) {
          return interaction.reply({ content: '⚠️ الصفحة غير صحيحة. حاول الأمر مرة أخرى.', ephemeral: true });
        }

        const role = interaction.guild?.roles.cache.get(roleId) || await interaction.guild?.roles.fetch(roleId).catch(() => null);
        if (!role) {
          return interaction.reply({ content: '❌ هذا الـ Role ID غير موجود الآن. ربما تم تغييره.', ephemeral: true });
        }

        const members = role.members.map(member => member);
        const onlineMembers = members.filter(member => member.presence?.status && member.presence.status !== 'offline' && member.presence.status !== 'invisible');
        const offlineMembers = members.filter(member => !member.presence?.status || member.presence.status === 'offline' || member.presence.status === 'invisible');
        const totalPages = Math.max(1, Math.ceil(members.length / ROLELIST_PAGE_SIZE));
        if (page >= totalPages) {
          return interaction.reply({ content: '⚠️ الصفحة غير متاحة. حاول الأمر مرة أخرى.', ephemeral: true });
        }

        const embed = getRoleListEmbed(role.name, onlineMembers.length, offlineMembers.length, members, page);
        const buttons = createRoleListButtons(roleId, page, totalPages);

        const processingId = `${interaction.id}:${Date.now()}`;
        console.log('[ROLE DEBUG]', `processingId=${processingId}`, `interaction.id=${interaction.id}`, `user=${interaction.user.id}`, `roleId=${roleId}`, `page=${page}`, `pid=${process.pid}`);
        const beforeStack = (new Error().stack || '').split('\n').slice(2,6).map(s => s.trim()).join(' | ');
        console.log('[ROLE STACK]', beforeStack);
        const updated = await interaction.update({ embeds: [embed], components: buttons ? [buttons] : [] }).catch(err => { console.error('[ROLE UPDATE ERROR]', err); return null; });
        console.log('[ROLE UPDATED]', `interaction.id=${interaction.id}`, `processingId=${processingId}`, `result=${updated ? 'ok' : 'fail'}`, `pid=${process.pid}`);
        return updated;
      }

      if (customId === 'accept' || customId.startsWith('accept_')) {
        const { applicantId, applicationNumber } = extractApplicantInfo(customId, interaction.message);
        let applicantTag = null;

        const applicantMember = applicantId
          ? await interaction.guild.members.fetch(applicantId).catch(() => null)
          : null;

        let roleAssignError = null;
        let roleAdded = false;

        if (!applicantId) {
          roleAssignError = 'Applicant ID could not be determined.';
        } else if (!applicantMember) {
          roleAssignError = 'Applicant is not present in the server.';
        }

        const role = AV_FAMILY_ROLE_ID
          ? await interaction.guild.roles.fetch(AV_FAMILY_ROLE_ID).catch(() => null)
          : null;

        if (!role) {
          roleAssignError = roleAssignError || 'AV Family role is not configured or not found.';
        }

        if (applicantMember && role) {
          try {
            await applicantMember.roles.add(role);
            roleAdded = true;
          } catch (err) {
            roleAssignError = `Failed to assign role: ${err.message}`;
            console.error('Failed to assign AV Family role:', err);
          }
        }

        const updateContent = roleAdded
          ? '✅ تم قبولك في الكلان، أهلاً بك في العائلة 🎉'
          : `⚠️ تم قبول الطلب ولكن حدث خطأ عند إعطاء رتبة AV Family: ${roleAssignError}`;

        await interaction.update({
          content: updateContent,
          components: []
        });

        applicantTag = applicantMember?.user?.tag || applicantTag;

        await sendStaffLog({
          action: '✅ Accepted',
          applicantUser: applicantMember?.user || { tag: applicantTag || 'Unknown', username: applicantTag || 'Unknown' },
          applicantId,
          staffUser: interaction.user,
          details: roleAdded ? 'Accepted and role assigned' : `Accepted with error: ${roleAssignError}`,
          applicationNumber
        }).catch(() => null);

        return;
      }

      if (customId === 'reject' || customId.startsWith('reject_')) {
        const { applicantId, applicationNumber } = extractApplicantInfo(customId, interaction.message);
        const applicantTag = applicantId ? (await interaction.guild.members.fetch(applicantId).then(m => m.user.tag).catch(() => null)) : null;

        await interaction.update({
          content: '❌ تم رفض طلبك',
          components: []
        });

        await sendStaffLog({
          action: '❌ Rejected',
          applicantUser: { tag: applicantTag || 'Unknown', username: applicantTag || 'Unknown' },
          applicantId,
          staffUser: interaction.user,
          details: 'Rejected',
          applicationNumber
        }).catch(() => null);

        return;
      }

      if (customId.startsWith('status_')) {
        await interaction.deferReply({ ephemeral: true });

        const applicationNumber = extractApplicationNumberFromCustomId(customId) || extractApplicationNumberFromMessage(interaction.message);
        const memberId = customId.split('_')[1];
        console.log('Status check for memberId:', memberId);
        if (!memberId) {
          return await interaction.editReply({
            content: '❌ ما قدرت ألقى ID العضو'
          });
        }

        const member = await interaction.guild.members.fetch(memberId).catch(() => null);
        if (!member) {
          console.log('Member fetch returned null for', memberId);
          return await interaction.editReply({
            content: '❌ العضو غير موجود في السيرفر'
          });
        }

        const voiceState = member.voice || interaction.guild.voiceStates.cache.get(member.id);
        const voiceChannel = voiceState?.channel || (voiceState?.channelId ? interaction.guild.channels.cache.get(voiceState.channelId) : null);
        console.log('member.voice channelId ->', voiceState?.channelId, 'voiceChannel ->', voiceChannel ? voiceChannel.id : null);
        const statusText = member.presence?.status || 'offline';
        const voiceText = voiceChannel ? `🎧 Current voice channel: ${voiceChannel.name}` : '❌ Current voice channel: Not in voice';
        const replyPayload = {
          content: `📌 Username: ${member.user.tag}\n🟢 Online status: ${statusText}\n${voiceText}`
        };

        await sendStaffLog({
          action: '👀 Show Status Used',
          applicantUser: member.user,
          applicantId: member.id,
          staffUser: interaction.user,
          details: 'Show Status used',
          applicationNumber
        }).catch(() => null);

        if (voiceChannel) {
          // Only include Move button when the member is in a voice channel
          replyPayload.components = [
            new ActionRowBuilder().addComponents(
              new ButtonBuilder()
                .setCustomId(`move_${member.id}_${applicationNumber}`)
                .setLabel('Move For Test')
                .setEmoji('🎧')
                .setStyle(ButtonStyle.Success)
            )
          ];
        }

        return await interaction.editReply(replyPayload);
      }

      if (customId.startsWith('move_')) {
        await interaction.deferReply({ ephemeral: true });
        const memberId = interaction.customId.split('_')[1];

        const member = await interaction.guild.members.fetch(memberId)
          .catch(() => null);

        if (!member) {
          return interaction.editReply({
            content: '❌ العضو غير موجود في السيرفر',
            ephemeral: true
          });
        }

        if (!TEST_VOICE_CHANNEL_ID) {
          return interaction.editReply({
            content: '❌ لم يتم تكوين رابط روم الاختبار في ملف .env',
            ephemeral: true
          });
        }

        const testVoice = await client.channels.fetch(TEST_VOICE_CHANNEL_ID).catch(() => null);
        if (!testVoice || !testVoice.isVoiceBased()) {
          return interaction.editReply({
            content: '❌ روم الاختبار غير موجود أو غير صالح',
            ephemeral: true
          });
        }

        // Move applicant first
        const moved = [];
        try {
          await member.voice.setChannel(testVoice);
          moved.push(member.user.tag);
        } catch (err) {
          console.error('Failed moving applicant:', err);
        }

        // Move clan leader(s): use role ID only from env.
        const clanRoleId = CLAN_LEADER_ROLE_ID;
        const clanRole = clanRoleId ? await interaction.guild.roles.fetch(clanRoleId).catch(() => null) : null;

        if (clanRole) {
          // Move any members with that role who are currently in voice
          const leaders = clanRole.members.filter(m => m.voice && m.voice.channel);
          for (const [id, leader] of leaders) {
            // Skip if it's the same as applicant (already moved)
            if (id === member.id) continue;
            try {
              await leader.voice.setChannel(testVoice);
              moved.push(leader.user.tag);
            } catch (err) {
              console.error('Failed moving leader', leader.user.tag, err);
            }
          }
        }

        if (moved.length === 0) {
          return interaction.editReply({
            content: '⚠️ لم يتم سحب أي مستخدم، ربما لا يوجد قائد كلان في فويس',
            ephemeral: true
          });
        }

        await sendStaffLog({
          action: '🎧 Move For Test',
          applicantUser: member.user,
          applicantId: member.id,
          staffUser: interaction.user,
          details: 'Moved to Test Voice',
          applicationNumber: extractApplicationNumberFromCustomId(customId) || extractApplicationNumberFromMessage(interaction.message)
        }).catch(() => null);

        return interaction.editReply({
          content: `✅ تم سحب المستخدمين إلى روم الاختبار: ${moved.join(', ')}`,
          ephemeral: true
        });
      }
    }

    if (interaction.isModalSubmit()) {
      if (interaction.customId === 'apply_form' || interaction.customId === 'event_apply_form') {
        const interactionId = interaction.id || `${interaction.user.id}_${Date.now()}`;
        let embedDescription;
        let submissionHash;

        if (interaction.customId === 'apply_form') {
          const name = interaction.fields.getTextInputValue('apply_name');
          const age = interaction.fields.getTextInputValue('apply_age');
          const playStyle = interaction.fields.getTextInputValue('apply_play_style');
          const gameId = interaction.fields.getTextInputValue('apply_game_id');
          submissionHash = createSubmissionHash(interaction.user.id, { name, age, playStyle, gameId });
          embedDescription = `**Name:** ${name}\n**Age:** ${age}\n**Apostado or eSports:** ${playStyle}\n**Game ID:** ${gameId}`;
        } else {
          const sqName = interaction.fields.getTextInputValue('event_sq_name');
          const sqSize = interaction.fields.getTextInputValue('event_sq_size');
          const details = interaction.fields.getTextInputValue('event_additional_info');
          submissionHash = createSubmissionHash(interaction.user.id, { sqName, sqSize, details });
          embedDescription = `**Event Application**\n**SQ Name:** ${sqName}\n**SQ Size:** ${sqSize}\n**Additional Info:** ${details || 'None'}`;
        }

        await interaction.deferReply({ ephemeral: true });

        // Ensure submission locks dir exists
        try { fs.mkdirSync(SUBMISSION_LOCKS_DIR, { recursive: true }); } catch (e) {}

        // Attempt to create an atomic lock file for this submission hash to prevent duplicates across processes
        const lockFilePath = path.join(SUBMISSION_LOCKS_DIR, `${submissionHash}.lock`);
        try {
          const fd = fs.openSync(lockFilePath, 'wx');
          fs.closeSync(fd);
        } catch (err) {
          if (err && err.code === 'EEXIST') {
            return await interaction.editReply({
              content: '⚠️ تم إرسال الطلب مسبقاً. الرجاء الانتظار حتى تتم مراجعته.',
              ephemeral: true
            });
          }
          console.error('Failed to create submission lock file:', err);
          return await interaction.editReply({ content: '❌ حصل خطأ داخلي', ephemeral: true });
        }

        // Double-check in-memory structures
        if (submittedApplications.ids.has(interactionId) || submittedApplications.hashes.has(submissionHash)) {
          // already recorded in memory; keep lock file and inform user
          return await interaction.editReply({
            content: '⚠️ تم إرسال الطلب مسبقاً. الرجاء الانتظار حتى تتم مراجعته.',
            ephemeral: true
          });
        }

        // Reserve application number and persist
        const applicationNumber = nextApplicationNumber;
        nextApplicationNumber += 1;
        saveNextApplicationNumber();

        // Record submission in memory and on disk
        submittedApplications.ids.add(interactionId);
        submittedApplications.hashes.add(submissionHash);
        const userHashes = submittedApplications.byUser.get(interaction.user.id) || new Set();
        userHashes.add(submissionHash);
        submittedApplications.byUser.set(interaction.user.id, userHashes);
        saveSubmittedApplications();

        const embed = new EmbedBuilder()
          .setColor('Blue')
          .setTitle(`📄 Application #${applicationNumber}`)
          .setDescription(embedDescription)
          .setFooter({ text: `Applicant ID: ${interaction.user.id}` });

        const row = new ActionRowBuilder().addComponents(
          new ButtonBuilder()
            .setCustomId(`accept_${interaction.user.id}_${applicationNumber}`)
            .setLabel('Accept')
            .setStyle(ButtonStyle.Success),
          new ButtonBuilder()
            .setCustomId(`reject_${interaction.user.id}_${applicationNumber}`)
            .setLabel('Reject')
            .setStyle(ButtonStyle.Danger),
          new ButtonBuilder()
            .setCustomId(`status_${interaction.user.id}_${applicationNumber}`)
            .setLabel('Show Status')
            .setStyle(ButtonStyle.Secondary),
          new ButtonBuilder()
            .setCustomId(`move_${interaction.user.id}_${applicationNumber}`)
            .setLabel('Move For Test')
            .setStyle(ButtonStyle.Primary)
        );

        const applicationsChannel = APPLICATIONS_CHANNEL_ID
          ? await client.channels.fetch(APPLICATIONS_CHANNEL_ID).catch(() => null)
          : null;
        const roleMention = CLAN_LEADER_ROLE_ID ? `<@&${CLAN_LEADER_ROLE_ID}>` : '';
        const targetChannel = applicationsChannel && applicationsChannel.isTextBased()
          ? applicationsChannel
          : (interaction.channel && interaction.channel.isTextBased() ? interaction.channel : null);

        let alreadySent = false;
        if (targetChannel) {
          alreadySent = await hasDuplicateApplicationMessage(targetChannel, interaction.user.id, applicationNumber);
        }

        if (alreadySent) {
          return await interaction.editReply({
            content: '⚠️ تم إرسال الطلب مسبقاً. لم نرسل نسخة أخرى.',
            ephemeral: true
          });
        }

        // Debug: processing id and app debug
        const processingId = `${interaction.id}:${Date.now()}`;
        const sendKey = `application_${interaction.user.id}_${applicationNumber}`;
        console.log('[APP DEBUG]', `processingId=${processingId}`, `interaction.id=${interaction.id}`, `user=${interaction.user.id}`, `customId=${interaction.customId}`, `applicationNumber=${applicationNumber}`, `submissionHash=${submissionHash}`, `targetChannel=${targetChannel?.id || 'none'}`, `sendKey=${sendKey}`, `pid=${process.pid}`);

        if (targetChannel) {
          console.log('[APP SEND]', `interaction.id=${interaction.id}`, `applicationNumber=${applicationNumber}`, `submissionHash=${submissionHash}`, `sendKey=${sendKey}`, `pid=${process.pid}`);
          const sentMsg = await safeChannelSend(targetChannel, { content: roleMention, embeds: [embed], components: [row] }, sendKey);
          if (sentMsg && sentMsg.id) {
            console.log('[APP SENT]', `message.id=${sentMsg.id}`, `interaction.id=${interaction.id}`, `applicationNumber=${applicationNumber}`);
            // persist message id mapping
            try {
              if (!submittedApplications.submissions) submittedApplications.submissions = new Map();
              submittedApplications.submissions.set(submissionHash, { applicationNumber, applicantId: interaction.user.id, messageId: sentMsg.id });
              saveSubmittedApplications();
            } catch (e) {
              console.error('Failed to persist submission message id:', e);
            }
          } else {
            console.error('[APP ERROR] send failed for', `interaction.id=${interaction.id}`, `applicationNumber=${applicationNumber}`);
          }
          // remove lock file after send attempt
          try { const lp = path.join(SUBMISSION_LOCKS_DIR, `${submissionHash}.lock`); if (fs.existsSync(lp)) fs.unlinkSync(lp); } catch (e) {}
        }

        await sendStaffLog({
          action: interaction.customId === 'event_apply_form' ? '📝 Event Application Submitted' : '📝 Application Submitted',
          applicantUser: interaction.user,
          applicantId: interaction.user.id,
          staffUser: { tag: 'System', username: 'System' },
          details: interaction.customId === 'event_apply_form' ? 'Event application submitted' : 'Application submitted',
          applicationNumber,
          logChannelId: interaction.customId === 'event_apply_form' ? EVENT_APPLICATION_LOG_CHANNEL_ID : undefined
        }).catch(() => null);

        return await interaction.editReply({
          content: '✅ تم استلام طلبك وسيتم مراجعته من الإدارة.',
          ephemeral: true
        });
      }
    }
  } catch (error) {
    console.error(error);
    if (interaction.deferred && !interaction.replied) {
      await interaction.editReply({ content: '❌ حصل خطأ', ephemeral: true }).catch(() => null);
    } else if (!interaction.replied && !interaction.deferred) {
      await interaction.reply({ content: '❌ حصل خطأ', ephemeral: true }).catch(() => null);
    }
  }
});

client.on('messageCreate', async message => {
  if (message.author.bot) return;
  const content = message.content.trim();
  if (content === '!ping') {
    return message.reply('🏓 Pong!');
  }

  if (content.toLowerCase().startsWith('&rolelist')) {
    const args = content.split(/\s+/);
    if (args.length < 2) {
      return message.reply('❌ استخدم: `&rolelist ROLE_ID`');
    }

    const roleId = args[1].replace(/[<@&>]/g, '');
    if (!/^\d{17,19}$/.test(roleId)) {
      return message.reply('❌ الرجاء إدخال Role ID صالح.');
    }

    const role = message.guild?.roles.cache.get(roleId) || await message.guild?.roles.fetch(roleId).catch(() => null);
    if (!role) {
      return message.reply('❌ هذا الـ Role ID غير موجود في السيرفر.');
    }

    const members = role.members.map(member => member);
    const onlineMembers = members.filter(member => member.presence?.status && member.presence.status !== 'offline' && member.presence.status !== 'invisible');
    const offlineMembers = members.filter(member => !member.presence?.status || member.presence.status === 'offline' || member.presence.status === 'invisible');
    const totalPages = Math.max(1, Math.ceil(members.length / ROLELIST_PAGE_SIZE));
    const embed = getRoleListEmbed(role.name, onlineMembers.length, offlineMembers.length, members, 0);
    const buttons = createRoleListButtons(role.id, 0, totalPages);

    const processingId = `${message.id || 'msg'}:${Date.now()}`;
    console.log('[ROLE REQ]', `processingId=${processingId}`, `user=${message.author.id}`, `roleId=${roleId}`, `channel=${message.channel.id}`, `pid=${process.pid}`);
    const sent = await message.reply({ embeds: [embed], components: buttons ? [buttons] : [] });
    try { console.log('[ROLE SENT]', `message.id=${sent.id}`, `processingId=${processingId}`, `user=${message.author.id}`, `roleId=${roleId}`, `pid=${process.pid}`); } catch (e) {}
    return sent;
  }

  if (
    content.toLowerCase() === '!applyagian' ||
    content.toLowerCase().startsWith('!applyagian ') ||
    content.toLowerCase() === '!applyagain' ||
    content.toLowerCase().startsWith('!applyagain ') ||
    content.toLowerCase() === '&applyagain' ||
    content.toLowerCase().startsWith('&applyagain ') ||
    content.toLowerCase() === '&applyagian' ||
    content.toLowerCase().startsWith('&applyagian ')
  ) {
    const args = content.split(/\s+/);
    const rawTargetId = args[1] || message.author.id;
    const targetId = rawTargetId.replace(/[<@!>]/g, '');

    if (!/^\d{17,19}$/.test(targetId)) {
      return message.reply('❌ الرجاء إدخال معرف مستخدم صالح.');
    }

    if (targetId !== message.author.id && !message.member?.permissions.has(PermissionsBitField.Flags.Administrator)) {
      return message.reply('🚫 يمكنك فقط إعادة التقديم عن نفسك أو اطلب من الإدارة استخدام الأمر لآخرين.');
    }

    const removedHashes = removeUserSubmittedApplicationHashes(targetId);
    const applicationsChannel = APPLICATIONS_CHANNEL_ID
      ? await client.channels.fetch(APPLICATIONS_CHANNEL_ID).catch(() => null)
      : null;
    const targetChannel = applicationsChannel && applicationsChannel.isTextBased()
      ? applicationsChannel
      : null;

    let removedMessages = 0;
    if (targetChannel) {
      removedMessages += await removeUserApplicationMessages(targetChannel, targetId);
    }
    if (message.channel && message.channel.isTextBased() && message.channel.id !== targetChannel?.id) {
      removedMessages += await removeUserApplicationMessages(message.channel, targetId);
    }

    applyAttempts.delete(targetId);
    const blacklistExpiry = blacklistedUsers.get(targetId);
    if (blacklistExpiry && blacklistExpiry !== Number.MAX_SAFE_INTEGER) {
      blacklistedUsers.delete(targetId);
      saveBlacklistedUsers();
    }

    if (removedHashes > 0 || removedMessages > 0) {
      return message.reply(`✅ تم حذف ${removedHashes} طلب سابق و${removedMessages} رسالة مكررة. يمكنك التقديم مرة أخرى الآن.`);
    }

    return message.reply('✅ لم يتم العثور على طلب سابق، لكن تمت إعادة تعيين حالة التقديم. يمكنك المحاولة مرة أخرى الآن.');
  }

  if (content.toLowerCase().startsWith('&apply')) {
    const args = content.split(/\s+/);
    if (args.length < 2) {
      return message.reply('❌ استخدم: `&apply <userid>`');
    }

    const targetId = args[1].replace(/[<@!>]/g, '');
    if (!/^\d{17,19}$/.test(targetId)) {
      return message.reply('❌ الرجاء إدخال معرف مستخدم صالح.');
    }

    if (targetId !== message.author.id && !message.member?.permissions.has(PermissionsBitField.Flags.Administrator)) {
      return message.reply('🚫 يمكنك فقط رفع الحظر عن نفسك أو اطلب من الإدارة استخدام هذا الأمر لآخرين.');
    }

    const expiry = blacklistedUsers.get(targetId);
    if (!expiry) {
      return message.reply('ℹ️ المستخدم غير محظور مؤقتاً.');
    }

    if (expiry === Number.MAX_SAFE_INTEGER) {
      return message.reply('🚫 هذا المستخدم محظور دائماً ولا يمكن رفع الحظر بهذا الأمر.');
    }

    blacklistedUsers.delete(targetId);
    saveBlacklistedUsers();
    applyAttempts.delete(targetId);

    return message.reply(`✅ تم رفع الحظر المؤقت للمستخدم <@${targetId}>. يمكنك المحاولة مرة أخرى الآن.`);
  }

  const args = content.split(/\s+/);
  const commandName = args[0].toLowerCase();

  if (commandName === '!blacklist' || commandName === '!unblacklist') {
    if (!requireAdminPermission(message)) {
      return;
    }

    const target = args[1];
    if (!target) {
      return message.reply('❌ Please provide a user mention or user ID.');
    }

    const targetId = target.replace(/[<@!>]/g, '');
    if (!/^\d{17,19}$/.test(targetId)) {
      return message.reply('❌ This is not a valid user ID.');
    }

    if (commandName === '!blacklist') {
      blacklistedUsers.set(targetId, Number.MAX_SAFE_INTEGER);
      saveBlacklistedUsers();
      await sendStaffLog({
        action: '🚫 Blacklisted',
        applicantUser: { tag: `<@${targetId}>`, username: targetId },
        applicantId: targetId,
        staffUser: message.author,
        details: 'Blacklisted'
      }).catch(() => null);
      return message.reply(`✅ <@${targetId}> has been blacklisted.`);
    }

    if (!blacklistedUsers.has(targetId)) {
      return message.reply('❌ This user is not blacklisted.');
    }

    blacklistedUsers.delete(targetId);
    saveBlacklistedUsers();
    await sendStaffLog({
      action: '🔓 Unblacklisted',
      applicantUser: { tag: `<@${targetId}>`, username: targetId },
      applicantId: targetId,
      staffUser: message.author,
      details: 'Unblacklisted'
    }).catch(() => null);
    return message.reply(`✅ <@${targetId}> has been removed from the blacklist.`);
  }

  if (content.toLowerCase() === '!clear apply log') {
    if (!requireAdminPermission(message)) {
      return;
    }

    if (!APPLY_LOG_CHANNEL_ID) {
      return message.reply('❌ Apply log channel is not configured in .env.');
    }

    const logChannel = await client.channels.fetch(APPLY_LOG_CHANNEL_ID).catch(() => null);
    if (!logChannel || !logChannel.isTextBased()) {
      return message.reply('❌ Apply log channel not found or is not a text channel.');
    }

    const messages = await logChannel.messages.fetch({ limit: 100 }).catch(() => null);
    if (!messages) {
      return message.reply('❌ Failed to fetch messages from the apply log channel.');
    }

    const deletable = messages.filter(msg => msg.author?.id === client.user.id);
    if (deletable.size === 0) {
      return message.reply('ℹ️ No bot apply log messages were found to clear.');
    }

    await logChannel.bulkDelete(deletable, true).catch(() => null);
    return message.reply(`✅ Cleared ${deletable.size} bot message(s) from the apply log channel.`);
  }

  if (content.toLowerCase() === '!clear applications') {
    if (!requireAdminPermission(message)) {
      return;
    }

    if (!APPLICATIONS_CHANNEL_ID) {
      return message.reply('❌ Applications channel is not configured in .env.');
    }

    const applicationsChannel = await client.channels.fetch(APPLICATIONS_CHANNEL_ID).catch(() => null);
    if (!applicationsChannel || !applicationsChannel.isTextBased()) {
      return message.reply('❌ Applications channel not found or is not a text channel.');
    }

    const messages = await applicationsChannel.messages.fetch({ limit: 100 }).catch(() => null);
    if (!messages) {
      return message.reply('❌ Failed to fetch messages from the applications channel.');
    }

    const deletable = messages.filter(msg => msg.author?.id === client.user.id);
    if (deletable.size === 0) {
      return message.reply('ℹ️ No bot application messages were found to clear.');
    }

    await applicationsChannel.bulkDelete(deletable, true).catch(() => null);
    return message.reply(`✅ Cleared ${deletable.size} bot message(s) from the applications channel.`);
  }

  // Admin command: remove duplicate apply messages across configured channels
  if (content.toLowerCase() === '!dedupeapply') {
    if (!requireAdminPermission(message)) return;

    let totalRemoved = 0;

    if (APPLY_MESSAGE_CHANNEL_ID) {
      const applyMsgChannel = await client.channels.fetch(APPLY_MESSAGE_CHANNEL_ID).catch(() => null);
      if (applyMsgChannel && applyMsgChannel.isTextBased()) {
        totalRemoved += await cleanOldApplyMessages(applyMsgChannel).catch(() => 0);
      }
    }

    if (APPLICATIONS_CHANNEL_ID && APPLICATIONS_CHANNEL_ID !== APPLY_MESSAGE_CHANNEL_ID) {
      const applicationsChannel2 = await client.channels.fetch(APPLICATIONS_CHANNEL_ID).catch(() => null);
      if (applicationsChannel2 && applicationsChannel2.isTextBased()) {
        totalRemoved += await cleanOldApplyMessages(applicationsChannel2).catch(() => 0);
      }
    }

    // Also try to clean duplicates in the channel where the command was invoked
    if (message.channel && message.channel.isTextBased()) {
      totalRemoved += await cleanOldApplyMessages(message.channel).catch(() => 0);
    }

    return message.reply(`✅ Removed ${totalRemoved} duplicate apply message(s).`);
  }

  // Admin command to post the apply message into the current channel
  if (content === '!postapply') {
    // require ManageGuild permission
    if (!message.member || !message.member.permissions.has(PermissionsBitField.Flags.ManageGuild)) {
      return message.reply('🚫 تحتاج صلاحية Manage Guild لتشغيل هذا الأمر.');
    }

    const embed = createApplyEmbed();
    const row = createApplyButtonRow();

    await cleanOldApplyMessages(message.channel);
    await safeChannelSend(message.channel, { embeds: [embed], components: [row] }, `postapply_${message.channel.id}`);
    return message.reply('✅ تم نشر رسالة التقديم هنا.');
  }
});

const DISCORD_TOKEN = (process.env.DISCORD_TOKEN || process.env.TOKEN)?.trim();
if (!DISCORD_TOKEN) {
  console.error('Discord bot token missing. Set TOKEN in .env locally and in Railway environment variables.');
  process.exit(1);
}

client.login(DISCORD_TOKEN).catch((error) => {
  console.error('Discord login failed:', error);
  process.exit(1);
});
