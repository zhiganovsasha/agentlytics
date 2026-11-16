const { execSync, execFileSync } = require('child_process');
const fs = require('fs');
const path = require('path');
const os = require('os');
const Database = require('better-sqlite3');
const { getAppDataPath } = require('./base');

const HOME = os.homedir();
const ANTIGRAVITY_USER_DIR = path.join(getAppDataPath('Antigravity'), 'User');
const ANTIGRAVITY_GLOBAL_STORAGE_DB = path.join(ANTIGRAVITY_USER_DIR, 'globalStorage', 'state.vscdb');
const ANTIGRAVITY_LOCAL_DIR = path.join(HOME, '.gemini', 'antigravity');
const ANTIGRAVITY_SUMMARIES_DB = path.join(ANTIGRAVITY_LOCAL_DIR, 'conversation_summaries.db');
const ANTIGRAVITY_CONVERSATIONS_DIR = path.join(ANTIGRAVITY_LOCAL_DIR, 'conversations');
const ANTIGRAVITY_BRAIN_DIR = path.join(ANTIGRAVITY_LOCAL_DIR, 'brain');
const OFFLINE_TRAJECTORY_SUMMARIES_KEYS = [
  'antigravityUnifiedStateSync.trajectorySummaries',
  'unifiedStateSync.trajectorySummaries',
];

// Static fallback for legacy placeholders no longer returned by the LS
const LEGACY_MODEL_MAP = {
  'MODEL_PLACEHOLDER_M1': 'Claude 3.5 Sonnet',
  'MODEL_PLACEHOLDER_M2': 'Claude 3.5 Sonnet',
  'MODEL_PLACEHOLDER_M3': 'Claude 3.5 Sonnet',
  'MODEL_PLACEHOLDER_M4': 'Claude 3.5 Haiku',
  'MODEL_PLACEHOLDER_M5': 'Claude 3.5 Haiku',
  'MODEL_PLACEHOLDER_M6': 'Claude 3.5 Haiku',
  'MODEL_PLACEHOLDER_M7': 'Claude 3.5 Sonnet',
  'MODEL_PLACEHOLDER_M8': 'Claude 3.5 Sonnet',
  'MODEL_PLACEHOLDER_M9': 'Claude 3.5 Sonnet',
  'MODEL_PLACEHOLDER_M10': 'Claude 3.5 Sonnet',
  'MODEL_CLAUDE_4_5_SONNET': 'Claude 4.5 Sonnet',
};

// Dynamic model map populated from GetUserStatus RPC (placeholder → friendly label)
let _modelMap = null;

function getModelMap() {
  if (_modelMap) return _modelMap;
  _modelMap = { ...LEGACY_MODEL_MAP };
  try {
    const resp = callRpc('GetUserStatus', {});
    const configs = resp?.userStatus?.cascadeModelConfigData?.clientModelConfigs || [];
    for (const c of configs) {
      const key = c.modelOrAlias?.model;
      const label = c.label;
      if (key && label) _modelMap[key] = label;
    }
  } catch {}
  return _modelMap;
}

// Convert friendly label → pricing-compatible model ID
// "Gemini 3.1 Pro (High)" → "gemini-3.1-pro"
// "Claude Sonnet 4.6 (Thinking)" → "claude-sonnet-4.6"
function labelToModelId(label) {
  return label
    .replace(/\s*\([^)]*\)\s*/g, '')  // strip "(High)", "(Thinking)", etc.
    .trim()
    .toLowerCase()
    .replace(/\s+/g, '-');             // spaces → dashes
}

function normalizeModel(modelId) {
  if (!modelId) return null;
  const map = getModelMap();
  const label = map[modelId];
  if (label) return labelToModelId(label);
  return modelId;
}

function fileUriToPath(uri) {
  try {
    const parsed = new URL(uri);
    if (parsed.protocol !== 'file:') return null;
    let filePath = decodeURIComponent(parsed.pathname);
    if (IS_WINDOWS && /^\/[A-Za-z]:/.test(filePath)) filePath = filePath.slice(1);
    return filePath || null;
  } catch {
    return null;
  }
}

function base64ToBytes(b64) {
  try {
    return Uint8Array.from(Buffer.from(String(b64 || '').trim(), 'base64'));
  } catch {
    return null;
  }
}

function bytesToUtf8(bytes) {
  try {
    return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
  } catch {
    return null;
  }
}

function readVarint(buf, offset) {
  let value = 0;
  let shift = 0;
  let i = offset;
  while (i < buf.length) {
    const b = buf[i];
    i += 1;
    value += (b & 0x7f) * (2 ** shift);
    if ((b & 0x80) === 0) return { value, offset: i };
    shift += 7;
    if (shift > 53) return null;
  }
  return null;
}

function readLengthDelimited(buf, offset) {
  const lenRes = readVarint(buf, offset);
  if (!lenRes) return null;
  const len = lenRes.value;
  const start = lenRes.offset;
  const end = start + len;
  if (end > buf.length) return null;
  return { bytes: buf.subarray(start, end), offset: end };
}

function skipField(buf, offset, wireType) {
  if (wireType === 0) {
    const v = readVarint(buf, offset);
    return v ? { offset: v.offset } : null;
  }
  if (wireType === 1) {
    const end = offset + 8;
    return end <= buf.length ? { offset: end } : null;
  }
  if (wireType === 2) {
    const ld = readLengthDelimited(buf, offset);
    return ld ? { offset: ld.offset } : null;
  }
  if (wireType === 5) {
    const end = offset + 4;
    return end <= buf.length ? { offset: end } : null;
  }
  return null;
}

// ============================================================
// Generic protobuf wire-format decoder (decode-on-demand).
// decodeProtoTree(buf) → { [fieldNumber]: [rawValue, ...] }
// where rawValue is a Number (varint fields) or Buffer (length-
// delimited / fixed fields). Use getF/getSub/getText helpers to
// walk the tree; nested messages are decoded lazily so that
// string fields are never lost to spurious nested parsing.
// ============================================================

function decodeProtoTree(buf) {
  const out = {};
  let offset = 0;
  while (offset < buf.length) {
    const tagRes = readVarint(buf, offset);
    if (!tagRes) return null;
    offset = tagRes.offset;

    const fieldNumber = Math.floor(tagRes.value / 8);
    const wireType = tagRes.value & 0x7;
    if (fieldNumber === 0) return null;

    if (wireType === 0) {
      const valueRes = readVarint(buf, offset);
      if (!valueRes) return null;
      offset = valueRes.offset;
      (out[fieldNumber] = out[fieldNumber] || []).push(valueRes.value);
    } else if (wireType === 1) {
      if (offset + 8 > buf.length) return null;
      (out[fieldNumber] = out[fieldNumber] || []).push(buf.subarray(offset, offset + 8));
      offset += 8;
    } else if (wireType === 2) {
      const ld = readLengthDelimited(buf, offset);
      if (!ld) return null;
      offset = ld.offset;
      (out[fieldNumber] = out[fieldNumber] || []).push(ld.bytes);
    } else if (wireType === 5) {
      if (offset + 4 > buf.length) return null;
      (out[fieldNumber] = out[fieldNumber] || []).push(buf.subarray(offset, offset + 4));
      offset += 4;
    } else {
      return null;
    }
  }
  return out;
}

// First raw value of field n (Number or Buffer)
function getF(node, n) {
  if (!node || !node[n] || node[n].length === 0) return null;
  return node[n][0];
}

// First nested message of field n (decoded lazily)
function getSub(node, n) {
  const v = getF(node, n);
  if (!v || !Buffer.isBuffer(v)) return null;
  return decodeProtoTree(v);
}

// First value of field n as strict-UTF-8 text (null if binary)
function getText(node, n) {
  const v = getF(node, n);
  if (typeof v === 'number') return String(v);
  if (!v || !Buffer.isBuffer(v)) return null;
  return bytesToUtf8(v);
}

function protoTimestamp(node) {
  // {1: seconds, 2: nanos} → epoch ms
  if (!node) return null;
  const sec = getF(node, 1);
  if (typeof sec !== 'number' || sec < 946684800 || sec > 4102444800) return null;
  const nanos = getF(node, 2);
  return Math.round(sec * 1000 + (typeof nanos === 'number' ? nanos / 1e6 : 0));
}

function* iterAllUtf8StringsInProto(buf, maxDepth, depth = 0) {
  if (depth > maxDepth) return;
  let offset = 0;
  while (offset < buf.length) {
    const tagRes = readVarint(buf, offset);
    if (!tagRes) return;
    offset = tagRes.offset;

    const wireType = tagRes.value & 0x7;
    if (wireType !== 2) {
      const skipped = skipField(buf, offset, wireType);
      if (!skipped) return;
      offset = skipped.offset;
      continue;
    }

    const ld = readLengthDelimited(buf, offset);
    if (!ld) return;
    offset = ld.offset;

    const asString = bytesToUtf8(ld.bytes);
    if (asString !== null) yield asString;
    yield* iterAllUtf8StringsInProto(ld.bytes, maxDepth, depth + 1);
  }
}

function parseTimestampMessage(bytes) {
  let seconds = null;
  let nanos = 0;
  let offset = 0;

  while (offset < bytes.length) {
    const tagRes = readVarint(bytes, offset);
    if (!tagRes) return null;
    offset = tagRes.offset;

    const fieldNumber = tagRes.value >>> 3;
    const wireType = tagRes.value & 0x7;

    if (wireType === 0) {
      const valueRes = readVarint(bytes, offset);
      if (!valueRes) return null;
      offset = valueRes.offset;
      if (fieldNumber === 1) seconds = valueRes.value;
      if (fieldNumber === 2) nanos = valueRes.value;
      continue;
    }

    const skipped = skipField(bytes, offset, wireType);
    if (!skipped) return null;
    offset = skipped.offset;
  }

  if (seconds == null) return null;
  if (seconds < 946684800 || seconds > 4102444800) return null;
  if (nanos >= 1e9) nanos = 0;

  return Math.round((seconds * 1000) + (nanos / 1e6));
}

function findTimestampInProto(bytes, maxDepth = 2, depth = 0) {
  const direct = parseTimestampMessage(bytes);
  if (direct) return direct;
  if (depth >= maxDepth) return null;

  let offset = 0;
  while (offset < bytes.length) {
    const tagRes = readVarint(bytes, offset);
    if (!tagRes) return null;
    offset = tagRes.offset;

    const wireType = tagRes.value & 0x7;
    if (wireType !== 2) {
      const skipped = skipField(bytes, offset, wireType);
      if (!skipped) return null;
      offset = skipped.offset;
      continue;
    }

    const ld = readLengthDelimited(bytes, offset);
    if (!ld) return null;
    offset = ld.offset;

    const nested = findTimestampInProto(ld.bytes, maxDepth, depth + 1);
    if (nested) return nested;
  }

  return null;
}

function readGlobalStateValue(key) {
  if (!fs.existsSync(ANTIGRAVITY_GLOBAL_STORAGE_DB)) return null;

  let db = null;
  try {
    db = new Database(ANTIGRAVITY_GLOBAL_STORAGE_DB, { readonly: true, fileMustExist: true });
    const row = db.prepare('SELECT value FROM ItemTable WHERE key = ?').get(key);
    if (!row) return null;
    const v = row.value;
    if (typeof v === 'string') return v;
    if (Buffer.isBuffer(v) || v instanceof Uint8Array) return Buffer.from(v).toString('utf-8');
    return v == null ? null : String(v);
  } catch {
    return null;
  } finally {
    if (db) db.close();
  }
}

function extractFolderFromSummaryProtoBytes(summaryProtoBytes) {
  for (const s of iterAllUtf8StringsInProto(summaryProtoBytes, 6)) {
    const match = s.match(/#?file:\/\/[^\s\x00-\x1f"]+/);
    if (!match) continue;
    let uri = match[0];
    if (uri.startsWith('#')) uri = uri.slice(1);
    const folder = fileUriToPath(uri);
    if (folder) return folder;
  }
  return null;
}

function extractOfflineMetaFromSummaryProtoBytes(summaryProtoBytes) {
  let title = null;
  let primaryCount = 0;
  let secondaryCount = 0;
  const timestamps = [];

  let offset = 0;
  while (offset < summaryProtoBytes.length) {
    const tagRes = readVarint(summaryProtoBytes, offset);
    if (!tagRes) break;
    offset = tagRes.offset;

    const fieldNumber = tagRes.value >>> 3;
    const wireType = tagRes.value & 0x7;

    if (wireType === 0) {
      const valueRes = readVarint(summaryProtoBytes, offset);
      if (!valueRes) break;
      offset = valueRes.offset;
      if (fieldNumber === 2) primaryCount = valueRes.value;
      if (fieldNumber === 16) secondaryCount = valueRes.value;
      continue;
    }

    if (wireType === 2) {
      const ld = readLengthDelimited(summaryProtoBytes, offset);
      if (!ld) break;
      offset = ld.offset;

      if (fieldNumber === 1 && !title) {
        const text = bytesToUtf8(ld.bytes);
        if (text && text.trim()) title = text.trim();
        continue;
      }

      if (fieldNumber === 3 || fieldNumber === 7 || fieldNumber === 10 || fieldNumber === 15) {
        const ts = fieldNumber === 15 ? findTimestampInProto(ld.bytes, 2) : (parseTimestampMessage(ld.bytes) || findTimestampInProto(ld.bytes, 1));
        if (ts) timestamps.push(ts);
        continue;
      }

      continue;
    }

    const skipped = skipField(summaryProtoBytes, offset, wireType);
    if (!skipped) break;
    offset = skipped.offset;
  }

  const uniqueTimestamps = [...new Set(timestamps)].sort((a, b) => a - b);

  return {
    title,
    folder: extractFolderFromSummaryProtoBytes(summaryProtoBytes),
    bubbleCount: Math.max(primaryCount || 0, secondaryCount || 0),
    createdAt: uniqueTimestamps[0] || null,
    lastUpdatedAt: uniqueTimestamps[uniqueTimestamps.length - 1] || null,
  };
}

function buildOfflineMetaMapFromGlobalStateTrajectorySummariesValue(outerValueBase64) {
  const outerBytes = base64ToBytes(outerValueBase64);
  if (!outerBytes) return {};

  const chats = {};
  let offset = 0;

  while (offset < outerBytes.length) {
    const tagRes = readVarint(outerBytes, offset);
    if (!tagRes) break;
    offset = tagRes.offset;

    const fieldNumber = tagRes.value >>> 3;
    const wireType = tagRes.value & 0x7;
    if (fieldNumber !== 1 || wireType !== 2) {
      const skipped = skipField(outerBytes, offset, wireType);
      if (!skipped) break;
      offset = skipped.offset;
      continue;
    }

    const entryLd = readLengthDelimited(outerBytes, offset);
    if (!entryLd) break;
    offset = entryLd.offset;

    let composerId = null;
    let summaryBase64 = null;
    let entryOffset = 0;

    while (entryOffset < entryLd.bytes.length) {
      const entryTag = readVarint(entryLd.bytes, entryOffset);
      if (!entryTag) break;
      entryOffset = entryTag.offset;

      const entryField = entryTag.value >>> 3;
      const entryWire = entryTag.value & 0x7;

      if (entryField === 1 && entryWire === 2) {
        const keyLd = readLengthDelimited(entryLd.bytes, entryOffset);
        if (!keyLd) break;
        entryOffset = keyLd.offset;
        composerId = bytesToUtf8(keyLd.bytes);
        continue;
      }

      if (entryField === 2 && entryWire === 2) {
        const valueLd = readLengthDelimited(entryLd.bytes, entryOffset);
        if (!valueLd) break;
        entryOffset = valueLd.offset;

        let valueOffset = 0;
        while (valueOffset < valueLd.bytes.length) {
          const valueTag = readVarint(valueLd.bytes, valueOffset);
          if (!valueTag) break;
          valueOffset = valueTag.offset;

          const valueField = valueTag.value >>> 3;
          const valueWire = valueTag.value & 0x7;
          if (valueField === 1 && valueWire === 2) {
            const summaryLd = readLengthDelimited(valueLd.bytes, valueOffset);
            if (!summaryLd) break;
            valueOffset = summaryLd.offset;
            summaryBase64 = bytesToUtf8(summaryLd.bytes);
            break;
          }

          const skipped = skipField(valueLd.bytes, valueOffset, valueWire);
          if (!skipped) break;
          valueOffset = skipped.offset;
        }

        continue;
      }

      const skipped = skipField(entryLd.bytes, entryOffset, entryWire);
      if (!skipped) break;
      entryOffset = skipped.offset;
    }

    if (!composerId || !summaryBase64) continue;
    const summaryProtoBytes = base64ToBytes(summaryBase64);
    if (!summaryProtoBytes) continue;

    chats[composerId] = extractOfflineMetaFromSummaryProtoBytes(summaryProtoBytes);
  }

  return chats;
}

// ============================================================
// Offline source: ~/.gemini/antigravity/conversation_summaries.db
// (works when Antigravity is closed; covers all platforms)
// ============================================================

function parseSqliteDatetime(s) {
  // "2026-11-15 11:53:19.8712335+00:00" → epoch ms
  if (!s || typeof s !== 'string') return null;
  const iso = s.replace(' ', 'T').replace(/(\.\d{3})\d+/, '$1');
  const t = Date.parse(iso);
  return Number.isNaN(t) ? null : t;
}

function workspaceUrisToFolder(json) {
  try {
    const uris = JSON.parse(json);
    if (!Array.isArray(uris)) return null;
    for (const uri of uris) {
      if (typeof uri !== 'string') continue;
      const folder = fileUriToPath(uri);
      if (folder) return folder;
    }
  } catch { /* ignore */ }
  return null;
}

function getLocalSummariesChats() {
  if (!fs.existsSync(ANTIGRAVITY_SUMMARIES_DB)) return [];

  let db = null;
  try {
    db = new Database(ANTIGRAVITY_SUMMARIES_DB, { readonly: true, fileMustExist: true });
    const rows = db.prepare(
      'SELECT conversation_id, title, step_count, last_modified_time, workspace_uris, agent_name, last_user_input_time FROM conversation_summaries'
    ).all();

    return rows.map((r) => ({
      source: 'antigravity',
      composerId: r.conversation_id,
      name: (r.title || '').trim() || null,
      createdAt: parseSqliteDatetime(r.last_user_input_time) || parseSqliteDatetime(r.last_modified_time),
      lastUpdatedAt: parseSqliteDatetime(r.last_modified_time),
      mode: r.agent_name || 'cascade',
      folder: workspaceUrisToFolder(r.workspace_uris),
      encrypted: false,
      bubbleCount: r.step_count || 0,
      _stepCount: r.step_count || 0,
      _type: 'antigravity-offline-local',
      _offline: true,
      _dbPath: ANTIGRAVITY_SUMMARIES_DB,
      _rawSource: 'offline-local-db',
    })).filter((c) => c.composerId);
  } catch {
    return [];
  } finally {
    if (db) db.close();
  }
}

function getOfflineChats() {
  // Primary: new Antigravity local storage (~/.gemini/antigravity)
  const local = getLocalSummariesChats();
  if (local.length > 0) return local;

  // Legacy fallback: VS Code-style globalStorage state.vscdb
  for (const key of OFFLINE_TRAJECTORY_SUMMARIES_KEYS) {
    const value = readGlobalStateValue(key);
    if (!value) continue;

    const map = buildOfflineMetaMapFromGlobalStateTrajectorySummariesValue(value);
    const chats = Object.entries(map).map(([composerId, meta]) => ({
      source: 'antigravity',
      composerId,
      name: meta.title || null,
      createdAt: meta.createdAt || null,
      lastUpdatedAt: meta.lastUpdatedAt || null,
      mode: 'cascade',
      folder: meta.folder || null,
      encrypted: false,
      bubbleCount: meta.bubbleCount || 0,
      _stepCount: meta.bubbleCount || 0,
      _type: 'antigravity-offline',
      _offline: true,
      _dbPath: ANTIGRAVITY_GLOBAL_STORAGE_DB,
      _rawSource: 'offline-global-state',
    }));

    if (chats.length > 0) {
      return chats.sort((a, b) => (b.lastUpdatedAt || b.createdAt || 0) - (a.lastUpdatedAt || a.createdAt || 0));
    }
  }

  return [];
}

// ============================================================
// Offline messages: ~/.gemini/antigravity/conversations/<id>.db
// Step payloads are raw protobuf (CortexStep). Known step types:
//   14  = user input        (text at field 19.2 / 19.3.1)
//   15  = agent turn        (prose at 20.1, tool output at 20.3/20.7.3,
//                            token usage at 5.9.{1,2,3,5})
//   132 = planner response  (tool calls at 5.4.[{1:id,2:name,3:args}],
//                            model uid at 5.11)
//   others (memory/knowledge/browser snapshots) are skipped
// ============================================================

const STEP_TYPE_USER_INPUT = 14;
const STEP_TYPE_AGENT_TURN = 15;
const STEP_TYPE_PLANNER_RESPONSE = 132;

function attachUsageToLastAssistant(messages, usage) {
  for (let i = messages.length - 1; i >= 0; i--) {
    if (messages[i].role === 'assistant') {
      messages[i]._inputTokens = (messages[i]._inputTokens || 0) + (usage.input || 0);
      messages[i]._outputTokens = (messages[i]._outputTokens || 0) + (usage.output || 0);
      messages[i]._cacheRead = (messages[i]._cacheRead || 0) + (usage.cacheRead || 0);
      return;
    }
    if (messages[i].role === 'user') return;
  }
}

function parseOfflineStep(top, messages) {
  const type = getF(top, 1);
  if (typeof type !== 'number') return null;

  if (type === STEP_TYPE_USER_INPUT) {
    const userInput = getSub(top, 19);
    if (!userInput) return null;
    let text = getText(userInput, 2);
    if (!text) {
      const nested = getSub(userInput, 3);
      text = nested ? getText(nested, 1) : null;
    }
    if (!text || !text.trim()) return null;
    return { role: 'user', content: text };
  }

  if (type === STEP_TYPE_PLANNER_RESPONSE) {
    const meta = getSub(top, 5);
    if (!meta) return null;

    const toolCalls = [];
    for (const raw of (meta[4] || [])) {
      if (!Buffer.isBuffer(raw)) continue;
      const tc = decodeProtoTree(raw);
      if (!tc) continue;
      const id = getText(tc, 1);
      const tcName = getText(tc, 2);
      const argsJson = getText(tc, 3);
      if (!tcName) continue;
      let args = {};
      try { args = argsJson ? JSON.parse(argsJson) : {}; } catch { args = {}; }
      toolCalls.push({ name: tcName, args, _id: id });
    }

    const modelUid = getF(meta, 11);
    const parts = toolCalls.map((tc) => {
      const argKeys = typeof tc.args === 'object' ? Object.keys(tc.args).join(', ') : '';
      return `[tool-call: ${tc.name}(${argKeys})]`;
    });

    if (parts.length === 0) return null;

    return {
      role: 'assistant',
      content: parts.join('\n'),
      _model: typeof modelUid === 'number' ? normalizeModel(String(modelUid)) : null,
      _toolCalls: toolCalls,
    };
  }

  if (type === STEP_TYPE_AGENT_TURN) {
    const meta = getSub(top, 5);
    const turn = getSub(top, 20);
    if (!turn) return null;

    // Build the message first (prose response or tool execution result)
    // Prose response to the user (field 20.1 / 20.8)
    let prose = getText(turn, 1);
    if (!prose || !prose.trim()) prose = getText(turn, 8);

    let msg = null;
    if (prose && prose.trim()) {
      const modelUid = meta ? getF(meta, 11) : null;
      msg = {
        role: 'assistant',
        content: prose.trim(),
        _model: typeof modelUid === 'number' ? normalizeModel(String(modelUid)) : null,
      };
    } else {
      // Tool execution result (field 20.3 = text, 20.7 = {1: callId, 3: resultJson})
      let output = getText(turn, 3);
      let toolName = null;
      if (!output || !output.trim()) {
        const toolResult = getSub(turn, 7);
        if (toolResult) {
          const resultJson = getText(toolResult, 3);
          const callId = getText(toolResult, 1);
          if (resultJson) {
            toolName = extractToolNameFromCallId(messages, callId);
            output = resultJson;
          }
        }
      }
      if (output && output.trim()) {
        const preview = output.substring(0, 500);
        msg = { role: 'tool', content: toolName ? `[${toolName}] ${preview}` : `[tool] ${preview}` };
      }
    }

    // Token usage lives at 5.9.{1: input, 2: output, 3: reasoning, 5: total}
    if (meta) {
      const usageNode = getSub(meta, 9);
      if (usageNode) {
        const input = getF(usageNode, 1);
        const output = getF(usageNode, 2);
        const reasoning = getF(usageNode, 3);
        const total = getF(usageNode, 5);
        const inputN = typeof input === 'number' ? input : 0;
        const outputN = typeof output === 'number' ? output : 0;
        const reasoningN = typeof reasoning === 'number' ? reasoning : 0;
        const totalN = typeof total === 'number' ? total : 0;
        const cacheRead = Math.max(0, totalN - inputN - outputN - reasoningN);
        if (inputN || outputN || cacheRead) {
          const usage = { input: inputN, output: outputN + reasoningN, cacheRead };
          if (msg && msg.role === 'assistant') {
            // This step IS the generation its usage belongs to
            msg._inputTokens = usage.input;
            msg._outputTokens = usage.output;
            msg._cacheRead = usage.cacheRead;
          } else {
            // Tool execution step: usage belongs to the previous planner generation
            attachUsageToLastAssistant(messages, usage);
          }
        }
      }
    }

    return msg;
  }

  return null;
}

function extractToolNameFromCallId(messages, callId) {
  if (!callId) return null;
  for (let i = messages.length - 1; i >= 0; i--) {
    const m = messages[i];
    if (m.role !== 'assistant' || !m._toolCalls) continue;
    for (const tc of m._toolCalls) {
      if (tc._id === callId) return tc.name;
    }
  }
  return null;
}

function getOfflineMessages(chat) {
  const dbPath = path.join(ANTIGRAVITY_CONVERSATIONS_DIR, `${chat.composerId}.db`);
  if (!fs.existsSync(dbPath)) return [];

  let db = null;
  try {
    db = new Database(dbPath, { readonly: true, fileMustExist: true });
    const rows = db.prepare('SELECT step_payload FROM steps ORDER BY idx').all();
    const messages = [];
    for (const row of rows) {
      const payload = row.step_payload;
      if (!payload || !Buffer.isBuffer(payload) || payload.length === 0) continue;
      try {
        const top = decodeProtoTree(payload);
        if (!top) continue;
        const msg = parseOfflineStep(top, messages);
        if (msg) messages.push(msg);
      } catch { /* skip malformed step */ }
    }
    return messages;
  } catch {
    return [];
  } finally {
    if (db) db.close();
  }
}

function mergeChats(liveChats, offlineChats) {
  if (liveChats.length === 0) return offlineChats;
  if (offlineChats.length === 0) return liveChats;

  const map = new Map();

  for (const chat of offlineChats) {
    map.set(chat.composerId, { ...chat });
  }

  for (const chat of liveChats) {
    const existing = map.get(chat.composerId);
    if (!existing) {
      map.set(chat.composerId, chat);
      continue;
    }

    map.set(chat.composerId, {
      ...existing,
      ...chat,
      name: chat.name || existing.name,
      createdAt: chat.createdAt || existing.createdAt,
      lastUpdatedAt: chat.lastUpdatedAt || existing.lastUpdatedAt,
      folder: chat.folder || existing.folder,
      bubbleCount: chat.bubbleCount || existing.bubbleCount,
      _stepCount: chat._stepCount || existing._stepCount,
    });
  }

  return Array.from(map.values()).sort((a, b) => (b.lastUpdatedAt || b.createdAt || 0) - (a.lastUpdatedAt || a.createdAt || 0));
}


// ============================================================
// Cross-platform process utilities
// ============================================================

const IS_WINDOWS = process.platform === 'win32';

function getProcessList() {
  try {
    if (IS_WINDOWS) {
      // Win32_Process via CIM (Get-Process has no CommandLine property)
      const output = execFileSync('powershell.exe', ['-NoProfile', '-Command',
        '@(Get-CimInstance Win32_Process | Where-Object { $_.CommandLine } | Select-Object ProcessId, CommandLine) | ConvertTo-Json -Compress'],
        { encoding: 'utf-8', maxBuffer: 32 * 1024 * 1024 });
      let procs;
      try { procs = JSON.parse(output); } catch { return []; }
      if (!procs) return [];
      if (!Array.isArray(procs)) procs = [procs];
      return procs
        .filter((p) => p && p.ProcessId && p.CommandLine)
        .map((p) => ({ pid: String(p.ProcessId), commandLine: String(p.CommandLine) }));
    } else {
      const output = execSync('ps aux', { encoding: 'utf-8', maxBuffer: 10 * 1024 * 1024 });
      return output.split('\n').slice(1).map(line => {
        const parts = line.trim().split(/\s+/);
        if (parts.length < 11) return null;
        const pid = parts[1];
        const commandLine = parts.slice(10).join(' ');
        return { commandLine, pid };
      }).filter(Boolean);
    }
  } catch { return []; }
}

function getListeningPorts(pid) {
  try {
    const output = IS_WINDOWS
      ? execSync('netstat -ano', { encoding: 'utf-8', maxBuffer: 32 * 1024 * 1024 })
      : execSync(`lsof -i TCP -P -n -a -p ${pid} 2>/dev/null`, { encoding: 'utf-8', maxBuffer: 10 * 1024 * 1024 });

    const ports = [];
    const re = IS_WINDOWS
      ? /127\.0\.0\.1:(\d+)\s+\S+\s+LISTENING\s+(\d+)/g
      : /TCP\s+127\.0\.0\.1:(\d+)\s+\(LISTEN\)/g;

    let match;
    while ((match = re.exec(output)) !== null) {
      if (IS_WINDOWS && match[2] !== String(pid)) continue;
      const port = parseInt(match[1], 10);
      if (port && !ports.includes(port)) ports.push(port);
    }
    return ports;
  } catch { return []; }
}

// ============================================================
// Find running Antigravity language server (port + CSRF token)
// ============================================================

let _lsCache = null;
let _lsCacheCheckedAt = 0;

function findLanguageServer() {
  if (_lsCache !== null && (Date.now() - _lsCacheCheckedAt) < 10000) return _lsCache || null;

  for (const proc of getProcessList()) {
    const { commandLine, pid } = proc;
    // Match language_server(.exe) / language_server_windows / _macos / _linux
    if (!/language_server(\.exe|_windows|_macos|_linux)?(\s|"|$)/i.test(commandLine)) continue;
    // Must be Antigravity's server (ide name override or app data dir)
    if (!/antigravity/i.test(commandLine)) continue;

    const csrfMatch = commandLine.match(/--csrf_token[=\s]+(\S+)/);
    if (!csrfMatch) continue;

    const ports = getListeningPorts(pid);
    if (ports.length === 0) continue;

    // Antigravity's LS listens on one HTTPS port (self-signed) and one
    // HTTP port. Explicit flags win when present.
    const httpsPortMatch = commandLine.match(/--https_server_port[=\s]+(\d+)/);
    const serverPortMatch = commandLine.match(/--server_port[=\s]+(\d+)/);

    let candidates = [];
    if (httpsPortMatch && parseInt(httpsPortMatch[1], 10) > 0) {
      candidates.push({ port: parseInt(httpsPortMatch[1], 10), scheme: 'https' });
    }
    if (serverPortMatch && parseInt(serverPortMatch[1], 10) > 0) {
      candidates.push({ port: parseInt(serverPortMatch[1], 10), scheme: 'http' });
    }
    for (const port of ports) {
      candidates.push({ port, scheme: 'https' });
      candidates.push({ port, scheme: 'http' });
    }

    _lsCache = { csrf: csrfMatch[1], pid, candidates };
    _lsCacheCheckedAt = Date.now();
    return _lsCache;
  }

  _lsCache = false;
  _lsCacheCheckedAt = Date.now();
  return null;
}

// ============================================================
// Connect protocol HTTP client (tries HTTPS then HTTP per port)
// ============================================================

let _rpcEndpoint = null; // { port, scheme } once discovered

function writeTempBody(data) {
  const os = require('os');
  const file = path.join(os.tmpdir(), `agentlytics-antigravity-${process.pid}-${Date.now()}.json`);
  fs.writeFileSync(file, data);
  return file;
}

function callRpc(method, body) {
  const ls = findLanguageServer();
  if (!ls) return null;

  const data = JSON.stringify(body || {});

  // Endpoint already probed: single attempt
  const attempts = _rpcEndpoint
    ? [_rpcEndpoint, ...ls.candidates.filter((c) => c.port !== _rpcEndpoint.port)]
    : ls.candidates;

  for (const cand of attempts) {
    const url = `${cand.scheme}://127.0.0.1:${cand.port}/exa.language_server_pb.LanguageServerService/${method}`;
    let bodyFile = null;
    try {
      bodyFile = writeTempBody(data);
      const insecureFlag = cand.scheme === 'https' ? ' -k' : '';
      const result = execSync(
        `curl -s${insecureFlag} --max-time 10 -X POST ${JSON.stringify(url)} ` +
        `-H "Content-Type: application/json" ` +
        `-H "x-codeium-csrf-token: ${ls.csrf}" ` +
        `-d @${JSON.stringify(bodyFile)}`,
        { encoding: 'utf-8', maxBuffer: 50 * 1024 * 1024, stdio: ['pipe', 'pipe', 'pipe'] }
      );
      if (!result || !result.trim()) continue;
      const parsed = JSON.parse(result);
      _rpcEndpoint = { port: cand.port, scheme: cand.scheme };
      return parsed;
    } catch {
      continue;
    } finally {
      if (bodyFile) { try { fs.unlinkSync(bodyFile); } catch { /* ignore */ } }
    }
  }

  return null;
}

// ============================================================
// Adapter interface
// ============================================================

const name = 'antigravity';

function getChats() {
  const resp = callRpc('GetAllCascadeTrajectories', {});
  const liveChats = [];

  if (resp && resp.trajectorySummaries) {
    for (const [cascadeId, summary] of Object.entries(resp.trajectorySummaries)) {
      const ws = (summary.workspaces || [])[0];
      const folder = ws?.workspaceFolderAbsoluteUri?.replace('file://', '') || null;
      const rawModel = summary.lastGeneratorModelUid;
      liveChats.push({
        source: 'antigravity',
        composerId: cascadeId,
        name: summary.summary || null,
        createdAt: summary.createdTime ? new Date(summary.createdTime).getTime() : null,
        lastUpdatedAt: summary.lastModifiedTime ? new Date(summary.lastModifiedTime).getTime() : null,
        mode: 'cascade',
        folder,
        encrypted: false,
        bubbleCount: summary.stepCount || 0,
        _stepCount: summary.stepCount,
        _model: rawModel ? normalizeModel(rawModel) : rawModel,
        _rawModel: rawModel,
      });
    }
  }

  return mergeChats(liveChats, getOfflineChats());
}

function getSteps(chat) {
  // Prefer GetCascadeTrajectorySteps (returns more steps than GetCascadeTrajectory)
  const resp = callRpc('GetCascadeTrajectorySteps', { cascadeId: chat.composerId });
  if (resp && resp.steps && resp.steps.length > 0) return resp.steps;

  // Fallback to old method
  const resp2 = callRpc('GetCascadeTrajectory', { cascadeId: chat.composerId });
  if (resp2 && resp2.trajectory && resp2.trajectory.steps) return resp2.trajectory.steps;

  return [];
}

/**
 * Get the tail messages beyond the step limit using generatorMetadata.
 * The last generatorMetadata entry with messagePrompts has the conversation context.
 * We find the overlap with step-based messages by matching the last user message content.
 */
function getTailMessages(chat, stepMessages) {
  const resp = callRpc('GetCascadeTrajectory', { cascadeId: chat.composerId });
  if (!resp || !resp.trajectory) return [];

  const gm = resp.trajectory.generatorMetadata || [];
  // Find the last entry that has messagePrompts
  let lastWithMsgs = null;
  for (let i = gm.length - 1; i >= 0; i--) {
    if (gm[i].chatModel && gm[i].chatModel.messagePrompts && gm[i].chatModel.messagePrompts.length > 0) {
      lastWithMsgs = gm[i];
      break;
    }
  }
  if (!lastWithMsgs) return [];

  const mp = lastWithMsgs.chatModel.messagePrompts;

  // Find the last user message from step-based parsing
  let lastUserContent = '';
  for (let i = stepMessages.length - 1; i >= 0; i--) {
    if (stepMessages[i].role === 'user' && stepMessages[i].content.length > 20) {
      lastUserContent = stepMessages[i].content;
      break;
    }
  }
  if (!lastUserContent) return [];

  // Find this message in the messagePrompts (search from end for efficiency)
  const needle = lastUserContent.substring(0, 50);
  let matchIdx = -1;
  for (let i = mp.length - 1; i >= 0; i--) {
    if (mp[i].source === 'CHAT_MESSAGE_SOURCE_USER' && mp[i].prompt && mp[i].prompt.includes(needle)) {
      matchIdx = i;
      break;
    }
  }
  if (matchIdx < 0 || matchIdx >= mp.length - 1) return [];

  // Convert everything after the match point to messages
  const tail = [];
  for (let i = matchIdx + 1; i < mp.length; i++) {
    const m = mp[i];
    const src = m.source || '';
    const prompt = m.prompt || '';
    if (!prompt || !prompt.trim()) continue;

    let role;
    if (src === 'CHAT_MESSAGE_SOURCE_USER') role = 'user';
    else if (src === 'CHAT_MESSAGE_SOURCE_SYSTEM') role = 'assistant';
    else if (src === 'CHAT_MESSAGE_SOURCE_TOOL') role = 'tool';
    else continue;

    tail.push({ role, content: prompt });
  }
  return tail;
}

function parseStep(step) {
  const type = step.type || '';
  const meta = step.metadata || {};

  if (type === 'CORTEX_STEP_TYPE_USER_INPUT' && step.userInput) {
    return {
      role: 'user',
      content: step.userInput.userResponse || step.userInput.items?.map(i => i.text).join('') || '',
    };
  }

  if (type === 'CORTEX_STEP_TYPE_ASK_USER_QUESTION' && step.askUserQuestion) {
    const q = step.askUserQuestion;
    return {
      role: 'user',
      content: q.userResponse || q.question || '',
    };
  }

  if (type === 'CORTEX_STEP_TYPE_PLANNER_RESPONSE' && step.plannerResponse) {
    const pr = step.plannerResponse;
    const parts = [];
    if (pr.thinking) parts.push(`[thinking] ${pr.thinking}`);
    const text = pr.modifiedResponse || pr.response || pr.textContent || '';
    if (text.trim()) parts.push(text.trim());
    const _toolCalls = [];
    if (pr.toolCalls && pr.toolCalls.length > 0) {
      for (const tc of pr.toolCalls) {
        let args = {};
        try { args = tc.argumentsJson ? JSON.parse(tc.argumentsJson) : {}; } catch { args = {}; }
        const argKeys = typeof args === 'object' ? Object.keys(args).join(', ') : '';
        parts.push(`[tool-call: ${tc.name}(${argKeys})]`);
        _toolCalls.push({ name: tc.name, args });
      }
    }
    if (parts.length > 0) {
      const model = meta.generatorModel || meta.generatorModelUid;
      return {
        role: 'assistant',
        content: parts.join('\n'),
        _model: model ? normalizeModel(model) : model,
        _toolCalls,
      };
    }
    return null;
  }

  // Tool-like step types
  if (type === 'CORTEX_STEP_TYPE_TOOL_EXECUTION' && step.toolExecution) {
    const te = step.toolExecution;
    const toolName = te.toolName || te.name || 'tool';
    const result = te.output || te.result || '';
    const preview = typeof result === 'string' ? result.substring(0, 500) : JSON.stringify(result).substring(0, 500);
    return { role: 'tool', content: `[${toolName}] ${preview}` };
  }

  if (type === 'CORTEX_STEP_TYPE_RUN_COMMAND' && step.runCommand) {
    const rc = step.runCommand;
    const cmd = rc.command || rc.commandLine || '';
    const out = (rc.output || rc.stdout || '').substring(0, 500);
    return { role: 'tool', content: `[run_command] ${cmd}${out ? '\n' + out : ''}` };
  }

  if (type === 'CORTEX_STEP_TYPE_COMMAND_STATUS' && step.commandStatus) {
    const cs = step.commandStatus;
    const out = (cs.output || cs.stdout || '').substring(0, 500);
    return out ? { role: 'tool', content: `[command_status] ${out}` } : null;
  }

  if (type === 'CORTEX_STEP_TYPE_VIEW_FILE' && step.viewFile) {
    const vf = step.viewFile;
    const filePath = vf.filePath || vf.path || '';
    return { role: 'tool', content: `[view_file] ${filePath}` };
  }

  if (type === 'CORTEX_STEP_TYPE_CODE_ACTION' && step.codeAction) {
    const ca = step.codeAction;
    const filePath = ca.filePath || ca.path || '';
    return { role: 'tool', content: `[code_action] ${filePath}` };
  }

  if (type === 'CORTEX_STEP_TYPE_GREP_SEARCH' && step.grepSearch) {
    const gs = step.grepSearch;
    const query = gs.query || gs.pattern || '';
    return { role: 'tool', content: `[grep_search] ${query}` };
  }

  if (type === 'CORTEX_STEP_TYPE_LIST_DIRECTORY' && step.listDirectory) {
    const ld = step.listDirectory;
    const dir = ld.directoryPath || ld.path || '';
    return { role: 'tool', content: `[list_directory] ${dir}` };
  }

  if (type === 'CORTEX_STEP_TYPE_MCP_TOOL' && step.mcpTool) {
    const mt = step.mcpTool;
    const mname = mt.toolName || mt.name || 'mcp_tool';
    return { role: 'tool', content: `[${mname}]` };
  }

  // Skip non-content steps
  if (type === 'CORTEX_STEP_TYPE_CHECKPOINT' || type === 'CORTEX_STEP_TYPE_RETRIEVE_MEMORY' ||
      type === 'CORTEX_STEP_TYPE_MEMORY' || type === 'CORTEX_STEP_TYPE_TODO_LIST' ||
      type === 'CORTEX_STEP_TYPE_EXIT_PLAN_MODE' || type === 'CORTEX_STEP_TYPE_PROXY_WEB_SERVER') {
    return null;
  }

  return null;
}

function getMessages(chat) {
  // Offline chats: parse local SQLite step payloads
  if (chat._offline) {
    const offlineMessages = getOfflineMessages(chat);
    if (offlineMessages.length > 0) return offlineMessages;
  }

  const steps = getSteps(chat);
  if (steps.length === 0 && !chat._offline) {
    // Live lookup returned nothing — fall back to the local DB
    const offlineMessages = getOfflineMessages(chat);
    if (offlineMessages.length > 0) return offlineMessages;
  }

  const messages = [];
  for (const step of steps) {
    const msg = parseStep(step);
    if (msg) messages.push(msg);
  }

  // If steps are truncated, fill in the tail from generatorMetadata
  const tail = getTailMessages(chat, messages);
  if (tail.length > 0) {
    messages.push(...tail);
  }

  return messages;
}

// ============================================================
// Usage / quota data from language server RPC
// ============================================================

function getUsage() {
  const { isSubscriptionAccessAllowed } = require('./base');
  if (!isSubscriptionAccessAllowed()) return null;
  const resp = callRpc('GetUserStatus', {});
  if (!resp || !resp.userStatus) return null;

  const us = resp.userStatus;
  const ps = us.planStatus || {};
  const pi = ps.planInfo || {};
  const modelConfigs = (us.cascadeModelConfigData || {}).clientModelConfigs || [];

  const models = modelConfigs.map((m) => {
    const qi = m.quotaInfo || {};
    return {
      label: m.label || null,
      model: m.modelOrAlias?.model || null,
      remainingFraction: qi.remainingFraction != null ? qi.remainingFraction : null,
      resetTime: qi.resetTime || null,
      supportsImages: m.supportsImages || false,
    };
  });

  // Antigravity returns credits already in display units (no ÷100 needed)
  const promptAlloc = ps.availablePromptCredits || 0;
  const promptUsed = ps.usedPromptCredits || 0;
  const flexAlloc = ps.availableFlexCredits || 0;
  const flexUsed = ps.usedFlexCredits || 0;
  const flowAlloc = ps.availableFlowCredits || 0;

  const remainingPrompt = Math.max(0, promptAlloc - promptUsed);
  const remainingFlex = Math.max(0, flexAlloc - flexUsed);
  const totalRemaining = remainingPrompt + remainingFlex;

  // Credit multipliers per model
  const creditMultipliers = (pi.creditMultiplierOverrides || []).reduce((acc, entry) => {
    const model = entry.modelOrAlias?.model;
    if (model && entry.creditMultiplier != null) acc[model] = entry.creditMultiplier;
    return acc;
  }, {});

  return {
    source: 'antigravity',
    plan: {
      name: pi.planName || null,
      tier: pi.teamsTier || null,
      monthlyPromptCredits: (pi.monthlyPromptCredits || 0) / 100,
      monthlyFlowCredits: (pi.monthlyFlowCredits || 0) / 100,
      canBuyMoreCredits: pi.canBuyMoreCredits || false,
    },
    usage: {
      promptCredits: { allocated: promptAlloc, used: promptUsed, remaining: remainingPrompt },
      flexCredits: { allocated: flexAlloc, used: flexUsed, remaining: remainingFlex },
      flowCredits: { allocated: flowAlloc },
      totalRemainingCredits: totalRemaining,
    },
    billingCycle: {
      start: ps.planStart || null,
      end: ps.planEnd || null,
    },
    features: {
      webSearch: pi.cascadeWebSearchEnabled || false,
      browser: pi.browserEnabled || false,
      knowledgeBase: pi.knowledgeBaseEnabled || false,
      autoRunCommands: pi.cascadeCanAutoRunCommands || false,
      commitMessages: pi.canGenerateCommitMessages || false,
    },
    models,
    creditMultipliers,
    user: {
      name: us.name || null,
      email: us.email || null,
    },
  };
}

function resetCache() { _lsCache = null; _lsCacheCheckedAt = 0; _modelMap = null; _sessionFolderMap = null; _rpcEndpoint = null; }

const labels = { 'antigravity': 'Antigravity' };

// Cache session→folder mapping so we only build it once per process
let _sessionFolderMap = null;
function getSessionFolderMap() {
  if (_sessionFolderMap) return _sessionFolderMap;
  _sessionFolderMap = new Map();
  try {
    const chats = getChats();
    for (const chat of chats) {
      if (chat.composerId && chat.folder) {
        _sessionFolderMap.set(chat.composerId, chat.folder);
      }
    }
  } catch { /* skip */ }
  return _sessionFolderMap;
}

function normalizePath(p) {
  if (!p) return p;
  return p.replace(/\/+$/, '').replace(/^file:\/\//, '');
}

function getArtifacts(folder) {
  const { scanArtifacts } = require('./base');
  const artifacts = folder ? scanArtifacts(folder, {
    editor: 'antigravity',
    label: 'Antigravity',
    files: [],
    dirs: ['.gemini/skills', '.gemini/rules', '.gemini/plans', '.gemini/workflows'],
  }) : [];

  // Add brain artifacts (task.md, implementation_plan.md, walkthrough.md) per session
  if (!folder || !fs.existsSync(ANTIGRAVITY_BRAIN_DIR)) return artifacts;

  const sessionMap = getSessionFolderMap();
  const normalizedFolder = normalizePath(folder);

  try {
    const sessions = fs.readdirSync(ANTIGRAVITY_BRAIN_DIR);
    const brainFileNames = ['task.md', 'implementation_plan.md', 'walkthrough.md'];
    for (const sessionId of sessions) {
      // Only include sessions that belong to this project folder
      const sessionFolder = normalizePath(sessionMap.get(sessionId));
      if (!sessionFolder || sessionFolder !== normalizedFolder) continue;

      const sessionDir = path.join(ANTIGRAVITY_BRAIN_DIR, sessionId);
      try {
        if (!fs.statSync(sessionDir).isDirectory()) continue;
      } catch { continue; }
      for (const fileName of brainFileNames) {
        const filePath = path.join(sessionDir, fileName);
        if (!fs.existsSync(filePath)) continue;
        try {
          const stat = fs.statSync(filePath);
          const content = fs.readFileSync(filePath, 'utf-8');
          if (!content.trim()) continue;
          const lines = content.split('\n').length;
          artifacts.push({
            name: fileName,
            path: filePath,
            relativePath: `brain/${sessionId.slice(0, 8)}/${fileName}`,
            size: stat.size,
            lines,
            modifiedAt: stat.mtimeMs,
            editor: 'antigravity',
            editorLabel: 'Antigravity',
          });
        } catch { /* skip unreadable */ }
      }
    }
  } catch { /* skip if brain dir unreadable */ }

  return artifacts;
}

function getMCPServers() {
  const { parseMcpConfigFile } = require('./base');
  // Antigravity uses similar config to Windsurf: ~/.codeium/antigravity/mcp_config.json
  const globalConfig = path.join(HOME, '.codeium', 'antigravity', 'mcp_config.json');
  const geminiConfig = path.join(ANTIGRAVITY_LOCAL_DIR, 'mcp_config.json');
  return [
    ...parseMcpConfigFile(globalConfig, { editor: 'antigravity', label: 'Antigravity', scope: 'global' }),
    ...parseMcpConfigFile(geminiConfig, { editor: 'antigravity', label: 'Antigravity', scope: 'global' }),
  ];
}

module.exports = { name, labels, getChats, getMessages, resetCache, getUsage, getArtifacts, getMCPServers };
