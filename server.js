'use strict';

/* Muse Spark chat demo backend.
 * Node.js built-ins only. No dependencies.
 * Reads MODEL_API_KEY from process environment only.
 * Serves static files from ./public only. Never reads outside this project.
 */

const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');

const UPSTREAM_URL = 'https://api.meta.ai/v1/chat/completions';
const MODEL = 'muse-spark-1.3';
const MAX_BODY_BYTES = 32 * 1024;
const MAX_MESSAGES = 30;
const MAX_CONTENT_CHARS = 4000;
const UPSTREAM_TIMEOUT_MS = 30000;

const PUBLIC_DIR = path.join(__dirname, 'public');

const STATIC_FILES = new Map([
  ['/', { file: 'index.html', type: 'text/html; charset=utf-8' }],
  ['/index.html', { file: 'index.html', type: 'text/html; charset=utf-8' }],
  ['/styles.css', { file: 'styles.css', type: 'text/css; charset=utf-8' }],
  ['/app.js', { file: 'app.js', type: 'text/javascript; charset=utf-8' }],
  ['/favicon.svg', { file: 'favicon.svg', type: 'image/svg+xml; charset=utf-8' }],
]);

const ALLOWED_ROLES = new Set(['user', 'assistant', 'system']);
const ALLOWED_ORIGIN_HOSTS = new Set(['127.0.0.1', 'localhost']);

function baseHeaders() {
  return {
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer',
  };
}

function sendJson(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, {
    ...baseHeaders(),
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': Buffer.byteLength(body),
    'Cache-Control': 'no-store',
  });
  res.end(body);
}

function isAllowedOrigin(req) {
  const origin = req.headers.origin;
  if (!origin) return true; // same-origin form/fetch without Origin, curl, etc.
  let parsed;
  try {
    parsed = new URL(origin);
  } catch {
    return false;
  }
  if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') return false;
  return parsed.protocol === 'http:' && ALLOWED_ORIGIN_HOSTS.has(parsed.hostname)
    && parsed.host === req.headers.host;
}

function readBody(req, maxBytes) {
  return new Promise((resolve, reject) => {
    const declared = Number(req.headers['content-length']);
    if (Number.isFinite(declared) && declared > maxBytes) {
      const err = new Error('Body too large');
      err.code = 'BODY_TOO_LARGE';
      reject(err);
      req.resume();
      return;
    }
    const chunks = [];
    let size = 0;
    req.on('data', (chunk) => {
      size += chunk.length;
      if (size > maxBytes) {
        const err = new Error('Body too large');
        err.code = 'BODY_TOO_LARGE';
        reject(err);
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    req.on('error', reject);
  });
}

function validateChatBody(body) {
  if (!body || typeof body !== 'object' || Array.isArray(body)) {
    return { ok: false, error: 'Request body must be a JSON object.' };
  }
  const { messages } = body;
  if (!Array.isArray(messages) || messages.length === 0) {
    return { ok: false, error: 'messages must be a non-empty array.' };
  }
  if (messages.length > MAX_MESSAGES) {
    return { ok: false, error: `messages must contain at most ${MAX_MESSAGES} items.` };
  }
  const clean = [];
  for (let i = 0; i < messages.length; i += 1) {
    const m = messages[i];
    if (!m || typeof m !== 'object' || Array.isArray(m)) {
      return { ok: false, error: `messages[${i}] must be an object.` };
    }
    if (!ALLOWED_ROLES.has(m.role)) {
      return { ok: false, error: `messages[${i}].role must be user, assistant, or system.` };
    }
    if (typeof m.content !== 'string') {
      return { ok: false, error: `messages[${i}].content must be a string.` };
    }
    const content = m.content.trim();
    if (content.length === 0) {
      return { ok: false, error: `messages[${i}].content must not be empty.` };
    }
    if (content.length > MAX_CONTENT_CHARS) {
      return { ok: false, error: `messages[${i}].content must be at most ${MAX_CONTENT_CHARS} characters.` };
    }
    clean.push({ role: m.role, content });
  }
  return { ok: true, messages: clean };
}

function timeoutSignal(ms) {
  if (typeof AbortSignal !== 'undefined' && typeof AbortSignal.timeout === 'function') {
    return { signal: AbortSignal.timeout(ms), cancel: () => {} };
  }
  const controller = new AbortController();
  const t = setTimeout(() => controller.abort(), ms);
  return { signal: controller.signal, cancel: () => clearTimeout(t) };
}

async function callUpstream({ messages, apiKey, fetchImpl, upstreamUrl, timeoutMs }) {
  const fetchFn = fetchImpl || globalThis.fetch;
  if (typeof fetchFn !== 'function') {
    throw new Error('fetch is not available');
  }
  const { signal, cancel } = timeoutSignal(timeoutMs);
  try {
    const res = await fetchFn(upstreamUrl, {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${apiKey}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ model: MODEL, messages }),
      signal,
    });
    return res;
  } finally {
    cancel();
  }
}

function extractReplyText(data) {
  const content = data && data.choices && data.choices[0] && data.choices[0].message
    ? data.choices[0].message.content
    : undefined;
  if (typeof content === 'string' && content.trim().length > 0) return content;
  // Some OpenAI-compatible servers use choices[0].text
  const text = data && data.choices && data.choices[0] ? data.choices[0].text : undefined;
  if (typeof text === 'string' && text.trim().length > 0) return text;
  return null;
}

function serveStatic(req, res, pathname) {
  if (req.method !== 'GET' && req.method !== 'HEAD') {
    sendJson(res, 405, { error: 'Method not allowed.' });
    return;
  }
  const entry = STATIC_FILES.get(pathname);
  if (!entry) {
    sendJson(res, 404, { error: 'Not found.' });
    return;
  }
  // Only ever read from PUBLIC_DIR; whitelist above prevents traversal.
  const abs = path.join(PUBLIC_DIR, entry.file);
  if (!abs.startsWith(PUBLIC_DIR + path.sep) && abs !== PUBLIC_DIR) {
    sendJson(res, 404, { error: 'Not found.' });
    return;
  }
  fs.readFile(abs, (err, data) => {
    if (err) {
      sendJson(res, 500, { error: 'Failed to load page.' });
      return;
    }
    const headers = {
      ...baseHeaders(),
      'Content-Type': entry.type,
      'Content-Length': data.length,
      'Cache-Control': 'no-store',
    };
    if (entry.file === 'index.html') {
      headers['Content-Security-Policy'] = [
        "default-src 'self'",
        "connect-src 'self'",
        "script-src 'self'",
        "style-src 'self'",
        "img-src 'self' data:",
        "object-src 'none'",
        "base-uri 'self'",
        'frame-ancestors \'none\'',
      ].join('; ');
    }
    res.writeHead(200, headers);
    if (req.method === 'HEAD') {
      res.end();
    } else {
      res.end(data);
    }
  });
}

async function handleChat(req, res, opts) {
  if (req.method !== 'POST') {
    sendJson(res, 405, { error: 'Method not allowed. Use POST.' });
    return;
  }
  if (!isAllowedOrigin(req)) {
    sendJson(res, 403, { error: 'Origin not allowed.' });
    return;
  }
  const ctype = String(req.headers['content-type'] || '');
  if (!ctype.toLowerCase().includes('application/json')) {
    sendJson(res, 415, { error: 'Content-Type must be application/json.' });
    return;
  }

  let raw;
  try {
    raw = await readBody(req, MAX_BODY_BYTES);
  } catch (err) {
    if (err && err.code === 'BODY_TOO_LARGE') {
      sendJson(res, 413, { error: 'Request body too large.' });
      return;
    }
    sendJson(res, 400, { error: 'Failed to read request body.' });
    return;
  }

  let parsed;
  try {
    parsed = raw ? JSON.parse(raw) : null;
  } catch {
    sendJson(res, 400, { error: 'Request body must be valid JSON.' });
    return;
  }

  const valid = validateChatBody(parsed);
  if (!valid.ok) {
    sendJson(res, 400, { error: valid.error });
    return;
  }

  // API key from environment only. Tests may inject an explicit value.
  const apiKey = Object.prototype.hasOwnProperty.call(opts, 'apiKey')
    ? opts.apiKey
    : process.env.MODEL_API_KEY;
  if (!apiKey || typeof apiKey !== 'string' || apiKey.trim().length === 0) {
    console.error('MODEL_API_KEY is not set');
    sendJson(res, 500, { error: 'Server is not configured. Set MODEL_API_KEY.' });
    return;
  }

  const upstreamUrl = opts.upstreamUrl || UPSTREAM_URL;
  const timeoutMs = Number.isFinite(opts.timeoutMs) ? opts.timeoutMs : UPSTREAM_TIMEOUT_MS;

  let upstreamRes;
  try {
    upstreamRes = await callUpstream({
      messages: valid.messages,
      apiKey: apiKey.trim(),
      fetchImpl: opts.fetchImpl,
      upstreamUrl,
      timeoutMs,
    });
  } catch (err) {
    const name = err && err.name ? String(err.name) : '';
    if (name === 'TimeoutError' || name === 'AbortError') {
      console.error('Upstream timeout');
      sendJson(res, 504, { error: 'Upstream request timed out. Try again.' });
      return;
    }
    console.error('Upstream request failed:', err && err.message ? err.message : err);
    sendJson(res, 502, { error: 'Upstream request failed. Try again.' });
    return;
  }

  if (!upstreamRes || !upstreamRes.ok) {
    const status = upstreamRes ? upstreamRes.status : 'unknown';
    console.error(`Upstream responded with status ${status}`);
    // Do not forward upstream body: it may contain sensitive details.
    sendJson(res, 502, { error: 'Upstream request failed. Try again.' });
    return;
  }

  let data;
  try {
    data = await upstreamRes.json();
  } catch {
    console.error('Upstream returned invalid JSON');
    sendJson(res, 502, { error: 'Upstream returned an invalid response.' });
    return;
  }

  const reply = extractReplyText(data);
  if (!reply) {
    console.error('Upstream response missing choices content');
    sendJson(res, 502, { error: 'Upstream returned an invalid response.' });
    return;
  }
  sendJson(res, 200, { reply });
}

function createServer(options = {}) {
  const server = http.createServer((req, res) => {
    let pathname = '/';
    try {
      const u = new URL(req.url || '/', 'http://127.0.0.1');
      pathname = u.pathname;
    } catch {
      sendJson(res, 400, { error: 'Bad request.' });
      return;
    }

    if (pathname === '/api/chat') {
      handleChat(req, res, options).catch((err) => {
        console.error('Chat handler error:', err && err.message ? err.message : err);
        if (!res.headersSent) sendJson(res, 500, { error: 'Internal server error.' });
      });
      return;
    }
    if (pathname === '/api/health') {
      if (req.method !== 'GET') {
        sendJson(res, 405, { error: 'Method not allowed.' });
        return;
      }
      sendJson(res, 200, { ok: true, model: MODEL });
      return;
    }
    serveStatic(req, res, pathname);
  });
  return server;
}

function parsePort(value, fallback) {
  const n = Number.parseInt(String(value), 10);
  if (Number.isFinite(n) && n > 0 && n < 65536) return n;
  return fallback;
}

if (require.main === module) {
  const host = process.env.HOST || '127.0.0.1';
  const port = parsePort(process.env.PORT, 3000);
  const server = createServer();
  server.listen(port, host, () => {
    console.log(`Muse Spark chat demo listening on http://${host}:${port}`);
    if (!process.env.MODEL_API_KEY) {
      console.log('MODEL_API_KEY is not set. Set it before sending chat requests.');
    }
  });
}

module.exports = {
  createServer,
  validateChatBody,
  MODEL,
  UPSTREAM_URL,
  MAX_BODY_BYTES,
  MAX_MESSAGES,
  MAX_CONTENT_CHARS,
  UPSTREAM_TIMEOUT_MS,
};
