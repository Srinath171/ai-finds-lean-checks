'use strict';

const { describe, it, beforeEach, afterEach } = require('node:test');
const assert = require('node:assert/strict');

const { createServer, MODEL, UPSTREAM_URL, MAX_MESSAGES } = require('../server.js');

async function startServer(options) {
  const server = createServer(options);
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  const { port } = server.address();
  return { server, base: `http://127.0.0.1:${port}` };
}

async function stopServer(server) {
  await new Promise((resolve) => server.close(resolve));
}

async function postChat(base, body, extraHeaders = {}) {
  const res = await fetch(`${base}/api/chat`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', ...extraHeaders },
    body: typeof body === 'string' ? body : JSON.stringify(body),
  });
  let json = null;
  try {
    json = await res.json();
  } catch {
    json = null;
  }
  return { res, json };
}

describe('POST /api/chat', () => {
  let server;
  let base;

  afterEach(async () => {
    if (server) {
      await stopServer(server);
      server = null;
    }
  });

  it('returns successful reply and forwards model + messages + bearer key', async () => {
    const seen = {};
    const fetchImpl = async (url, opts) => {
      seen.url = url;
      seen.auth = opts.headers.Authorization;
      seen.body = JSON.parse(opts.body);
      return {
        ok: true,
        status: 200,
        json: async () => ({ choices: [{ message: { content: 'Hello from Spark!' } }] }),
      };
    };
    ({ server, base } = await startServer({ fetchImpl, apiKey: 'test-key-123' }));

    const { res, json } = await postChat(base, {
      messages: [{ role: 'user', content: 'Hi' }],
    });

    assert.equal(res.status, 200);
    assert.equal(json.reply, 'Hello from Spark!');
    assert.equal(seen.url, UPSTREAM_URL);
    assert.equal(seen.auth, 'Bearer test-key-123');
    assert.equal(seen.body.model, MODEL);
    assert.equal(MODEL, 'muse-spark-1.3');
    assert.deepEqual(seen.body.messages, [{ role: 'user', content: 'Hi' }]);
  });

  it('returns 500 without leaking details when API key is missing', async () => {
    let called = false;
    const fetchImpl = async () => {
      called = true;
      return { ok: true, status: 200, json: async () => ({}) };
    };
    ({ server, base } = await startServer({ fetchImpl, apiKey: '' }));

    const { res, json } = await postChat(base, {
      messages: [{ role: 'user', content: 'Hi' }],
    });

    assert.equal(res.status, 500);
    assert.match(json.error, /not configured/i);
    assert.equal(called, false);
  });

  it('rejects invalid input variants with 400', async () => {
    const fetchImpl = async () => {
      throw new Error('upstream must not be called for invalid input');
    };
    ({ server, base } = await startServer({ fetchImpl, apiKey: 'test-key' }));

    const cases = [
      [{}, /messages/],
      [{ messages: [] }, /non-empty/],
      [{ messages: [{ role: 'user', content: '   ' }] }, /not be empty/],
      [{ messages: [{ role: 'hacker', content: 'x' }] }, /role/],
      [{ messages: [{ role: 'user', content: 42 }] }, /string/],
      [{ messages: Array.from({ length: MAX_MESSAGES + 1 }, () => ({ role: 'user', content: 'x' })) }, /at most/],
      [{ messages: [{ role: 'user', content: 'x'.repeat(4001) }] }, /at most 4000/],
    ];
    for (const [body, pattern] of cases) {
      const { res, json } = await postChat(base, body);
      assert.equal(res.status, 400, `expected 400 for ${JSON.stringify(body).slice(0, 80)}`);
      assert.match(json.error, pattern);
    }

    // Invalid JSON
    const bad = await postChat(base, '{not-json');
    assert.equal(bad.res.status, 400);
  });

  it('rejects oversized bodies with 413', async () => {
    const fetchImpl = async () => {
      throw new Error('upstream must not be called for oversized body');
    };
    ({ server, base } = await startServer({ fetchImpl, apiKey: 'test-key' }));
    const { res } = await postChat(base, {
      messages: [{ role: 'user', content: 'y'.repeat(40 * 1024) }],
    });
    assert.equal(res.status, 413);
  });

  it('returns safe 502 when upstream fails', async () => {
    // HTTP 500 from upstream
    {
      const fetchImpl = async () => ({ ok: false, status: 500, json: async () => ({}) });
      ({ server, base } = await startServer({ fetchImpl, apiKey: 'k' }));
      const { res, json } = await postChat(base, { messages: [{ role: 'user', content: 'Hi' }] });
      assert.equal(res.status, 502);
      assert.match(json.error, /upstream/i);
      await stopServer(server);
      server = null;
    }
    // Network throw
    {
      const fetchImpl = async () => {
        throw new Error('boom');
      };
      ({ server, base } = await startServer({ fetchImpl, apiKey: 'k' }));
      const { res, json } = await postChat(base, { messages: [{ role: 'user', content: 'Hi' }] });
      assert.equal(res.status, 502);
      assert.match(json.error, /upstream/i);
      await stopServer(server);
      server = null;
    }
    // Missing content shape
    {
      const fetchImpl = async () => ({ ok: true, status: 200, json: async () => ({ choices: [] }) });
      ({ server, base } = await startServer({ fetchImpl, apiKey: 'k' }));
      const { res, json } = await postChat(base, { messages: [{ role: 'user', content: 'Hi' }] });
      assert.equal(res.status, 502);
      assert.match(json.error, /invalid response/i);
      await stopServer(server);
      server = null;
    }
  });

  it('rejects disallowed Origin with 403', async () => {
    let called = false;
    const fetchImpl = async () => {
      called = true;
      return { ok: true, status: 200, json: async () => ({}) };
    };
    ({ server, base } = await startServer({ fetchImpl, apiKey: 'k' }));
    const { res } = await postChat(
      base,
      { messages: [{ role: 'user', content: 'Hi' }] },
      { Origin: 'https://evil.example.com' }
    );
    assert.equal(res.status, 403);
    assert.equal(called, false);
  });

  it('serves UI and blocks path traversal', async () => {
    ({ server, base } = await startServer({ apiKey: 'k', fetchImpl: async () => ({}) }));
    const page = await fetch(`${base}/`);
    assert.equal(page.status, 200);
    assert.match(page.headers.get('content-type'), /text\/html/);

    const traversal = await fetch(`${base}/..%2Fserver.js`);
    assert.equal(traversal.status, 404);
  });
});
