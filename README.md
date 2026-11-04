# Muse Spark Chat Demo

Small local chat demo for the Muse Spark **Standard** model `muse-spark-1.3`.
Node.js built-in HTTP server plus vanilla HTML/CSS/JS. No dependencies.

## API key requirement

This app needs its own **separate pay-as-you-go Meta API key** set as
`MODEL_API_KEY`. It calls `https://api.meta.ai/v1/chat/completions` directly.

Do **not** use Muse login credentials for this app. They are not an API key
and must never be pasted into `.env` or sent to the API.

## Setup (Windows)

Requirements: Node.js 20.6+ (for `--env-file`).

```powershell
Copy-Item .env.example .env
# Edit .env and set MODEL_API_KEY to your pay-as-you-go key.

node --env-file=.env server.js
```

Open [http://localhost:3000](http://localhost:3000) in a browser.

Optional environment variables:

- `PORT` (default `3000`)
- `HOST` (default `localhost`; keep the loopback default unless you
  understand the exposure)

## How it works

- `GET /` serves the chat UI from `public/`.
- `POST /api/chat` accepts `{ "messages": [{ "role", "content" }] }`,
  validates it, then forwards `{ "model": "muse-spark-1.3", "messages" }`
  to the upstream chat-completions endpoint with
  `Authorization: Bearer MODEL_API_KEY`.
- `GET /api/health` returns `{ "ok": true, "model": "muse-spark-1.3" }`.

## Security notes

- `MODEL_API_KEY` is read from the process environment only.
- The server only reads static files from `public/` (whitelisted names).
  It never reads credentials or files outside this project.
- Binds `localhost` by default.
- Validates JSON input; body capped at 32 KiB; history capped at 30
  messages; each message capped at 4000 characters.
- Upstream timeout is 30 seconds; upstream bodies are never forwarded to
  clients (safe generic errors only).
- `Origin` header is validated against `localhost` / `localhost` when present.
- Frontend renders all message text with `textContent` (XSS-safe);
  HTML responses send a restrictive Content-Security-Policy.

## Tests

Built-in runner, upstream mocked (no network):

```powershell
npm test
```

Covers: successful reply, missing API key, invalid input variants,
upstream failure variants, origin rejection, and static path traversal.
