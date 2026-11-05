'use strict';

/* Vanilla chat client. XSS-safe: renders all text via textContent only. */
(function () {
  const MAX_HISTORY = 30;
  const REQUEST_TIMEOUT_MS = 35000;

  const messagesEl = document.getElementById('messages');
  const form = document.getElementById('chat-form');
  const input = document.getElementById('input');
  const sendBtn = document.getElementById('send-btn');
  const clearBtn = document.getElementById('clear-btn');
  const statusEl = document.getElementById('status');
  const errorEl = document.getElementById('error');
  const themeToggle = document.getElementById('theme-toggle');

  const THEME_KEY = 'theme';

  function systemTheme() {
    return window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches
      ? 'dark'
      : 'light';
  }

  function storedTheme() {
    try {
      const value = window.localStorage.getItem(THEME_KEY);
      return value === 'dark' || value === 'light' ? value : null;
    } catch {
      return null;
    }
  }

  function applyTheme(theme) {
    document.documentElement.dataset.theme = theme;
    const isDark = theme === 'dark';
    themeToggle.textContent = isDark ? 'Light mode' : 'Dark mode';
    themeToggle.setAttribute('aria-pressed', String(isDark));
    themeToggle.setAttribute('aria-label', isDark ? 'Switch to light mode' : 'Switch to dark mode');
  }

  function initTheme() {
    applyTheme(storedTheme() || systemTheme());
    themeToggle.addEventListener('click', () => {
      const next = document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark';
      try {
        window.localStorage.setItem(THEME_KEY, next);
      } catch {
        // Private browsing etc.: still apply for this session.
      }
      applyTheme(next);
    });
    // No stored choice: keep following the OS if it changes.
    if (!storedTheme() && window.matchMedia) {
      const query = window.matchMedia('(prefers-color-scheme: dark)');
      const onChange = (event) => {
        if (!storedTheme()) applyTheme(event.matches ? 'dark' : 'light');
      };
      if (typeof query.addEventListener === 'function') {
        query.addEventListener('change', onChange);
      } else if (typeof query.addListener === 'function') {
        query.addListener(onChange);
      }
    }
  }

  initTheme();

  /** @type {{role: string, content: string}[]} */
  let history = [];
  let pending = false;

  function scrollToBottom() {
    messagesEl.scrollTop = messagesEl.scrollHeight;
  }

  function addMessage(role, text) {
    const wrap = document.createElement('div');
    wrap.className = role === 'user' ? 'message user' : 'message assistant';

    const meta = document.createElement('p');
    meta.className = 'meta';
    meta.textContent = role === 'user' ? 'You' : 'Spark';

    const body = document.createElement('p');
    body.className = 'text';
    body.textContent = String(text); // never innerHTML

    wrap.appendChild(meta);
    wrap.appendChild(body);
    messagesEl.appendChild(wrap);
    scrollToBottom();
  }

  function setLoading(loading, label) {
    pending = loading;
    sendBtn.disabled = loading;
    clearBtn.disabled = loading;
    input.disabled = loading;
    if (loading) {
      statusEl.hidden = false;
      statusEl.dataset.loading = 'true';
      statusEl.textContent = label || 'Sending…';
    } else {
      statusEl.hidden = true;
      statusEl.dataset.loading = 'false';
      statusEl.textContent = '';
    }
  }

  function showError(message) {
    errorEl.hidden = false;
    errorEl.textContent = message;
  }

  function clearError() {
    errorEl.hidden = true;
    errorEl.textContent = '';
  }

  function clearConversation() {
    if (pending) return;
    history = [];
    messagesEl.replaceChildren();
    clearError();
    addMessage('assistant', 'Conversation cleared. What would you like to talk about?');
    input.focus();
  }

  function trimHistory() {
    if (history.length > MAX_HISTORY) {
      history = history.slice(history.length - MAX_HISTORY);
    }
  }

  async function readError(res) {
    try {
      const data = await res.json();
      if (data && typeof data.error === 'string' && data.error.trim()) {
        return data.error.trim();
      }
    } catch {
      // fall through to generic message
    }
    if (res.status === 413) return 'Message too long. Please shorten it and try again.';
    if (res.status === 403) return 'Request was blocked by origin check.';
    if (res.status === 500) return 'Server is not configured or failed. Check MODEL_API_KEY.';
    if (res.status === 502 || res.status === 504) return 'Upstream request failed. Please try again.';
    return `Request failed (${res.status}). Please try again.`;
  }

  async function send(text) {
    const payload = { messages: history.slice(-28).map(m => ({ ...m, content: m.content.slice(0, 4000) })).concat([{ role: 'user', content: text }]) };
    while (new TextEncoder().encode(JSON.stringify(payload)).length > 32000 && payload.messages.length > 1) {
      payload.messages.splice(0, 2);
    }
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), REQUEST_TIMEOUT_MS);
    try {
      const res = await fetch('/api/chat', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload),
        signal: controller.signal,
      });
      if (!res.ok) {
        throw new Error(await readError(res));
      }
      const data = await res.json();
      if (!data || typeof data.reply !== 'string' || !data.reply.trim()) {
        throw new Error('Server returned an invalid response.');
      }
      return data.reply;
    } finally {
      clearTimeout(timer);
    }
  }

  form.addEventListener('submit', async (event) => {
    event.preventDefault();
    if (pending) return;
    const text = input.value.trim();
    if (!text) return;

    clearError();
    addMessage('user', text);
    input.value = '';
    setLoading(true);

    try {
      const reply = await send(text);
      history.push({ role: 'user', content: text });
      history.push({ role: 'assistant', content: reply });
      trimHistory();
      addMessage('assistant', reply);
    } catch (err) {
      if (err && err.name === 'AbortError') {
        showError('Request timed out. Please try again.');
      } else {
        showError(err && err.message ? err.message : 'Request failed. Please try again.');
      }
    } finally {
      setLoading(false);
      input.focus();
    }
  });

  // Enter sends, Shift+Enter adds a newline.
  input.addEventListener('keydown', (event) => {
    if (event.key === 'Enter' && !event.shiftKey && !event.isComposing) {
      event.preventDefault();
      form.requestSubmit();
    }
  });

  clearBtn.addEventListener('click', clearConversation);
})();
