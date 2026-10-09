/**
 * Coster LiveChat Widget (Phase 1)
 * =================================
 * One generic script for all clients — the only thing that changes per client is
 * the Channel ID. Configuration (appearance, page targeting, customer
 * identification, default application, notification) is fetched from the Coster
 * backend at runtime, so changing a color or a page rule never requires editing
 * or redeploying this script.
 *
 * Usage (embedded widget):
 *   <script src="https://livechat.coster.example/widget.js"
 *           data-channel-id="LC-0002" async></script>
 *
 * Usage (SDK / programmatic):
 *   CosterLiveChat.init({ channelId: 'LC-0002' });
 *   CosterLiveChat.identify('<SIGNED_IDENTITY_TOKEN>');
 *
 * Usage (Direct Chat / full-page):
 *   <script src="widget.js"></script>
 *   <script>
 *     CosterLiveChat.init({ channelId: 'LC-0003', mode: 'direct', handoffToken: '...' });
 *   </script>
 *
 * PRD coverage implemented here (functional surface):
 *   - Floating launcher (bubble / bar-pill) + chat room          (10.3.5, 10.3.4)
 *   - Runtime config from backend                                 (FR-10/11/12)
 *   - Page targeting: allowed domain, include/exclude, matcher,
 *     SPA route handling                                          (10.1.3, FR-15/16/17)
 *   - Customer identification: visitor / pre-chat / logged-in,
 *     identify(token)                                             (10.2, 10.14)
 *   - Full-page Direct Chat mode                                  (10.14.2)
 *   - Inbound media + location from the composer                  (10.5.1, 10.3.4)
 *   - Notification sound + browser notification                   (10.3.6)
 *   - WebSocket messaging + Delivery Report (Sent/Delivered/Read) (10.9.2)
 *
 * All styles are namespaced under `.coster-widget` to avoid collisions.
 */
(function () {
  'use strict';

  if (window.__COSTER_LIVECHAT__) return;
  window.__COSTER_LIVECHAT__ = true;

  // ---------------------------------------------------------------------------
  // Tiny utils
  // ---------------------------------------------------------------------------
  function s(obj, path, fb) {
    var parts = String(path).split('.');
    var cur = obj;
    for (var i = 0; i < parts.length; i++) {
      if (cur == null) return fb;
      cur = cur[parts[i]];
    }
    return (cur === undefined || cur === null) ? fb : cur;
  }

  function clamp(n, min, max) {
    n = Number(n);
    if (isNaN(n)) n = min;
    return Math.max(min, Math.min(max, n));
  }

  function escapeHtml(str) {
    var div = document.createElement('div');
    div.appendChild(document.createTextNode(String(str == null ? '' : str)));
    return div.innerHTML;
  }

  function escapeAttr(str) {
    return String(str == null ? '' : str)
      .replace(/&/g, '&amp;').replace(/"/g, '&quot;')
      .replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  function isObject(v) { return v && typeof v === 'object' && !Array.isArray(v); }

  function deepMerge(base, over) {
    var out = Array.isArray(base) ? base.slice() : {};
    Object.keys(base).forEach(function (k) {
      var b = base[k];
      var has = over && Object.prototype.hasOwnProperty.call(over, k);
      var o = has ? over[k] : undefined;
      if (o === undefined) out[k] = b;
      else if (isObject(b) && isObject(o)) out[k] = deepMerge(b, o);
      else out[k] = o;
    });
    if (over) {
      Object.keys(over).forEach(function (k) {
        if (!Object.prototype.hasOwnProperty.call(out, k)) out[k] = over[k];
      });
    }
    return out;
  }

  function getScriptAttribute(name) {
    var scripts = document.getElementsByTagName('script');
    for (var i = 0; i < scripts.length; i++) {
      var value = scripts[i].getAttribute(name);
      if (value !== null) return value;
    }
    return null;
  }

  function getQueryParam(name) {
    try {
      return new URLSearchParams(window.location.search).get(name);
    } catch (e) {
      return null;
    }
  }

  function randomHex(n) {
    var out = '';
    for (var i = 0; i < n; i++) out += '0123456789ABCDEF'[Math.floor(Math.random() * 16)];
    return out;
  }

  function genMessageId() {
    return 'MSG-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 8);
  }

  function formatSize(b) {
    if (b == null) return '';
    if (b < 1024) return b + ' B';
    if (b < 1048576) return (b / 1024).toFixed(1) + ' KB';
    return (b / 1048576).toFixed(1) + ' MB';
  }

  // ---------------------------------------------------------------------------
  // Persistent state
  // ---------------------------------------------------------------------------
  var LS = {
    visitor: 'coster.livechat.visitorId',        // browser-scoped (PRD BR-15)
    muted: 'coster.livechat.muted',              // browser-scoped (FR-58)
    state: 'coster.livechat.state',              // per channel below
    prechat: 'coster.livechat.prechat',
    messages: 'coster.livechat.messages'
  };

  function loadJSON(key, fallback) {
    try {
      var raw = window.localStorage.getItem(key);
      return raw ? JSON.parse(raw) : fallback;
    } catch (e) { return fallback; }
  }

  function saveJSON(key, value) {
    try { window.localStorage.setItem(key, JSON.stringify(value)); } catch (e) {}
  }

  // --- resolved at init ---
  var channelId = getScriptAttribute('data-channel-id') || 'LC-0001';
  var mode = 'widget';
  var handoffToken = null;

  var cfg = {};
  var palette = {};

  var visitorId = loadJSON(LS.visitor, null);
  if (!visitorId) {
    visitorId = 'VIS-' + randomHex(8);
    saveJSON(LS.visitor, visitorId);
  }

  var muted = !!loadJSON(LS.muted, false);

  var state, prechatData, messages;

  var customerId = null;
  var customerName = null;

  // DOM refs
  var launcherEl, popupEl, directEl, bodyEl, footerEl, composerInput, fileInput;
  var pageVisible = true;
  var unreadIds = [];
  var lastSoundAt = 0;

  // Delivery tracking (WhatsApp-style ticks). messageId -> timeout id.
  var deliveryTimers = {};
  var DELIVERY_TIMEOUT = 10000; // ms to reach Delivered before marking Failed

  // Infinite-load pagination state.
  var oldestCursor = null;   // cursor for the oldest currently-loaded message
  var hasMore = false;       // true when older messages remain on the server
  var loadingOlder = false;  // guards concurrent "load older" requests

  // Per-kind upload size limits (bytes).
  var FILE_MAX = {
    image: 5 * 1024 * 1024,
    video: 16 * 1024 * 1024,
    audio: 16 * 1024 * 1024,
    document: 20 * 1024 * 1024
  };
  // Max size we embed as dataUrl (base64) and persist, so a preview/download is
  // available even after reload. Above this, we keep metadata only.
  var DATAURL_MAX = 4 * 1024 * 1024;

  function perChannelKey(base) { return base + '.' + channelId; }

  // ---------------------------------------------------------------------------
  // Fixed chat copy
  // ---------------------------------------------------------------------------
  var CHAT_TEXT = {
    agentInitial: 'A',
    agentGreeting: 'Hello! How can we help you today?',
    composerPlaceholder: 'Type a message...'
  };

  // ---------------------------------------------------------------------------
  // Defaults (fallback when the API is unreachable) — mirrors config.json "*"
  // ---------------------------------------------------------------------------
  var DEFAULTS = {
    channelName: 'Customer Care',
    status: 'Active',
    defaultApplication: 'Chatbot',
    identityMode: 'prechat',
    identification: {
      prechatEnabled: true,
      prechat: { name: true, email: true, phone: false, company: false },
      customFields: []
    },
    pageTargeting: { allowedDomains: [], mode: 'all', rules: [] },
    notification: { soundEnabled: true, tone: 'default', browserEnabled: true },
    appearance: {
      web: {
        csName: 'Customer Care',
        subtitle: 'Typically replies instantly',
        brandIcon: '',
        greetingTitle: 'Hello there!',
        welcomeMessage: 'Welcome! How can we help you today?',
        welcomeIcon: '',
        description: 'Ask a Question',
        delay: 0,
        autoExpand: false,
        ctaTextEnabled: true,
        ctaText: 'Chat with us',
        ctaIconData: '',
        borderRadius: 28,
        loginSubtitle: 'Please fill in the details before chatting.',
        loginButton: 'Start Chat',
        csAvatar: '',
        baseColor: '#2f9df4',
        agentBubbleColor: '#ffffff',
        agentBubbleText: '#344054',
        customerBubbleColor: '#2f9df4',
        customerBubbleText: '#ffffff',
        chatBackground: '#f8fafc',
        launcherType: 'bubble',
        launcherIcon: '',
        launcherText: 'Chat with us',
        launcherPosition: 'bottom-right',
        launcherSize: 56,
        launcherBottom: 24,
        launcherSide: 24,
        launcherShadow: true
      }
    }
  };

  var API_BASE = getScriptAttribute('data-api-base') || 'http://localhost:3000';
  var WS_URL = API_BASE.replace(/^http/, 'ws') + '/ws';

  // ---------------------------------------------------------------------------
  // Page targeting (10.1.3 / FR-15/16/17)
  // ---------------------------------------------------------------------------
  function matchRule(rule, path) {
    var v = rule.value || '';
    if (rule.matcher === 'startsWith') return path.indexOf(v) === 0;
    if (rule.matcher === 'contains') return path.indexOf(v) !== -1;
    return path === v; // equals
  }

  function pageTargetingPass(pt) {
    if (!pt) return true;

    // Allowed domains (empty => allow all).
    var domains = pt.allowedDomains || [];
    if (domains.length) {
      var host = window.location.hostname.toLowerCase();
      var allowed = domains.some(function (d) {
        var dd = String(d).toLowerCase();
        return host === dd || host.endsWith('.' + dd);
      });
      if (!allowed) return false;
    }

    if (!pt.mode || pt.mode === 'all') return true;

    var rules = pt.rules || [];
    var path = window.location.pathname;
    var includes = rules.filter(function (r) { return r.action !== 'exclude'; });
    var excludes = rules.filter(function (r) { return r.action === 'exclude'; });

    var included = includes.length === 0 || includes.some(function (r) { return matchRule(r, path); });
    var excluded = excludes.some(function (r) { return matchRule(r, path); });
    return included && !excluded;
  }

  function applyPageTargeting() {
    pageVisible = pageTargetingPass(s(cfg, 'pageTargeting', null));
    if (mode === 'direct') return; // Direct Chat is Coster's own page (no targeting).
    if (launcherEl) launcherEl.style.display = pageVisible ? 'flex' : 'none';
    if (!pageVisible && popupEl) close();
  }

  // SPA route handling (FR-17): re-evaluate without a full reload.
  function bindSpaRoutes() {
    var lastPath = window.location.pathname + window.location.search;
    function recheck() {
      var now = window.location.pathname + window.location.search;
      if (now !== lastPath) {
        lastPath = now;
        applyPageTargeting();
      }
    }
    window.addEventListener('popstate', recheck);
    window.addEventListener('hashchange', recheck);
    if (window.history && history.pushState) {
      var push = history.pushState, rep = history.replaceState;
      history.pushState = function () { var r = push.apply(this, arguments); recheck(); return r; };
      history.replaceState = function () { var r = rep.apply(this, arguments); recheck(); return r; };
    }
  }

  // ---------------------------------------------------------------------------
  // Notification sound (built-in tone, no custom upload — FR-57) + browser notify
  // ---------------------------------------------------------------------------
  var audioCtx = null;

  function ensureAudio() {
    try {
      var AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return;
      if (!audioCtx) audioCtx = new AC();
      if (audioCtx.state === 'suspended') audioCtx.resume();
    } catch (e) {}
  }

  // Built-in Coster notification tones (FR-57: admin picks one, no custom upload).
  // Each step is [frequency, startOffsetSeconds, durationSeconds].
  var TONES = {
    'default': [[880, 0, 0.14], [660, 0.14, 0.24]],
    'chime':   [[659.25, 0, 0.18], [987.77, 0.18, 0.3]],
    'ding':    [[1046.5, 0, 0.28]],
    'soft':    [[523.25, 0, 0.15], [659.25, 0.15, 0.3]]
  };

  function playSound() {
    if (muted || !s(cfg, 'notification.soundEnabled', true)) return;
    // One sound per response batch (FR-48/61): debounce.
    var now = Date.now();
    if (now - lastSoundAt < 300) return;
    lastSoundAt = now;
    try {
      ensureAudio();
      if (!audioCtx) return;
      var t = audioCtx.currentTime;
      var steps = TONES[s(cfg, 'notification.tone', 'default')] || TONES['default'];
      steps.forEach(function (step) {
        var start = t + step[1];
        var dur = step[2];
        var osc = audioCtx.createOscillator();
        var gain = audioCtx.createGain();
        osc.type = 'sine';
        osc.frequency.setValueAtTime(step[0], start);
        gain.gain.setValueAtTime(0.0001, start);
        gain.gain.exponentialRampToValueAtTime(0.12, start + 0.02);
        gain.gain.exponentialRampToValueAtTime(0.0001, start + dur);
        osc.connect(gain);
        gain.connect(audioCtx.destination);
        osc.start(start);
        osc.stop(start + dur + 0.05);
      });
    } catch (e) {}
  }

  function requestBrowserPermission() {
    if (!s(cfg, 'notification.browserEnabled', true)) return;
    if (!('Notification' in window)) return;
    if (Notification.permission === 'default') {
      try { Notification.requestPermission(); } catch (e) {}
    }
  }

  function browserNotify(text) {
    if (!s(cfg, 'notification.browserEnabled', true)) return;
    if (!('Notification' in window)) return;
    if (Notification.permission !== 'granted') return;
    if (document.visibilityState === 'visible') return; // don't notify while focused
    try {
      new Notification(s(cfg, 'appearance.web.csName', 'Coster LiveChat'), {
        body: text || 'Pesan baru dari Customer Service'
      });
    } catch (e) {}
  }

  // ---------------------------------------------------------------------------
  // WebSocket client (message + Delivery Report)
  // ---------------------------------------------------------------------------
  var ws = null;
  var wsConnected = false;
  var reconnectTimer = null;
  var reconnectDelay = 1000; // 1s -> backoff to max 30s
  var intentionalClose = false;

  function clearReconnectTimer() {
    if (reconnectTimer) { clearTimeout(reconnectTimer); reconnectTimer = null; }
  }

  function scheduleReconnect() {
    if (reconnectTimer) return; // already scheduled
    if (typeof WebSocket === 'undefined') return;
    reconnectTimer = setTimeout(function () {
      reconnectTimer = null;
      connect();
    }, reconnectDelay);
    reconnectDelay = Math.min(reconnectDelay * 2, 30000);
  }

  function connect() {
    if (typeof WebSocket === 'undefined') return;
    if (ws && (ws.readyState === 0 || ws.readyState === 1)) return; // already connecting/open

    clearReconnectTimer();
    try { ws = new WebSocket(WS_URL); } catch (e) { scheduleReconnect(); return; }

    ws.onopen = function () {
      wsConnected = true;
      reconnectDelay = 1000;
      backendSend({
        type: 'connect',
        channelId: channelId,
        visitorId: visitorId
      });
      if (handoffToken) backendSend({ type: 'identify', token: handoffToken });
      sendPrechat();            // re-send saved pre-chat data (reload / reconnect)
      resendPendingMessages();  // auto-retry messages that failed while offline
    };

    ws.onmessage = function (ev) {
      var m;
      try { m = JSON.parse(ev.data); } catch (e) { return; }
      onServerMessage(m);
    };

    ws.onclose = function () {
      wsConnected = false;
      if (!intentionalClose) scheduleReconnect();
    };

    ws.onerror = function () {
      // Usually followed by onclose; mark disconnected so sends are rejected.
      wsConnected = false;
    };
  }

  // Re-dispatch any customer message still stuck in Sending/Failed after a
  // reconnect — so nothing needs a page refresh (WhatsApp-style auto-resend).
  function resendPendingMessages() {
    var changed = false;
    messages.forEach(function (m) {
      if (m.from === 'customer' && (m.status === 'Failed' || m.status === 'Sending')) {
        m.status = 'Sending';
        clearDeliveryTimer(m.id);
        dispatchCustomerMessage(m);
        changed = true;
      }
    });
    if (changed) {
      saveJSON(perChannelKey(LS.messages), messages);
      renderChat();
    }
  }

  function backendSend(obj) {
    if (wsConnected && ws && ws.readyState === 1) {
      try { ws.send(JSON.stringify(obj)); return true; }
      catch (e) { return false; }
    }
    return false;
  }

  // ---------------------------------------------------------------------------
  // Incoming server messages
  // ---------------------------------------------------------------------------
  function onServerMessage(m) {
    switch (m.type) {
      case 'connected':
        if (m.visitorId) visitorId = m.visitorId;
        break;
      case 'identity':
        if (m.resolved && m.customerId) {
          customerId = m.customerId;
          customerName = m.name || customerName;
          if (state.stage !== 'chat') goToStage('chat');
          renderHeader();
        }
        break;
      case 'history':
        receiveHistory(m);
        break;
      case 'history_page':
        receiveHistoryPage(m);
        break;
      case 'agent_message':
        receiveAgentMessage(m);
        break;
      case 'delivery':
        updateDeliveryStatus(m.messageId, m.status);
        break;
      case 'system':
        pushSystem(m.text);
        break;
      case 'error':
        pushSystem('[error] ' + (m.message || m.code));
        break;
    }
  }

  function isActivelyViewing() {
    var open = mode === 'direct' ? true : (popupEl && popupEl.classList.contains('coster-widget--open'));
    return open && document.visibilityState === 'visible';
  }

  function markAllRead() {
    unreadIds.forEach(function (id) {
      backendSend({ type: 'delivery', messageId: id, status: 'Read' });
    });
    unreadIds = [];
  }

  // Convert a server message (wire shape) into the local message model.
  function hydrateMessage(m) {
    if (m.senderType === 'system') return { from: 'system', text: m.text };
    var from = m.senderType === 'visitor' ? 'customer' : 'agent';
    var item = {
      id: m.messageId,
      from: from,
      kind: m.kind || 'text',
      text: m.text || '',
      status: m.status || (from === 'customer' ? 'Delivered' : 'Sent')
    };
    if (from === 'agent') item.role = m.senderType === 'bot' ? 'bot' : 'agent';
    var meta = m.meta;
    if (meta) {
      if (meta.name != null) item.name = meta.name;
      if (meta.mime != null) item.mime = meta.mime;
      if (meta.size != null) item.size = meta.size;
      if (meta.dataUrl != null) item.dataUrl = meta.dataUrl;
      if (meta.lat != null) item.lat = meta.lat;
      if (meta.lng != null) item.lng = meta.lng;
    }
    return item;
  }

  function receiveHistory(m) {
    // Server is the source of truth for past messages — survives page reload
    // AND browser switch once the visitor is identified. Replace local state
    // with the LATEST page only (infinite load pulls older pages on demand).
    messages = (m.messages || []).map(hydrateMessage);
    hasMore = !!m.hasMore;
    oldestCursor = m.nextCursor || null;
    saveJSON(perChannelKey(LS.messages), messages);
    renderStage();
  }

  // Prepend an older page (user scrolled to the top). Preserves scroll position
  // so the view doesn't jump when messages are added above.
  function receiveHistoryPage(m) {
    loadingOlder = false;
    var older = (m.messages || []).map(hydrateMessage);
    var prevHeight = bodyEl ? bodyEl.scrollHeight : 0;
    var prevTop = bodyEl ? bodyEl.scrollTop : 0;

    // Merge, skipping any id already present (guard against cursor overlap).
    var seen = {};
    messages.forEach(function (x) { if (x.id) seen[x.id] = 1; });
    var fresh = older.filter(function (x) { return !seen[x.id]; });
    if (fresh.length) messages = fresh.concat(messages);

    hasMore = !!m.hasMore;
    oldestCursor = m.nextCursor || null;
    saveJSON(perChannelKey(LS.messages), messages);
    renderStage();

    // Keep the same message under the viewport.
    if (bodyEl) bodyEl.scrollTop = (bodyEl.scrollHeight - prevHeight) + prevTop;
  }

  function receiveAgentMessage(m) {
    messages.push({
      id: m.messageId,
      from: 'agent',
      role: m.from || 'bot',
      kind: m.kind || 'text',
      text: m.text,
      name: m.name,
      dataUrl: m.dataUrl,
      lat: m.lat,
      lng: m.lng,
      mime: m.mime,
      size: m.size
    });
    saveJSON(perChannelKey(LS.messages), messages);
    renderStage();
    // Acknowledge Delivery Report (outbound from Coster's perspective).
    backendSend({ type: 'delivery', messageId: m.messageId, status: 'Delivered' });
    if (isActivelyViewing()) {
      backendSend({ type: 'delivery', messageId: m.messageId, status: 'Read' });
    } else {
      unreadIds.push(m.messageId);
      playSound();
      browserNotify(m.text);
    }
  }

  // ---------------------------------------------------------------------------
  // Infinite load (older messages on scroll-to-top)
  // ---------------------------------------------------------------------------
  function bindInfiniteScroll() {
    if (!bodyEl) return;
    bodyEl.addEventListener('scroll', function () {
      if (loadingOlder || !hasMore || !oldestCursor) return;
      if (bodyEl.scrollTop <= 40) loadOlder();
    });
  }

  function loadOlder() {
    if (loadingOlder || !hasMore || !oldestCursor) return;
    loadingOlder = true;
    backendSend({ type: 'load_older', cursor: oldestCursor });
  }

  // ---------------------------------------------------------------------------
  // Stylesheet (uses resolved palette)
  // ---------------------------------------------------------------------------
  function computePalette() {
    var w = s(cfg, 'appearance.web', {});
    palette = {
      base: w.baseColor || '#2f9df4',
      agentBg: w.agentBubbleColor || '#ffffff',
      agentText: w.agentBubbleText || '#344054',
      custBg: w.customerBubbleColor || '#2f9df4',
      custText: w.customerBubbleText || '#ffffff',
      chatBg: w.chatBackground || '#f8fafc'
    };
  }

  function injectStyles() {
    var base = palette.base;
    var css = [
      '.coster-widget * { box-sizing: border-box; margin: 0; padding: 0; font-family: "Segoe UI Variable Text", "Segoe UI", Inter, system-ui, -apple-system, BlinkMacSystemFont, sans-serif; }',

      // Launcher
      '.coster-widget--launcher {',
      '  position: fixed; z-index: 2147483000;',
      '  border: none; color: #ffffff; cursor: pointer;',
      '  display: flex; align-items: center; justify-content: center; gap: 7px;',
      '  transition: transform 0.15s ease, box-shadow 0.15s ease;',
      '}',
      '.coster-widget--launcher:hover { transform: scale(1.05); }',
      '.coster-widget--launcher svg { width: 26px; height: 26px; flex: 0 0 auto; }',
      '.coster-widget--launcher img { width: 26px; height: 26px; object-fit: cover; border-radius: 4px; flex: 0 0 auto; }',
      '.coster-widget--launcher-text { font-size: 13px; font-weight: 700; white-space: nowrap; }',

      // Popup
      '.coster-widget--popup {',
      '  position: fixed; z-index: 2147483001;',
      '  width: 360px; max-width: calc(100vw - 40px); max-height: calc(100vh - 116px);',
      '  background: #ffffff; border-radius: 16px; overflow: hidden;',
      '  box-shadow: 0 18px 42px rgba(15, 23, 42, 0.25); border: 1px solid #dfe4ea;',
      '  display: flex; flex-direction: column;',
      '  opacity: 0; transform: translateY(12px); pointer-events: none;',
      '  transition: opacity 0.2s ease, transform 0.2s ease;',
      '}',
      '.coster-widget--popup.coster-widget--open { opacity: 1; transform: translateY(0); pointer-events: auto; }',

      // Direct chat full-page
      '.coster-widget--direct {',
      '  position: fixed; inset: 0; z-index: 2147483001; background: ' + palette.chatBg + ';',
      '  display: flex; flex-direction: column;',
      '}',

      // Header
      '.coster-widget--header { padding: 15px; background: ' + base + '; color: #ffffff; display: flex; gap: 10px; align-items: center; flex-shrink: 0; }',
      '.coster-widget--brand-logo { width: 38px; height: 38px; border-radius: 10px; background: #ffffff; color: ' + base + '; display: grid; place-items: center; font-weight: 800; font-size: 18px; flex-shrink: 0; overflow: hidden; }',
      '.coster-widget--brand-logo img { width: 100%; height: 100%; object-fit: cover; }',
      '.coster-widget--header-text { flex: 1; min-width: 0; }',
      '.coster-widget--header h4 { font-size: 14px; margin: 0 0 3px; font-weight: 700; }',
      '.coster-widget--header small { font-size: 11px; opacity: 0.9; }',
      '.coster-widget--close { background: transparent; border: none; color: #ffffff; cursor: pointer; font-size: 22px; line-height: 1; padding: 0 2px; flex-shrink: 0; opacity: 0.9; }',
      '.coster-widget--close:hover { opacity: 1; }',
      '.coster-widget--mute { background: transparent; border: none; color: #ffffff; cursor: pointer; font-size: 16px; line-height: 1; padding: 0 2px; flex-shrink: 0; opacity: 0.9; }',
      '.coster-widget--mute:hover { opacity: 1; }',

      // Body
      '.coster-widget--body { padding: 14px; background: ' + palette.chatBg + '; min-height: 260px; flex: 1 1 auto; overflow-y: auto; }',
      '.coster-widget--direct .coster-widget--body { min-height: 0; }',

      // Welcome
      '.coster-widget--welcome { background: #ffffff; border-radius: 12px; padding: 14px; box-shadow: 0 2px 8px rgba(0,0,0,0.06); }',
      '.coster-widget--welcome-icon { width: 38px; height: 38px; border-radius: 10px; background: #eaf6ff; display: grid; place-items: center; color: ' + base + '; margin-bottom: 10px; font-size: 20px; overflow: hidden; }',
      '.coster-widget--welcome-icon img { width: 100%; height: 100%; object-fit: cover; }',
      '.coster-widget--welcome h5 { font-size: 15px; margin: 0 0 6px; color: #1f2937; }',
      '.coster-widget--welcome p { font-size: 13px; color: #667085; line-height: 1.45; margin: 0; }',
      '.coster-widget--welcome-desc { margin-top: 8px; padding: 7px 8px; background: #f2f4f7; border-radius: 8px; font-size: 12px; color: #475467; }',
      '.coster-widget--cta { margin-top: 12px; width: 100%; border: 0; background: ' + base + '; color: #ffffff; border-radius: ' + s(cfg, 'appearance.web.borderRadius', 28) + 'px; padding: 11px; font-weight: 700; font-size: 13px; cursor: pointer; }',
      '.coster-widget--cta img { width: 16px; height: 16px; vertical-align: middle; margin-right: 5px; border-radius: 3px; }',
      '.coster-widget--cta:hover { filter: brightness(1.06); }',

      // Pre-chat
      '.coster-widget--prechat { background: #ffffff; border-radius: 12px; padding: 14px; }',
      '.coster-widget--prechat .coster-widget--sub { margin-bottom: 8px; font-size: 11px; color: #667085; }',
      '.coster-widget--field { box-sizing: border-box; width: 100%; height: 34px; border: 1px solid #d8dde5; border-radius: 7px; margin: 7px 0; padding: 7px 9px; font-size: 12px; color: #1f2937; outline: none; }',
      '.coster-widget--field::placeholder { color: #98a2b3; }',
      '.coster-widget--field:focus { border-color: ' + base + '; }',
      '.coster-widget--select { box-sizing: border-box; width: 100%; height: 34px; border: 1px solid #d8dde5; border-radius: 7px; margin: 7px 0; padding: 5px 9px; font-size: 12px; color: #1f2937; outline: none; background: #fff; }',
      '.coster-widget--check-field { display: flex; align-items: center; gap: 6px; margin: 7px 0; font-size: 12px; color: #475467; }',
      '.coster-widget--start-btn { box-sizing: border-box; margin-top: 8px; width: 100%; border: 0; border-radius: 8px; background: ' + base + '; color: #ffffff; padding: 10px; font-size: 12px; font-weight: 700; cursor: pointer; }',
      '.coster-widget--start-btn:hover { filter: brightness(1.06); }',

      // Chat
      '.coster-widget--chat { display: flex; flex-direction: column; gap: 2px; }',
      '.coster-widget--agent-row { display: flex; align-items: flex-end; gap: 6px; }',
      '.coster-widget--agent-avatar { width: 26px; height: 26px; border-radius: 50%; background: #e9eef3; display: grid; place-items: center; font-size: 11px; color: #475467; flex-shrink: 0; overflow: hidden; }',
      '.coster-widget--agent-avatar img { width: 100%; height: 100%; object-fit: cover; }',
      '.coster-widget--bubble { max-width: 78%; padding: 8px 10px; border-radius: 11px; font-size: 13px; margin: 6px 0; line-height: 1.4; word-wrap: break-word; }',
      '.coster-widget--customer-bubble { margin-left: auto; }',
      '.coster-widget--msg-status { display: block; text-align: right; font-size: 10px; color: #98a2b3; margin: -2px 0 4px; padding-right: 2px; min-height: 12px; }',
      '.coster-widget--msg-status.is-read { color: ' + base + '; }',
      '.coster-widget--status-badge { display: inline-block; color: #ffffff; background: #ef4444; border-radius: 50%; width: 16px; height: 16px; line-height: 16px; text-align: center; font-weight: 700; font-size: 11px; }',
      '.coster-widget--system { text-align: center; font-size: 11px; color: #98a2b3; margin: 8px 0; }',
      '.coster-widget--media { max-width: 100%; border-radius: 8px; display: block; }',
      '.coster-widget--imgwrap { display: block; cursor: pointer; }',
      '.coster-widget--imgwrap img { transition: opacity 0.15s ease; }',
      '.coster-widget--imgwrap:hover img { opacity: 0.88; }',
      '.coster-widget--file { display: flex; align-items: center; gap: 6px; }',
      '.coster-widget--file-name { font-weight: 600; }',
      '.coster-widget--file-size { opacity: 0.7; font-size: 11px; }',
      '.coster-widget--file-download { margin-left: auto; display: inline-flex; align-items: center; justify-content: center; width: 28px; height: 28px; border-radius: 50%; background: rgba(0,0,0,0.06); text-decoration: none; font-size: 15px; flex-shrink: 0; }',
      '.coster-widget--file-download:hover { background: rgba(0,0,0,0.12); }',
      '.coster-widget--bubble a { color: inherit; text-decoration: underline; }',

      // Composer
      '.coster-widget--composer { background: #ffffff; border-top: 1px solid #e4e7ec; padding: 9px; display: flex; gap: 7px; flex-shrink: 0; align-items: center; }',
      '.coster-widget--composer input { flex: 1; border: 1px solid #d8dde5; border-radius: 20px; padding: 0 12px; height: 34px; font-size: 13px; outline: none; color: #1f2937; min-width: 0; }',
      '.coster-widget--composer input:focus { border-color: ' + base + '; }',
      '.coster-widget--iconbtn { width: 34px; height: 34px; border: 1px solid #d8dde5; border-radius: 50%; background: #ffffff; cursor: pointer; font-size: 15px; line-height: 1; display: inline-flex; align-items: center; justify-content: center; padding: 0; flex-shrink: 0; }',
      '.coster-widget--iconbtn:hover { border-color: ' + base + '; }',
      '.coster-widget--send { width: 34px; height: 34px; border: 0; border-radius: 50%; background: ' + base + '; color: #ffffff; cursor: pointer; font-size: 15px; line-height: 1; display: inline-flex; align-items: center; justify-content: center; padding: 0; flex-shrink: 0; }',
      '.coster-widget--send:hover { filter: brightness(1.06); }'
    ].join('\n');

    var style = document.createElement('style');
    style.type = 'text/css';
    style.setAttribute('data-coster-widget', 'styles');
    if (style.styleSheet) style.styleSheet.cssText = css;
    else style.appendChild(document.createTextNode(css));
    document.head.appendChild(style);
  }

  var CHAT_ICON =
    '<svg viewBox="0 0 24 24" xmlns="http://www.w3.org/2000/svg">' +
    '<path fill="currentColor" d="M4 3h16a2 2 0 0 1 2 2v11a2 2 0 0 1-2 2H11l-5 4v-4H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2Z"/>' +
    '</svg>';

  // ---------------------------------------------------------------------------
  // Build the widget DOM
  // ---------------------------------------------------------------------------
  function buildHeader(withClose) {
    var csName = s(cfg, 'appearance.web.csName', 'Customer Care');
    var brandIcon = s(cfg, 'appearance.web.brandIcon', '');
    var subtitle = s(cfg, 'appearance.web.subtitle', 'Typically replies instantly');
    var logoHtml = brandIcon
      ? '<img src="' + escapeAttr(brandIcon) + '" alt="">'
      : escapeHtml((customerName || csName).charAt(0).toUpperCase());

    var header = document.createElement('div');
    header.className = 'coster-widget--header';
    header.innerHTML =
      '<div class="coster-widget--brand-logo">' + logoHtml + '</div>' +
      '<div class="coster-widget--header-text">' +
      '<h4>' + escapeHtml(customerName || csName) + '</h4>' +
      '<small>' + escapeHtml(customerName ? 'Identified customer' : subtitle) + '</small>' +
      '</div>';

    // Mute/Unmute toggle (FR-58) — browser-scoped customer preference.
    var muteBtn = document.createElement('button');
    muteBtn.className = 'coster-widget--mute';
    muteBtn.setAttribute('aria-label', muted ? 'Unmute' : 'Mute');
    muteBtn.setAttribute('aria-pressed', String(muted));
    muteBtn.innerHTML = muted ? '&#128263;' : '&#128266;';
    muteBtn.addEventListener('click', function () { setMuted(!muted); });
    header.appendChild(muteBtn);

    if (withClose) {
      var closeBtn = document.createElement('button');
      closeBtn.className = 'coster-widget--close';
      closeBtn.setAttribute('aria-label', 'Tutup');
      closeBtn.innerHTML = '&times;';
      closeBtn.addEventListener('click', close);
      header.appendChild(closeBtn);
    }
    return header;
  }

  function renderHeader() {
    if (!popupEl && !directEl) return;
    var header = buildHeader(mode !== 'direct');
    var container = directEl || popupEl;
    var old = container.querySelector('.coster-widget--header');
    if (old) container.replaceChild(header, old);
    else container.insertBefore(header, container.firstChild);
  }

  function buildWidget() {
    if (mode === 'direct') {
      directEl = document.createElement('div');
      directEl.className = 'coster-widget--direct';
      directEl.appendChild(buildHeader(false));

      bodyEl = document.createElement('div');
      bodyEl.className = 'coster-widget--body';
      footerEl = document.createElement('div');
      footerEl.className = 'coster-widget--composer';

      directEl.appendChild(bodyEl);
      directEl.appendChild(footerEl);
      document.body.appendChild(directEl);

      // Direct Chat opens the conversation directly (full-page) — no launcher.
      state.stage = 'chat';
      renderStage();
      return;
    }

    var pos = s(cfg, 'appearance.web.launcherPosition', 'bottom-right') === 'bottom-left' ? 'left' : 'right';
    var size = clamp(s(cfg, 'appearance.web.launcherSize', 56), 40, 88);
    var bottom = clamp(s(cfg, 'appearance.web.launcherBottom', 24), 8, 80);
    var side = clamp(s(cfg, 'appearance.web.launcherSide', 24), 8, 80);
    var isBar = s(cfg, 'appearance.web.launcherType', 'bubble') === 'bar';
    var hasShadow = s(cfg, 'appearance.web.launcherShadow', true);
    var launcherIcon = s(cfg, 'appearance.web.launcherIcon', '');
    var launcherText = s(cfg, 'appearance.web.launcherText', 'Chat with us');

    launcherEl = document.createElement('button');
    launcherEl.className = 'coster-widget--launcher';
    launcherEl.setAttribute('aria-label', 'Buka livechat');

    var iconHtml = launcherIcon
      ? '<img src="' + escapeAttr(launcherIcon) + '" alt="">'
      : CHAT_ICON;
    launcherEl.innerHTML = iconHtml + (isBar ? '<span class="coster-widget--launcher-text">' + escapeHtml(launcherText) + '</span>' : '');

    launcherEl.style[pos] = side + 'px';
    launcherEl.style.bottom = bottom + 'px';
    launcherEl.style.height = size + 'px';
    launcherEl.style.width = isBar ? Math.max(128, Math.min(210, size * 2.8)) + 'px' : size + 'px';
    launcherEl.style.borderRadius = isBar ? '999px' : '50%';
    launcherEl.style.background = palette.base;
    launcherEl.style.boxShadow = hasShadow ? '0 9px 24px rgba(47, 157, 244, 0.35)' : 'none';

    popupEl = document.createElement('div');
    popupEl.className = 'coster-widget--popup';
    popupEl.setAttribute('role', 'dialog');
    popupEl.setAttribute('aria-label', 'Livechat');
    popupEl.style[pos] = side + 'px';
    popupEl.style.bottom = (bottom + size + 16) + 'px';

    popupEl.appendChild(buildHeader(true));

    bodyEl = document.createElement('div');
    bodyEl.className = 'coster-widget--body';
    footerEl = document.createElement('div');
    footerEl.className = 'coster-widget--composer';
    footerEl.style.display = 'none';

    popupEl.appendChild(bodyEl);
    popupEl.appendChild(footerEl);

    launcherEl.addEventListener('click', toggle);

    document.body.appendChild(launcherEl);
    document.body.appendChild(popupEl);
  }

  function open() {
    requestBrowserPermission();
    setOpen(true);
    renderStage();
    markAllRead();
  }
  function close() { setOpen(false); }
  function toggle() { popupEl.classList.contains('coster-widget--open') ? close() : open(); }

  function setOpen(isOpen) {
    if (mode === 'direct' || !popupEl) return;
    if (isOpen) popupEl.classList.add('coster-widget--open');
    else popupEl.classList.remove('coster-widget--open');
    launcherEl.setAttribute('aria-expanded', String(isOpen));
  }

  // ---------------------------------------------------------------------------
  // Stage rendering
  // ---------------------------------------------------------------------------
  function renderStage() {
    if (!bodyEl) return;
    bodyEl.innerHTML = '';
    footerEl.innerHTML = '';
    footerEl.style.display = (state.stage === 'chat' || mode === 'direct') ? 'flex' : 'none';
    if (mode === 'direct') renderChat();
    else if (state.stage === 'welcome') renderWelcome();
    else if (state.stage === 'prechat') renderPrechat();
    else renderChat();
  }

  function goToStage(stage) {
    state.stage = stage;
    saveJSON(perChannelKey(LS.state), state);
    renderStage();
  }

  function renderWelcome() {
    var welcomeIcon = s(cfg, 'appearance.web.welcomeIcon', '');
    var greetingTitle = s(cfg, 'appearance.web.greetingTitle', 'Hello there!');
    var welcomeMessage = s(cfg, 'appearance.web.welcomeMessage', 'Welcome! How can we help you today?');
    var description = s(cfg, 'appearance.web.description', 'Ask a Question');
    var ctaTextEnabled = s(cfg, 'appearance.web.ctaTextEnabled', true);
    var ctaText = s(cfg, 'appearance.web.ctaText', 'Chat with us');
    var ctaIconData = s(cfg, 'appearance.web.ctaIconData', '');

    var iconHtml = welcomeIcon ? '<img src="' + escapeAttr(welcomeIcon) + '" alt="">' : '&#128075;';

    var card = document.createElement('div');
    card.className = 'coster-widget--welcome';
    card.innerHTML =
      '<div class="coster-widget--welcome-icon">' + iconHtml + '</div>' +
      '<h5>' + escapeHtml(greetingTitle) + '</h5>' +
      '<p>' + escapeHtml(welcomeMessage) + '</p>' +
      '<div class="coster-widget--welcome-desc">' + escapeHtml(description) + '</div>';

    var cta = document.createElement('button');
    cta.className = 'coster-widget--cta';
    var ctaIconHtml = ctaIconData ? '<img src="' + escapeAttr(ctaIconData) + '" alt="">' : (ctaTextEnabled ? '&#128172; ' : '');
    cta.innerHTML = ctaIconHtml + (ctaTextEnabled ? escapeHtml(ctaText) : '');
    cta.addEventListener('click', function () {
      requestBrowserPermission();
      goToStage(s(cfg, 'identification.prechatEnabled', true) ? 'prechat' : 'chat');
    });
    card.appendChild(cta);
    bodyEl.appendChild(card);
  }

  function buildPrechatFields() {
    var standard = [];
    var p = s(cfg, 'identification.prechat', {});
    if (p.name) standard.push({ label: 'Name', type: 'Text', required: true });
    if (p.email) standard.push({ label: 'Email', type: 'Email', required: true });
    if (p.phone) standard.push({ label: 'Phone', type: 'Phone', required: false });
    if (p.company) standard.push({ label: 'Company', type: 'Text', required: false });
    var custom = s(cfg, 'identification.customFields', []).map(function (f) {
      return { label: f.label, type: f.type || 'Text', options: f.options || null, required: !!f.required };
    });
    return standard.concat(custom);
  }

  function fieldInputType(type) {
    type = String(type || 'Text').toLowerCase();
    if (type === 'email') return 'email';
    if (type === 'number') return 'number';
    if (type === 'phone') return 'tel';
    return 'text';
  }

  function renderPrechat() {
    var card = document.createElement('div');
    card.className = 'coster-widget--prechat';
    card.innerHTML = '<div class="coster-widget--sub">' + escapeHtml(s(cfg, 'appearance.web.loginSubtitle', 'Please fill in the details before chatting.')) + '</div>';

    var controls = {};
    buildPrechatFields().forEach(function (f) {
      var type = String(f.type || 'Text').toLowerCase();
      if (type === 'dropdown' && Array.isArray(f.options)) {
        var sel = document.createElement('select');
        sel.className = 'coster-widget--select';
        sel.setAttribute('data-field', f.label);
        sel.innerHTML = '<option value="">' + escapeHtml(f.label) + '</option>' +
          f.options.map(function (o) { return '<option value="' + escapeAttr(o) + '">' + escapeHtml(o) + '</option>'; }).join('');
        card.appendChild(sel);
        controls[f.label] = sel;
      } else if (type === 'checkbox') {
        var label = document.createElement('label');
        label.className = 'coster-widget--check-field';
        var cb = document.createElement('input');
        cb.type = 'checkbox';
        cb.setAttribute('data-field', f.label);
        label.appendChild(cb);
        label.appendChild(document.createTextNode(f.label));
        card.appendChild(label);
        controls[f.label] = cb;
      } else {
        var input = document.createElement('input');
        input.className = 'coster-widget--field';
        input.type = fieldInputType(type);
        input.placeholder = f.label;
        input.value = prechatData[f.label] || '';
        input.setAttribute('data-field', f.label);
        card.appendChild(input);
        controls[f.label] = input;
      }
    });

    var startBtn = document.createElement('button');
    startBtn.className = 'coster-widget--start-btn';
    startBtn.textContent = s(cfg, 'appearance.web.loginButton', 'Start Chat');
    startBtn.addEventListener('click', function () {
      Object.keys(controls).forEach(function (label) {
        var el = controls[label];
        prechatData[label] = el.type === 'checkbox' ? el.checked : el.value.trim();
      });
      saveJSON(perChannelKey(LS.prechat), prechatData);
      sendPrechat();
      goToStage('chat');
    });

    card.appendChild(startBtn);
    bodyEl.appendChild(card);
  }

  // Build the structured profile from pre-chat fields (standard keys are the
  // fixed labels "Name"/"Email"/"Phone"/"Company"; the rest become customFields).
  function collectPrechatProfile() {
    var profile = { name: '', email: '', phone: '', company: '', customFields: {} };
    if (!prechatData) return profile;
    profile.name = prechatData['Name'] || '';
    profile.email = prechatData['Email'] || '';
    profile.phone = prechatData['Phone'] || '';
    profile.company = prechatData['Company'] || '';
    var standard = ['Name', 'Email', 'Phone', 'Company'];
    Object.keys(prechatData).forEach(function (k) {
      if (standard.indexOf(k) === -1 && prechatData[k] != null && prechatData[k] !== '' && prechatData[k] !== false) {
        profile.customFields[k] = prechatData[k];
      }
    });
    return profile;
  }

  function sendPrechat() {
    var p = collectPrechatProfile();
    var hasCustom = Object.keys(p.customFields).length > 0;
    if (!p.name && !p.email && !p.phone && !p.company && !hasCustom) return;
    backendSend({
      type: 'prechat',
      name: p.name,
      email: p.email,
      phone: p.phone,
      company: p.company,
      customFields: hasCustom ? p.customFields : null
    });
  }

  // Message content -> safe HTML.
  function contentHtml(msg) {
    if (msg.kind === 'location' && msg.lat != null && msg.lng != null) {
      var link = 'https://maps.google.com/?q=' + encodeURIComponent(msg.lat + ',' + msg.lng);
      return '&#128205; Location<br><a href="' + link + '" target="_blank" rel="noopener">' + Number(msg.lat).toFixed(5) + ', ' + Number(msg.lng).toFixed(5) + '</a>';
    }
    if (msg.kind === 'image') {
      // Inline preview; click opens the full image in a new tab.
      if (msg.dataUrl) {
        return '<a class="coster-widget--imgwrap" href="' + msg.dataUrl + '" target="_blank" rel="noopener">' +
          '<img class="coster-widget--media" src="' + msg.dataUrl + '" alt="image"></a>';
      }
      return fileChip(msg, '&#128247;');
    }
    if (msg.kind === 'video') return fileChip(msg, '&#127909;');
    if (msg.kind === 'audio') return fileChip(msg, '&#127908;');
    if (msg.kind === 'document') return fileChip(msg, '&#128196;');
    return escapeHtml(msg.text || '');
  }

  function fileChip(msg, icon) {
    var name = escapeHtml(msg.name || 'file');
    var size = formatSize(msg.size);
    var inner = icon +
      ' <span class="coster-widget--file-name">' + name + '</span>' +
      (size ? ' <span class="coster-widget--file-size">(' + size + ')</span>' : '');
    // Download button when the file content (dataUrl) is available.
    var dl = msg.dataUrl
      ? '<a class="coster-widget--file-download" href="' + msg.dataUrl + '" download="' + escapeAttr(msg.name || 'file') + '" title="Download">&#128229;</a>'
      : '';
    return '<div class="coster-widget--file">' + inner + dl + '</div>';
  }

  function statusText(status) {
    if (status === 'Failed') return '<span class="coster-widget--status-badge">!</span>';
    if (status === 'Sending') return '&#128337;';           // clock — still sending
    if (status === 'Read') return '&#10003;&#10003;';        // double blue
    if (status === 'Delivered') return '&#10003;&#10003;';   // double gray
    return '&#10003;';                                       // single gray (sent)
  }

  function applyStatus(el, status, messageId) {
    el.innerHTML = statusText(status);
    el.className = 'coster-widget--msg-status' + (status === 'Read' ? ' is-read' : '');
    el.style.cursor = status === 'Failed' ? 'pointer' : '';
    el.title = status === 'Failed' ? 'Gagal terkirim — klik untuk kirim ulang' : '';
    el.onclick = status === 'Failed' ? function () { retryMessage(messageId); } : null;
  }

  function renderChat() {
    if (!bodyEl) return;

    var csAvatar = s(cfg, 'appearance.web.csAvatar', '');
    var avatarHtml = csAvatar ? '<img src="' + escapeAttr(csAvatar) + '" alt="">' : escapeHtml(CHAT_TEXT.agentInitial);

    var chat = document.createElement('div');
    chat.className = 'coster-widget--chat';

    messages.forEach(function (msg) {
      if (msg.from === 'system') {
        var sys = document.createElement('div');
        sys.className = 'coster-widget--system';
        sys.textContent = msg.text;
        chat.appendChild(sys);
      } else if (msg.from === 'agent') {
        var row = document.createElement('div');
        row.className = 'coster-widget--agent-row';
        var b = document.createElement('div');
        b.className = 'coster-widget--bubble coster-widget--agent-bubble';
        b.style.background = palette.agentBg;
        b.style.color = palette.agentText;
        b.innerHTML = contentHtml(msg);
        row.innerHTML = '<div class="coster-widget--agent-avatar">' + avatarHtml + '</div>';
        row.appendChild(b);
        chat.appendChild(row);
      } else {
        var bubble = document.createElement('div');
        bubble.className = 'coster-widget--bubble coster-widget--customer-bubble';
        bubble.style.background = palette.custBg;
        bubble.style.color = palette.custText;
        bubble.innerHTML = contentHtml(msg);
        chat.appendChild(bubble);

        var status = document.createElement('span');
        status.setAttribute('data-status', msg.id);
        applyStatus(status, msg.status || 'Sent', msg.id);
        chat.appendChild(status);
      }
    });

    bodyEl.appendChild(chat);

    // Composer
    footerEl.innerHTML = '';

    var attachBtn = document.createElement('button');
    attachBtn.className = 'coster-widget--iconbtn';
    attachBtn.setAttribute('aria-label', 'Attach file');
    attachBtn.innerHTML = '&#128206;';
    attachBtn.addEventListener('click', function () { fileInput.click(); });

    var locBtn = document.createElement('button');
    locBtn.className = 'coster-widget--iconbtn';
    locBtn.setAttribute('aria-label', 'Send location');
    locBtn.innerHTML = '&#128205;';
    locBtn.addEventListener('click', sendLocation);

    composerInput = document.createElement('input');
    composerInput.type = 'text';
    composerInput.placeholder = CHAT_TEXT.composerPlaceholder;
    composerInput.addEventListener('keydown', function (e) {
      if (e.key === 'Enter') sendMessage();
    });

    var sendBtn = document.createElement('button');
    sendBtn.className = 'coster-widget--send';
    sendBtn.innerHTML = '&#10148;';
    sendBtn.addEventListener('click', sendMessage);

    footerEl.appendChild(attachBtn);
    footerEl.appendChild(locBtn);
    footerEl.appendChild(composerInput);
    footerEl.appendChild(sendBtn);

    if (mode !== 'direct') composerInput.focus();

    // Auto-scroll to bottom.
    bodyEl.scrollTop = bodyEl.scrollHeight;
  }

  // ---------------------------------------------------------------------------
  // Outbound (customer -> Coster)
  // ---------------------------------------------------------------------------
  function buildPayload(msg) {
    var payload = { type: 'customer_message', messageId: msg.id, kind: msg.kind || 'text' };
    if (msg.kind === 'text') payload.text = msg.text;
    else if (msg.kind === 'location') { payload.lat = msg.lat; payload.lng = msg.lng; }
    else {
      payload.name = msg.name;
      payload.size = msg.size;
      payload.mime = msg.mime;
      if (msg.dataUrl) payload.dataUrl = msg.dataUrl;
    }
    return payload;
  }

  function clearDeliveryTimer(id) {
    if (deliveryTimers[id]) { clearTimeout(deliveryTimers[id]); delete deliveryTimers[id]; }
  }

  function markMessageFailed(messageId) {
    for (var i = 0; i < messages.length; i++) {
      if (messages[i].id === messageId) {
        // Only a message still "Sending" (no server ack) can fail. Once the
        // server accepted it (Sent/Delivered/Read) it is "terkirim".
        if (messages[i].status !== 'Sending') return;
        messages[i].status = 'Failed';
        break;
      }
    }
    saveJSON(perChannelKey(LS.messages), messages);
    var el = document.querySelector('[data-status="' + messageId + '"]');
    if (el) applyStatus(el, 'Failed', messageId);
  }

  // Arm the failure timer and send. Returns the payload (for retry).
  function dispatchCustomerMessage(msg) {
    var payload = buildPayload(msg);
    var ok = backendSend(payload);
    if (!ok) {
      // Offline / not connected — try to (re)connect so the message can go out.
      if (!ws || ws.readyState !== 1) connect();
    }
    deliveryTimers[msg.id] = setTimeout(function () {
      markMessageFailed(msg.id);
    }, ok ? DELIVERY_TIMEOUT : 800);
    return ok;
  }

  function sendCustomerMessage(msg) {
    msg.id = genMessageId();
    msg.from = 'customer';
    msg.status = 'Sending';
    messages.push(msg);
    saveJSON(perChannelKey(LS.messages), messages);
    renderChat();
    dispatchCustomerMessage(msg);
  }

  function retryMessage(messageId) {
    var msg = null;
    for (var i = 0; i < messages.length; i++) {
      if (messages[i].id === messageId) { msg = messages[i]; break; }
    }
    if (!msg || msg.from !== 'customer') return;
    clearDeliveryTimer(messageId);
    msg.status = 'Sending';
    saveJSON(perChannelKey(LS.messages), messages);
    renderChat();
    // Ensure a connection (dispatch re-arms it too) then send immediately.
    if (!wsConnected) connect();
    dispatchCustomerMessage(msg);
  }

  function sendMessage() {
    if (!composerInput) return;
    var text = composerInput.value.trim();
    if (!text) return;
    composerInput.value = '';
    sendCustomerMessage({ kind: 'text', text: text });
  }

  function classifyFile(f) {
    var t = String(f.type || '').toLowerCase();
    var ext = String(f.name || '').split('.').pop().toLowerCase();
    if (t.indexOf('image/') === 0) return 'image';
    if (t.indexOf('video/') === 0) return 'video';
    if (t.indexOf('audio/') === 0) return 'audio';
    // Documents: explicit whitelist, so unsupported files (e.g. .exe) are rejected.
    var docExts = ['pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'csv', 'txt', 'zip'];
    if (docExts.indexOf(ext) !== -1 || t.indexOf('text/') === 0 || t.indexOf('application/pdf') === 0 || t.indexOf('application/zip') === 0) return 'document';
    return null;
  }

  function validateFile(f) {
    var kind = classifyFile(f);
    if (!kind) return { error: 'Tipe file tidak diizinkan: ' + f.name };
    var max = FILE_MAX[kind];
    if (f.size > max) return { error: 'File terlalu besar: ' + f.name + ' (maks ' + formatSize(max) + ')' };
    return { kind: kind };
  }

  function sendLocation() {
    if (!navigator.geolocation) { pushSystem('⚠️ Lokasi tidak didukung di browser ini.'); return; }
    navigator.geolocation.getCurrentPosition(function (pos) {
      sendCustomerMessage({ kind: 'location', lat: pos.coords.latitude, lng: pos.coords.longitude });
    }, function () {
      // EC-22: controlled feedback, conversation continues.
      pushSystem('⚠️ Tidak dapat memperoleh lokasi. Silakan kirim pesan lain.');
    });
  }

  function pushSystem(text) {
    messages.push({ from: 'system', text: text });
    saveJSON(perChannelKey(LS.messages), messages);
    renderChat();
  }

  function updateDeliveryStatus(messageId, status) {
    for (var i = 0; i < messages.length; i++) {
      if (messages[i].id === messageId) {
        messages[i].status = status;
        break;
      }
    }
    if (status === 'Sent' || status === 'Delivered' || status === 'Read') clearDeliveryTimer(messageId);
    saveJSON(perChannelKey(LS.messages), messages);
    var el = document.querySelector('[data-status="' + messageId + '"]');
    if (el) applyStatus(el, status, messageId);
  }

  // ---------------------------------------------------------------------------
  // Visibility (delay / auto-expand)
  // ---------------------------------------------------------------------------
  function applyVisibility() {
    if (mode === 'direct') return;
    if (!pageVisible) { launcherEl.style.display = 'none'; return; }
    var delay = clamp(s(cfg, 'appearance.web.delay', 0), 0, 60);
    var auto = !!s(cfg, 'appearance.web.autoExpand', false);
    if (delay > 0) launcherEl.style.display = 'none';
    setTimeout(function () {
      if (!launcherEl) return;
      launcherEl.style.display = pageVisible ? 'flex' : 'none';
      if (auto && pageVisible) open();
    }, delay * 1000);
  }

  // ---------------------------------------------------------------------------
  // Config fetch + init
  // ---------------------------------------------------------------------------
  function fetchConfig() {
    var url = API_BASE + '/config/' + encodeURIComponent(channelId);
    return fetch(url, { cache: 'no-store' })
      .then(function (r) { if (!r.ok) throw new Error('HTTP ' + r.status); return r.json(); })
      .then(function (data) { return deepMerge(DEFAULTS, data || {}); })
      .catch(function () { return DEFAULTS; });
  }

  function init(opts) {
    opts = opts || {};
    if (opts.channelId) channelId = opts.channelId;
    if (opts.mode) mode = opts.mode;
    if (opts.handoffToken) handoffToken = opts.handoffToken;

    state = loadJSON(perChannelKey(LS.state), { stage: 'welcome' });
    prechatData = loadJSON(perChannelKey(LS.prechat), {});
    messages = loadJSON(perChannelKey(LS.messages), []);
    customerId = opts.customerId || null;
    customerName = opts.customerName || null;

    fetchConfig().then(function (c) {
      cfg = c;
      computePalette();
      if (!pageTargetingPass(c.pageTargeting)) {
        if (opts.onBlocked) opts.onBlocked();
        return; // widget must not render on this domain/page (EC-19)
      }
      injectStyles();
      bindSpaRoutes();
      buildFileInput();
      buildWidget();
      bindInfiniteScroll();
      applyPageTargeting();
      applyVisibility();
      connect();
      // Logged-in / Direct Chat handoff: establish identity via secure token.
      if (handoffToken) identify(handoffToken);
    });
  }

  function buildFileInput() {
    fileInput = document.createElement('input');
    fileInput.type = 'file';
    fileInput.style.display = 'none';
    fileInput.accept = 'image/*,video/*,audio/*,.pdf,.doc,.docx,.xls,.xlsx,.ppt,.pptx,.csv,.txt,.zip';
    fileInput.addEventListener('change', function () {
      var f = fileInput.files && fileInput.files[0];
      fileInput.value = '';
      if (!f) return;

      // WhatsApp-style upload validation (FR-50 / EC error handling).
      var v = validateFile(f);
      if (v.error) { pushSystem('⚠️ ' + v.error); return; }

      var msg = { kind: v.kind, name: f.name, size: f.size, mime: f.type };
      // Embed content (base64) so images can preview and files can download —
      // including after reload / across browsers. Images always; other files
      // only up to DATAURL_MAX (larger files send metadata only).
      var wantDataUrl = v.kind === 'image' || f.size <= DATAURL_MAX;
      if (wantDataUrl) {
        var fr = new FileReader();
        fr.onload = function () { msg.dataUrl = fr.result; sendCustomerMessage(msg); };
        fr.onerror = function () { sendCustomerMessage(msg); };
        fr.readAsDataURL(f);
      } else {
        sendCustomerMessage(msg);
      }
    });
    document.body.appendChild(fileInput);
  }

  // ---------------------------------------------------------------------------
  // Public API (CosterLiveChat) — supports async command queue
  // ---------------------------------------------------------------------------
  function identify(token) {
    if (!token) return;
    handoffToken = token;
    // identity must be verified by the backend; never trust a browser value (FR-30/31).
    if (wsConnected) backendSend({ type: 'identify', token: token });
  }

  function setMuted(val) {
    muted = !!val;
    saveJSON(LS.muted, muted);
    // Reflect state on any open header toggle (FR-58).
    var btns = document.querySelectorAll('.coster-widget--mute');
    for (var i = 0; i < btns.length; i++) {
      btns[i].setAttribute('aria-label', muted ? 'Unmute' : 'Mute');
      btns[i].setAttribute('aria-pressed', String(muted));
      btns[i].innerHTML = muted ? '&#128263;' : '&#128266;';
    }
    // Best-effort sync to backend (dummy logs only; preference is browser-scoped).
    if (wsConnected) backendSend({ type: 'mute', muted: muted });
  }

  var api = {
    init: init,
    identify: identify,
    open: open,
    close: close,
    mute: function () { setMuted(true); },
    unmute: function () { setMuted(false); },
    version: '0.2.0'
  };

  var prior = window.CosterLiveChat;
  window.CosterLiveChat = api;
  if (Array.isArray(prior)) {
    prior.forEach(function (cmd) {
      if (typeof api[cmd[0]] === 'function') api[cmd[0]].apply(api, cmd.slice(1));
    });
  }

  // ---------------------------------------------------------------------------
  // Auto-init from the script tag / Direct Chat URL
  // ---------------------------------------------------------------------------
  function isDirectUrl() {
    return (getQueryParam('h') !== null) || window.location.pathname.indexOf('/chat/') === 0;
  }

  function autoInit() {
    var cid = getScriptAttribute('data-channel-id');
    var m = getScriptAttribute('data-mode') || (isDirectUrl() ? 'direct' : 'widget');
    var h = getQueryParam('h');
    if (!cid) {
      var pm = (window.location.pathname.match(/\/chat\/([A-Za-z0-9_-]+)/) || [])[1];
      if (pm) { cid = pm; m = 'direct'; }
    }
    if (!cid) return;
    init({ channelId: cid, mode: m, handoffToken: h || undefined });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', autoInit);
  } else {
    autoInit();
  }

  // Re-send Read when the tab becomes visible again (Read-before-Delivered allowed).
  document.addEventListener('visibilitychange', function () {
    if (document.visibilityState === 'visible') markAllRead();
  });
})();
