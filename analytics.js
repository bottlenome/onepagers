/* Cloudflare Web Analytics for the public OnePagers site only.
 * The site token is a public beacon identifier, not an API credential.
 * See privacy.html and docs/tasks/web-analytics.md for scope and verification.
 */
(() => {
  'use strict';
  const SITE_TOKEN = '33b09d18ddc04bef8e483ecc8a2316b4';
  const BASE = '/onepagers/';
  const pages = new Set([
    '', 'index.html',
    'counter/', 'counter/index.html',
    'rainbow-reversi/', 'rainbow-reversi/index.html',
    'browser-rpg/', 'browser-rpg/index.html',
    'sakurai-methodology/', 'sakurai-methodology/index.html',
    'teichmuller/', 'teichmuller/index.html',
    'verify-teichmuller-errors/', 'verify-teichmuller-errors/index.html',
    'iut-lean-verification/', 'iut-lean-verification/index.html',
    'iut-lean-verification/report.html',
    'learn-ddd/', 'learn-ddd/index.html',
    'llm-architecture/', 'llm-architecture/index.html',
    'nback-training/', 'nback-training/index.html',
    'windvale/', 'windvale/index.html',
  ]);

  // Fail closed until a real site token is configured. Local copies, previews,
  // unlisted pages, and embedded reports must not send analytics.
  if (!/^[a-f0-9]{32}$/.test(SITE_TOKEN)
      || location.protocol !== 'https:'
      || location.hostname !== 'bottlenome.github.io'
      || !location.pathname.startsWith(BASE)
      || !pages.has(location.pathname.slice(BASE.length))
      || window.self !== window.top
      || document.querySelector('script[data-cf-beacon]')) return;

  const beacon = document.createElement('script');
  beacon.type = 'module';
  beacon.src = 'https://static.cloudflareinsights.com/beacon.min.js';
  beacon.referrerPolicy = 'strict-origin';
  // Static documents: do not treat in-page UI changes as additional page views.
  beacon.dataset.cfBeacon = JSON.stringify({ token: SITE_TOKEN, spa: false });
  document.body.appendChild(beacon);
})();
