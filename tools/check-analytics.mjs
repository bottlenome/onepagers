import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const read = (file) => fs.readFileSync(path.join(root, file), 'utf8');
const projects = ['counter', 'rainbow-reversi', 'browser-rpg', 'sakurai-methodology',
  'teichmuller', 'verify-teichmuller-errors', 'iut-lean-verification', 'learn-ddd',
  'llm-architecture', 'nback-training', 'windvale'];
const included = ['index.html', ...projects.map(p => `${p}/index.html`),
  'iut-lean-verification/report.html'];
let checks = 0;
for (const file of included) {
  const html = read(file);
  assert.equal((html.match(/<script defer src="(?:\.\/|\.\.\/)analytics\.js"><\/script>/g) || []).length, 1, file);
  assert.equal((html.match(/data-onepagers-privacy/g) || []).length, 1, file);
  assert.ok(!html.includes('static.cloudflareinsights.com'), `Use the scoped loader: ${file}`);
  assert.match(html, /href="(?:\.\/|\.\.\/)privacy\.html"/);
  checks++;
}
for (const file of ['open-chatbot/index.html', 'bonsai-chat/index.html', 'privacy.html']) {
  const html = read(file);
  assert.ok(!/analytics\.js|data-cf-beacon|static\.cloudflareinsights\.com/.test(html), file);
  checks++;
}
for (const file of ['browser-rpg/build.sh', 'verify-teichmuller-errors/src/template.html']) {
  assert.equal((read(file).match(/src="\.\.\/analytics\.js"/g) || []).length, 1, file);
  checks++;
}
const source = read('analytics.js');
const token = source.match(/const SITE_TOKEN = '([^']*)';/)?.[1];
assert.notEqual(token, undefined, 'Site token declaration exists');
if (process.argv.includes('--release')) {
  assert.match(token, /^[a-f0-9]{32}$/, 'Release needs the real dashboard-issued public site token');
}
function run({ pathname = '/onepagers/', hostname = 'bottlenome.github.io', protocol = 'https:', embedded = false, duplicate = false, configured = true, repeat = false } = {}) {
  const appended = [];
  const window = {};
  window.self = window;
  window.top = embedded ? {} : window;
  const context = vm.createContext({
    window,
    location: { pathname, hostname, protocol, search: '?private=must-not-be-read', hash: '#private' },
    document: {
      querySelector(selector) { assert.equal(selector, 'script[data-cf-beacon]'); return duplicate || appended.length ? {} : null; },
      createElement(tag) { assert.equal(tag, 'script'); return { dataset: {} }; },
      body: { appendChild(element) { appended.push(element); } },
    },
  });
  // Test-only token stays in this VM; never replace the source file or send requests.
  const testSource = source.replace(/const SITE_TOKEN = '[^']*';/, `const SITE_TOKEN = '${configured ? '1234567890abcdef1234567890abcdef' : ''}';`);
  vm.runInContext(testSource, context);
  if (repeat) vm.runInContext(testSource, context);
  return appended;
}
for (const file of included) {
  const elements = run({ pathname: `/onepagers/${file}`, repeat: true });
  assert.equal(elements.length, 1, file);
  assert.equal(elements[0].src, 'https://static.cloudflareinsights.com/beacon.min.js');
  assert.equal(elements[0].type, 'module');
  assert.equal(elements[0].referrerPolicy, 'strict-origin');
  assert.deepEqual(JSON.parse(elements[0].dataset.cfBeacon), { token: '1234567890abcdef1234567890abcdef', spa: false });
  checks++;
}
for (const p of ['', ...projects.map(p => `${p}/`)]) {
  assert.equal(run({ pathname: `/onepagers/${p}` }).length, 1, p);
  checks++;
}
for (const options of [
  { configured: false }, { embedded: true }, { duplicate: true },
  { hostname: 'localhost' }, { hostname: 'preview.example.com' },
  { hostname: 'bottlenome.github.io.attacker.example' }, { protocol: 'file:' }, { protocol: 'http:' },
  ...['/', '/other/', '/onepagers-copy/', '/onepagers/privacy.html', '/onepagers/open-chatbot/',
    '/onepagers/open-chatbot/index.html', '/onepagers/bonsai-chat/', '/onepagers/bonsai-chat/index.html',
    '/onepagers/unapproved/index.html', '/onepagers/counter/private.html'].map(pathname => ({ pathname })),
]) {
  assert.equal(run(options).length, 0, JSON.stringify(options));
  checks++;
}
console.log(`Analytics checks passed: ${checks}. Production token: ${token ? 'configured' : 'NOT configured (inactive preparation)'}.`);
