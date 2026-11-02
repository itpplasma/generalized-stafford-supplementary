// Browser checks of the generated pages using Chrome's pipe protocol; no npm dependency.
// Usage: node scripts/check-site.mjs [SITE_DIR] [OUTPUT_DIR]   (CHROMIUM_PATH selects the browser)
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawn} from 'node:child_process';
import {pathToFileURL} from 'node:url';

const root = path.resolve(process.argv[2] ?? path.join(import.meta.dirname, '..'));
const output = path.resolve(process.argv[3] ?? fs.mkdtempSync(path.join(os.tmpdir(), 'site-check-')));
const chrome = process.env.CHROMIUM_PATH ?? ['/usr/bin/chromium', '/usr/bin/google-chrome-stable',
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'].find(p => fs.existsSync(p));
const profile = fs.mkdtempSync(path.join(os.tmpdir(), 'site-check-profile-'));
const browser = spawn(chrome, ['--headless', '--no-sandbox', '--disable-gpu',
  '--disable-background-networking', '--no-first-run', '--no-default-browser-check',
  '--user-data-dir=' + profile, '--remote-debugging-pipe'],
  {stdio: ['ignore', 'ignore', 'pipe', 'pipe', 'pipe']});
let nextId = 0, buffer = '', diagnostics = '';
const pending = new Map(), errors = [], external = [];
browser.stderr.on('data', b => { diagnostics += b; });
browser.stdio[4].on('data', b => {
  buffer += b;
  for (let end; (end = buffer.indexOf('\0')) >= 0;) {
    const text = buffer.slice(0, end); buffer = buffer.slice(end + 1);
    if (!text) continue;
    const message = JSON.parse(text);
    if (message.id && pending.has(message.id)) {
      const p = pending.get(message.id); pending.delete(message.id); clearTimeout(p.timer);
      message.error ? p.reject(Error(JSON.stringify(message.error))) : p.resolve(message.result);
    } else if (message.method === 'Runtime.exceptionThrown') {
      errors.push(message.params.exceptionDetails.exception?.description ?? message.params.exceptionDetails.text);
    } else if (message.method === 'Network.requestWillBeSent' && /^https?:/.test(message.params.request.url)) {
      external.push(message.params.request.url);
    }
  }
});
function send(method, params = {}, sessionId) {
  return new Promise((resolve, reject) => {
    const id = ++nextId;
    const timer = setTimeout(() => { pending.delete(id); reject(Error('CDP timeout: ' + method)); }, 30000);
    pending.set(id, {resolve, reject, timer});
    browser.stdio[3].write(JSON.stringify({id, method, params, ...(sessionId ? {sessionId} : {})}) + '\0');
  });
}
browser.on('exit', (code, signal) => {
  for (const p of pending.values()) { clearTimeout(p.timer); p.reject(Error(`Chrome exited ${code}/${signal}: ${diagnostics.slice(-1000)}`)); }
  pending.clear();
});
let session;
async function evaluate(expression) {
  const r = await send('Runtime.evaluate', {expression, returnByValue: true, awaitPromise: true}, session);
  if (r.exceptionDetails) throw Error(JSON.stringify(r.exceptionDetails));
  return r.result.value;
}
const loaded = () => evaluate(`new Promise(resolve => { const done = () => setTimeout(resolve, 150); if (document.readyState === 'complete') done(); else addEventListener('load', done, {once:true}); })`);
async function open(file, width = 1440, height = 1000, mobile = false) {
  await send('Emulation.setDeviceMetricsOverride', {width, height, deviceScaleFactor: 1, mobile}, session);
  const [name, hash] = file.split('#');
  await send('Page.navigate', {url: pathToFileURL(path.join(root, name)).href + (hash ? '#' + hash : '')}, session);
  await loaded();
}
async function shot(name, full = false) {
  const params = {format: 'png'};
  if (full) {
    const m = await send('Page.getLayoutMetrics', {}, session);
    params.clip = {x: 0, y: 0, width: m.cssContentSize.width, height: Math.min(m.cssContentSize.height, 6000), scale: 1};
    params.captureBeyondViewport = true;
  }
  const r = await send('Page.captureScreenshot', params, session);
  fs.writeFileSync(path.join(output, name), Buffer.from(r.data, 'base64'));
}
// Every local link of a page resolves to a file and, with a hash, to an id in it.
async function checkLinks(file) {
  const links = await evaluate(`[...new Set([...document.querySelectorAll('a[href]')].map(a => a.getAttribute('href')))]`);
  const local = links.filter(h => !/^[a-z]+:/.test(h));
  for (const href of local) {
    const [target, anchor] = href.split('#');
    const resolved = target ? path.resolve(path.dirname(path.join(root, file)), target) : path.join(root, file);
    assert.ok(fs.existsSync(resolved), `${file}: missing ${href}`);
    if (anchor && resolved.endsWith('.html')) {
      const text = fs.readFileSync(resolved, 'utf8');
      assert.ok(text.includes(`id="${decodeURIComponent(anchor)}"`), `${file}: missing anchor ${href}`);
    }
  }
  const previews = await evaluate(`(() => { const d = JSON.parse(document.getElementById('lean-previews')?.textContent ?? '{}');
    return [...document.querySelectorAll('a[data-p]')].filter(a => !d[a.dataset.p]).length; })()`);
  assert.equal(previews, 0, `${file}: links without preview data`);
  return local.length;
}
const receipt = {pages: {}};
try {
  fs.mkdirSync(output, {recursive: true});
  const target = await send('Target.createTarget', {url: 'about:blank'});
  ({sessionId: session} = await send('Target.attachToTarget', {targetId: target.targetId, flatten: true}));
  for (const name of ['Page', 'Runtime', 'Network']) await send(name + '.enable', {}, session);

  await open('index.html');
  receipt.pages['index.html'] = {local_links: await checkLinks('index.html')};
  // First screen: title, status line and the proof-structure graph; nothing starts open.
  const first = await evaluate(`(() => { const vis = e => e && e.getBoundingClientRect().bottom <= innerHeight;
    return {title: vis(document.querySelector('header.hero h1')), status: vis(document.querySelector('.status')),
      graph: vis(document.querySelector('.overview-graph .lr svg')),
      open_details: document.querySelectorAll('main details[open]').length}; })()`);
  receipt.first_screen = first;
  assert.deepEqual(first, {title: true, status: true, graph: true, open_details: 0});
  await shot('index-desktop.png');
  // One card per numbered environment (items of an unmapped environment get their own);
  // every mapped card shows a Lean statement without a click.
  const map = fs.readFileSync(path.join(root, 'verification/paper/statement-map.yaml'), 'utf8');
  const mapped = new Set([...map.matchAll(/^  - label: (\S+)/gm)].map(m => m[1]));
  const paper = JSON.parse(fs.readFileSync(path.join(root, 'verification/paper/paper.json'), 'utf8'));
  const cards = paper.envs.filter(e => e.label).flatMap(e => e.items.length && !mapped.has(e.label)
    ? e.items.map(i => i.label) : [e.label]);
  const shown = await evaluate(`[...document.querySelectorAll('article.card')].map(c => [c.id.slice(6),
    !!c.querySelector('.lean > .stmt-lean > pre.lean-src'), c.classList.contains('def')])`);
  assert.deepEqual(shown.map(x => x[0]).sort(), [...cards].sort());
  receipt.cards = shown.length;
  for (const [label, visible, def] of shown) assert.ok(def || !mapped.has(label) || visible, `no visible Lean statement: ${label}`);
  // Every compared theorem appears with its statement.
  const record = JSON.parse(fs.readFileSync(path.join(root, 'verification/record.json'), 'utf8'));
  const leanText = await evaluate(`[...document.querySelectorAll('.lean > .stmt-lean > pre.lean-src')].map(p => p.textContent).join('\\n')`);
  for (const name of record.comparator.theorem_names) {
    assert.ok(leanText.includes('theorem ' + name.split('.').pop() + ' '), `compared theorem not shown: ${name}`);
  }
  receipt.known_cards = await evaluate(`document.querySelectorAll('#known article.card').length`);
  assert.equal(receipt.known_cards, (map.match(/^    cite:/gm) || []).length);
  receipt.step_rows = await evaluate(`document.querySelectorAll('#structure details.step').length`);
  assert.equal(receipt.step_rows, Object.keys(paper.steps).length);
  assert.equal(await evaluate(`document.querySelectorAll('.katex-error').length`), 0);
  // An opened lemma: its card is the target, with the variables in scope opened.
  await evaluate(`location.hash = 'paper-lem:central'`);
  await evaluate(`new Promise(r => setTimeout(r, 150))`);
  await evaluate(`(() => { document.querySelector('[id="paper-lem:central"] details.vars').open = true; })()`);
  await evaluate(`document.querySelector('[id="paper-lem:central"] a[data-p]').focus()`);
  assert.equal(await evaluate(`getComputedStyle(document.querySelector('.lean-preview')).display`), 'block');
  await shot('index-lemma-open.png');
  await evaluate(`document.activeElement.blur(); location.hash = 'step-descent-step'`);
  await evaluate(`new Promise(r => setTimeout(r, 150))`);
  assert.equal(await evaluate(`document.getElementById('step-descent-step').open`), true);
  await shot('index-descent-step.png');
  await send('Emulation.setEmulatedMedia', {features: [{name: 'prefers-color-scheme', value: 'dark'}]}, session);
  await open('index.html');
  await evaluate(`document.getElementById('results').scrollIntoView()`);
  await shot('index-dark.png');
  await send('Emulation.setEmulatedMedia', {features: [{name: 'prefers-color-scheme', value: 'light'}]}, session);
  await open('index.html', 390, 844, true);
  assert.equal(await evaluate('document.documentElement.scrollWidth > innerWidth + 1'), false, 'index.html overflows at phone width');
  await shot('index-phone.png');
  await evaluate(`location.hash = 'paper-lem:schur'`);
  await evaluate(`new Promise(r => setTimeout(r, 150))`);
  await shot('index-phone-lemma.png');

  await open('lean-dag.html');
  receipt.pages['lean-dag.html'] = {local_links: await checkLinks('lean-dag.html'),
    open_details: await evaluate(`document.querySelectorAll('main details[open]').length`)};
  assert.equal(receipt.pages['lean-dag.html'].open_details, 0);
  await shot('lean-dag-desktop.png');
  await evaluate(`location.hash = 'key-step:descent'`);
  await evaluate(`new Promise(r => setTimeout(r, 100))`);
  assert.equal(await evaluate(`document.getElementById('key-step:descent').open`), true);
  await shot('lean-dag-descent.png');
  await open('lean-dag.html', 390, 844, true);
  assert.equal(await evaluate('document.documentElement.scrollWidth > innerWidth + 1'), false, 'lean-dag.html overflows at phone width');
  await shot('lean-dag-phone.png');

  await open('verification/index.html');
  receipt.pages['verification/index.html'] = {local_links: await checkLinks('verification/index.html')};
  await shot('verification-desktop.png');
  await open('verification/index.html', 390, 844, true);
  assert.equal(await evaluate('document.documentElement.scrollWidth > innerWidth + 1'), false, 'verification overflows at phone width');

  // Source pages: highlighted Lean, rendered doc comments, single line spacing, marked target line.
  const source = 'sources/formal/GeneralizedStafford/Germs.lean.html';
  for (const scheme of ['light', 'dark']) {
    await send('Emulation.setEmulatedMedia', {features: [{name: 'prefers-color-scheme', value: scheme}]}, session);
    await open(source + '#L107');
    const page = await evaluate(`(() => { const rows = [...document.querySelectorAll('.src > .l')].slice(0, 60);
      const steps = rows.slice(1).filter((r, i) => +r.dataset.n === +rows[i].dataset.n + 1 && !rows[i].classList.contains('raw'))
        .map(r => r.getBoundingClientRect().top - r.previousElementSibling.getBoundingClientRect().top).sort((a, b) => a - b);
      const lh = parseFloat(getComputedStyle(rows[0]).lineHeight);
      const hit = document.querySelector('.hit'), r = hit && hit.getBoundingClientRect();
      return {keywords: document.querySelectorAll('.src .kw').length, doc_math: document.querySelectorAll('.doc .katex').length,
        line_step: steps[steps.length >> 1] / lh, marked: !!hit && r.top >= 0 && r.bottom <= innerHeight}; })()`);
    receipt.pages[source] = page;
    assert.ok(page.keywords > 50 && page.doc_math > 10, 'source page lacks highlighting or rendered doc math');
    assert.ok(Math.abs(page.line_step - 1) < 0.05, `source lines are not single-spaced: ${page.line_step}`);
    assert.ok(page.marked, 'target line is not marked on screen');
    await shot(`source-germs-L107-${scheme}.png`);
  }
  await send('Emulation.setEmulatedMedia', {features: [{name: 'prefers-color-scheme', value: 'light'}]}, session);
  receipt.pages[source].local_links = await checkLinks(source);
  await open('sources/formal/GeneralizedStafford/TheoremA.lean.html');
  await shot('source-theoremA.png');
  await open(source, 390, 844, true);
  assert.equal(await evaluate('document.documentElement.scrollWidth > innerWidth + 1'), false, 'source page overflows at phone width');
  await shot('source-germs-phone.png');

  assert.deepEqual(errors, []);
  assert.deepEqual(external, []);
  Object.assign(receipt, {status: 'passed', javascript_errors: errors.length, offline_requests: external.length,
    phone_overflow: false, screenshots: output});
  console.log(JSON.stringify(receipt, null, 1));
} finally {
  try { await send('Browser.close'); } catch {}
  browser.kill();
}
