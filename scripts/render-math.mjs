// Render TeX math to static HTML with KaTeX, in one batch.
// Usage: node scripts/render-math.mjs KATEX_DIR < {"macros": {...}, "items": [{"tex": "...", "display": false}]}
// Writes a JSON list of HTML strings; a formula KaTeX rejects is an error.
import fs from 'node:fs';
import path from 'node:path';
import {createRequire} from 'node:module';

const katex = createRequire(import.meta.url)(path.resolve(process.argv[2]));
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
const out = input.items.map(({tex, display}) => katex.renderToString(tex, {
  displayMode: display, macros: {...input.macros}, throwOnError: true, strict: 'ignore', output: 'html'}));
process.stdout.write(JSON.stringify({version: katex.version, html: out}));
