#!/usr/bin/env python3
"""Link every elaborated identifier in the Lean code to its declaration.

Uses verification/lean-references/references.json, which records Lean's own
.ilean reference data (see extract-lean-references.py); no name is resolved
lexically. Every bundled source page is re-rendered from its own source lines
with syntax highlighting, links and rendered doc comments (KaTeX); so are the Lean blocks
`<pre class="lean-src" data-src="formal:FILE" data-line="N">` of the top-level
pages. Project and library declarations open their bundled page, Mathlib and
Lean core declarations their pinned GitHub source. Hovering or focusing a link
shows the declaration's doc comment and signature, embedded in the page so it
works offline. The script is idempotent.
"""
import html, json, os, re, sys

from common import PAGES, REFS, ROOT
import leanhl

TOP_PAGES = ['index.html', 'lean-dag.html', 'verification/index.html']


def load():
    data = json.loads(REFS.read_text())
    by_line = {}
    for key, spans in data['files'].items():
        lines = by_line[key] = {}
        for line, col, length, target in spans:
            lines.setdefault(line, []).append((col, length, target))
    return data, by_line


def href(data, target, here):
    name, repo, path, line = data['targets'][target]
    if repo in PAGES:
        rel = os.path.relpath(ROOT / PAGES[repo] / (path + '.html'), here)
        return f'{rel if rel.startswith(".") else "./" + rel}#L{line}'
    return f'{data["urls"][repo]}{path}#L{line}'


def link_tags(data, text, spans, here):
    """(col, length, opening tag) of the recorded references of one line."""
    out, pos = [], 0
    for col, length, target in sorted(spans):
        if col < pos or col + length > len(text):
            continue
        name = data['targets'][target][0]
        # The preview replaces the native tooltip; without one, keep the name as title.
        hint = (f'data-p="{target}" aria-label="{html.escape(name)}"' if str(target) in data['previews']
                else f'title="{html.escape(name)}"')
        out.append((col, length, f'<a class="ref" href="{html.escape(href(data, target, here))}" {hint}>'))
        pos = col + length
    return out


PREVIEW_CSS = (
    '.lean-preview{position:fixed;z-index:9999;display:none;max-width:min(680px,calc(100vw - 16px));'
    'background:var(--card,#fffef8);color:var(--fg,#1d1d1f);border:1px solid var(--line,#c9c5bb);border-radius:6px;'
    'box-shadow:0 6px 24px rgba(0,0,0,.18);padding:6px 9px;font:12px/1.45 ui-monospace,Menlo,Consolas,monospace;'
    'pointer-events:none;text-align:left}'
    '.lean-preview .lp-head{font-weight:600;overflow-wrap:anywhere}'
    '.lean-preview .lp-loc{color:var(--mute,#6b6b6b);font-size:11px;overflow-wrap:anywhere}'
    '.lean-preview .lp-doc{font:13px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif;margin:5px 0 0;'
    'padding-left:8px;border-left:2px solid var(--line,#c9c5bb)}.lean-preview .lp-doc p{margin:.2em 0}'
    '.lean-preview .lp-doc ul,.lean-preview .lp-doc ol{margin:.2em 0;padding-left:1.2em}'
    '.lean-preview .lp-doc h3,.lean-preview .lp-doc h4{font-size:1em;margin:.2em 0}'
    '.lean-preview .lp-doc code{font:12px ui-monospace,Menlo,Consolas,monospace}.lean-preview math{font-size:1.08em}'
    '.lean-preview pre{margin:5px 0 0;white-space:pre-wrap;overflow-wrap:anywhere;max-height:50vh;'
    'overflow:hidden;font:inherit;background:none;border:0;padding:0}')
PREVIEW_JS = r"""(()=>{
const data=JSON.parse(document.getElementById('lean-previews').textContent);
const box=document.createElement('div');box.className='lean-preview';box.setAttribute('role','tooltip');
document.body.append(box);let timer;
function add(cls,text){const e=document.createElement(cls==='pre'?'pre':'div');if(cls!=='pre')e.className=cls;e.textContent=text;box.append(e);return e;}
function show(a){
  const d=data[a.dataset.p];if(!d)return;const [head,loc,body,doc]=d;
  box.replaceChildren();add('lp-head',head);add('lp-loc',loc);if(doc)add('lp-doc','').innerHTML=doc;add('pre',body);
  box.style.display='block';const r=a.getBoundingClientRect(),w=box.offsetWidth,h=box.offsetHeight;
  box.style.left=Math.max(8,Math.min(r.left,innerWidth-w-8))+'px';
  box.style.top=(r.bottom+6+h<innerHeight?r.bottom+6:Math.max(8,r.top-h-6))+'px';}
function hide(){clearTimeout(timer);box.style.display='none';}
const pick=e=>e.target.closest&&e.target.closest('a[data-p]');
document.addEventListener('mouseover',e=>{const a=pick(e);clearTimeout(timer);if(a)timer=setTimeout(()=>show(a),150);else hide();});
document.addEventListener('focusin',e=>{const a=pick(e);if(a)show(a);else hide();});
document.addEventListener('focusout',hide);document.addEventListener('scroll',hide,true);
document.addEventListener('keydown',e=>{if(e.key==='Escape')hide();});
})();"""
BEGIN, END = '<!--lean-previews-->', '<!--/lean-previews-->'


def embed_previews(data, text):
    """Embed the previews of the declarations this page links, before </body>."""
    text = re.sub(re.escape(BEGIN) + '.*?' + re.escape(END), '', text, flags=re.S)
    ids = sorted(set(re.findall(r'data-p="(\d+)"', text)), key=int)
    if not ids:
        return text
    def location(target):
        name, repo, path, line = data['targets'][target]
        return f'{path}:{line}' + ('' if repo in PAGES else f' · {repo}')
    payload = json.dumps({i: [data['targets'][int(i)][0], location(int(i)), *data['rendered'][i]] for i in ids},
                         ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')
    block = (f'{BEGIN}<style>{PREVIEW_CSS}</style><script type="application/json" id="lean-previews">'
             f'{payload}</script><script>{PREVIEW_JS}</script>{END}')
    head, sep, tail = text.rpartition('</body>')
    return head + block + sep + tail if sep else text + block


def link_page(data, by_line, repo, page, math):
    rel = str(page.relative_to(ROOT / PAGES[repo]))[:-len('.html')]
    spans = by_line.get(f'{repo}:{rel}')
    if spans is None:
        return 0, None
    text = page.read_text()
    lines = leanhl.parse_page(text)
    links = {n: link_tags(data, lines[n - 1], found, page.parent) for n, found in spans.items() if n <= len(lines)}
    head, _, rest = text.partition(leanhl.BEGIN)
    _, _, tail = rest.partition(leanhl.END)
    # Style and script follow the current renderer, not the extraction run.
    head = re.sub(r'<style>.*?</style>', lambda _: f'<style>{leanhl.PAGE_CSS}</style>', head, count=1, flags=re.S)
    tail = re.sub(r'</main><script>.*?</script>', lambda _: f'</main><script>{leanhl.PAGE_JS}</script>', tail,
                  count=1, flags=re.S)
    body = leanhl.code(lines, links, math)
    return sum(map(len, links.values())), (head, body, tail)


BLOCK = re.compile(r'<pre class="(lean-src[^"]*)" data-src="([^"]+)" data-line="(\d+)">(.*?)</pre>', re.S)


def link_top(data, by_line, page, stats):
    text = page.read_text()
    cache = {}
    def block(m):
        cls, key, start, body = m[1], m[2], int(m[3]), leanhl.plain(m[4])
        spans = by_line.get(key, {})
        repo, rel = key.split(':', 1)
        if key not in cache:
            source = ROOT / PAGES[repo] / (rel + '.html')
            cache[key] = leanhl.parse_page(source.read_text()) if source.exists() else None
        lines = cache[key]
        rows = body.split('\n')
        # A statement block may stop inside its last line (before `:=`).
        src = lines[start - 1:start - 1 + len(rows)] if lines else []
        if len(src) != len(rows) or src[:-1] != rows[:-1] or not src[-1].startswith(rows[-1]):
            stats['unmatched'].append(f'{page.relative_to(ROOT)}: {key}#L{start}')
            return m[0]
        stats['blocks'] += 1
        colours = leanhl.tokenize(rows)
        out = []
        for i, row in enumerate(rows):
            found = link_tags(data, row, spans.get(start + i, []), page.parent)
            stats['linked'] += len(found)
            out.append(leanhl.render_line(row, colours[i], found))
        return f'<pre class="{cls}" data-src="{key}" data-line="{start}">' + '\n'.join(out) + '</pre>'
    text = BLOCK.sub(block, text)
    page.write_text(embed_previews(data, text))


def render_previews(data):
    """Doc comments of the hover previews as Markdown with MathML formulas: {id: [body, doc html]}."""
    math, ids, docs, bodies = leanhl.Math('mathml'), [], [], []
    for i, text in data['previews'].items():
        doc, body = leanhl.split_doc(text)
        ids.append(i)
        bodies.append(body)
        docs.append(leanhl.markdown(doc, math) if doc else '')
    data['rendered'] = dict(zip(ids, zip(bodies, math.fill(docs))))


def main():
    data, by_line = load()
    render_previews(data)
    stats = dict(linked=0, blocks=0, unmatched=[])
    for name in TOP_PAGES:
        if (ROOT / name).exists():
            link_top(data, by_line, ROOT / name, stats)
    pages = refs = 0
    math, rendered = leanhl.Math(), []
    for repo, base in PAGES.items():
        for page in sorted((ROOT / base).rglob('*.lean.html')):
            n, parts = link_page(data, by_line, repo, page, math)
            if parts:
                rendered.append((page, parts))
            refs += n
            pages += 1
    bodies = math.fill([parts[1] for _, parts in rendered])
    for (page, (head, _, tail)), body in zip(rendered, bodies):
        page.write_text(embed_previews(data, head + leanhl.BEGIN + body + leanhl.END + tail))
    print(f'{len(math.items)} doc-comment formulas rendered with KaTeX.')
    print(f'{stats["linked"]} links in {stats["blocks"]} Lean blocks of the top pages; '
          f'{refs} links in {pages} source pages.')
    if stats['unmatched']:
        sys.exit('Lean blocks differing from their source lines: ' + ', '.join(stats['unmatched']))


if __name__ == '__main__':
    main()
