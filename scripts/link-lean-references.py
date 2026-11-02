#!/usr/bin/env python3
"""Link every elaborated identifier in the Lean code to its declaration.

Uses verification/lean-references/references.json, which records Lean's own
.ilean reference data (see extract-lean-references.py); no name is resolved
lexically. Links are added to every bundled source page and to the Lean blocks
`<pre class="lean-src" data-src="formal:FILE" data-line="N">` of the top-level
pages. Project and library declarations open their bundled page, Mathlib and
Lean core declarations their pinned GitHub source. Hovering or focusing a link
shows the declaration's doc comment and signature, embedded in the page so it
works offline. The script is idempotent.
"""
import html, json, os, re, sys

from common import PAGES, REFS, ROOT

PAGE_CSS = 'a.ref{color:inherit;text-decoration:underline dotted;text-underline-offset:2px}a.ref:hover{text-decoration-style:solid}'
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


def link_text(data, text, spans, here, cls):
    """Escape one line of source text and wrap the recorded references."""
    out, pos = [], 0
    for col, length, target in sorted(spans):
        if col < pos or col + length > len(text):
            continue
        name = data['targets'][target][0]
        # The preview replaces the native tooltip; without one, keep the name as title.
        hint = (f'data-p="{target}" aria-label="{html.escape(name)}"' if str(target) in data['previews']
                else f'title="{html.escape(name)}"')
        out.append(html.escape(text[pos:col], quote=False))
        out.append(f'<a class="{cls}" href="{html.escape(href(data, target, here))}" '
                   f'{hint}>{html.escape(text[col:col + length], quote=False)}</a>')
        pos = col + length
    out.append(html.escape(text[pos:], quote=False))
    return ''.join(out)


PREVIEW_CSS = (
    '.lean-preview{position:fixed;z-index:9999;display:none;max-width:min(680px,calc(100vw - 16px));'
    'background:var(--card,#fffef8);color:var(--fg,#1d1d1f);border:1px solid var(--line,#c9c5bb);border-radius:6px;'
    'box-shadow:0 6px 24px rgba(0,0,0,.18);padding:6px 9px;font:12px/1.45 ui-monospace,Menlo,Consolas,monospace;'
    'pointer-events:none;text-align:left}'
    '.lean-preview .lp-head{font-weight:600;overflow-wrap:anywhere}'
    '.lean-preview .lp-loc{color:var(--mute,#6b6b6b);font-size:11px;overflow-wrap:anywhere}'
    '.lean-preview pre{margin:5px 0 0;white-space:pre-wrap;overflow-wrap:anywhere;max-height:50vh;'
    'overflow:hidden;font:inherit;background:none;border:0;padding:0}')
PREVIEW_JS = r"""(()=>{
const data=JSON.parse(document.getElementById('lean-previews').textContent);
const box=document.createElement('div');box.className='lean-preview';box.setAttribute('role','tooltip');
document.body.append(box);let timer;
function add(cls,text){const e=document.createElement(cls==='pre'?'pre':'div');if(cls!=='pre')e.className=cls;e.textContent=text;box.append(e);}
function show(a){
  const d=data[a.dataset.p];if(!d)return;const [head,loc,body]=d;
  box.replaceChildren();add('lp-head',head);add('lp-loc',loc);add('pre',body);
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
    payload = json.dumps({i: [data['targets'][int(i)][0], location(int(i)), data['previews'][i]] for i in ids},
                         ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')
    block = (f'{BEGIN}<style>{PREVIEW_CSS}</style><script type="application/json" id="lean-previews">'
             f'{payload}</script><script>{PREVIEW_JS}</script>{END}')
    head, sep, tail = text.rpartition('</body>')
    return head + block + sep + tail if sep else text + block


LINE = re.compile(r'<span id="L(\d+)"><a href="#L\1">\1</a> (.*?)</span>(?=\n|</pre>)')


def plain(fragment):
    return html.unescape(re.sub(r'<[^>]+>', '', fragment))


def link_page(data, by_line, repo, page):
    rel = str(page.relative_to(ROOT / PAGES[repo]))[:-len('.html')]
    spans = by_line.get(f'{repo}:{rel}')
    if spans is None:
        return 0
    text = page.read_text()
    count = 0
    def line(m):
        nonlocal count
        n, body = int(m[1]), plain(m[2])
        found = spans.get(n, [])
        count += len(found)
        return (f'<span id="L{n}"><a href="#L{n}">{n}</a> '
                f'{link_text(data, body, found, page.parent, "ref")}</span>')
    head, sep, rest = text.partition('<pre>')
    if PAGE_CSS not in head:
        head = head.replace('</style>', PAGE_CSS + '</style>', 1)
    page.write_text(embed_previews(data, head + sep + LINE.sub(line, rest)))
    return count


BLOCK = re.compile(r'<pre class="lean-src" data-src="([^"]+)" data-line="(\d+)">(.*?)</pre>', re.S)


def link_top(data, by_line, page, stats):
    text = page.read_text()
    def block(m):
        key, start, body = m[1], int(m[2]), plain(m[3])
        spans = by_line.get(key, {})
        repo, rel = key.split(':', 1)
        source = ROOT / PAGES[repo] / (rel + '.html')
        lines = [plain(x[2]) for x in LINE.finditer(source.read_text())] if source.exists() else None
        rows = body.split('\n')
        if lines is None or lines[start - 1:start - 1 + len(rows)] != rows:
            stats['unmatched'].append(f'{page.relative_to(ROOT)}: {key}#L{start}')
            return m[0]
        stats['blocks'] += 1
        out = []
        for i, row in enumerate(rows):
            found = spans.get(start + i, [])
            stats['linked'] += len(found)
            out.append(link_text(data, row, found, page.parent, 'ref'))
        return f'<pre class="lean-src" data-src="{m[1]}" data-line="{start}">' + '\n'.join(out) + '</pre>'
    text = BLOCK.sub(block, text)
    if 'class="lean-src"' in text and PAGE_CSS not in text:
        text = text.replace('</style>', PAGE_CSS + '</style>', 1)
    page.write_text(embed_previews(data, text))


def main():
    data, by_line = load()
    stats = dict(linked=0, blocks=0, unmatched=[])
    for name in TOP_PAGES:
        if (ROOT / name).exists():
            link_top(data, by_line, ROOT / name, stats)
    pages = refs = 0
    for repo, base in PAGES.items():
        for page in sorted((ROOT / base).rglob('*.lean.html')):
            refs += link_page(data, by_line, repo, page)
            pages += 1
    print(f'{stats["linked"]} links in {stats["blocks"]} Lean blocks of the top pages; '
          f'{refs} links in {pages} source pages.')
    if stats['unmatched']:
        sys.exit('Lean blocks differing from their source lines: ' + ', '.join(stats['unmatched']))


if __name__ == '__main__':
    main()
