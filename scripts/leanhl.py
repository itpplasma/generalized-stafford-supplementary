"""Lean syntax highlighting, doc-comment rendering and the bundled source pages.

Shared by scripts/extract-lean-references.py (writes the pages), by
scripts/link-lean-references.py (re-renders them with links and rendered doc
comments) and by scripts/build-site.py (statement extraction). Every source
line stays in the page as text, so the pages can be re-rendered from
themselves.
"""
import html, json, os, re, subprocess
from pathlib import Path

from common import CACHE, ROOT, TOKENS, esc

KATEX = Path(os.environ.get('SUPPLEMENTARY_KATEX', CACHE / 'node/node_modules/katex'))

CMD = {'theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'instance', 'inductive', 'where', 'namespace',
       'section', 'end', 'variable', 'universe', 'open', 'import', 'public', 'module', 'private', 'protected',
       'noncomputable', 'include', 'omit', 'attribute', 'example', 'set_option', 'macro', 'syntax', 'deriving',
       'extends', 'opaque', 'axiom', 'partial', 'unsafe', 'nonrec', 'mutual', 'export', 'scoped', 'local',
       'irreducible_def', 'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'elab', 'macro_rules',
       'termination_by', 'decreasing_by', 'in', 'meta'}
TERM = {'fun', 'λ', 'by', 'have', 'show', 'let', 'if', 'then', 'else', 'match', 'with', 'from', 'at', 'calc', 'do',
        'return', 'suffices', 'obtain', 'this', 'forall', 'exists', 'nomatch', 'nofun', 'using'}
TACTIC = {'exact', 'rw', 'rwa', 'simp', 'simpa', 'intro', 'intros', 'refine', 'apply', 'rfl', 'constructor', 'cases',
          'rcases', 'induction', 'use', 'exists', 'ext', 'congr', 'linarith', 'omega', 'ring', 'norm_num', 'field_simp',
          'aesop', 'tauto', 'decide', 'trivial', 'contradiction', 'exfalso', 'by_contra', 'push_neg', 'specialize',
          'change', 'unfold', 'dsimp', 'subst', 'rintro', 'refine\'', 'left', 'right', 'split', 'next', 'all_goals',
          'any_goals', 'first', 'try', 'repeat', 'classical', 'infer_instance', 'exact_mod_cast', 'norm_cast',
          'push_cast', 'gcongr', 'positivity', 'nlinarith', 'abel', 'noncomm_ring', 'convert', 'filter_upwards',
          'set', 'clear', 'revert', 'generalize', 'conv', 'lift', 'choose', 'wlog', 'by_cases', 'nontriviality',
          'haveI', 'letI', 'calc', 'symm', 'trans', 'rename_i', 'simp_rw', 'erw', 'module', 'linear_combination'}
SORT = {'Prop', 'Type', 'Sort'}
IDENT_START = re.compile(r"[A-Za-z_α-κμ-ωΑ-Ωἀ-῾℀-⅏𝒜-𝖟]")
IDENT = re.compile(r"(?:[A-Za-z_α-κμ-ωΑ-Ωἀ-῾℀-⅏𝒜-𝖟][\w'!?ₐ-ₜ₀-₉ᵢ-ᵪⱼ]*|«[^»]*»)"
                   r"(?:\.(?:[A-Za-z_α-κμ-ωΑ-Ωἀ-῾℀-⅏𝒜-𝖟][\w'!?ₐ-ₜ₀-₉ᵢ-ᵪⱼ]*|«[^»]*»|\d+))*")
NUMBER = re.compile(r'\d+(?:\.\d+)?')


def tokenize(lines):
    """Per line, the coloured spans (start, end, class) of the whole file.
    Classes: kw (command), tm (term keyword), tc (tactic), so (sort), sr (sorry),
    cm (comment), dc (doc comment), st (string), nu (number), at (attribute)."""
    out, depth, kind = [], 0, 'cm'
    for line in lines:
        spans, i, n = [], 0, len(line)
        while i < n:
            if depth:
                j, start = i, i
                while j < n and depth:
                    if line.startswith('-/', j):
                        depth -= 1
                        j += 2
                    elif line.startswith('/-', j):
                        depth += 1
                        j += 2
                    else:
                        j += 1
                spans.append((start, j, kind))
                i = j
                continue
            c = line[i]
            if line.startswith('--', i):
                spans.append((i, n, 'cm'))
                break
            if line.startswith('/-', i):
                kind = 'dc' if line.startswith(('/--', '/-!'), i) else 'cm'
                depth = 1
                j = i + 3 if kind == 'dc' else i + 2
                start = i
                while j < n and depth:
                    if line.startswith('-/', j):
                        depth -= 1
                        j += 2
                    elif line.startswith('/-', j):
                        depth += 1
                        j += 2
                    else:
                        j += 1
                spans.append((start, j, kind))
                i = j
                continue
            if c == '"':
                j = i + 1
                while j < n and line[j] != '"':
                    j += 2 if line[j] == '\\' else 1
                spans.append((i, min(j + 1, n), 'st'))
                i = j + 1
                continue
            if line.startswith('@[', i):
                j, d = i + 2, 1
                while j < n and d:
                    d += {'[': 1, ']': -1}.get(line[j], 0)
                    j += 1
                spans.append((i, j, 'at'))
                i = j
                continue
            m = IDENT.match(line, i) if IDENT_START.match(c) or c == '«' else None
            if m and not (i and re.match(r"[\w'.]", line[i - 1])):
                w = m[0]
                cls = ('kw' if w in CMD else 'tm' if w in TERM else 'tc' if w in TACTIC else 'so' if w in SORT
                       else 'sr' if w in ('sorry', 'admit') else None)
                if cls:
                    spans.append((i, m.end(), cls))
                i = m.end()
                continue
            m = NUMBER.match(line, i)
            if m and not (i and re.match(r'\w', line[i - 1])):
                spans.append((i, m.end(), 'nu'))
                i = m.end()
                continue
            i += 1
        out.append(spans)
    return out


def render_line(text, colours, links=()):
    """HTML of one source line: colour spans, with link anchors (col, length, open_tag)."""
    marks = []  # (pos, order, html)
    for a, b, cls in colours:
        marks.append((a, 1, f'<span class="{cls}">'))
        marks.append((b, 0, '</span>'))
    for col, length, tag in links:
        # A link never crosses a colour boundary: identifiers are uncoloured or one token.
        marks.append((col, 2, tag))
        marks.append((col + length, -1, '</a>'))
    marks.sort(key=lambda m: (m[0], m[1]))
    out, pos = [], 0
    for p, _, tag in marks:
        out.append(esc(text[pos:p]))
        out.append(tag)
        pos = p
    out.append(esc(text[pos:]))
    return ''.join(out)


# -- doc comments ------------------------------------------------------------
OPERATORS = {'Kdim', 'dim', 'Hom', 'End', 'rank', 'deg', 'Ann', 'Ext', 'Tor', 'Spec', 'ker', 'im', 'gr', 'Frac',
             'GKdim', 'udim', 'lcm', 'gcd', 'id', 'ord', 'max', 'min', 'sup', 'inf', 'card', 'char', 'Kdim_'}
CODE_HINTS = re.compile(r':=|⟨|⟩|\bfun\b|\bby\b|^#|[A-Za-z]\.[A-Za-z]|[a-z]_[a-z]{2,}|\bSubmodule\b|\bModule\b'
                        r'|[A-Z][a-z]+[A-Z][A-Za-z]*[a-z][A-Z]?|[a-z][A-Z]{2,}|\[[A-Z]')
UNICODE_TEX = {'⧸': '/', 'ᵐᵒᵖ': '^{\\mathrm{op}}', '⁰': '^{0}', '•': '\\cdot ', '⁻¹': '^{-1}', '∘': '\\circ ',
               '⬝': '\\cdot ', '‖': '\\|', '∣': '\\mid ', '…': '\\dots ', '·': '\\cdot ', '−': '-', '′': "'"}


def looks_like_code(s):
    return bool(CODE_HINTS.search(s)) or len(s) > 90


def to_tex(s):
    for u, t in UNICODE_TEX.items():
        s = s.replace(u, t)
    s = re.sub(r'_([A-Za-z]{2,}|\d{2,})', r'_{\\mathrm{\1}}', s)
    # A space between two operands is function application or a product: keep a thin space.
    s = re.sub(r"(?<=[\w)}'ᵖ⁰])\s+(?=[\w(\\])", r'\\, ', s)
    def word(m):
        w = m[0]
        if w in OPERATORS:
            return f'\\operatorname{{{w}}}'
        return f'\\text{{{w}}}' if len(w) >= 3 else w
    out, i = [], 0
    for m in re.finditer(r'\\[A-Za-z]+\{[^}]*\}|\\[A-Za-z]+', s):
        out.append(re.sub(r'(?<![A-Za-z\\])[A-Za-z]{2,}', word, s[i:m.start()]))
        out.append(m[0])
        i = m.end()
    out.append(re.sub(r'(?<![A-Za-z\\])[A-Za-z]{2,}', word, s[i:]))
    return ''.join(out).replace('}\\, \\text{', '}\\ \\text{')


class Math:
    """Collects formulas, renders them with KaTeX in one batch, then fills placeholders."""

    def __init__(self):
        self.items = []

    def add(self, tex, display=False, fallback=None):
        self.items.append(dict(tex=tex, display=display, fallback=fallback))
        return f'\x00M{len(self.items) - 1}\x00'

    def fill(self, texts):
        if not self.items:
            return texts
        r = subprocess.run(['node', str(ROOT / 'scripts/render-math.mjs'), str(KATEX)], text=True,
                           input=json.dumps(dict(macros={}, lenient=True,
                                                 items=[dict(tex=x['tex'], display=x['display']) for x in self.items])),
                           capture_output=True, check=True)
        rendered = json.loads(r.stdout)['html']
        def sub(m):
            k = int(m[1])
            h = rendered[k]
            if h is None:
                return self.items[k]['fallback'] or f'<code>{esc(self.items[k]["tex"])}</code>'
            return h
        return [re.sub(r'\x00M(\d+)\x00', sub, t) for t in texts]


def md_inline(text, math):
    """Inline Markdown of a doc comment: math, code, emphasis, links."""
    parts, i = [], 0
    pattern = re.compile(r'\$\$(.+?)\$\$|\$([^$\n]+?)\$|``(.+?)``|`([^`]+)`')
    for m in pattern.finditer(text):
        parts.append(('t', text[i:m.start()]))
        if m[1] or m[2]:
            parts.append(('h', math.add((m[1] or m[2]).strip(), bool(m[1]))))
        else:
            s = m[3] or m[4]
            code = f'<code>{esc(s)}</code>'
            parts.append(('h', code if looks_like_code(s) else math.add(to_tex(s), fallback=code)))
        i = m.end()
    parts.append(('t', text[i:]))
    out = []
    for kind, s in parts:
        if kind == 'h':
            out.append(s)
            continue
        s = esc(s)
        s = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', s)
        s = re.sub(r'(?<![\w*])\*([^*\s][^*]*?)\*(?![\w*])', r'<em>\1</em>', s)
        s = re.sub(r'\[([^\]]+)\]\((https?://[^)\s]+)\)', r'<a href="\2">\1</a>', s)
        s = re.sub(r'\[([^\]]+)\]\(([^)\s]+)\)', r'\1', s)
        out.append(s)
    return ''.join(out)


def markdown(text, math):
    """Block Markdown of a doc comment: headings, lists, code fences, paragraphs."""
    lines, out, i = text.split('\n'), [], 0
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
        elif line.startswith('```'):
            j = i + 1
            while j < len(lines) and not lines[j].strip().startswith('```'):
                j += 1
            out.append(f'<pre>{esc(chr(10).join(lines[i + 1:j]))}</pre>')
            i = j + 1
        elif re.match(r'#{1,6} ', line):
            level = min(len(line) - len(line.lstrip('#')) + 2, 6)
            out.append(f'<h{level}>{md_inline(line.lstrip("#").strip(), math)}</h{level}>')
            i += 1
        elif re.match(r'([-*+]|\d+[.)]) ', line):
            ordered = line[0].isdigit()
            items = []
            while i < len(lines) and lines[i].strip():
                s = lines[i].strip()
                if re.match(r'([-*+]|\d+[.)]) ', s):
                    items.append(re.sub(r'^([-*+]|\d+[.)]) ', '', s))
                else:
                    items[-1] += ' ' + s
                i += 1
            tag = 'ol' if ordered else 'ul'
            out.append(f'<{tag}>' + ''.join(f'<li>{md_inline(x, math)}</li>' for x in items) + f'</{tag}>')
        else:
            para = []
            while i < len(lines) and lines[i].strip() and not lines[i].strip().startswith(('```', '#')) \
                    and not (para and re.match(r'([-*+]|\d+[.)]) ', lines[i].strip())):
                para.append(lines[i].strip())
                i += 1
            out.append(f'<p>{md_inline(" ".join(para), math)}</p>')
    return ''.join(out)


def doc_blocks(lines):
    """Doc and module comments that occupy whole lines: [(first, last, kind, text)], 1-based."""
    blocks, i = [], 0
    while i < len(lines):
        s = lines[i].lstrip()
        if s.startswith(('/--', '/-!')):
            kind = 'mod' if s.startswith('/-!') else 'decl'
            j, depth, body = i, 0, []
            while j < len(lines):
                t = lines[j]
                depth += t.count('/-') - t.count('-/')
                body.append(t)
                if depth <= 0:
                    break
                j += 1
            last = body[-1] if body else ''
            if j < len(lines) and last.rstrip().endswith('-/') and depth == 0:
                text = '\n'.join(body).strip()[3:-2]
                indent = min((len(x) - len(x.lstrip()) for x in text.split('\n')[1:] if x.strip()), default=0)
                text = '\n'.join(x[indent:] if k else x for k, x in enumerate(text.split('\n')))
                blocks.append((i + 1, j + 1, kind, text.strip()))
                i = j + 1
                continue
        i += 1
    return blocks


# -- pages -------------------------------------------------------------------
COLOURS_LIGHT = ('--kw:#7c2f9e;--tm:#7c2f9e;--tc:#1f6f78;--so:#a1307a;--sr:#c0362c;--cm:#6b7280;--dc:#4b6b3c;'
                 '--st:#9a4a12;--nu:#9a4a12;--at:#7a6b3a;--ref:#1d4f91;--gut:#9aa0a6;--docbg:#f3f5ef')
COLOURS_DARK = ('--kw:#cf9df5;--tm:#cf9df5;--tc:#6cc4cc;--so:#f08ac8;--sr:#ff8a80;--cm:#9aa1ab;--dc:#a9c995;'
                '--st:#e4a76f;--nu:#e4a76f;--at:#c9b77a;--ref:#8fbaf3;--gut:#6b7078;--docbg:#1f2420')
COLOURS = (f':root{{{COLOURS_LIGHT}}}@media (prefers-color-scheme:dark){{:root:not([data-theme="light"]){{{COLOURS_DARK}}}}}'
           f':root[data-theme="dark"]{{{COLOURS_DARK}}}')
CODE_CSS = COLOURS + (
    '.kw,.tm{color:var(--kw);font-weight:600}.tc{color:var(--tc)}.so{color:var(--so)}.sr{color:var(--sr);font-weight:700}'
    '.cm{color:var(--cm);font-style:italic}.dc{color:var(--dc)}.st,.nu{color:var(--st)}.at{color:var(--at)}'
    'a.ref{color:var(--ref);text-decoration:none}a.ref:hover,a.ref:focus{text-decoration:underline}')

PAGE_CSS = TOKENS + CODE_CSS + '''
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.5 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
header{position:sticky;top:0;z-index:2;background:var(--bg);border-bottom:1px solid var(--line);padding:8px 16px;
display:flex;flex-wrap:wrap;align-items:baseline;gap:2px 16px}
header h1{font:600 15px/1.3 ui-monospace,Menlo,Consolas,monospace;margin:0;overflow-wrap:anywhere}
header p{margin:0;color:var(--mute);font-size:13px}header label{margin-left:auto;font-size:13px;color:var(--mute);cursor:pointer;text-decoration:underline dotted}
#raw:checked~header label{color:var(--fg);font-weight:600}
a{color:var(--accent)}
.src{padding:10px 0 50vh;font:13px/1.55 ui-monospace,"SF Mono",Menlo,Consolas,monospace}
.l{display:grid;grid-template-columns:4.2em minmax(0,1fr);padding-right:16px}
.n{color:var(--gut);text-align:right;padding-right:1.1em;text-decoration:none;user-select:none}
.n:hover{color:var(--accent)}
.c{white-space:pre-wrap;overflow-wrap:anywhere;min-height:1.55em}
.l:target,.hit{background:var(--hl)}
[id^="L"]{scroll-margin-top:30vh}
.doc{display:grid;grid-template-columns:4.2em minmax(0,1fr);padding-right:16px;margin:3px 0}
.doc .md{font:14px/1.55 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;background:var(--docbg);
border-left:3px solid var(--dc);border-radius:0 6px 6px 0;padding:4px 12px;max-width:52rem}
.doc.mod .md{background:none;border-left-color:var(--line)}
.doc .md p{margin:.3em 0}.doc .md ul,.doc .md ol{margin:.3em 0;padding-left:1.4em}
.doc .md h3,.doc .md h4,.doc .md h5{margin:.35em 0 .2em;font-size:1.05em}.doc.mod .md h3{font-size:1.2em}
.doc .md code{font:12.5px ui-monospace,Menlo,Consolas,monospace;background:var(--soft);padding:0 3px;border-radius:3px}
.doc .md pre{font:12.5px/1.5 ui-monospace,Menlo,Consolas,monospace;white-space:pre-wrap}
.doc{position:relative}.anc{position:absolute;top:0;left:0}
.l.raw{display:none}
#raw:checked~main .doc{display:none}#raw:checked~main .l.raw{display:grid}
@media (max-width:640px){.l,.doc{grid-template-columns:2.9em minmax(0,1fr);padding-right:8px}.n{padding-right:.6em}
.src{font-size:12px}header label{margin-left:0}}
'''
PAGE_JS = '''(()=>{function mark(){document.querySelectorAll('.hit').forEach(e=>e.classList.remove('hit'));
const t=document.getElementById(location.hash.slice(1));if(!t)return;
if(t.classList.contains('anc'))t.parentElement.classList.add('hit');}
addEventListener('hashchange',mark);mark();})();'''
BEGIN, END = '<!--code-->', '<!--/code-->'
LINE = re.compile(r'<div class="l[^"]*"[^>]*? data-n="(\d+)"><a class="n"[^>]*>\d+</a><span class="c">(.*?)</span></div>')


def plain(fragment):
    return html.unescape(re.sub(r'<[^>]+>', '', fragment))


def parse_page(text):
    """The source lines of a page, in order."""
    found = {int(m[1]): plain(m[2]) for m in LINE.finditer(text)}
    return [found[i] for i in range(1, len(found) + 1)]


def code(lines, links=None, math=None):
    """Body of a source page: highlighted lines, rendered doc comments (raw lines kept, hidden)."""
    colours = tokenize(lines)
    links = links or {}
    docs = {b[0]: b for b in doc_blocks(lines)} if math is not None else {}
    out, i = [], 1
    def row(n, cls=''):
        ident = '' if cls else f' id="L{n}"'
        return (f'<div class="l{cls}"{ident} data-n="{n}"><a class="n" href="#L{n}">{n}</a>'
                f'<span class="c">{render_line(lines[n - 1], colours[n - 1], links.get(n, ()))}</span></div>')
    while i <= len(lines):
        if i in docs:
            first, last, kind, text = docs[i]
            anchors = ''.join(f'<span class="anc" id="L{n}"></span>' for n in range(first, last + 1))
            out.append(f'<div class="doc {kind}">{anchors}<a class="n" href="#L{first}">{first}</a>'
                       f'<div class="md">{markdown(text, math)}</div></div>')
            out.extend(row(n, ' raw') for n in range(first, last + 1))
            i = last + 1
        else:
            out.append(row(i))
            i += 1
    return '<div class="src">' + ''.join(out) + '</div>'


def page(rel, label, commit, lines, depth, source_url=None):
    home = '../' * depth + 'index.html'
    gh = f' · <a href="{esc(source_url)}">GitHub</a>' if source_url else ''
    return (f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width, initial-scale=1"><title>{esc(rel)}</title>'
            f'<link rel="stylesheet" href="{"../" * depth}assets/katex/katex.min.css">'
            f'<style>{PAGE_CSS}</style></head><body><input type="checkbox" id="raw" hidden>'
            f'<header><h1>{esc(rel)}</h1>'
            f'<p>{esc(label)} at {esc(commit[:12])}{gh} · <a href="{home}">overview</a></p>'
            f'<label for="raw" title="Show doc comments as source text">raw comments</label></header>'
            f'<main>{BEGIN}{code(lines)}{END}</main><script>{PAGE_JS}</script></body></html>\n')
