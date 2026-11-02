#!/usr/bin/env python3
"""Generate index.html (overview and paper comparison) and verification/index.html.

Inputs: the paper's numbered environments, proofs and proof steps
(verification/paper/paper.json, from scripts/paper.py), its statement map
(verification/paper/statement-map.yaml), the Lean reference data and
dependency graph (verification/lean-references, verification/lean-dag), the
verification record and data/citations.json (printed pages of cited items).
No statement, number or title is kept by hand. The build fails when the map,
the paper, the Lean data or the challenge disagree. Run
scripts/link-lean-references.py afterwards to link the Lean blocks.
"""
from pathlib import Path
import argparse, html, json, os, re, sys

from common import BASE_CSS, CITATIONS, CONFIG, DAG, OVERVIEW, PAGES, PAPER_FILE, RECORD, REFS, ROOT, attr, esc, \
    names_of, statement_map
from graphs import HEAD, SVG_CSS, label, node, svg
import leanhl

refs = json.loads(REFS.read_text())
dag = json.loads(DAG.read_text())
record = json.loads(RECORD.read_text())
paper = json.loads(PAPER_FILE.read_text())
smap = statement_map()
CHALLENGE = CONFIG['formal']['challenge']['file']
LIB = CONFIG['library']['label']
by_name, by_place = {}, {}
for i, (name, repo, rel, line) in enumerate(refs['targets']):
    by_name.setdefault(name, i)
    by_place[name, repo, rel] = i

ENVS = {e['label']: e for e in paper['envs'] if e['label']}
ITEMS = {i['label']: (e, i) for e in paper['envs'] for i in e['items']}
MAP = {e['label']: e for e in smap['environments']}
STEPS = {s['step']: s for s in smap.get('proof_steps', [])}
SECTIONS = {s['label']: s for s in paper['sections']}
MAIN = ('thm:A', 'thm:Aprime')
DESCENT = ('descent-base', 'descent-step', 'descent-termination')


# -- Lean links --------------------------------------------------------------
def target(name, rel=None):
    """Target index of a declaration, preferring the one in file `rel`."""
    if rel and (name, 'formal', rel) in by_place:
        return by_place[name, 'formal', rel]
    return by_name.get(name)


def href(i, here=ROOT, line=None):
    name, repo, rel, decl_line = refs['targets'][i]
    if repo not in PAGES:
        return f'{refs["urls"][repo]}{rel}#L{line or decl_line}'
    return f'{os.path.relpath(ROOT / PAGES[repo] / (rel + ".html"), here)}#L{line or decl_line}'


def short(name):
    return re.sub(r'^(GeneralizedStafford|AlgebraicAnalysis)\.', '', name)


def decl(name, here=ROOT, rel=None, text=None):
    i = target(name, rel)
    if i is None:
        raise SystemExit(f'no declaration for {name}')
    preview = f' data-p="{i}"' if str(i) in refs['previews'] else ''
    return (f'<a class="decl" href="{attr(href(i, here))}"{preview} aria-label="{attr(name)}">'
            f'{esc(text or short(name))}</a>')


# -- paper helpers -----------------------------------------------------------
def clean(h):
    return re.sub(r'<span class="item-anchor"[^>]*></span>', '', h or '')


def env_of(label):
    """(name, statement, summary, title, page) of an environment or an item."""
    if label in ENVS:
        e = ENVS[label]
        return e['name'], clean(e['statement']), clean(e['summary']), e['title'], e['page']
    e, i = ITEMS[label]
    return e['name'] + i['number'], clean(i['statement']), clean(i['summary']), None, e['page']


def text_of(h):
    """Plain text of rendered HTML (KaTeX keeps the TeX in its annotation)."""
    h = re.sub(r'<span class="katex-html".*?</span></span></span>(?=</span>)', '', h or '', flags=re.S)
    h = re.sub(r'<annotation encoding="application/x-tex">(.*?)</annotation>', r'\1', h, flags=re.S)
    h = re.sub(r'<span class="katex-mathml">|<math.*?<semantics>.*?(?=<annotation)', '', h, flags=re.S)
    return re.sub(r'\s+', ' ', html.unescape(re.sub(r'<[^>]+>', '', h))).strip()


def kind_of(e):
    return 'known' if 'cite' in e else 'result' if e.get('challenge') else 'lemma'


def pdf_link(page):
    return f'<a href="paper/main.pdf#page={page}">PDF p. {page}</a>'


# -- Lean graph helpers ------------------------------------------------------
def closure():
    out = {}
    for start, v in dag['nodes'].items():
        seen, todo = set(), list(v['keys'])
        while todo:
            k = todo.pop()
            if k not in seen:
                seen.add(k)
                todo.extend(dag['nodes'][k]['keys'])
        out[start] = seen - {start}
    return out


BELOW = closure()


def users_of(label):
    """Key declarations whose Lean proof uses `label` first (no key below them does)."""
    nodes = dag['nodes']
    users = [k for k, v in nodes.items() if k != 'SOL' and (label in v['keys'] or label in v.get('cites', []))]
    return [k for k in users if not any(b in users for b in BELOW[k])]


def key_name(k):
    if k == 'step:descent':
        return 'Proof of Theorem A′', '#step-descent-base'
    if k.startswith('step:'):
        return STEPS[k[5:]]['title'], f'#step-{k[5:]}'
    return env_of(k)[0], f'#paper-{k}'


def check_structure():
    """Every edge of the overview graph must be a Lean dependency."""
    spec = {n['id']: n for n in OVERVIEW['structure']['nodes']}
    def keys(n):
        ks = [l for l in n.get('labels', []) if l in dag['nodes']]
        return ks + (['step:descent'] if n.get('steps') else [])
    bad = []
    for a, b in OVERVIEW['structure']['edges']:
        src, dst = spec[a], spec[b]
        labels = set(src.get('labels', [])) | set(keys(src))
        ok = any(x in BELOW[y] or x in dag['nodes'][y].get('cites', []) for x in labels for y in keys(dst))
        if not ok:
            bad.append(f'{a} -> {b}')
    if bad:
        raise SystemExit('structure edges without a Lean dependency: ' + ', '.join(bad))


def compress(labels):
    """`Lemmas 3.2–3.9`, `Theorem 7.4(a)–(e)`, `Corollary C, Propositions 6.1–6.2`."""
    names = [env_of(l)[0] for l in labels]
    if len(names) == 1:
        return names[0]
    groups = []
    for n in names:
        kind, _, num = n.partition(' ')
        if groups and groups[-1][0] == kind and re.fullmatch(r'[\d.]+', num) and re.fullmatch(r'[\d.]+', groups[-1][1][-1]):
            groups[-1][1].append(num)
        elif groups and groups[-1][0] == kind and '(' in num and '(' in groups[-1][1][-1]:
            groups[-1][1].append(num)
        else:
            groups.append((kind, [num]))
    out = []
    for kind, nums in groups:
        if len(nums) == 1:
            out.append(f'{kind} {nums[0]}')
        elif '(' in nums[0]:
            out.append(f'{kind} {nums[0]}–{nums[-1][nums[-1].index("("):]}')
        else:
            out.append(f'{kind}s {nums[0]}–{nums[-1]}' if not kind.endswith('s') else f'{kind} {nums[0]}–{nums[-1]}')
    return ', '.join(out)


def structure_dot(rankdir):
    head = HEAD.replace('fontsize=9 ', 'fontsize=10.5 ').replace('nodesep=0.16', 'nodesep=0.22')
    out = ['digraph G {\n', head.replace('ranksep=0.3', 'ranksep=0.42' if rankdir == 'LR' else 'ranksep=0.24'),
           f'  rankdir={rankdir};\n']
    cited = set()
    for n in OVERVIEW['structure']['nodes']:
        labels = n.get('labels', [])
        known = labels and all('cite' in MAP[l] for l in labels)
        text = n.get('name') or compress(labels)
        cap = n.get('caption')
        if cap == 'section':
            last = labels[-1]
            sec = ENVS[last]['section'] if last in ENVS else ITEMS[last][0]['section']
            cap = f'§{sec["number"]} {sec["title"]}'
        elif cap and cap.startswith('sec:'):
            cap = f'§{SECTIONS[cap]["number"]} {SECTIONS[cap]["title"]}'
        cls = 'cited' if known else 'goal' if set(labels) & set(MAIN) else 'dep' if n['id'] in ('germ', 'sel', 'desc') else 'stmt'
        if known:
            cited.add(n['id'])
        first = labels[0] if labels else None
        hrefv = f'#step-{n["steps"][0]}' if n.get('steps') else f'#paper-{first}'
        extra = dict(peripheries=2) if cls == 'goal' else {}
        out.append(node(n['id'], label(text, cap, width=30 if known else 24), cls, href=hrefv, tooltip=attr(text), **extra))
    for a, b in OVERVIEW['structure']['edges']:
        out.append(f'  "{a}" -> "{b}"' + (' [class="ext" style=dashed]' if a in cited else '') + ';\n')
    out.append('}\n')
    return ''.join(out)


# -- Lean statements ---------------------------------------------------------
DECL = re.compile(r'(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public)\s+)*'
                  r'(theorem|lemma|instance|example|def|abbrev|structure|class|inductive|opaque|axiom)\b')
OPEN, CLOSE = '([{⟨', ')]}⟩'
_SRC = {}


def src(repo, rel):
    """Source lines and their colour spans, read back from the bundled page."""
    if (repo, rel) not in _SRC:
        lines = leanhl.parse_page((ROOT / PAGES[repo] / (rel + '.html')).read_text())
        _SRC[repo, rel] = lines, leanhl.tokenize(lines)
    return _SRC[repo, rel]


def code_mask(line, colours):
    """Positions of a line outside comments and strings."""
    mask = [True] * len(line)
    for a, b, cls in colours:
        if cls in ('cm', 'dc', 'st'):
            for k in range(a, min(b, len(line))):
                mask[k] = False
    return mask


def statement_rows(repo, rel, line, end=None, full=False):
    """(first line, rows) of the declaration that starts at `line` (1-based), from
    its keyword to the `:=` or `where` that begins its proof or body; with
    `full`, through the end of its declaration range. Doc comments and
    attribute-only lines before the keyword are skipped."""
    lines, colours = src(repo, rel)
    i = line - 1
    if lines[i].lstrip().startswith('/--'):
        while '-/' not in lines[i]:
            i += 1
        i += 1
    while i < len(lines) and not DECL.match(lines[i].strip()):
        i += 1
        if i > line + 40:
            raise SystemExit(f'no declaration keyword after {rel}:{line}')
    # `let`, `have` and their instance forms inside a type own the next `:=`.
    rows, depth, owned = [], 0, 0
    stop = min(end or len(lines), len(lines))
    for n in range(i, stop):
        text = lines[n]
        if full:
            rows.append(text)
            continue
        if n > i and depth == 0 and (not text.strip() or text.lstrip().startswith('|')):
            break
        mask = code_mask(text, colours[n])
        for j, ch in enumerate(text):
            if not mask[j]:
                continue
            if ch in OPEN:
                depth += 1
            elif ch in CLOSE:
                depth -= 1
            elif depth == 0 and re.match(r'(letI|haveI|let|have)\b', text[j:]) and (j == 0 or not text[j - 1].isalnum()):
                owned += 1
            elif depth == 0 and text.startswith(':=', j) and owned:
                owned -= 1
            elif depth == 0 and text.startswith(':=', j):
                if text[:j].strip():
                    rows.append(text[:j].rstrip())
                return i + 1, rows
            elif depth == 0 and text.startswith('where', j) and (j == 0 or not text[j - 1].isalnum()) \
                    and (j + 5 == len(text) or not text[j + 5].isalnum()):
                rows.append(text[:j + 5])
                return i + 1, rows
        rows.append(text)
    while rows and not rows[-1].strip():
        rows.pop()
    return i + 1, rows


def scope_variables(repo, rel, upto):
    """`variable` commands in scope at line `upto` (1-based): [(first line, rows)]."""
    lines, colours = src(repo, rel)
    stack, i = [[]], 0
    while i < upto - 1:
        t = lines[i].strip()
        if not colours[i] or colours[i][0][2] not in ('cm', 'dc'):
            if re.match(r'(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|public\s+)*(section|namespace)\b', t):
                stack.append([])
            elif re.match(r'end\b', t) and len(stack) > 1:
                stack.pop()
            elif re.match(r'variable\b', t) and not t.endswith(' in'):
                j = i + 1
                while j < upto - 1 and lines[j][:1] in (' ', '\t') and lines[j].strip():
                    j += 1
                stack[-1].append((i + 1, lines[i:j]))
                i = j
                continue
        i += 1
    return [v for frame in stack for v in frame]


IDENT_TOKEN = re.compile(r"[A-Za-z_α-κμ-ωΑ-Ω𝒜-𝖟][A-Za-z0-9_'.α-κμ-ωΑ-Ω₀-₉]*")
BRACKETS = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}


def source_binders(variables):
    """Binders of `variable` commands: dicts with names, type, instance flag and
    (row index in the command list, start, end) of their source text."""
    out = []
    for k, (first, rows) in enumerate(variables):
        for r, text in enumerate(rows):
            j = 0
            while j < len(text):
                if text[j] in BRACKETS:
                    close, depth, e = BRACKETS[text[j]], 0, j
                    while e < len(text):
                        depth += text[e] in '([{⦃⟨'
                        depth -= text[e] in ')]}⦄⟩'
                        if depth == 0:
                            break
                        e += 1
                    inner = text[j + 1:e]
                    m = re.match(r'\s*([^:()\[\]{}]+?)\s*:(?!=)\s*(.*)$', inner, re.S)
                    names, typ = (m[1].split(), m[2]) if m else ([], inner)
                    out.append(dict(names=names, type=typ, inst=text[j] == '[', at=(k, r, j, e + 1)))
                    j = e + 1
                else:
                    j += 1
    return out


def same_head(a, b):
    return a == b or a.endswith('.' + b) or b.endswith('.' + a)


def included_binders(name, variables):
    """Source binders of `variables` that Lean included in `name`: Lean puts the
    included section variables first, in source order, so its leading binders
    are matched in order (named ones by name, instances by class and variables)."""
    lean = refs['binders'].get(name)
    if lean is None:
        raise SystemExit(f'no elaborated binders for {name}; re-extract with --formal')
    src_b = source_binders(variables)
    var_names = {n for b in src_b for n in b['names']}
    def sig(t):
        toks = IDENT_TOKEN.findall(t)
        return (toks[0] if toks else ''), frozenset(x for x in toks[1:] if x in var_names)
    keep, j = set(), 0
    for bname, info, btype in lean:
        btype = ' '.join(btype.split())
        hit = None
        for k in range(j, len(src_b)):
            b = src_b[k]
            for n in b['names'] or [None]:
                if (k, n) in keep:
                    continue
                if info == 'inst' and b['inst'] and not b['names']:
                    (h1, v1), (h2, v2) = sig(b['type']), sig(btype)
                    ok = same_head(h1, h2) and v1 == v2
                else:
                    ok = n == bname
                if ok:
                    hit = (k, n)
                    break
            if hit:
                break
        if not hit:
            break
        keep.add(hit)
        j = hit[0]
    return src_b, keep


def variable_lines(name, repo, rel, variables):
    """The included variable binders as source lines: whole lines when every binder
    on them is included (linked like any Lean block), otherwise only the included
    binders, highlighted without links."""
    src_b, keep = included_binders(name, variables)
    out = []
    for k, (first, rows) in enumerate(variables):
        for r, text in enumerate(rows):
            here = [(i, b) for i, b in enumerate(src_b) if b['at'][:2] == (k, r)]
            used = []
            for i, b in here:
                names = [n for n in b['names'] if (i, n) in keep] if b['names'] else ([None] if (i, None) in keep else [])
                if names:
                    used.append((b, names))
            if not used:
                continue
            if len(used) == len(here) and all(not b['names'] or len(ns) == len(b['names']) for b, ns in used):
                out.append(pre(repo, rel, first + r, [text], ' ctx'))
                continue
            parts = []
            for b, ns in used:
                _, _, a, e = b['at']
                frag = text[a:e]
                if b['names'] and len(ns) < len(b['names']):
                    frag = f'{frag[0]}{" ".join(ns)} : {b["type"]}{frag[-1]}'
                parts.append(frag)
            line = ('variable ' if text.lstrip().startswith('variable') else '  ') + ' '.join(parts)
            out.append(f'<pre class="lean-src ctx frag">{leanhl.render_line(line, leanhl.tokenize([line])[0])}</pre>')
    return out


def pre(repo, rel, first, rows, cls=''):
    return (f'<pre class="lean-src{cls}" data-src="{repo}:{esc(rel)}" data-line="{first}">'
            f'{esc(chr(10).join(rows))}</pre>')


def src_link(i, line=None):
    return f'<a class="srclink" href="{attr(href(i, ROOT, line))}">source</a>'


def lean_statement(name, rel=None, context=True):
    """The Lean statement of a declaration as a code block: header and type, no proof."""
    i = target(name, rel)
    if i is None:
        raise SystemExit(f'no declaration for {name}')
    _, repo, path, line = refs['targets'][i]
    if repo not in PAGES:
        return f'<div class="stmt-lean ext"><code>{decl(name)}</code> <span class="mute small">(Mathlib)</span></div>'
    end = refs['decls'].get(f'{repo}:{path}', {}).get(name, [line, None])[1]
    first, rows = statement_rows(repo, path, line, end)
    # Section variables carry hypotheses of the statement: all those in scope, shown above it.
    # Section variables that Lean included carry hypotheses of the statement: show them above it.
    shown = variable_lines(name, repo, path, scope_variables(repo, path, first)) if context else []
    ctx = '<div class="ctxs">' + ''.join(shown) + '</div>' if shown else ''
    return f'<div class="stmt-lean">{src_link(i, first)}{ctx}{pre(repo, path, first, rows)}</div>'


def challenge_statement(name):
    """A compared challenge theorem and the Statement definitions its type names, in full."""
    key = 'formal:' + CHALLENGE
    ranges = refs['decls'][key]
    start, end = ranges[name]
    used = []
    for line, col, length, t in refs['files'][key]:
        tname, repo, rel, _ = refs['targets'][t]
        if start <= line <= end and rel == CHALLENGE and tname != name and tname in ranges \
                and tname.endswith('Statement') and tname not in used:
            used.append(tname)
    parts = []
    for n in used:
        a, b = ranges[n]
        first, rows = statement_rows('formal', CHALLENGE, a, b, full=True)
        parts.append(pre('formal', CHALLENGE, first, rows))
    first, rows = statement_rows('formal', CHALLENGE, start, end)
    parts.append(pre('formal', CHALLENGE, first, rows))
    return (f'<div class="stmt-lean">{src_link(target(name, CHALLENGE), first)}' + ''.join(parts) + '</div>')


def lean_step_lines(name):
    """`-- Step N` comments inside a project declaration: {N: line}."""
    i = target(name)
    _, repo, rel, line = refs['targets'][i]
    end = refs['decls'].get(f'{repo}:{rel}', {}).get(name, [line, line + 400])[1]
    lines = src(repo, rel)[0]
    out = {}
    for n in range(line - 1, min(end, len(lines))):
        m = re.match(r'\s*-- Step (\d+)', lines[n])
        if m:
            out[int(m[1])] = n + 1
    return i, out


def lean_column(e):
    """Lean side of a card: compared statements first, then the theorems proving them."""
    parts = []
    if e.get('status') == 'missing':
        parts.append(f'<p class="missing">No Lean statement: {esc(e.get("missing", ""))}</p>')
    if e.get('challenge'):
        n = len(e['challenge'])
        parts.append(f'<p class="lab">Compared statement{"s" if n > 1 else ""} '
                     f'<span class="mute">(challenge file, checked by Comparator)</span></p>')
        parts.extend(challenge_statement(x['name']) for x in e['challenge'])
        lib = e.get('library', []) + e.get('algebraic_analysis', [])
        if lib:
            parts.append(f'<details class="proved"><summary>Proved by {len(lib)} Lean theorem{"s" if len(lib) > 1 else ""}: '
                         + ', '.join(f'<code>{esc(short(x["name"]))}</code>' for x in lib) + '</summary>'
                         + ''.join(lean_statement(x['name']) for x in lib) + '</details>')
    else:
        for field, where in (('library', ''), ('algebraic_analysis', f' in {LIB}')):
            xs = e.get(field, [])
            if xs:
                parts.append(f'<p class="lab">Lean statement{"s" if len(xs) > 1 else ""}{where}</p>')
                parts.extend(lean_statement(x['name']) for x in xs)
    return ''.join(parts)


# -- cards -------------------------------------------------------------------
def card_head(name, title, page, lab):
    sub = f' <span class="ttl">{title}</span>' if title else ''
    graph = f' · <a href="lean-dag.html#key-{lab}">Lean graph</a>' if lab in dag['nodes'] else ''
    return (f'<header><h3>{esc(name)}{sub}</h3><span class="links small">'
            f'<a href="paper/main.pdf#page={page}">PDF p.&nbsp;{page}</a>{graph}</span></header>')


def paper_proofs(lab):
    env = ENVS.get(lab)
    if not env or not env['proofs']:
        return ''
    return ''.join(f'<details class="pproof"><summary>Proof in the paper</summary>{clean(p["html"])}</details>'
                   for p in env['proofs'])


def card(lab, extra=''):
    e = MAP[lab]
    name, statement, summary, title, page = env_of(lab)
    title = title or (None if lab in ITEMS else None)
    return (f'<article class="card" id="paper-{lab}">{card_head(name, title, page, lab)}<div class="pair">'
            f'<div class="paper">{extra}<div class="stmt">{statement}</div>{paper_proofs(lab)}</div>'
            f'<div class="lean">{lean_column(e)}</div></div></article>')


def definition_card(lab):
    env = ENVS[lab]
    title = f' <span class="ttl">{env["title"]}</span>' if env['title'] else ''
    return (f'<article class="card def" id="paper-{lab}"><header><h3>{esc(env["name"])}{title}</h3>'
            f'<span class="links small"><a href="paper/main.pdf#page={env["page"]}">PDF p.&nbsp;{env["page"]}</a></span>'
            f'</header><div class="pair"><div class="paper"><div class="stmt">{clean(env["statement"])}</div></div>'
            f'<div class="lean"><p class="mute small">A definition: the Lean statements of the results that use it '
            f'unfold it.</p></div></div></article>')


def page_of(key, item):
    k = f'{key} {item}'
    if k not in CITATIONS['pages']:
        raise SystemExit(f'no printed page for {k} in data/citations.json')
    return CITATIONS['pages'][k]


def reference(env):
    parts = []
    for key, loc in env['cite']:
        b = paper['bib'][key]
        items = re.split(r',\s*', loc)
        pages = [page_of(key, it) for it in items]
        where = ', '.join(f'{it} ({p})' if p else it for it, p in zip(items, pages))
        parts.append(f'<a href="#bib-{key}">[{b["n"]}]</a> {esc(b["author"])} {esc(b["year"])}, {esc(where)}')
    return '; '.join(parts)


def known_card(lab):
    env = ENVS[lab]
    users = users_of(lab)
    used = ', '.join(f'<a href="{key_name(u)[1]}">{esc(key_name(u)[0])}</a>' for u in users) \
        or '<span class="mute">no use found in the Lean proof</span>'
    extra = (f'<p class="ref small">Cited from {reference(env)}. Used by {used}.</p>')
    return card(lab, extra)


def attribution_rows():
    keys = CONFIG['paper'].get('attributions', [])
    for e in smap['environments']:
        for k in keys:
            if k in e.get('cite', ''):
                raise SystemExit(f'{k} is cited by mapped environment {e["label"]}; it is not an attribution only')
    seen, out = set(), []
    for a in paper['attributions']:
        if a['html'] in seen:
            continue
        seen.add(a['html'])
        b = paper['bib'][a['bib']]
        out.append(f'<li><p class="small mute">main.tex lines {a["lines"][0]}–{a["lines"][1]}, citing '
                   f'<a href="#bib-{a["bib"]}">[{b["n"]}]</a> {esc(b["author"])} {esc(b["year"])}</p>{a["html"]}</li>')
    return ''.join(out)


def step_row(step):
    s, m = paper['steps'][step], STEPS[step]
    names = names_of(m)
    lean = ''.join(lean_statement(n, context=False) for n in names)
    rows = ''
    if s['substeps']:
        project = [n for n in names if n.startswith('GeneralizedStafford')]
        lines = {}
        if project:
            i, lines = lean_step_lines(project[0])
        if project and lines and set(lines) != {x['n'] for x in s['substeps']}:
            raise SystemExit(f'step {step}: paper steps {[x["n"] for x in s["substeps"]]} vs Lean steps {sorted(lines)}')
        rows = ''.join(
            f'<div class="pair sub"><div class="paper">{clean(x["html"])}</div><div class="lean small">'
            + (f'<a href="{attr(href(i, ROOT, lines[x["n"]]))}">Lean: step {x["n"]}, line {lines[x["n"]]}</a>'
               if x['n'] in lines else '<span class="mute">no marked Lean step</span>') + '</div></div>'
            for x in s['substeps'])
        body = (f'<div class="pair"><div class="paper"><p class="mute small">The Lean theorem for this part of the proof. '
                f'Each step of the paper below links to the line of the Lean proof that marks it.</p></div>'
                f'<div class="lean">{lean}</div></div>{rows}')
    else:
        body = f'<div class="pair"><div class="paper">{clean(s["html"])}</div><div class="lean">{lean}</div></div>'
    where = env_of(s['env'])[0]
    part = 'statement' if s['part'] == 'statement' else 'proof'
    return (f'<details class="step" id="step-{step}"><summary><b>{esc(m["title"])}</b> '
            f'<span class="mute">· {part} of <a href="#paper-{s["env"]}">{esc(where)}</a></span></summary>'
            f'<div class="step-body">{body}</div></details>')


def printed_dot():
    out = ['digraph G {\n', HEAD, '  rankdir=TB;\n']
    for env in paper['envs']:
        lab = env['label']
        if not lab:
            continue
        e = MAP.get(lab) or (MAP.get(env['items'][0]['label']) if env['items'] else None)
        cls = ('std' if e is None else 'cited' if 'cite' in e else 'goal' if lab in MAIN
               else 'stmt' if any(MAP.get(x, {}).get('challenge') for x in [lab] + [i['label'] for i in env['items']]) else 'dep')
        cap = text_of(env['title']) if env['title'] and not (e and 'cite' in e) else ''
        hrefv = f'#paper-{env["items"][0]["label"]}' if env['items'] and lab not in MAP else f'#paper-{lab}'
        out.append(node(lab, label(env['name'], cap, width=24), cls, href=hrefv, tooltip=attr(env['name'])))
    for a, b in paper['edges']:
        out.append(f'  "{a}" -> "{b}";\n')
    out.append('}\n')
    return ''.join(out)


def bibliography():
    return ''.join(f'<li id="bib-{k}" value="{b["n"]}">{b["html"]}</li>'
                   for k, b in sorted(paper['bib'].items(), key=lambda kv: kv[1]['n']))


INDEX_CSS = BASE_CSS + SVG_CSS + leanhl.CODE_CSS + '''
main{max-width:1240px;padding:0 20px 80px}
nav.top{position:sticky;top:0;z-index:5;background:var(--bg);border-bottom:1px solid var(--line);margin:0 -20px;
padding:9px 20px;gap:.2rem 1.3rem;font-size:.88rem}
nav.top a{color:var(--mute)}nav.top a:hover{color:var(--accent)}
[id]{scroll-margin-top:56px}
.sr{position:absolute;width:1px;height:1px;overflow:hidden;clip:rect(0 0 0 0)}
header.hero{padding:34px 0 8px;max-width:58rem}
header.hero .kicker{font-size:.8rem;letter-spacing:.06em;text-transform:uppercase;color:var(--mute);margin:0 0 .4rem}
header.hero h1{font-size:1.75rem;line-height:1.2;font-weight:650;letter-spacing:-.01em}
header.hero .lede{font-size:1.02rem;margin:.6rem 0 .9rem;color:var(--fg)}
.status{font-size:.86rem;color:var(--mute);margin:0;display:flex;flex-wrap:wrap;gap:.2rem 1.4rem}
.status b{color:var(--ok);font-weight:600}.status .pending{color:var(--warn)}
.overview-graph{margin:26px 0 8px}
.overview-graph .fig{border:1px solid var(--line);border-radius:10px;background:var(--card);padding:10px}
.overview-graph .lr{display:block}.overview-graph .tb{display:none}
.hint{font-size:.82rem;color:var(--mute);margin:.4rem 0 0}
section.part{margin-top:48px}
section.part>h2{font-size:1.3rem;margin:0 0 .25rem;font-weight:650}
section.part>.intro{color:var(--mute);font-size:.92rem;margin:0 0 1rem;max-width:58rem}
h3.sec{font-size:.8rem;text-transform:uppercase;letter-spacing:.06em;color:var(--mute);font-weight:600;margin:28px 0 8px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;margin:0 0 16px;overflow:hidden}
.card>header{display:flex;flex-wrap:wrap;justify-content:space-between;align-items:baseline;gap:.2rem 1rem;
padding:10px 16px 0}
.card h3{font-size:1.02rem;font-weight:650}.card h3 .ttl{font-weight:400;color:var(--mute)}
.card .links{color:var(--mute)}.card .links a{color:var(--mute)}.card .links a:hover{color:var(--accent)}
.card:target{border-color:var(--accent);box-shadow:0 0 0 2px color-mix(in srgb,var(--accent) 30%,transparent)}
.pair{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.3fr);gap:0}
.pair>.paper{padding:8px 16px 14px;font-size:.95rem;line-height:1.55}
.pair>.lean{padding:8px 16px 14px;border-left:1px solid var(--line);background:var(--soft)}
.card.def .pair>.lean{background:none}
.stmt p{margin:.35rem 0}.stmt dl{margin:.3rem 0;display:grid;grid-template-columns:auto 1fr;gap:.2rem .5rem}
.stmt dt{font-weight:600}.stmt dd{margin:0}
.katex{font-size:1.05em}.katex-display{margin:.45rem 0;overflow-x:auto;overflow-y:hidden}
p.lab{font-size:.74rem;text-transform:uppercase;letter-spacing:.05em;color:var(--mute);margin:.2rem 0 .3rem;font-weight:600}
p.lab .mute{text-transform:none;letter-spacing:0;font-weight:400}
.stmt-lean{position:relative;margin:0 0 .55rem}
.stmt-lean+p.lab{margin-top:.8rem}
a.srclink{float:right;position:relative;z-index:1;margin:7px 9px 0 10px;font-size:.72rem;color:var(--mute)}
a.srclink:hover{color:var(--accent)}
pre.lean-src{background:var(--card);border:1px solid var(--line);border-radius:6px;padding:8px 10px;
margin:0 0 4px;white-space:pre-wrap;overflow-wrap:anywhere;font-size:12.5px;line-height:1.55;tab-size:2}
.ctxs{border-left:2px solid var(--line);margin:0 0 6px;padding:2px 0}
pre.lean-src.ctx{font-size:11.5px;line-height:1.5;background:none;border:0;border-radius:0;padding:0 8px;margin:0;opacity:.85}
details.vars>summary,details.proved>summary,details.pproof>summary{font-size:.8rem;color:var(--mute);margin:.15rem 0}
details.vars[open]>summary,details.proved[open]>summary{margin-bottom:.3rem}
details.proved{margin-top:.5rem}details.proved code{font-size:.78rem}
details.pproof{margin-top:.6rem;font-size:.92rem}details.pproof[open]{border-top:1px dashed var(--line);padding-top:.3rem}
p.ref{color:var(--mute);margin:.1rem 0 .4rem}
.missing{color:var(--warn)}
.legend-line{font-size:.88rem;color:var(--mute);margin:0 0 1rem;max-width:62rem}
.legend-line b{color:var(--fg);font-weight:600}
details.step{background:var(--card);border:1px solid var(--line);border-radius:10px;margin:0 0 10px}
details.step>summary{padding:10px 16px;font-size:.95rem}
.step-body{border-top:1px solid var(--line)}
.pair.sub{border-top:1px solid var(--line)}
details.block{margin:0 0 10px;background:var(--card);border:1px solid var(--line);border-radius:10px}
details.block>summary{padding:10px 16px;font-weight:600}
details.block>div{padding:0 16px 14px;border-top:1px solid var(--line)}
.attrib{font-size:.9rem;padding-left:1.1rem}.attrib li{margin:.5rem 0}
ol.bib{font-size:.88rem;padding-left:2rem}ol.bib li{margin:.25rem 0}
.facts{display:grid;grid-template-columns:8rem minmax(0,1fr);gap:.45rem 1rem;font-size:.92rem;margin:0 0 18px;max-width:62rem}
.facts dt{color:var(--mute)}.facts dd{margin:0}
@media (max-width:640px){.facts{grid-template-columns:1fr;gap:.1rem}.facts dd{margin-bottom:.5rem}}
.srclist{columns:2 18rem;font-size:.85rem;padding-left:1.1rem}
@media (max-width:860px){.pair{grid-template-columns:minmax(0,1fr)}.pair>.lean{border-left:0;border-top:1px solid var(--line)}}
@media (max-width:640px){
main{padding:0 16px 60px}nav.top{margin:0 -16px;padding:8px 16px;gap:1rem;flex-wrap:nowrap;overflow-x:auto;white-space:nowrap;scrollbar-width:none}
header.hero{padding-top:22px}header.hero h1{font-size:1.4rem}
.overview-graph .lr{display:none}.overview-graph .tb{display:block}
.card>header,.pair>.paper,.pair>.lean{padding-left:12px;padding-right:12px}
pre.lean-src{font-size:12px;white-space:pre;overflow-wrap:normal;overflow-x:auto}pre.lean-src.ctx{white-space:pre-wrap;overflow-wrap:anywhere}a.srclink{float:none;display:block;text-align:right;margin:0 0 2px}
}
'''

OPEN_JS = '''(()=>{function open(){const t=document.getElementById(decodeURIComponent(location.hash.slice(1)));
if(!t)return;for(let p=t;p;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;t.scrollIntoView();}
addEventListener('hashchange',open);open();})();'''


def index():
    check_structure()
    compared = record['comparator']['theorem_names']
    mapped = {x['name'] for e in smap['environments'] for x in e.get('challenge', [])}
    if set(compared) != mapped:
        raise SystemExit(f'compared theorems and the statement map differ: {sorted(set(compared) ^ mapped)}')
    f = record['formal']
    axioms = 'propext, Classical.choice, Quot.sound'
    assert sorted(axioms.split(', ')) == sorted(record['comparator']['permitted_axioms'])
    order = [l for e in paper['envs'] for l in ([e['label']] if e['label'] else []) + [i['label'] for i in e['items']]]
    labels = [l for l in order if l in MAP]
    unmapped = [e['label'] for e in paper['envs'] if e['label'] and e['label'] not in MAP and not e['items']]
    results = ''.join(card(l) for l in labels if kind_of(MAP[l]) == 'result')
    lemmas, current = [], None
    for env in paper['envs']:
        lab = env['label']
        if not lab or (lab in MAP and kind_of(MAP[lab]) != 'lemma') or (lab not in MAP and lab not in unmapped):
            continue
        sec = env['section']
        if sec['label'] != current:
            current = sec['label']
            lemmas.append(f'<h3 class="sec">§{sec["number"]} {esc(sec["title"])}</h3>')
        lemmas.append(card(lab) if lab in MAP else definition_card(lab))
    known = ''.join(known_card(l) for l in labels if kind_of(MAP[l]) == 'known')
    # References to sections in the rendered statements point at the first card of the section.
    parts = [results, ''.join(lemmas), known]
    placed = set()
    for sec in SECTIONS:
        for e in paper['envs']:
            tag = f'<article class="card" id="paper-{e["label"]}">'
            hit = next((k for k, h in enumerate(parts) if tag in h), None) if e['section']['label'] == sec else None
            if hit is not None:
                parts[hit] = parts[hit].replace(tag, f'<span id="paper-{sec}"></span>' + tag, 1)
                placed.add(sec)
                break
    results, lemma_html, known = parts
    rest = ''.join(f'<span id="paper-{sec}"></span>' for sec in SECTIONS if sec not in placed)
    hyps = ' · '.join(f'<b>{a}</b> {b}' for a, b in paper['hypotheses'])
    steps = ''.join(step_row(s) for s in STEPS)
    formal_files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / PAGES['formal']).rglob('*.lean.html'))
    lib_files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / PAGES['library']).rglob('*.lean.html'))
    src_list = lambda files, base: ''.join(f'<li><a href="{attr(p)}">{esc(p[len(base) + 1:-5])}</a></li>' for p in files)
    pc = paper['commit']
    gh = f'https://github.com/{CONFIG["formal"]["repo"]}'
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(CONFIG["title"])}</title>
<meta name="description" content="{attr(paper["title"])}: every result of the paper beside its Lean statement.">
<link rel="stylesheet" href="assets/katex/katex.min.css">
<style>{INDEX_CSS}</style>
</head><body>
<main>
<nav class="top" aria-label="Sections"><a href="#results">Main results</a><a href="#lemmas">Lemmas</a><a href="#known">Known results</a><a href="#structure">Proof structure</a><a href="#verification">Verification</a><a href="paper/main.pdf">Paper PDF</a></nav>
<header class="hero" id="overview">
<p class="kicker">Paper and Lean, side by side</p>
<h1>{esc(paper["title"])}</h1>
<p class="lede">Every numbered result of the paper, stated as in the paper on the left and as in the Lean&nbsp;4 formalization on the right, so that each statement can be checked against its formal counterpart.</p>
<p class="status"><span><b>{len(compared)} compared statements machine-checked</b></span><span>formal proof <a href="{gh}/tree/{f["commit"]}"><code>{f["commit"][:7]}</code></a></span><span>axioms {esc(axioms)}</span><span class="pending">human review pending</span></p>
</header>
<section class="overview-graph" aria-labelledby="h-graph">
<h2 id="h-graph" class="sr">Proof structure</h2>
<div class="fig lr">{svg(structure_dot("LR"), title="Proof structure")}</div>
<div class="fig tb">{svg(structure_dot("TB"), title="Proof structure")}</div>
<p class="hint">How the results depend on each other in the Lean proof. Click a box to go to its statement.</p>
</section>

<section class="part" id="results" aria-labelledby="h-results">
<h2 id="h-results">Main results</h2>
<p class="intro">Each compared statement is a theorem of the challenge file whose proof Comparator checked against the formal proof. Hover a Lean name for its declaration; “source” opens the full Lean file at that line.</p>
<p class="legend-line">{hyps}.</p>
{results}
</section>

<section class="part" id="lemmas" aria-labelledby="h-lemmas">
<h2 id="h-lemmas">Lemmas</h2>
<p class="intro">The lemmas of the proof in the order of the paper, each beside the Lean theorem that proves it. Names from {esc(LIB)} are proved in that pinned Lean library, which the formal proof imports.</p>
{lemma_html}
</section>

<section class="part" id="known" aria-labelledby="h-known">
<h2 id="h-known">Known results (cited, formalized)</h2>
<p class="intro">The paper quotes these results from the literature instead of proving them. The Lean proof does not assume them: each is proved in Lean in the form shown.</p>
{known}
<details class="block" id="attributions"><summary>Attributions the Lean proof does not use</summary><div>
<p class="small mute">Passages of the paper crediting results that no Lean declaration formalizes.</p>
<ul class="attrib">{attribution_rows()}</ul></div></details>
</section>

<section class="part" id="structure" aria-labelledby="h-structure">
<h2 id="h-structure">Proof structure details</h2>
<p class="intro">The proof steps that the paper's statement map ties to Lean, with the Lean lines of each step, and the dependency graphs.</p>{rest}
{steps}
<details class="block" id="printed-graph"><summary>Dependency graph of the printed proofs</summary><div>
<p class="small">An arrow X → Y means that the statement or proof of Y refers to X. Amber: known results; purple: Theorems A and A′; grey: definitions. Click a node to go to its statement.</p>
<div class="fig">{svg(printed_dot(), title="Printed-proof dependency graph")}</div></div></details>
<p class="small"><a href="lean-dag.html">Lean dependency graph</a>: the key declarations and everything below them, expandable to all {len(dag["full"])} project declarations.</p>
</section>

<section class="part" id="verification" aria-labelledby="h-verification">
<h2 id="h-verification">Verification</h2>
<dl class="facts">
<dt>Formal proof</dt><dd><a href="{gh}/tree/{f["commit"]}">{esc(CONFIG["formal"]["repo"])}</a> at <code title="{f["commit"]}">{f["commit"][:12]}</code>, Lean <code>{esc(f["toolchain"].split(":")[-1])}</code></dd>
<dt>Paper</dt><dd>{esc(paper["repo"])} at <code title="{pc}">{pc[:12]}</code>, <a href="paper/main.pdf">PDF</a> ({paper["pdf"]["pages"]} pages)</dd>
<dt>Axioms</dt><dd>the {len(compared)} compared theorems use only {esc(axioms)}</dd>
<dt>Scope</dt><dd>Machine checks show that the Lean proofs prove the Lean statements. Whether the statements say what the paper says is what this page lets a reader check; human review is pending.</dd>
<dt>Record</dt><dd><a href="verification/index.html">Verification record</a>: pins, challenge checksum, verifier commands and their recorded results</dd>
</dl>
<details class="block" id="sources"><summary>Lean source files</summary><div>
<p class="small mute">Bundled for offline reading, with every identifier linked to its declaration.</p>
<p class="lab">{esc(CONFIG["formal"]["label"])} ({len(formal_files)} files)</p><ul class="srclist">{src_list(formal_files, PAGES["formal"])}</ul>
<p class="lab">{esc(LIB)} ({len(lib_files)} files)</p><ul class="srclist">{src_list(lib_files, PAGES["library"])}</ul></div></details>
<details class="block" id="references"><summary>References of the paper</summary><div><ol class="bib">{bibliography()}</ol></div></details>
</section>
</main>
<script>{OPEN_JS}</script>
</body></html>
'''


# -- verification page -------------------------------------------------------
def md_inline(text, base):
    out = esc(text)
    out = re.sub(r'`([^`]+)`', r'<code>\1</code>', out)
    out = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', out)
    out = re.sub(r'(?<![\w*])\*([^*\s][^*]*)\*(?![\w*])', r'<i>\1</i>', out)
    def link(m):
        url = m[2]
        if not re.match(r'[a-z]+:', url):
            url = base + (url[3:] if url.startswith('../') else 'docs/' + url)
        return f'<a href="{attr(url)}">{m[1]}</a>'
    return re.sub(r'\[([^\]]+)\]\(([^)]+)\)', link, out)


def markdown(text, base):
    """The small Markdown subset of the verification record."""
    out, lines, i = [], text.split('\n'), 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('```'):
            j = i + 1
            while not lines[j].startswith('```'):
                j += 1
            out.append(f'<pre class="cmd">{esc(chr(10).join(lines[i + 1:j]))}</pre>')
            i = j + 1
        elif line.startswith('#'):
            level = len(line) - len(line.lstrip('#'))
            out.append(f'<h{level + 1}>{md_inline(line.lstrip("#").strip(), base)}</h{level + 1}>')
            i += 1
        elif line.startswith('|'):
            rows = []
            while i < len(lines) and lines[i].startswith('|'):
                rows.append([c.strip() for c in lines[i].strip().strip('|').split('|')])
                i += 1
            head, body = rows[0], rows[2:]
            out.append('<div class="tbl"><table><thead><tr>' + ''.join(f'<th>{md_inline(c, base)}</th>' for c in head)
                       + '</tr></thead><tbody>' + ''.join('<tr>' + ''.join(f'<td>{md_inline(c, base)}</td>' for c in r)
                                                          + '</tr>' for r in body) + '</tbody></table></div>')
        elif line.strip():
            para = []
            while i < len(lines) and lines[i].strip() and not lines[i].startswith(('#', '|', '```')):
                para.append(lines[i])
                i += 1
            out.append(f'<p>{md_inline(" ".join(para), base)}</p>')
        else:
            i += 1
    return '\n'.join(out)


def verification():
    here = ROOT / 'verification'
    f, rec = record['formal'], record['verification_record']
    gh = f'https://github.com/{f["repo"]}/blob/{rec["commit"]}/'
    pins = [
        ('Formal repository', f'<code>{esc(f["repo"])}</code> at <code>{f["commit"]}</code> ({f["commit_date"]})'),
        ('Lean toolchain', f'<code>{esc(f["toolchain"])}</code>'),
        (LIB, f'<code>{esc(CONFIG["library"]["repo"])}</code> at <code>{record["library"]["commit"]}</code>'),
        ('Mathlib', f'<code>{record["packages"]["mathlib"]["rev"]}</code>'),
        ('Challenge file', f'<code>{esc(record["challenge"]["file"])}</code>, sha256 <code>{record["challenge"]["sha256"]}</code>'),
        ('Byte-identical copies', ', '.join(f'<code>{esc(k)}</code>: {"yes" if v else "no"}'
                                            for k, v in record['challenge']['identical_copies'].items())),
        ('Compared theorems', f'{len(record["comparator"]["theorem_names"])} (<code>{esc(record["comparator"]["file"])}</code>), '
                              f'permitted axioms {esc(", ".join(record["comparator"]["permitted_axioms"]))}, '
                              f'NanoDa {"enabled" if record["comparator"].get("enable_nanoda") else "disabled"}'),
        ('Library endpoints audited', f'{record["endpoints"]["count"]} names in <code>{esc(record["endpoints"]["file"])}</code>'),
        ('Reference data built from', f'checkout at <code>{f["built_checkout_commit"]}</code>. {esc(f["built_checkout_note"])}'),
        ('Paper', f'<code>{esc(paper["repo"])}</code> at <code>{paper["commit"]}</code> ({paper["commit_date"]}); '
                  f'statement map pinned to <code>{smap["pin"]}</code>'),
        ('Bundled paper PDF', f'<a href="../{paper["pdf"]["path"]}">{paper["pdf"]["path"]}</a>, {paper["pdf"]["pages"]} pages, '
                              f'built with latexmk from the commit, sha256 <code>{paper["pdf"]["sha256"]}</code>'),
        ('Mathematics rendering', f'KaTeX {esc(paper["katex"])} (bundled, MIT licence)'),
    ]
    table = ''.join(f'<tr><th>{esc(k)}</th><td>{v}</td></tr>' for k, v in pins)
    other = ''.join(f'<tr><td><code>{esc(k)}</code></td><td><code>{esc(v["rev"])}</code></td><td>{esc(v["url"])}</td></tr>'
                    for k, v in sorted(record['packages'].items()))
    groups = []
    for e in smap['environments']:
        if not e.get('challenge'):
            continue
        name = env_of(e['label'])[0]
        items = ''.join(f'<li>{decl(c["name"], here, rel=CHALLENGE)}</li>' for c in e['challenge'])
        groups.append(f'<li><a href="../index.html#paper-{e["label"]}">{esc(name)}</a> '
                      f'<span class="mute">({esc(e["title"])})</span><ul>{items}</ul></li>')
    checked = ''.join(f'<li>{esc(c)}</li>' for c in record['checked_here'])
    rerun = ', '.join(f'<code>{esc(c)}</code>' for c in record['not_rerun'])
    css = BASE_CSS + '''main{max-width:980px}section{margin:1.2rem 0}th{white-space:nowrap}
pre.cmd{background:var(--soft);border:1px solid var(--line);border-radius:6px;padding:8px 10px;white-space:pre-wrap;overflow-wrap:anywhere}
.record h2,.record h3{font-size:1rem}.record{font-size:.92rem}td{overflow-wrap:anywhere}
table.pins th{color:var(--fg);width:13rem}@media (max-width:640px){table.pins th{width:auto;white-space:normal}}'''
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Verification record</title>
<meta name="description" content="Pins, challenge checksum and verifier results of the Lean proof of Theorem A.">
<style>{css}</style>
</head><body>
<main>
<nav class="top"><a href="../index.html">Overview</a><a href="../lean-dag.html">Lean graph</a><a href="index.html" aria-current="page">Verification</a></nav>
<h1>Verification record</h1>
<p>The Lean proof is checked by the formal repository's own verifiers. This page records the exact pins, the
checksum of the challenge file that states the compared theorems, and the verifier commands and results as the
formal repository records them. Machine checks establish that the Lean proofs prove the Lean statements; whether
those statements say what the paper says is a separate question, and neither is human review.</p>
<section><h2>Pins</h2><div class="tbl"><table class="pins"><tbody>{table}</tbody></table></div>
<details><summary class="small">All {len(record["packages"])} Lake packages at the pin</summary>
<div class="tbl"><table><thead><tr><th>Package</th><th>Revision</th><th>Source</th></tr></thead><tbody>{other}</tbody></table></div></details>
</section>
<section><h2>Verifier commands and recorded results</h2>
<p class="small mute">Quoted from <code>{esc(rec["path"])}</code> of the formal repository at <code>{rec["commit"]}</code>. {esc(rec["note"])}</p>
<div class="record">{markdown(rec["release_record"], gh)}</div>
<details><summary>What each gate establishes</summary><div class="record">{markdown(rec["gates"], gh)}</div></details>
<details><summary>The full verification document</summary><div class="record">{markdown((here / "formal-verification.md").read_text(), gh)}</div>
<p class="small"><a href="formal-verification.md">Unmodified copy</a> (sha256 <code>{rec["sha256"]}</code>)</p></details>
</section>
<section><h2>Checked when this site was generated</h2><ul>{checked}
<li>the statement map's labels, citations and proof steps agree with the paper source (scripts/paper.py)</li>
<li>the statement map's compared statements are exactly the {len(record["comparator"]["theorem_names"])} of <code>comparator.json</code></li></ul>
<p class="small mute">Not re-run for this site: {rerun}. Their results above are those recorded by the formal repository.
Machine-readable: <a href="record.json">record.json</a>, <a href="paper/paper.json">paper/paper.json</a>.</p></section>
<section><h2>The {len(record["comparator"]["theorem_names"])} compared theorems</h2>
<p class="small mute">Grouped by the paper environment that states them; each name opens its statement in the bundled challenge file.</p>
<ul>{"".join(groups)}</ul></section>
</main>
</body></html>
'''


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    (ROOT / 'index.html').write_text(index())
    (ROOT / 'verification/index.html').write_text(verification())
    print('Wrote index.html and verification/index.html')


if __name__ == '__main__':
    main()
