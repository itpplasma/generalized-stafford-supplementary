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


def source_lines(repo, rel):
    page = ROOT / PAGES[repo] / (rel + '.html')
    return [html.unescape(re.sub(r'<[^>]+>', '', m[1]))
            for m in re.finditer(r'<span id="L\d+"><a href="#L\d+">\d+</a> (.*?)</span>(?=\n|</pre>)', page.read_text())]


def statement_block(name):
    """The challenge theorem and the Statement definitions its type names."""
    key = 'formal:' + CHALLENGE
    ranges = refs['decls'][key]
    start, end = ranges[name]
    used = []
    for line, col, length, t in refs['files'][key]:
        tname, repo, rel, _ = refs['targets'][t]
        if start <= line <= end and rel == CHALLENGE and tname != name and tname in ranges \
                and tname.endswith('Statement') and tname not in used:
            used.append(tname)
    lines = source_lines('formal', CHALLENGE)
    blocks = []
    for n in used + [name]:
        a, b = ranges[n]
        while b > a and not lines[b - 1].strip():
            b -= 1
        if n == name:  # the challenge proof is a deliberate `sorry`
            while b > a and lines[b - 1].strip() in ('sorry', 'by'):
                b -= 1
        blocks.append(f'<pre class="lean-src" data-src="{key}" data-line="{a}">{esc(chr(10).join(lines[a - 1:b]))}</pre>')
    return ''.join(blocks)


def lean_step_lines(name):
    """`-- Step N` comments inside a project declaration: {N: line}."""
    i = target(name)
    _, repo, rel, line = refs['targets'][i]
    end = refs['decls'].get(f'{repo}:{rel}', {}).get(name, [line, line + 400])[1]
    lines = source_lines(repo, rel)
    out = {}
    for n in range(line - 1, min(end, len(lines))):
        m = re.match(r'\s*-- Step (\d+)', lines[n])
        if m:
            out[int(m[1])] = n + 1
    return i, out


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
        return 'Proof of Theorem A′', '#lemma-descent'
    if k.startswith('step:'):
        return STEPS[k[5:]]['title'], f'#cmp-{k}'
    return env_of(k)[0], f'#{kind_of(MAP[k])}-{k}'


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
        hrefv = '#lemma-descent' if n.get('steps') else f'#{kind_of(MAP[first])}-{first}'
        extra = dict(peripheries=2) if cls == 'goal' else {}
        out.append(node(n['id'], label(text, cap, width=30 if known else 24), cls, href=hrefv, tooltip=attr(text), **extra))
    for a, b in OVERVIEW['structure']['edges']:
        out.append(f'  "{a}" -> "{b}"' + (' [class="ext" style=dashed]' if a in cited else '') + ';\n')
    out.append('}\n')
    return ''.join(out)


# -- Lean panels -------------------------------------------------------------
def lean_panel(e, here=ROOT):
    parts = []
    if e.get('status') == 'missing':
        parts.append(f'<p class="missing">No Lean statement: {esc(e.get("missing", ""))}</p>')
    if e.get('challenge'):
        n = len(e['challenge'])
        parts.append('<h4>Compared Lean statements</h4><ul class="decls">'
                     + ''.join(f'<li>{decl(x["name"], here, rel=CHALLENGE)}</li>' for x in e['challenge']) + '</ul>')
    if e.get('library'):
        parts.append('<h4>Lean theorems</h4><ul class="decls">'
                     + ''.join(f'<li>{decl(x["name"], here)}</li>' for x in e['library']) + '</ul>')
    if e.get('algebraic_analysis'):
        parts.append(f'<h4>{esc(LIB)} declarations</h4><ul class="decls">'
                     + ''.join(f'<li>{decl(x["name"], here)}</li>' for x in e['algebraic_analysis']) + '</ul>')
    if e.get('challenge'):
        n = len(e['challenge'])
        parts.append(f'<details><summary class="small">Lean text of the compared statement{"s" if n > 1 else ""}</summary>'
                     + ''.join(statement_block(x['name']) for x in e['challenge']) + '</details>')
    if e.get('label') in dag['nodes']:
        parts.append(f'<p class="small"><a href="lean-dag.html#key-{e["label"]}">Dependencies in the Lean graph</a></p>')
    return ''.join(parts)


def first_lean(e):
    names = names_of(e, ('library', 'algebraic_analysis')) or names_of(e, ('challenge',))
    if not names:
        return '<span class="missing">no Lean statement</span>'
    more = f' <span class="mute">+{len(names) - 1}</span>' if len(names) > 1 else ''
    where = '' if names_of(e, ('library', 'challenge')) else f' · in {esc(LIB)}'
    return decl(names[0], text=names[0].rpartition('.')[2]) + more + where


# -- overview rows -----------------------------------------------------------
def result_row(lab):
    e = MAP[lab]
    name, statement, summary, title, page = env_of(lab)
    n = len(e['challenge'])
    sub = f'<small>{title}</small>' if title else ''
    return (f'<li id="result-{lab}"><details><summary><span class="t">{esc(name)}{sub}</span>'
            f'<span class="s clamp">{summary}</span><span class="b" title="compared Lean statements">Lean: {n}</span>'
            f'</summary><div><div class="stmt">{statement}</div>{lean_panel(e)}'
            f'<p class="small"><a href="#paper-{lab}">Paper and Lean side by side</a> · {pdf_link(page)}</p>'
            f'</div></details></li>')


def lemma_row(lab):
    e = MAP[lab]
    name, statement, summary, title, page = env_of(lab)
    return (f'<li id="lemma-{lab}"><details><summary><span class="t">{esc(name)}</span>'
            f'<span class="s">{title or esc(e["title"])}</span><span class="l">{first_lean(e)}</span></summary>'
            f'<div><div class="stmt">{statement}</div>{lean_panel(e)}'
            f'<p class="small"><a href="#paper-{lab}">Paper and Lean side by side</a> · {pdf_link(page)}</p>'
            f'</div></details></li>')


def descent_row():
    names = [x['name'] for s in DESCENT for x in STEPS[s].get('library', [])]
    sec = SECTIONS['sec:descent']
    items = ''.join(f'<li><a href="#cmp-step:{s}">{esc(STEPS[s]["title"])}</a>: '
                    + ', '.join(decl(x['name']) for x in STEPS[s].get('library', [])) + '</li>' for s in DESCENT)
    return (f'<li id="lemma-descent"><details><summary><span class="t">Proof of Theorem A′</span>'
            f'<span class="s">two-call descent, §{sec["number"]} {esc(sec["title"])}</span>'
            f'<span class="l">{decl(names[1], text=names[1].rpartition(".")[2])} <span class="mute">+{len(names) - 1}</span>'
            f'</span></summary><div><p>The mapped proof steps of the paper and their Lean declarations:</p>'
            f'<ul>{items}</ul><p class="small"><a href="lean-dag.html#key-step:descent">Dependencies in the Lean graph</a></p>'
            f'</div></details></li>')


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
        where = ', '.join(f'{it} ({p})' if p else f'{it} (page not checked)' for it, p in zip(items, pages))
        parts.append(f'<a href="#bib-{key}">[{b["n"]}]</a> {esc(b["author"])} {esc(b["year"])}, {esc(where)}')
    return '<br>'.join(parts)


def known_rows():
    rows = []
    for lab, e in MAP.items():
        if 'cite' not in e:
            continue
        env = ENVS[lab]
        users = users_of(lab)
        used = ', '.join(f'<a href="{key_name(u)[1]}">{esc(key_name(u)[0])}</a>' for u in users) \
            or '<span class="mute">no use found in the Lean proof</span>'
        rows.append(f'<tr id="known-{lab}"><td class="cite"><b>{esc(env["name"])}</b><div class="small">{reference(env)}</div>'
                    f'<div class="small">{pdf_link(env["page"])} · <a href="#paper-{lab}">side by side</a></div></td>'
                    f'<td><div class="stmt">{clean(env["statement"])}</div></td>'
                    f'<td><ul class="decls">'
                    + ''.join(f'<li>{decl(n, text=".".join(n.split(".")[-2:]))}</li>' for n in names_of(e)) +
                    f'</ul></td><td class="small">{used}</td></tr>')
    return ''.join(rows)


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
        b = paper['bib'][a['key']]
        out.append(f'<li><p class="small mute">main.tex lines {a["lines"][0]}–{a["lines"][1]}, citing '
                   f'<a href="#bib-{a["key"]}">[{b["n"]}]</a> {esc(b["author"])} {esc(b["year"])}</p>{a["html"]}</li>')
    return ''.join(out)


# -- paper comparison --------------------------------------------------------
def cmp_status(lab):
    if lab not in MAP:
        return '<span class="tag">definition</span>'
    e = MAP[lab]
    if e.get('status') == 'missing':
        return '<span class="tag missing">no Lean statement</span>'
    n = len(names_of(e))
    tag = '<span class="tag known">known result</span>' if 'cite' in e else ''
    return f'{tag}<span class="tag">Lean: {n}</span>'


def cmp_row(env):
    lab = env['label']
    title = f' <span class="mute">({env["title"]})</span>' if env['title'] else ''
    proofs = ''.join(f'<details class="proof"><summary class="small">Proof (main.tex lines {p["lines"][0]}–{p["lines"][1]})'
                     f'</summary>{clean(p["html"])}</details>' for p in env['proofs'])
    if env['items'] and lab not in MAP:
        intro = re.split(r'<dl>', clean(env['statement']))[0]
        subs = ''.join(
            f'<div class="sub" id="paper-{i["label"]}"><div class="paper"><b>{esc(i["number"])}</b> {clean(i["statement"])}</div>'
            f'<div class="lean">{lean_panel(MAP[i["label"]])}</div></div>' for i in env['items'])
        status = f'<span class="tag">Lean: {sum(len(names_of(MAP[i["label"]])) for i in env["items"])}</span>'
        body = f'<div class="cmp-intro">{intro}{proofs}</div>{subs}'
    else:
        lean = lean_panel(MAP[lab]) if lab in MAP else '<p class="mute small">Definition; definitions are not mapped to Lean.</p>'
        status = cmp_status(lab)
        body = f'<div class="sub"><div class="paper">{clean(env["statement"])}{proofs}</div><div class="lean">{lean}</div></div>'
    return (f'<details class="cmp" id="paper-{lab}"><summary><span class="t">{esc(env["name"])}{title}</span>{status}</summary>'
            f'<div class="cmp-body"><p class="small mute">main.tex lines {env["lines"][0]}–{env["lines"][1]} · '
            f'{pdf_link(env["page"])}</p>{body}</div></details>')


def step_row(step):
    s, m = paper['steps'][step], STEPS[step]
    names = names_of(m)
    lean = ('<ul class="decls">' + ''.join(f'<li>{decl(n)}</li>' for n in names) + '</ul>')
    if s['substeps']:
        project = [n for n in names if n.startswith('GeneralizedStafford')]
        lines = {}
        if project:
            i, lines = lean_step_lines(project[0])
        rows = ''.join(
            f'<div class="sub"><div class="paper">{clean(x["html"])}</div><div class="lean">'
            + (f'<a class="decl" href="{attr(href(i, ROOT, lines[x["n"]]))}">Lean step {x["n"]}, line {lines[x["n"]]}</a>'
               if x['n'] in lines else '<span class="mute small">no marked Lean step</span>') + '</div></div>'
            for x in s['substeps'])
        if project and lines and set(lines) != {x['n'] for x in s['substeps']}:
            raise SystemExit(f'step {step}: paper steps {[x["n"] for x in s["substeps"]]} vs Lean steps {sorted(lines)}')
        body = f'<div class="sub"><div class="paper"></div><div class="lean">{lean}</div></div>{rows}'
    else:
        body = f'<div class="sub"><div class="paper">{clean(s["html"])}</div><div class="lean">{lean}</div></div>'
    where = env_of(s['env'])[0]
    return (f'<details class="cmp" id="cmp-step:{step}"><summary><span class="t">{esc(m["title"])}</span>'
            f'<span class="tag">step <code>{esc(step)}</code></span><span class="tag">Lean: {len(names)}</span></summary>'
            f'<div class="cmp-body"><p class="small mute">{"Statement" if s["part"] == "statement" else "Proof"} of '
            f'<a href="#paper-{s["env"]}">{esc(where)}</a>, main.tex lines {s["lines"][0]}–{s["lines"][1]}</p>{body}</div></details>')


def comparison():
    groups, current = [], None
    for env in paper['envs']:
        if not env['label']:
            continue
        sec = env['section']
        if sec['label'] != current:
            current = sec['label']
            groups.append(f'<h3 id="paper-{sec["label"]}">§{sec["number"]} {esc(sec["title"])}</h3>')
        groups.append(cmp_row(env))
    for lab in SECTIONS:
        if f'id="paper-{lab}"' not in ''.join(groups):
            groups.append(f'<span id="paper-{lab}"></span>')
    steps = ''.join(step_row(s) for s in STEPS)
    return ''.join(groups), steps


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
        out.append(node(lab, label(env['name'], cap, width=24), cls, href=f'#paper-{lab}', tooltip=attr(env['name'])))
    for a, b in paper['edges']:
        out.append(f'  "{a}" -> "{b}";\n')
    out.append('}\n')
    return ''.join(out)


def bibliography():
    return ''.join(f'<li id="bib-{k}" value="{b["n"]}">{b["html"]}</li>'
                   for k, b in sorted(paper['bib'].items(), key=lambda kv: kv[1]['n']))


INDEX_CSS = BASE_CSS + SVG_CSS + '''
header.hero{margin-bottom:.6rem}
.status{display:flex;flex-wrap:wrap;gap:.25rem .6rem;margin:.45rem 0 .2rem;font-size:.86rem}
.status span,.status a{text-decoration:none;background:var(--soft);border:1px solid var(--line);border-radius:999px;padding:.05rem .55rem}
.status .ok{color:var(--ok);border-color:color-mix(in srgb,var(--ok) 45%,var(--line))}
.status .pending{color:var(--warn);border-color:color-mix(in srgb,var(--warn) 45%,var(--line))}
.hyps{font-size:.86rem;margin:.35rem 0 0;color:var(--mute)}.hyps b{color:var(--fg);font-weight:600}
.hyps details{display:inline}.hyps details[open]{display:block}.hyps details p{color:var(--fg)}
.hint{font-size:.82rem;color:var(--mute);margin:0}
.structure{padding:8px 10px;margin-bottom:12px}
.structure .head{display:flex;flex-wrap:wrap;align-items:baseline;gap:0 1rem}.structure h2{margin:0}
.structure .lr{display:block}.structure .tb{display:none}
.grid{display:grid;grid-template-columns:minmax(0,1.12fr) minmax(0,1fr);gap:12px;align-items:start}
.rows{list-style:none;margin:0;padding:0}
.rows>li{border-top:1px solid var(--line)}.rows>li:first-child{border-top:0}
.rows>li>details>summary{list-style:none;display:grid;grid-template-columns:8.2rem minmax(0,1fr);gap:.1rem .6rem;
padding:.32rem .2rem;align-items:baseline}
.rows>li>details>summary::-webkit-details-marker{display:none}
.rows>li>details>summary:hover,.rows>li>details[open]>summary{background:var(--soft)}
.results .rows>li>details>summary{grid-template-columns:8.2rem minmax(0,1fr) auto}
.rows .t{font-weight:600;font-size:.92rem}.rows .t small{display:block;font-weight:400;color:var(--mute);font-size:.76rem}
.rows .s{font-size:.88rem;line-height:1.4}.rows .l{grid-column:2;font-size:.78rem;color:var(--mute)}
.rows .b{font-size:.74rem;color:var(--mute);white-space:nowrap}
.clamp{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.rows>li>details>div{padding:.3rem .4rem .8rem 1.2rem;font-size:.9rem;border-left:3px solid var(--line);margin:.2rem 0 .4rem .2rem}
h4{margin:.55rem 0 .15rem;font-size:.78rem;text-transform:uppercase;letter-spacing:.04em;color:var(--mute)}
ul.decls{margin:.1rem 0;padding-left:1.1rem}
.stmt p{margin:.3rem 0}.stmt dl,.cmp dl{margin:.3rem 0;display:grid;grid-template-columns:auto 1fr;gap:.2rem .5rem}
.stmt dt,.cmp dt{font-weight:600}.stmt dd,.cmp dd{margin:0}
.katex{font-size:1.04em}.katex-display{margin:.4rem 0;overflow-x:auto;overflow-y:hidden}
.missing{color:var(--warn)}
.cited{margin-top:14px;border-left:4px solid var(--citedk);background:color-mix(in srgb,var(--cited) 35%,var(--card))}
.cited td.cite{min-width:11rem}.cited table{font-size:.88rem}.cited td:nth-child(3){min-width:13rem;overflow-wrap:anywhere}
.attrib{font-size:.88rem;padding-left:1.1rem}.attrib li{margin:.4rem 0}
.panel.paper-cmp{margin-top:14px}
.cmp{border:1px solid var(--line);border-radius:6px;margin:.35rem 0;background:var(--card)}
.cmp>summary{padding:.35rem .6rem;display:flex;flex-wrap:wrap;gap:.2rem .6rem;align-items:baseline}
.cmp>summary .t{font-weight:600;margin-right:auto}
.tag{font-size:.74rem;color:var(--mute);border:1px solid var(--line);border-radius:999px;padding:0 .45rem}
.tag.known{color:var(--citedk);border-color:var(--citedk)}.tag.missing{color:var(--warn)}
.cmp-body{padding:0 .6rem .6rem}
.sub{display:grid;grid-template-columns:minmax(0,1.25fr) minmax(0,1fr);gap:.4rem 1rem;border-top:1px solid var(--line);padding:.4rem 0}
.sub .lean{font-size:.88rem;border-left:3px solid var(--depk);padding-left:.6rem}
details.proof{margin:.3rem 0;padding:.2rem .5rem;background:var(--soft);border-radius:6px}
.more{margin-top:14px;display:grid;grid-template-columns:repeat(auto-fit,minmax(16rem,1fr));gap:12px}
.more ul{margin:.2rem 0;padding-left:1.1rem;font-size:.88rem}
ol.bib{font-size:.85rem;padding-left:2rem}ol.bib li{margin:.2rem 0}
@media (max-width:900px){.grid{grid-template-columns:1fr}.sub{grid-template-columns:1fr}.sub .lean{border-left:0;border-top:2px solid var(--depk);padding:.3rem 0 0}}
@media (max-width:640px){
 .structure .lr{display:none}.structure .tb{display:block}
 .rows>li>details>summary,.results .rows>li>details>summary{grid-template-columns:1fr}.rows .l,.rows .b{grid-column:1}
 .rows>li>details>div{padding-left:.6rem}h1{font-size:1.25rem}
 .cited table,.cited tbody,.cited tr,.cited td{display:block}.cited thead{display:none}.cited tr{border-bottom:1px solid var(--line);padding:.4rem 0}
}
'''

OPEN_JS = '''(()=>{function open(){const t=document.getElementById(decodeURIComponent(location.hash.slice(1)));
if(!t)return;for(let p=t;p;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;
if(t.tagName==='DETAILS')t.open=true;const d=t.querySelector(':scope>details');if(d)d.open=true;
t.scrollIntoView({block:'nearest'});}
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
    results = ''.join(result_row(l) for l in labels if kind_of(MAP[l]) == 'result')
    lemmas = ''.join(lemma_row(l) for l in labels if kind_of(MAP[l]) == 'lemma') + descent_row()
    hyps = ' · '.join(f'<b>{a}</b> {b}' for a, b in paper['hypotheses'])
    cmp_rows, step_rows = comparison()
    formal_files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / PAGES['formal']).rglob('*.lean.html'))
    lib_files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / PAGES['library']).rglob('*.lean.html'))
    src_list = lambda files, base: ''.join(f'<li><a href="{attr(p)}">{esc(p[len(base) + 1:-5])}</a></li>' for p in files)
    pc = paper['commit']
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(CONFIG["title"])}</title>
<meta name="description" content="{attr(paper["title"])}: the paper beside its Lean formalization.">
<link rel="stylesheet" href="assets/katex/katex.min.css">
<style>{INDEX_CSS}</style>
</head><body>
<main>
<nav class="top"><a href="index.html" aria-current="page">Overview</a><a href="#citations">Known results</a><a href="#paper">Paper and Lean</a><a href="lean-dag.html">Lean graph</a><a href="verification/index.html">Verification</a><a href="paper/main.pdf">Paper (PDF)</a></nav>
<header class="hero">
<h1>{esc(paper["title"])}: the paper and its Lean proof</h1>
<div class="status"><a class="ok" href="verification/index.html">all {len(compared)} compared statements machine-checked</a>
<span>Lean <code>{f["commit"][:7]}</code></span><span>paper <code>{pc[:7]}</code></span>
<span>axioms: {esc(axioms)}</span><span class="pending">human review pending</span></div>
<div class="hyps">{hyps}. <details><summary>Conventions</summary><p>{paper["conventions"]}</p></details></div>
</header>
<section class="panel structure" aria-labelledby="h-structure">
<div class="head"><h2 id="h-structure">Proof structure</h2><p class="hint">Click a node or a row for the paper's statement and its Lean declarations; hover or focus a Lean name to see its Lean statement.</p></div>
<div class="fig lr">{svg(structure_dot("LR"), title="Proof structure")}</div>
<div class="fig tb">{svg(structure_dot("TB"), title="Proof structure")}</div>
</section>
<div class="grid">
<section class="panel results" aria-labelledby="h-results">
<h2 id="h-results">Main results</h2>
<ol class="rows">{results}</ol>
</section>
<section class="panel lemmas" aria-labelledby="h-lemmas">
<h2 id="h-lemmas">Lemmas and their Lean form</h2>
<ol class="rows">{lemmas}</ol>
<p class="small mute">Names marked {esc(LIB)} are proved in that pinned Lean library, which the project imports.
Results the paper quotes from the literature are listed under <a href="#citations">known results</a>.</p>
</section>
</div>
<section class="panel cited" id="citations" aria-labelledby="h-citations">
<h2 id="h-citations">Known results, formalized in Lean</h2>
<p class="small">The paper states these results with a reference in place of a proof. The Lean proof does not assume them: each is
proved in Lean, in the form of the declarations listed. “Used by” names the first of our results whose Lean proof uses it,
computed from Lean's dependency graph.</p>
<div class="tbl"><table><thead><tr><th>Reference</th><th>Statement in the paper</th><th>Lean</th><th>Used by</th></tr></thead>
<tbody>{known_rows()}</tbody></table></div>
<h3 style="margin-top:.8rem">Attribution, not used by the proof</h3>
<p class="small mute">Passages of the paper crediting results that no Lean declaration formalizes; the Lean proof does not depend on them.</p>
<ul class="attrib">{attribution_rows()}</ul>
</section>
<section class="panel paper-cmp" id="paper" aria-labelledby="h-paper">
<h2 id="h-paper">Paper and Lean side by side</h2>
<p class="small">Every numbered environment of the paper (<a href="paper/main.pdf">PDF</a>, commit <code>{pc[:7]}</code>, {paper["pdf"]["pages"]} pages),
rendered from its LaTeX source, beside the Lean declarations its statement map assigns to it; then the mapped proof steps.
Rows open on click; proofs open separately.</p>
{cmp_rows}
<h3 id="paper-steps">Mapped proof steps</h3>
{step_rows}
<details class="cmp" id="printed-graph"><summary><span class="t">Dependency graph of the printed proofs</span><span class="tag">{len(paper["edges"])} edges</span></summary>
<div class="cmp-body"><p class="small">An arrow X → Y means that the statement or proof of Y refers to X, by <code>\\ref</code> or by
the name of a main theorem. Amber: known results; purple: Theorems A and A′; grey: definitions. Click a node to open its row.</p>
<div class="fig">{svg(printed_dot(), title="Printed-proof dependency graph")}</div></div></details>
<details class="cmp" id="references"><summary><span class="t">References of the paper</span></summary>
<div class="cmp-body"><ol class="bib">{bibliography()}</ol></div></details>
</section>
<div class="more">
<section class="panel" id="sources" aria-labelledby="h-sources">
<h2 id="h-sources">Lean sources</h2>
<p class="small">Bundled for offline reading; every identifier links to its declaration.</p>
<details><summary class="small">{len(formal_files)} project files ({esc(CONFIG["formal"]["label"])})</summary><ul>{src_list(formal_files, PAGES["formal"])}</ul></details>
<details><summary class="small">{len(lib_files)} library files ({esc(LIB)})</summary><ul>{src_list(lib_files, PAGES["library"])}</ul></details>
</section>
<section class="panel" aria-labelledby="h-records">
<h2 id="h-records">Records</h2>
<ul>
<li><a href="verification/index.html">Verification record</a>: pins, challenge sha256, verifier commands and results</li>
<li><a href="lean-dag.html">Lean dependency graph</a>, contracted to the key declarations, expandable to all {len(dag["full"])} project declarations</li>
<li>Paper <code>{esc(paper["repo"])}</code> at <code>{pc}</code>; formal proof <code>{esc(CONFIG["formal"]["repo"])}</code> at <code>{f["commit"]}</code></li>
</ul>
</section>
</div>
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
