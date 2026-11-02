#!/usr/bin/env python3
"""Generate index.html (overview) and verification/index.html.

Inputs: site.json, data/overview.json and the generated records under
verification/ (references.json, lean-dag/graph.json, record.json). Run
scripts/link-lean-references.py afterwards to link the Lean blocks. With
--statement-map PATH the Lean names of data/overview.json are checked against
the paper's statement-map.yaml (requires PyYAML).
"""
from pathlib import Path
import argparse, html, json, os, re, sys

from common import BASE_CSS, CITATIONS, CONFIG, DAG, OVERVIEW, PAGES, RECORD, REFS, ROOT, attr, esc
from graphs import HEAD, SVG_CSS, label, node, svg

refs = json.loads(REFS.read_text())
dag = json.loads(DAG.read_text())
record = json.loads(RECORD.read_text())
CHALLENGE = CONFIG['formal']['challenge']['file']
by_name, by_place = {}, {}
for i, (name, repo, rel, line) in enumerate(refs['targets']):
    by_name.setdefault(name, i)
    by_place[name, repo, rel] = i


def target(name, rel=None):
    """Target index of a declaration, preferring the one in file `rel`."""
    if rel and (name, 'formal', rel) in by_place:
        return by_place[name, 'formal', rel]
    return by_name.get(name)


def href(i, here=ROOT, line=None):
    name, repo, rel, decl_line = refs['targets'][i]
    base = Path(PAGES[repo]) / (rel + '.html') if repo in PAGES else None
    if base is None:
        return f'{refs["urls"][repo]}{rel}#L{line or decl_line}'
    path = os.path.relpath(ROOT / base, here)
    return f'{path}#L{line or decl_line}'


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


def step_line(step):
    """Source line of a proof step: the marker comment inside the declaration."""
    i = target(step['decl'])
    name, repo, rel, line = refs['targets'][i]
    if 'marker' not in step:
        return i, None
    lines = source_lines(repo, rel)
    for n in range(line - 1, len(lines)):
        if lines[n].strip().startswith(step['marker']):
            return i, n + 1
    raise SystemExit(f'marker {step["marker"]!r} not found after {name}')


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
        body = '\n'.join(lines[a - 1:b])
        blocks.append(f'<pre class="lean-src" data-src="{key}" data-line="{a}">{esc(body)}</pre>')
    return ''.join(blocks)


def steps_html(steps, here=ROOT):
    items = []
    for s in steps:
        i, line = step_line(s)
        where = (f'<a class="decl" href="{attr(href(i, here, line))}">Lean, line {line}</a>' if line
                 else decl(s['decl'], here))
        items.append(f'<li>{esc(s["text"])} <span class="lean-at">{where}</span></li>')
    return f'<ol class="steps">{"".join(items)}</ol>'


# The structure graph is checked against Lean: every drawn edge X -> Y must be
# a dependency of some key of Y on some key of X in the contracted Lean graph.
def check_structure():
    nodes = dag['nodes']
    below = {}
    def deps(k):
        if k not in below:
            below[k] = set()
            for j in nodes[k]['keys']:
                below[k] |= {j} | deps(j)
        return below[k]
    spec = {n['id']: n for n in OVERVIEW['structure']['nodes']}
    def backed(a, b):
        if 'cites' in spec[a]:  # a cited result: some key of b uses it in Lean
            return any(c in nodes[y]['cites'] for c in spec[a]['cites'] for y in spec[b]['keys'])
        return any(x in deps(y) for x in spec[a]['keys'] for y in spec[b]['keys'])
    bad = [f'{a} -> {b}' for a, b in OVERVIEW['structure']['edges'] if not backed(a, b)]
    if bad:
        raise SystemExit('structure edges without a Lean dependency: ' + ', '.join(bad))


def structure_dot(rankdir):
    head = HEAD.replace('fontsize=9 ', 'fontsize=10.5 ').replace('nodesep=0.16', 'nodesep=0.22')
    out = ['digraph G {\n', head.replace('ranksep=0.3', 'ranksep=0.42' if rankdir == 'LR' else 'ranksep=0.24'),
           f'  rankdir={rankdir};\n']
    main = {'ap', 'a'}
    for n in OVERVIEW['structure']['nodes']:
        cls = 'goal' if n['id'] in main else ('cited' if 'cites' in n else (
            'dep' if n['id'] in ('germ', 'sel', 'desc') else 'stmt'))
        extra = dict(peripheries=2) if n['id'] in main else {}
        out.append(node(n['id'], label(n['text'], n['sub'], width=34 if cls == 'cited' else 22), cls, href=n['href'],
                        tooltip=attr(n['text']), **extra))
    cited = {n['id'] for n in OVERVIEW['structure']['nodes'] if 'cites' in n}
    for a, b in OVERVIEW['structure']['edges']:
        out.append(f'  "{a}" -> "{b}"' + (' [class="ext" style=dashed]' if a in cited else '') + ';\n')
    out.append('  { rank=same; "lit-core"; "germ" }\n  { rank=same; "lit-apps"; "c" }\n}\n')
    return ''.join(out)


INDEX_CSS = BASE_CSS + SVG_CSS + '''
header.hero{margin-bottom:.6rem}
.status{display:flex;flex-wrap:wrap;gap:.25rem .6rem;margin:.45rem 0 .2rem;font-size:.86rem}
.status span,.status a{text-decoration:none;background:var(--soft);border:1px solid var(--line);border-radius:999px;padding:.05rem .55rem}
.status .ok{color:var(--ok);border-color:color-mix(in srgb,var(--ok) 45%,var(--line))}
.status .pending{color:var(--warn);border-color:color-mix(in srgb,var(--warn) 45%,var(--line))}
.hyps{font-size:.86rem;margin:.35rem 0 0;color:var(--mute)}.hyps b{color:var(--fg);font-weight:600}
.hint{font-size:.82rem;color:var(--mute);margin:.25rem 0 0}
.structure{padding:8px 10px;margin-bottom:12px}
.structure .head{display:flex;flex-wrap:wrap;align-items:baseline;gap:0 1rem}.structure h2{margin:0}.structure .hint{margin:0}
.structure .lr{display:block}.structure .tb{display:none}
.grid{display:grid;grid-template-columns:minmax(0,1.12fr) minmax(0,1fr);gap:12px;align-items:start}
.rows{list-style:none;margin:0;padding:0}
.rows>li{border-top:1px solid var(--line)}.rows>li:first-child{border-top:0}
.rows>li>details>summary{list-style:none;display:grid;grid-template-columns:8.6rem minmax(0,1fr);gap:.1rem .6rem;
padding:.32rem .2rem;align-items:baseline}
.rows>li>details>summary::-webkit-details-marker{display:none}
.rows>li>details>summary:hover{background:var(--soft)}
.rows .t{font-weight:600;font-size:.92rem}.rows .t small{display:block;font-weight:400;color:var(--mute);font-size:.76rem}
.rows .s{font-size:.88rem;line-height:1.38}
.rows .l{grid-column:2;font-size:.78rem;color:var(--mute)}
.results .rows>li>details>summary{grid-template-columns:8.6rem minmax(0,1fr) auto}
.rows .b{font-size:.74rem;color:var(--mute);white-space:nowrap}
.rows>li>details[open]>summary{background:var(--soft)}
.rows>li>details>div{padding:.3rem .4rem .8rem 1.2rem;font-size:.9rem;border-left:3px solid var(--line);margin:.2rem 0 .4rem .2rem}
.rows details>div h4{margin:.55rem 0 .15rem;font-size:.8rem;text-transform:uppercase;letter-spacing:.04em;color:var(--mute)}
.rows ul.decls{margin:.1rem 0;padding-left:1.1rem}
ol.steps{margin:.2rem 0;padding-left:0;list-style:none}ol.steps li{margin:.25rem 0}
.lean-at{white-space:nowrap}

.placeholder{border-style:dashed;margin-top:14px}
.missing{color:var(--warn)}
.cited{margin-top:14px;border-left:4px solid var(--citedk);background:color-mix(in srgb,var(--cited) 35%,var(--card))}
.cited td.cite{font-weight:600;white-space:normal;min-width:10rem}.cited ul.decls{margin:0;padding-left:1rem}
.cited table{font-size:.88rem}.cited td:nth-child(3){min-width:14rem;overflow-wrap:anywhere}
.more{margin-top:14px;display:grid;grid-template-columns:repeat(auto-fit,minmax(16rem,1fr));gap:12px}
.more ul{margin:.2rem 0;padding-left:1.1rem;font-size:.88rem}
@media (max-width:900px){.grid{grid-template-columns:1fr}}
@media (max-width:640px){
 .structure .lr{display:none}.structure .tb{display:block}
 .rows>li>details>summary{grid-template-columns:1fr}.rows .l,.rows .b{grid-column:1}
 .rows>li>details>div{padding-left:.6rem}
 h1{font-size:1.25rem}
}
'''

OPEN_JS = '''(()=>{function open(){const t=document.getElementById(decodeURIComponent(location.hash.slice(1)));
if(!t)return;for(let p=t;p;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;
const d=t.querySelector(':scope>details');if(d)d.open=true;t.scrollIntoView({block:'nearest'});}
addEventListener('hashchange',open);open();})();'''


def result_row(r):
    n = len(r['challenge'])
    ch = ''.join(f'<li>{decl(c, rel=CHALLENGE)}</li>' for c in r['challenge'])
    lib = ''.join(f'<li>{decl(c)}</li>' for c in r['library'])
    steps = f'<h4>Proof outline</h4>{steps_html(r["steps"])}' if r.get('steps') else ''
    blocks = ''.join(statement_block(c) for c in r['challenge'])
    return (f'<li id="result-{r["id"]}"><details><summary><span class="t">{esc(r["title"])}'
            f'<small>{esc(r["name"])}</small></span><span class="s">{esc(r["short"])}</span>'
            f'<span class="b" title="compared Lean statements">Lean: {n}</span>'
            f'</summary><div><p>{esc(r["statement"])}</p>'
            f'<p class="small mute">Paper label <code>{esc(r["label"])}</code></p>'
            f'<h4>Compared Lean statements</h4><ul class="decls">{ch}</ul>'
            f'<h4>Library theorems proving them</h4><ul class="decls">{lib}</ul>{steps}'
            f'<details><summary class="small">Lean text of the compared statement{"s" if n > 1 else ""}</summary>'
            f'{blocks}</details></div></details></li>')


def lemma_row(m):
    names = m['lean'] + m.get('library', [])
    if names:
        first = decl(names[0], text=names[0].rpartition('.')[2])
        more = f' <span class="mute">+{len(names) - 1}</span>' if len(names) > 1 else ''
        where = '' if m['lean'] else f' · in {esc(CONFIG["library"]["label"])}'
    else:
        first, more, where = '<span class="missing">no Lean statement</span>', '', ''
    tag = f'Paper label <code>{esc(m["label"])}</code>' if m.get('label') else ''
    if m.get('map_steps'):
        tag += (' · ' if tag else '') + 'proof steps ' + ', '.join(f'<code>{esc(x)}</code>' for x in m['map_steps'])
    own = ''.join(f'<li>{decl(c)}</li>' for c in m['lean'])
    lib = ''.join(f'<li>{decl(c)}</li>' for c in m.get('library', []))
    body = f'<p>{esc(m["missing"])}</p>' if m.get('missing') else ''
    body += f'<p class="small mute">{tag}</p>' if tag else ''
    if own:
        body += f'<h4>Lean declarations</h4><ul class="decls">{own}</ul>'
    if lib:
        body += f'<h4>{esc(CONFIG["library"]["label"])} declarations</h4><ul class="decls">{lib}</ul>'
    if m.get('steps'):
        body += f'<h4>Proof steps</h4>{steps_html(m["steps"])}'
    if m['id'] in dag['nodes']:
        body += f'<p class="small"><a href="lean-dag.html#key-{m["id"]}">Dependencies in the Lean graph</a></p>'
    return (f'<li id="lemma-{m["id"]}"><details><summary><span class="t">{esc(m["title"])}</span>'
            f'<span class="s">{esc(m["short"])}</span>'
            f'<span class="l">{first}{more}{where}</span></summary><div>{body}</div></details></li>')


def first_users():
    """For each citation, the key declarations that use it first: a key is
    dropped when a key it depends on already uses the citation."""
    nodes = dag['nodes']
    below = {}
    def deps(k):
        if k not in below:
            below[k] = set()
            for j in nodes[k]['keys']:
                below[k] |= {j} | deps(j)
        return below[k]
    out = {}
    for key in CITATIONS['citations']:
        users = [k for k, v in nodes.items() if key in v['cites']]
        out[key] = [k for k in users if not any(key in nodes[b]['cites'] for b in deps(k))]
    return out


def citation_rows():
    titles = {**{r['id']: r['title'] for r in OVERVIEW['results']},
              **{m['id']: m['title'] for m in OVERVIEW['lemmas']},
              **{m['id']: m['title'] for m in OVERVIEW['formal_only']}}
    anchors = {**{r['id']: f'#result-{r["id"]}' for r in OVERVIEW['results']},
               **{m['id']: f'#lemma-{m["id"]}' for m in OVERVIEW['lemmas']}}
    users = first_users()
    rows = []
    for key, c in CITATIONS['citations'].items():
        lean = ''.join(f'<li>{decl(n, text=".".join(n.split(".")[-2:]))}</li>' for n in c['lean'])
        used = ', '.join(f'<a href="{anchors[u]}">{esc(titles[u])}</a>' if u in anchors else esc(titles[u])
                         for u in users[key] if u != 'SOL')
        rows.append(f'<tr id="cite-{re.sub(r"[^A-Za-z0-9]+", "-", key).strip("-")}"><td class="cite">{esc(c["cite"])}</td><td>{esc(c["claim"])}'
                    f'<div class="small mute">{esc(c["status"])}</div></td>'
                    f'<td><ul class="decls">{lean}</ul></td><td class="small">{used}</td></tr>')
    return ''.join(rows)


def index():
    check_structure()
    f = record['formal']
    n_cmp = len(record['comparator']['theorem_names'])
    axioms = 'propext, Classical.choice, Quot.sound'
    assert sorted(axioms.split(', ')) == sorted(record['comparator']['permitted_axioms'])
    hyps = ' · '.join(f'<b>{esc(a)}</b> {esc(b)}' for a, b in OVERVIEW['hypotheses'])
    results = ''.join(result_row(r) for r in OVERVIEW['results'])
    lemmas = ''.join(lemma_row(m) for m in OVERVIEW['lemmas'])
    formal_files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / PAGES['formal']).rglob('*.lean.html'))
    lib_files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / PAGES['library']).rglob('*.lean.html'))
    src_list = lambda files, base: ''.join(
        f'<li><a href="{attr(p)}">{esc(p[len(base) + 1:-5])}</a></li>' for p in files)
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(CONFIG["title"])}</title>
<meta name="description" content="{attr(CONFIG["subtitle"])}">
<style>{INDEX_CSS}</style>
</head><body>
<main>
<nav class="top"><a href="index.html" aria-current="page">Overview</a><a href="lean-dag.html">Lean graph</a><a href="verification/index.html">Verification</a><a href="#paper">Paper comparison</a><a href="#sources">Sources</a></nav>
<header class="hero">
<h1>Affine generation over simple Noetherian rings with infinite centre: the Lean proof</h1>
<div class="status"><a class="ok" href="verification/index.html">all {n_cmp} compared statements machine-checked</a>
<span>formal commit <code>{f["commit"][:7]}</code>, {f["commit_date"][:10]}</span>
<span>axioms: {esc(axioms)}</span><span class="pending">human review pending</span></div>
<p class="hyps">{hyps}. Right modules; Kdim is the right deviation dimension; “regular” means a two-sided non-zero-divisor.</p>
</header>
<section class="panel structure" aria-labelledby="h-structure">
<div class="head"><h2 id="h-structure">Proof structure</h2><p class="hint">Click a node or a row for the full statement, its proof outline and the Lean declarations; hover or focus a Lean name to see its statement.</p></div>
<div class="fig lr">{svg(structure_dot("LR"), title="Proof structure")}</div>
<div class="fig tb">{svg(structure_dot("TB"), title="Proof structure")}</div>
</section>
<div class="grid">
<section class="panel results" aria-labelledby="h-results">
<h2 id="h-results">Main results</h2>
<ol class="rows">{results}</ol>
</section>
<section class="panel lemmas" aria-labelledby="h-lemmas">
<h2 id="h-lemmas">Main lemmas and their Lean form</h2>
<ol class="rows">{lemmas}</ol>
<p class="small mute">Lemmas marked {esc(CONFIG["library"]["label"])} are proved in that pinned Lean library, which the project imports.
Results the paper only cites are listed separately under <a href="#citations">cited from the literature</a>.
The <a href="lean-dag.html">Lean graph</a> shows all dependencies between these declarations.</p>
</section>
</div>
<section class="panel cited" id="citations" aria-labelledby="h-citations">
<h2 id="h-citations">Cited from the literature, formalized in Lean</h2>
<p class="small">The paper cites these results without proof. The Lean proof does not assume them: each is proved in the
pinned {esc(CONFIG["library"]["label"])} library, and the Lean declarations below are the forms it uses.
“First used by” is computed from the Lean dependency graph.</p>
<div class="tbl"><table><thead><tr><th>Citation</th><th>Statement used</th><th>Lean ({esc(CONFIG["library"]["label"])})</th><th>First used by</th></tr></thead>
<tbody>{citation_rows()}</tbody></table></div>
</section>
<section class="panel placeholder" id="paper" aria-labelledby="h-paper">
<h2 id="h-paper">Paper and Lean side by side</h2>
<p class="mute">Follows the paper draft. This section will set each theorem, lemma and proof step of the paper beside
the Lean declarations it is mapped to, using the labels shown above, together with a dependency graph of the printed proofs.</p>
</section>
<div class="more">
<section class="panel" id="sources" aria-labelledby="h-sources">
<h2 id="h-sources">Lean sources</h2>
<p class="small">Bundled for offline reading; every identifier links to its declaration.</p>
<details><summary class="small">{len(formal_files)} project files ({esc(CONFIG["formal"]["label"])})</summary><ul>{src_list(formal_files, PAGES["formal"])}</ul></details>
<details><summary class="small">{len(lib_files)} library files ({esc(CONFIG["library"]["label"])}, imported modules)</summary><ul>{src_list(lib_files, PAGES["library"])}</ul></details>
</section>
<section class="panel" aria-labelledby="h-records">
<h2 id="h-records">Records</h2>
<ul>
<li><a href="verification/index.html">Verification record</a>: pins, challenge sha256, verifier commands and results</li>
<li><a href="lean-dag.html">Lean dependency graph</a>, contracted to the key declarations, expandable to all {len(dag["full"])} project declarations</li>
<li>Formal repository <code>{esc(CONFIG["formal"]["repo"])}</code> at <code>{f["commit"]}</code></li>
</ul>
</section>
</div>
</main>
<script>{OPEN_JS}</script>
</body></html>
'''


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
            head, body = rows[0], [r for r in rows[2:]]
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
        (CONFIG['library']['label'], f'<code>{esc(CONFIG["library"]["repo"])}</code> at <code>{record["library"]["commit"]}</code>'),
        ('Mathlib', f'<code>{record["packages"]["mathlib"]["rev"]}</code>'),
        ('Challenge file', f'<code>{esc(record["challenge"]["file"])}</code>, sha256 <code>{record["challenge"]["sha256"]}</code>'),
        ('Byte-identical copies', ', '.join(f'<code>{esc(k)}</code>: {"yes" if v else "no"}'
                                            for k, v in record['challenge']['identical_copies'].items())),
        ('Compared theorems', f'{len(record["comparator"]["theorem_names"])} (<code>{esc(record["comparator"]["file"])}</code>), '
                              f'permitted axioms {esc(", ".join(record["comparator"]["permitted_axioms"]))}, '
                              f'NanoDa {"enabled" if record["comparator"].get("enable_nanoda") else "disabled"}'),
        ('Library endpoints audited', f'{record["endpoints"]["count"]} names in <code>{esc(record["endpoints"]["file"])}</code>'),
        ('Reference data built from', f'checkout at <code>{f["built_checkout_commit"]}</code>. {esc(f["built_checkout_note"])}'),
    ]
    table = ''.join(f'<tr><th>{esc(k)}</th><td>{v}</td></tr>' for k, v in pins)
    other = ''.join(f'<tr><td><code>{esc(k)}</code></td><td><code>{esc(v["rev"])}</code></td><td>{esc(v["url"])}</td></tr>'
                    for k, v in sorted(record['packages'].items()))
    groups = []
    listed = set()
    for r in OVERVIEW['results']:
        items = ''.join(f'<li>{decl(c, here, rel=CHALLENGE)}</li>' for c in r['challenge'])
        listed |= set(r['challenge'])
        groups.append(f'<li><a href="../index.html#result-{r["id"]}">{esc(r["title"])}</a> '
                      f'<span class="mute">({esc(r["name"])})</span><ul>{items}</ul></li>')
    unlisted = [n for n in record['comparator']['theorem_names'] if n not in listed]
    if unlisted:
        raise SystemExit('compared theorems missing from data/overview.json: ' + ', '.join(unlisted))
    checked = ''.join(f'<li>{esc(c)}</li>' for c in record['checked_here'])
    rerun = ', '.join(f'<code>{esc(c)}</code>' for c in record['not_rerun'])
    css = BASE_CSS + '''main{max-width:980px}section{margin:1.2rem 0}th{white-space:nowrap}
pre.cmd{background:var(--soft);border:1px solid var(--line);border-radius:6px;padding:8px 10px;white-space:pre-wrap;overflow-wrap:anywhere}
.record h2,.record h3{font-size:1rem}.record{font-size:.92rem}
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
<p class="small mute">Quoted from <code>{esc(rec["path"])}</code> of the formal repository at <code>{rec["commit"]}</code>. {esc(rec["note"])}
</p>
<div class="record">{markdown(rec["release_record"], gh)}</div>
<details><summary>What each gate establishes</summary><div class="record">{markdown(rec["gates"], gh)}</div></details>
<details><summary>The full verification document</summary><div class="record">{markdown((here / "formal-verification.md").read_text(), gh)}</div>
<p class="small"><a href="formal-verification.md">Unmodified copy</a> (sha256 <code>{rec["sha256"]}</code>)</p></details>
</section>
<section><h2>Checked when this site was generated</h2><ul>{checked}</ul>
<p class="small mute">Not re-run for this site: {rerun}. Their results above are those recorded by the formal repository.
Machine-readable: <a href="record.json">record.json</a>.</p></section>
<section><h2>The {len(record["comparator"]["theorem_names"])} compared theorems</h2>
<p class="small mute">Each name opens its statement in the bundled challenge file.</p>
<ul>{"".join(groups)}</ul></section>
</main>
</body></html>
'''


def check_statement_map(path):
    import yaml
    smap = yaml.safe_load(Path(path).read_text())
    envs = {e['label']: e for e in smap['environments']}
    steps = {s['step']: s for s in smap.get('proof_steps', [])}
    problems, notes = [], []
    if smap.get('pin') != CONFIG['formal']['commit']:
        problems.append(f'statement map pin {smap.get("pin")} differs from {CONFIG["formal"]["commit"]}')
    for r in OVERVIEW['results']:
        e = envs.get(r['label'])
        if not e:
            problems.append(f'{r["label"]}: not in the statement map')
            continue
        for field in ('challenge', 'library'):
            theirs = {x['name'] for x in e.get(field, [])}
            if theirs != set(r[field]):
                problems.append(f'{r["label"]} {field}: map {sorted(theirs)} vs overview {sorted(r[field])}')
    for m in OVERVIEW['lemmas']:
        ours, lib = set(m['lean']), set(m.get('library', []))
        if m.get('label'):
            e = envs.get(m['label'])
            if not e:
                problems.append(f'{m["label"]}: not in the statement map')
            elif e.get('status') == 'missing':
                if ours or lib or 'missing' not in m:
                    problems.append(f'{m["label"]}: missing in the map, but the overview cites Lean names')
                notes.append(f'{m["label"]}: no Lean counterpart ({e["missing"]})')
            else:
                for field, have in (('library', ours), ('algebraic_analysis', lib)):
                    theirs = {x['name'] for x in e.get(field, [])}
                    if not theirs <= have:
                        problems.append(f'{m["label"]} {field}: {sorted(theirs - have)} missing from the overview')
                    if have - theirs and theirs:
                        notes.append(f'{m["label"]} {field}: overview also cites {sorted(have - theirs)}')
        for s in m.get('map_steps', []):
            if s not in steps:
                problems.append(f'step {s}: not in the statement map')
            elif not {x['name'] for x in steps[s]['library']} <= ours:
                problems.append(f'step {s}: map names missing from the overview')
    covered = {r['label'] for r in OVERVIEW['results']} | {m.get('label') for m in OVERVIEW['lemmas']}
    for label, e in envs.items():
        if label not in covered:
            notes.append(f'{label}: in the statement map, not shown ({e.get("status", "mapped")})')
    if 'citations' in smap:  # the paper's citation section, once it exists, keyed like data/citations.json
        theirs = smap['citations']
        theirs = set(theirs) if isinstance(theirs, dict) else {c.get('key') for c in theirs}
        ours = set(CITATIONS['citations'])
        for k in sorted(ours - theirs):
            notes.append(f'citation {k}: not in the statement map')
        for k in sorted(theirs - ours):
            notes.append(f'citation {k}: in the statement map, not in data/citations.json')
    for n in notes:
        print('note:', n)
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--statement-map', type=Path, help="the paper's statement-map.yaml")
    args = parser.parse_args()
    if args.statement_map:
        problems = check_statement_map(args.statement_map)
        if problems:
            sys.exit('statement map mismatch:\n  ' + '\n  '.join(problems))
        print('statement map: labels and Lean names agree')
    (ROOT / 'index.html').write_text(index())
    (ROOT / 'verification/index.html').write_text(verification())
    print('Wrote index.html and verification/index.html')


if __name__ == '__main__':
    main()
