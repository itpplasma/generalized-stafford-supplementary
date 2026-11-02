#!/usr/bin/env python3
"""Render the dependency DAG of the Lean proof to lean-dag.html.

With --formal (a built checkout with the Lean state of the pinned commit) the
script runs scripts/LeanDag.lean and scripts/LeanDeclRanges.lean, contracts
Lean's own dependency graph to the key declarations of data/overview.json and
stores the result in verification/lean-dag/graph.json. Without --formal it
renders from that file. Every edge comes from the constants Lean records in
the declarations' types and proofs; nothing is inferred from names. Library
modules listed under `dag.leaves` of site.json appear as cited inputs.
Requires Graphviz (`dot`).
"""
from pathlib import Path
import argparse, json, re

from common import BASE_CSS, CITATIONS, CONFIG, DAG, OVERVIEW, PAGES, ROOT, attr, check_formal, comparator_names, \
    esc, lean_run, scratch
from graphs import FILL, HEAD, SVG_CSS, label, name_lines, node, svg, width

LEAVES = {leaf['id']: leaf for leaf in CONFIG['dag']['leaves']}
HELPERS = CONFIG['dag'].get('helpers', 8)


def keys(compared):
    """Key nodes: id -> dict(names, title, short, label, kind), in reading order."""
    out = {}
    for item in OVERVIEW['lemmas']:
        if item['lean']:
            out[item['id']] = dict(names=item['lean'], title=item['title'], short=item['short'],
                                   label=item.get('label'), kind='dep', anchor=f'lemma-{item["id"]}')
    for item in OVERVIEW['formal_only']:
        names = compared if item['lean'] == 'comparator' else item['lean']
        out[item['id']] = dict(names=names, title=item['title'], short=item['short'], label=None,
                               kind='goal' if item['id'] == 'SOL' else 'step', anchor=None)
    for item in OVERVIEW['results']:
        out[item['id']] = dict(names=item['library'], title=item['title'], short=item['name'],
                               label=item['label'], kind='goal' if item['id'] in ('AP', 'A') else 'stmt',
                               anchor=f'result-{item["id"]}')
    seen = {}
    for nid, k in out.items():
        for n in k['names']:
            if n in seen:
                raise SystemExit(f'{n} belongs to two key nodes: {seen[n]}, {nid}')
            seen[n] = nid
    return out


def leaf_of(module):
    """The first leaf whose prefix matches; earlier leaves take precedence."""
    for lid, leaf in LEAVES.items():
        if any(module.startswith(p) for p in leaf['prefixes']):
            return lid
    return None


def visible(g, name):
    last = name.rpartition('.')[2]
    return (g[name]['kind'] in ('theorem', 'def') and '._' not in name and not name.startswith('_private')
            and not re.fullmatch(r'eq_\d+|eq_def|match_\d+|proof_\d+|_.*|inst.*', last))


def extract(formal):
    check_formal(formal)
    compared = comparator_names(formal)
    K = keys(compared)
    with scratch() as tmp:
        tmp = Path(tmp)
        (tmp / 'modules.txt').write_text('\n'.join(CONFIG['dag']['imports']) + '\n')
        (tmp / 'roots.txt').write_text('\n'.join(CONFIG['dag']['roots']) + '\n')
        lean_run(formal, 'LeanDag.lean', tmp / 'modules.txt', tmp / 'roots.txt', tmp / 'raw.json')
        raw = json.loads((tmp / 'raw.json').read_text())
        g, ext = raw['constants'], raw['externals']
        owner = {name: nid for nid, k in K.items() for name in k['names']}
        missing = [n for n in owner if n not in g]
        if missing:
            raise SystemExit('unknown key declarations: ' + ', '.join(missing))

        def result(name):
            """A theorem that is not an instance (by attribute or Lean's `inst` naming) or projection."""
            return (name in ext and ext[name][1] == 'theorem' and not ext[name][2]
                    and not name.rpartition('.')[2].startswith('inst'))

        cited = {n: key for key, c in CITATIONS['citations'].items() for n in c['lean']}
        missing = [n for n in cited if n not in ext]
        if missing:
            raise SystemExit('cited declarations the project does not use directly: ' + ', '.join(missing))
        memo = {}
        def reach(start, stop):
            """Keys and leaves reached from `start` through constants outside `stop`."""
            if (start, stop) in memo:
                return memo[start, stop]
            found, leaves, cites, todo, seen = set(), set(), set(), [start], {start}
            while todo:
                c = todo.pop()
                for e in g[c]['external']:
                    if result(e) and (lid := leaf_of(ext[e][0])):
                        leaves.add(lid)
                    if e in cited:
                        cites.add(cited[e])
                for d in g[c]['uses']:
                    if d in owner and d not in stop:
                        found.add(owner[d])
                    elif d in g and d not in seen and d not in owner:
                        seen.add(d)
                        todo.append(d)
            memo[start, stop] = found, leaves, cites
            return memo[start, stop]

        nodes = {}
        for nid, k in K.items():
            stop = frozenset(k['names'])
            found, leaves, cites, helpers = set(), set(), set(), {}
            for name in k['names']:
                f, l, c = reach(name, stop)
                found |= f
                leaves |= l
                cites |= c
                for d in g[name]['uses']:
                    if d in g and d not in owner and visible(g, d) and g[d]['kind'] == 'theorem':
                        hk, hl, _ = reach(d, stop)
                        helpers[d] = dict(keys=sorted(hk - {nid}), leaves=sorted(hl))
            nodes[nid] = dict(keys=sorted(found - {nid}), leaves=sorted(leaves), cites=sorted(cites),
                              helpers=helpers)
        unused = sorted(set(cited.values()) - {c for v in nodes.values() for c in v['cites']})
        if unused:
            raise SystemExit('citations whose Lean declarations no key declaration uses: ' + ', '.join(unused))

        full = {n: dict(module=v['module'], kind=v['kind'],
                        uses=sorted(d for d in v['uses'] if d in g and visible(g, d)))
                for n, v in g.items() if visible(g, n)}
        names = sorted(full)
        (tmp / 'names.txt').write_text('\n'.join(names) + '\n')
        lean_run(formal, 'LeanDeclRanges.lean', tmp / 'modules.txt', tmp / 'names.txt', tmp / 'ranges.json')
        ranges = json.loads((tmp / 'ranges.json').read_text())
    DAG.parent.mkdir(parents=True, exist_ok=True)
    DAG.write_text(json.dumps(dict(
        schema=1, formal_commit=CONFIG['formal']['commit'], compared=compared,
        source='Constants used by types and proofs (scripts/LeanDag.lean); lines from findDeclarationRanges?. '
               '`nodes` is the graph contracted to the key declarations; `full` lists every visible '
               'project theorem and definition with the project constants it uses.',
        nodes=nodes, full=full, ranges={n: ranges[n] for n in names if n in ranges}),
        indent=0, ensure_ascii=False) + '\n')


def source_href(ranges, name, here=ROOT):
    module, line = ranges[name]
    return f'./{PAGES["formal"]}/{module.replace(".", "/")}.lean.html#L{line}'


def reduce_leaves(nodes):
    """Draw a leaf only into the first nodes that use it: drop X -> K when a
    key below K (one K depends on) already uses X."""
    below = {}
    def closure(nid):
        if nid not in below:
            below[nid] = set()
            for k in nodes[nid]['keys']:
                below[nid] |= {k} | closure(k)
        return below[nid]
    return {nid: [l for l in v['leaves'] if not any(l in nodes[b]['leaves'] for b in closure(nid))]
            for nid, v in nodes.items()}


def closure(nodes):
    """All keys each key depends on, transitively."""
    out = {}
    def deps(k):
        if k not in out:
            out[k] = set()
            for j in nodes[k]['keys']:
                out[k] |= {j} | deps(j)
        return out[k]
    for k in nodes:
        deps(k)
    return out


def reduce_keys(nodes):
    """Transitive reduction of the key edges (Lean edges skipping a level)."""
    below = closure(nodes)
    return {nid: sorted(set(v['keys']) - set().union(*[below[k] for k in v['keys']]))
            for nid, v in nodes.items()}


def key_label(K, nid, width_):
    k = K[nid]
    small = k['names'][0].split('.')[-1] + (f' (+{len(k["names"]) - 1})' if len(k['names']) > 1 else '')
    return label(k['title'], k['short'], small, width_, name_lines(small, width_ + 8))


def overall_dot(K, data):
    nodes = data['nodes']
    keys_, leaves = reduce_keys(nodes), reduce_leaves(nodes)
    out = ['digraph G {\n', HEAD]
    used = [l for l in LEAVES if any(l in ls for ls in leaves.values())]
    for lid in used:
        out.append(node('X:' + lid, label(None, LEAVES[lid]['text'], LEAVES[lid]['source'], width=22),
                        'cited', href=f'#leaf-{lid}', tooltip=attr(LEAVES[lid]['source'])))
    for nid in K:
        extra = dict(peripheries=2) if K[nid]['kind'] == 'goal' else {}
        out.append(node(nid, key_label(K, nid, 24), K[nid]['kind'], href=f'#key-{nid}',
                        tooltip=attr(K[nid]['names'][0]), **extra))
    out.append('  { rank=max; "SOL" }\n')
    for nid in K:
        for k in keys_[nid]:
            out.append(f'  "{k}" -> "{nid}";\n')
        for lid in leaves[nid]:
            out.append(f'  "X:{lid}" -> "{nid}" [class="ext" style=dashed];\n')
    out.append('}\n')
    return ''.join(out)


def proof_dot(K, data, nid):
    v, ranges = data['nodes'][nid], data['ranges']
    out = ['digraph G {\n', HEAD]
    inputs = [('K:' + k, k) for k in v['keys']] + [('X:' + l, l) for l in v['leaves']]
    for key, ident in inputs:
        if key.startswith('K:'):
            out.append(node(key, key_label(K, ident, 30), 'dep', href=f'#key-{ident}'))
        else:
            out.append(node(key, label(None, LEAVES[ident]['text'], LEAVES[ident]['source'], width=30),
                            'cited', href=f'#leaf-{ident}'))
    if inputs:
        out.append('  { rank=min; ' + ' '.join(f'"{k}"' for k, _ in inputs) + ' }\n')
    helpers = sorted(v['helpers'].items(), key=lambda kv: (-len(kv[1]['keys']) - len(kv[1]['leaves']), kv[0]))
    shown = [h for h in helpers if h[1]['keys'] or h[1]['leaves']][:HELPERS]
    covered = set()
    for i, (h, hv) in enumerate(shown):
        hid = f'h{i}'
        lines = '<BR/>'.join(esc(l) for l in name_lines(h.split('.')[-1], 34))
        out.append(node(hid, f'<{lines}>', 'step',
                        href=source_href(ranges, h) if h in ranges else '', tooltip=attr(h)))
        for k in hv['keys']:
            out.append(f'  "K:{k}" -> "{hid}";\n')
            covered.add('K:' + k)
        for l in hv['leaves']:
            out.append(f'  "X:{l}" -> "{hid}" [class="ext" style=dashed];\n')
            covered.add('X:' + l)
        out.append(f'  "{hid}" -> "goal";\n')
    rest = len(v['helpers']) - len(shown)
    if rest > 0:
        out.append(node('more', label(None, f'+ {rest} further lemmas used directly', width=40), 'std'))
        out.append('  "more" -> "goal" [style=dotted];\n')
    for key, _ in inputs:
        if key not in covered:
            style = ' [class="ext" style=dashed]' if key.startswith('X:') else ''
            out.append(f'  "{key}" -> "goal"{style};\n')
    first = K[nid]['names'][0]
    out.append(node('goal', key_label(K, nid, 44), 'goal', peripheries=2,
                    href=source_href(ranges, first) if first in ranges else ''))
    out.append('  { rank=max; "goal" }\n}\n')
    return ''.join(out)


def decl_link(ranges, name, strip=True):
    shown = re.sub(r'^GeneralizedStafford\.', '', name) if strip else name
    if name not in ranges:
        return f'<code>{esc(shown)}</code>'
    return f'<a class="decl" href="{source_href(ranges, name)}">{esc(shown)}</a>'


PAGE_CSS = BASE_CSS + SVG_CSS + '''
main{max-width:1180px}
.card{background:var(--card);border:1px solid var(--line);border-radius:8px;margin:.5rem 0}
.card>summary{padding:8px 12px;display:flex;gap:.6rem;align-items:baseline;flex-wrap:wrap}
.card>summary::-webkit-details-marker{display:none}.card>summary::before{content:"▸";color:var(--mute)}
.card[open]>summary::before{content:"▾"}.card>div{padding:0 12px 10px}
.card .tag{font-size:.78rem;color:var(--mute)}
.fig.big{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:8px}
ul.adj{list-style:none;padding:0;margin:.3rem 0;font-size:.85rem}ul.adj li{padding:.15rem 0;border-bottom:1px solid var(--line)}
ul.adj .uses{color:var(--mute)}
.cites{border-left:3px solid var(--citedk);padding-left:.5rem}
'''

OPEN_JS = '''(()=>{function open(){const t=document.getElementById(decodeURIComponent(location.hash.slice(1)));
if(!t)return;for(let p=t;p;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;t.scrollIntoView();}
addEventListener('hashchange',open);open();})();'''


def page(data):
    K = keys(data['compared'])
    nodes, ranges = data['nodes'], data['ranges']
    kinds = [('cited', 'library input (AlgebraicAnalysis)'), ('dep', 'main lemma'), ('step', 'formal-only step'),
             ('stmt', 'result'), ('goal', 'main theorem or the compared statements')]
    legend = ''.join(f'<li style="--f:var(--{FILL[c]});--k:var(--{FILL[c]}k)">{t}</li>' for c, t in kinds)
    cards = []
    for nid, k in K.items():
        dot = proof_dot(K, data, nid)
        tag = f'<span class="tag">{esc(k["label"])}</span>' if k['label'] else ''
        back = f' · <a href="index.html#{k["anchor"]}">overview row</a>' if k['anchor'] else ''
        decls = ' · '.join(decl_link(ranges, n) for n in k['names'][:12])
        if len(k['names']) > 12:
            decls += f' · and {len(k["names"]) - 12} more'
        cites = nodes[nid].get('cites', [])
        cited = (f'<p class="small cites">Cited from the literature, formalized: '
                 + '; '.join(f'<a href="index.html#citations">{esc(CITATIONS["citations"][c]["cite"])}</a>' for c in cites)
                 + '</p>') if cites else ''
        direct = sorted(nodes[nid]['helpers'])
        listing = (f'<details><summary class="small">All {len(direct)} project lemmas used directly</summary>'
                   f'<ul class="adj">{"".join(f"<li>{decl_link(ranges, h)}</li>" for h in direct)}</ul></details>'
                   if direct else '')
        cards.append(f'<details class="card" id="key-{nid}"><summary><h3>{esc(k["title"])}</h3>{tag}'
                     f'<span class="mute small">{esc(k["short"])}</span></summary><div>'
                     f'<p class="small">{decls}{back}</p>'
                     f'{cited}'
                     f'<div class="fig">{svg(dot, title=k["title"] + " dependencies")}</div>{listing}</div></details>')
    leaves = reduce_leaves(nodes)
    rows = []
    for lid, leaf in LEAVES.items():
        users = [K[n]['title'] for n in K if lid in nodes[n]['leaves']]
        rows.append(f'<tr id="leaf-{lid}"><td>{esc(leaf["text"])}</td><td>{esc(leaf["source"])}</td>'
                    f'<td><code>{esc(", ".join(leaf["prefixes"]))}</code></td><td>{len(users)}</td></tr>')
    full = data['full']
    by_module = {}
    for name, v in sorted(full.items()):
        by_module.setdefault(v['module'], []).append(name)
    modules = []
    for module, names in sorted(by_module.items()):
        items = ''.join(f'<li>{decl_link(ranges, n)} <span class="uses">← '
                        f'{", ".join(re.sub(r"^GeneralizedStafford.", "", u) for u in full[n]["uses"]) or "no project constants"}'
                        f'</span></li>' for n in names)
        modules.append(f'<details><summary><code>{esc(module)}</code> <span class="mute small">'
                       f'({len(names)})</span></summary><ul class="adj">{items}</ul></details>')
    edges = sum(len(v['uses']) for v in full.values())
    commit = data['formal_commit']
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Lean proof graph</title>
<meta name="description" content="Dependency graph of the Lean proof of Theorem A, computed from Lean's environment.">
<style>{PAGE_CSS}</style>
</head><body>
<main>
<nav class="top"><a href="index.html">Overview</a><a href="lean-dag.html" aria-current="page">Lean graph</a><a href="verification/index.html">Verification</a></nav>
<h1>Lean proof graph</h1>
<p>How the key declarations of the Lean proof (formal commit <code>{commit[:12]}</code>) depend on each other.
Every edge is computed from the constants Lean records in each declaration's statement and proof,
contracted to the {len(K)} key declarations: an arrow A → B means that the Lean proof of B uses A,
possibly through lemmas that are not key declarations. Edges implied by longer paths are omitted, and a library
input is drawn only into the first key declarations that use it. General algebra from Mathlib is not drawn.
Click a node to expand its own graph.</p>
<ul class="legend">{legend}</ul>
<div class="fig big">{svg(overall_dot(K, data), title="Contracted Lean dependency graph")}</div>
<h2 style="margin-top:1.6rem">Key declarations</h2>
<p class="small mute">Each entry shows what enters the proof: the key declarations and library inputs it reaches
without passing another key declaration, the named lemmas it uses directly (at most {HELPERS}, chosen by how many
inputs they carry), and the declaration itself at the bottom.</p>
{"".join(cards)}
<h2 style="margin-top:1.6rem" id="leaves">Library inputs</h2>
<p class="small mute">A theorem from one of these modules, used by a key declaration, counts as a use of the input.</p>
<div class="tbl"><table><thead><tr><th>Input</th><th>Source</th><th>Lean modules</th><th>Key declarations using it</th></tr></thead>
<tbody>{"".join(rows)}</tbody></table></div>
<h2 style="margin-top:1.6rem" id="full">Full project graph</h2>
<details><summary>All {len(full)} project theorems and definitions with the project constants each one uses ({edges} edges), by module</summary>
{"".join(modules)}</details>
<p class="small mute" style="margin-top:1.4rem">Generated by <code>scripts/build-lean-dag.py</code> from
<code>verification/lean-dag/graph.json</code>. The graph is a reading aid for the checked proof.</p>
</main>
<script>{OPEN_JS}</script>
</body></html>
'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, help='built checkout with the Lean state of the pinned commit')
    args = parser.parse_args()
    if args.formal:
        extract(args.formal.resolve())
    data = json.loads(DAG.read_text())
    (ROOT / 'lean-dag.html').write_text(page(data))
    print(f'Wrote lean-dag.html: {len(keys(data["compared"]))} key declarations, '
          f'{len({l for v in data["nodes"].values() for l in v["leaves"]})} library inputs, '
          f'{len(data["full"])} project declarations.')
