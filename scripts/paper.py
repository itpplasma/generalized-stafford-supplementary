#!/usr/bin/env python3
"""Build the paper and extract its numbered environments for the reader pages.

Exports the pinned commit of the paper repository (site.json `paper`) with
`git archive`, builds main.pdf with latexmk, and reads main.tex, main.aux
(numbers and pages), main.bbl (citation numbers) and statement-map.yaml.
Statements, proofs, titles and references are rendered from the LaTeX
source: pandoc for the text, KaTeX for the mathematics. Nothing about the
paper is kept by hand except data/steps.json, which locates the mapped proof
steps in the text. The script fails on any disagreement between the source,
the .aux file and the statement map.

Writes paper/main.pdf, assets/katex/ (stylesheet and fonts),
verification/paper/paper.json and verification/paper/statement-map.yaml.
"""
from pathlib import Path
import argparse, hashlib, html, json, os, re, shutil, subprocess

import yaml

from common import CACHE, CONFIG, ROOT, git

PAPER = ROOT / 'verification/paper'
STEPS = json.loads((ROOT / 'data/steps.json').read_text())['steps']
KINDS = {'theorem': 'Theorem', 'lemma': 'Lemma', 'proposition': 'Proposition', 'corollary': 'Corollary',
         'definition': 'Definition', 'mainthm': None, 'quotedconj': None}
KATEX = Path(os.environ.get('SUPPLEMENTARY_KATEX', CACHE / 'node/node_modules/katex'))


def group(s, i, opening='{'):
    """End index (exclusive) of the group opening at s[i]; brackets ignore braced text."""
    closing = {'{': '}', '[': ']'}[opening]
    assert s[i] == opening, s[i:i + 30]
    depth = 0
    for j in range(i, len(s)):
        c = s[j]
        if c == '\\':
            continue
        if opening == '{':
            depth += (c == '{') - (c == '}')
            if depth == 0:
                return j + 1
        else:
            if c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
            elif c == ']' and depth == 0:
                return j + 1
    raise ValueError('unbalanced group at ' + s[i:i + 40])


def strip_comments(tex):
    return '\n'.join(re.sub(r'(?<!\\)%.*$', '', line) for line in tex.split('\n'))


def drop_command(tex, name, optional=False):
    """Remove every \\name[opt]{arg}."""
    out, pos = [], 0
    for m in re.finditer(r'\\' + name + r'(?![A-Za-z])', tex):
        if m.start() < pos:
            continue
        j = m.end()
        if optional and j < len(tex) and tex[j] == '[':
            j = group(tex, j, '[')
        if j < len(tex) and tex[j] == '{':
            j = group(tex, j)
        out.append(tex[pos:m.start()])
        pos = j
    return ''.join(out) + tex[pos:]


def tex_text(s):
    """Plain text of a short TeX name such as `Theorem A$'$`."""
    s = s.replace("$'$", '′').replace('~', ' ')
    s = re.sub(r'\\textup\s*', '', s)
    return re.sub(r'\s+', ' ', s.replace('{', '').replace('}', '').replace('$', '')).strip()


def aux_labels(aux):
    out = {}
    for m in re.finditer(r'\\newlabel\{([^}]*)\}', aux):
        i = m.end()
        if aux[i] != '{':
            continue
        end = group(aux, i)
        inner, parts, j = aux[i + 1:end - 1], [], 0
        while j < len(inner) and len(parts) < 3:
            k = group(inner, j)
            parts.append(inner[j + 1:k - 1])
            j = k
        out[m[1]] = dict(number=tex_text(parts[0]), page=int(parts[1]) if parts[1].isdigit() else parts[1])
    return out


def bibliography(bbl):
    items = {}
    for n, m in enumerate(re.finditer(r'\\bibitem\[(.*?)\]\{([^}]*)\}(.*?)\\endbibitem', bbl, re.S), 1):
        who = re.search(r'\\citeauthoryear\{(.*?)\}\{(.*?)\}', m[1], re.S)
        body = re.sub(r'\\doiurl\{([^}]*)\}', r'\\url{https://doi.org/\1}', m[3])
        body = re.sub(r'\\begin\{b\w+\}|\\end\{b\w+\}', '', body)
        body = re.sub(r'\\b(?!egin|ibitem)[a-z]+(?=\{)', '', body)
        items[m[2]] = dict(n=n, author=tex_text(who[1].replace('\n', ' ')) if who else '',
                           year=who[2] if who else '', tex=body.strip())
    return items


class Paper:
    def __init__(self, src):
        self.src = src
        tex = (src / 'main.tex').read_text()
        self.tex = tex
        self.labels = aux_labels((src / 'main.aux').read_text())
        self.bib = bibliography((src / 'main.bbl').read_text())
        pre = tex[:tex.index('\\begin{document}')]
        self.preamble = '\n'.join(l for l in pre.split('\n')
                                  if l.startswith(('\\newcommand', '\\DeclareMathOperator')) and 'mainthm' not in l)
        self.macros = {f'\\{m[1]}': f'\\operatorname{{{m[2]}}}'
                       for m in re.finditer(r'\\DeclareMathOperator\{\\(\w+)\}\{(\w+)\}', pre)}
        self.macros.update({'\\cS': '\\mathcal{S}', '\\op': '\\mathrm{op}'})
        self.parse()

    def line(self, offset):
        return self.tex.count('\n', 0, offset) + 1

    def parse(self):
        tex, doc = self.tex, self.tex.index('\\begin{document}')
        self.sections = [dict(offset=m.start(), title=m[2], label=None) for m in
                         re.finditer(r'\\section(\*?)\{((?:[^{}]|\{[^{}]*\})*)\}', tex)]
        for s in self.sections:
            m = re.search(r'\\label\{(sec:[^}]*)\}', tex[s['offset']:s['offset'] + 300])
            s['label'] = m[1] if m else None
            s['number'] = self.labels[s['label']]['number'] if s['label'] in self.labels else ''
        self.envs, by_name, last = [], {}, None
        pattern = r'\\begin\{(' + '|'.join(list(KINDS) + ['proof']) + r')\}'
        for m in re.finditer(pattern, tex[doc:]):
            kind, start = m[1], doc + m.start()
            end = tex.index('\\end{' + kind + '}', start)
            i, arg = doc + m.end(), None
            if kind in ('mainthm', 'quotedconj'):
                j = group(tex, i)
                arg, i = tex[i + 1:j - 1], j
            elif tex[i] == '[':
                j = group(tex, i, '[')
                arg, i = tex[i + 1:j - 1], j
            body = tex[i:end]
            if kind == 'proof':
                target = last
                if arg:
                    name = re.sub(r'^Proof of\s*', '', re.sub(r'[~\s]+', ' ', arg)).strip()
                    if name not in by_name:
                        raise SystemExit(f'proof of unknown statement: {arg}')
                    target = by_name[name]
                target['proofs'].append(dict(tex=body, lines=[self.line(i), self.line(end)]))
                continue
            label = re.match(r'\s*\\label\{([^}]*)\}', body)
            label = label[1] if label else None
            items = re.findall(r'\\item\s*\\label\{([^}]*)\}', body)
            sec = [s for s in self.sections if s['offset'] < start][-1] if start > self.sections[0]['offset'] else None
            if kind in ('mainthm', 'quotedconj'):
                name = tex_text(arg)
                key = re.sub(r'[~\s]+', ' ', arg).strip()
            else:
                if label is None:
                    raise SystemExit(f'numbered {kind} at line {self.line(start)} without a label')
                name = f'{KINDS[kind]} {self.labels[label]["number"]}'
                key = name
            env = dict(kind=kind, label=label, name=name, arg=arg if kind not in ('mainthm', 'quotedconj') else None,
                       tex=body, items=items, proofs=[], lines=[self.line(start), self.line(end)],
                       section=dict(number=sec['number'], title=plain_section(sec['title']), label=sec['label'])
                       if sec else None)
            if label:
                env['page'] = self.labels[label]['page']
            self.envs.append(env)
            by_name[key] = env
            if label:
                last = env
        self.by_label = {e['label']: e for e in self.envs if e['label']}

    # -- rendering -----------------------------------------------------
    def ref(self, label):
        if label not in self.labels:
            raise SystemExit(f'\\ref to unknown label {label}')
        return self.labels[label]['number']

    def cite(self, opt, keys):
        nums = []
        for k in keys.split(','):
            k = k.strip()
            if k not in self.bib:
                raise SystemExit(f'citation of unknown key {k}')
            nums.append(f'\\href{{#bib-{k}}}{{{self.bib[k]["n"]}}}')
        return '[' + ', '.join(nums) + (', ' + opt if opt else '') + ']'

    def prepare(self, tex, summary=False):
        tex = strip_comments(tex)
        for name, opt in (('formalrefof', False), ('formalref', True), ('noformal', False), ('leanref', False)):
            tex = drop_command(tex, name, opt)
        tex = re.sub(r'\\(smallskip|medskip|bigskip|noindent|raggedbottom)\b', '', tex)
        tex = re.sub(r'\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{(?:[^{}]|\{[^{}]*\})*\}', r'\1', tex)

        def equation(m):
            body = m[1]
            tag = re.search(r'\\label\{([^}]*)\}', body)
            body = re.sub(r'\\label\{[^}]*\}', '', body).strip()
            return f'\\[{body}' + (f'\\tag{{{self.ref(tag[1])}}}' if tag else '') + '\\]'
        tex = re.sub(r'\\begin\{equation\}(.*?)\\end\{equation\}', equation, tex, flags=re.S)

        def enumerate_(m):
            opts, body = m[1] or '', m[2]
            tmpl = re.search(r'label=((?:[^,{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)', opts)
            tmpl = re.sub(r'\\textup\{(.*)\}', r'\1', tmpl[1]) if tmpl else None
            parts = re.split(r'\\item\b', body)[1:]
            out = []
            for n, part in enumerate(parts, 1):
                lab = (tmpl.replace('\\arabic*', str(n)).replace('\\alph*', 'abcdefghij'[n - 1])
                       .replace('\\roman*', ['i', 'ii', 'iii', 'iv', 'v', 'vi'][n - 1])) if tmpl else f'{n}.'
                anchor = re.match(r'\s*\\label\{([^}]*)\}', part)
                if anchor:
                    part = part[anchor.end():]
                    lab = f'@@ITEM:{anchor[1]}@@' + lab
                out.append((lab, part.strip()))
            if summary:
                return ' '.join(f'{l} {p}' for l, p in out)
            return ('\\begin{description}' + ''.join(f'\\item[{l}] {p}\n' for l, p in out)
                    + '\\end{description}')
        tex = re.sub(r'\\begin\{enumerate\}(?:\[((?:[^\[\]]|\{[^{}]*\})*)\])?(.*?)\\end\{enumerate\}',
                     enumerate_, tex, flags=re.S)
        tex = re.sub(r'\\label\{[^}]*\}', '', tex)
        tex = re.sub(r'\\eqref\{([^}]*)\}', lambda m: f'({self.ref(m[1])})', tex)
        tex = re.sub(r'\\ref\{([^}]*)\}', lambda m: f'\\href{{#paper-{m[1]}}}{{{self.ref(m[1])}}}', tex)
        tex = re.sub(r'\\cite(?:\[([^\]]*)\])?\{([^}]*)\}', lambda m: self.cite(m[1], m[2]), tex)
        if summary:
            tex = re.sub(r'\\\[(.*?)\\\]', lambda m: f'${m[1].strip()}$', tex, flags=re.S)
            tex = re.sub(r'\n\s*\n', ' ', tex)
        return tex

    def pandoc(self, tex):
        run = subprocess.run(['pandoc', '-f', 'latex', '-t', 'html', '--math-method=katex', '--wrap=none'],
                             input=self.preamble + '\n' + tex, capture_output=True, text=True)
        if run.returncode:
            raise SystemExit(f'pandoc failed: {run.stderr.strip()}\n--- fragment ---\n{tex[:800]}')
        out = run.stdout
        out = re.sub(r'@@ITEM:([^@]*)@@', lambda m: f'<span class="item-anchor" id="paper-{m[1]}"></span>', out)
        return out.replace('<a href="#', '<a class="xref" href="#')


def render_all(paper, fragments, inline):
    """Render {key: tex} to HTML; `inline` keys become one paragraph without <p>."""
    htmls = {k: paper.pandoc(v) for k, v in fragments.items()}
    maths = []
    rx = re.compile(r'<span class="math (inline|display)">(.*?)</span>', re.S)
    for h in htmls.values():
        for m in rx.finditer(h):
            tex = html.unescape(m[2]).strip()
            tex = re.sub(r'^\\\(|\\\)$', '', tex)
            tex = re.sub(r'^\\\[|\\\]$', '', tex)
            maths.append(dict(tex=tex, display=m[1] == 'display'))
    out = subprocess.run(['node', str(ROOT / 'scripts/render-math.mjs'), str(KATEX)],
                         input=json.dumps(dict(macros=paper.macros, items=maths)),
                         capture_output=True, text=True, check=True).stdout
    rendered = json.loads(out)
    it = iter(rendered['html'])
    result = {}
    for k, h in htmls.items():
        h = rx.sub(lambda m: next(it), h)
        if k in inline:
            h = re.sub(r'^\s*<p>|</p>\s*$', '', h.strip())
        result[k] = h.strip()
    return result, rendered['version']


def plain_title(tex):
    i = tex.index('\\title')
    i = group(tex, i + len('\\title'), '[') if tex[i + len('\\title')] == '[' else i + len('\\title')
    return re.sub(r'\s+', ' ', tex[i + 1:group(tex, i) - 1]).replace("'", '’')


def plain_section(title):
    title = re.sub(r'\\texorpdfstring\{(?:[^{}]|\{[^{}]*\})*\}\{((?:[^{}]|\{[^{}]*\})*)\}', r'\1', title)
    return tex_text(title)


def cite_pairs(arg):
    """(key, locator) pairs of the \\cite commands in an environment argument."""
    return [(k.strip(), (m[1] or '').replace('~', ' ').strip()) for m in
            re.finditer(r'\\cite(?:\[([^\]]*)\])?\{([^}]*)\}', arg or '') for k in m[2].split(',')]


def map_pairs(cite):
    return [(m[1], m[2].strip()) for m in re.finditer(r'\[(\w+),\s*([^\]]*)\]', cite)]


MAIN_REFS = {'thm:Aprime': r"A\$'\$", 'thm:A': r"(?:Theorems?~A|and~A)(?!\$|[\w])", 'cor:B': r'Corollary~B\b',
             'cor:C': r'Corollary~C\b'}


def dependencies(paper):
    """Edges of the printed proofs: the statements each statement or proof refers to."""
    item_parent = {i: e['label'] for e in paper.envs for i in e['items']}
    nodes = {e['label'] for e in paper.envs if e['label']}
    edges = set()
    for e in paper.envs:
        if not e['label']:
            continue
        text = strip_comments(e['tex'] + ''.join(p['tex'] for p in e['proofs']))
        found = {item_parent.get(r, r) for r in re.findall(r'\\(?:ref|eqref)\{([^}]*)\}', text)}
        found |= {lab for lab, rx in MAIN_REFS.items() if re.search(rx, text)}
        for f in found:
            if f in nodes and f != e['label']:
                edges.add((f, e['label']))
    return sorted(edges)


def build(paper_repo):
    p = CONFIG['paper']
    commit = p['commit']
    src = CACHE / f'paper-{commit[:12]}'
    shutil.rmtree(src, ignore_errors=True)
    src.mkdir(parents=True)
    archive = subprocess.run(['git', '-C', str(paper_repo), 'archive', commit], capture_output=True, check=True).stdout
    subprocess.run(['tar', '-x', '-C', str(src)], input=archive, check=True)
    env = dict(os.environ, SOURCE_DATE_EPOCH=git(paper_repo, 'log', '-1', '--format=%ct', commit).strip(),
               FORCE_SOURCE_DATE='1')
    log = subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error', 'main.tex'],
                         cwd=src, env=env, capture_output=True, text=True)
    if log.returncode:
        raise SystemExit('latexmk failed:\n' + log.stdout[-3000:])
    warnings = re.findall(r'LaTeX Warning: (Reference|Citation) .*? undefined', (src / 'main.log').read_text())
    if warnings:
        raise SystemExit('undefined references or citations in the paper build')
    return src


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper', type=Path, required=True, help='clone of the paper repository')
    args = parser.parse_args()
    src = build(args.paper.resolve())
    paper = Paper(src)
    smap = yaml.safe_load((src / CONFIG['paper']['map']).read_text())
    if smap['pin'] != CONFIG['formal']['commit']:
        raise SystemExit(f'statement map pin {smap["pin"]} differs from the formal pin {CONFIG["formal"]["commit"]}')

    # The map and the paper must agree on labels and citations.
    problems = []
    item_parent = {i: e for e in paper.envs for i in e['items']}
    for e in smap['environments']:
        lab = e['label']
        env = paper.by_label.get(lab) or item_parent.get(lab)
        if env is None:
            problems.append(f'{lab}: in the statement map, not in main.tex')
            continue
        if 'cite' in e and map_pairs(e['cite']) != cite_pairs(env['arg']):
            problems.append(f'{lab}: map cite {e["cite"]!r} differs from the paper {cite_pairs(env["arg"])}')
        if 'cite' not in e and lab in paper.by_label and cite_pairs(env['arg']):
            problems.append(f'{lab}: cited in the paper, no cite in the map')
    mapped = {e['label'] for e in smap['environments']}
    for env in paper.envs:
        lab = env['label']
        if lab and env['kind'] not in ('definition',) and lab not in mapped and not (env['items'] and set(env['items']) <= mapped):
            problems.append(f'{lab}: numbered {env["kind"]} without a statement-map entry')
    for s in smap.get('proof_steps', []):
        if s['step'] not in STEPS:
            problems.append(f'proof step {s["step"]}: no entry in data/steps.json')
    if problems:
        raise SystemExit('paper and statement map disagree:\n  ' + '\n  '.join(problems))

    # Fragments to render.
    frags, inline = {}, set()
    for e in paper.envs:
        key = e['label'] or e['name']
        body = e['tex']
        frags[f'env:{key}'] = paper.prepare(body)
        frags[f'sum:{key}'] = paper.prepare(body, summary=True)
        inline.add(f'sum:{key}')
        if e['arg']:
            frags[f'arg:{key}'] = paper.prepare(e['arg'], summary=True)
            inline.add(f'arg:{key}')
        for n, pr in enumerate(e['proofs']):
            frags[f'proof:{key}:{n}'] = paper.prepare(pr['tex'])
        for item in e['items']:
            m = re.search(r'\\item\s*\\label\{' + re.escape(item) + r'\}(.*?)(?=\\item\b|\\end\{enumerate\})', body, re.S)
            frags[f'item:{item}'] = paper.prepare(m[1])
            frags[f'itemsum:{item}'] = paper.prepare(m[1], summary=True)
            inline.add(f'itemsum:{item}')
    steps = {}
    for step, loc in STEPS.items():
        env = paper.by_label[loc['env']]
        if loc['part'] == 'statement':
            text, lines = env['tex'], env['lines']
            sub = []
        else:
            whole = ''.join(p['tex'] for p in env['proofs'])
            a = whole.find(loc['from'])
            if a < 0:
                raise SystemExit(f'step {step}: {loc["from"]!r} not found in the proof of {loc["env"]}')
            b = whole.find(loc['to'], a) if 'to' in loc else len(whole)
            if b < 0:
                raise SystemExit(f'step {step}: {loc["to"]!r} not found in the proof of {loc["env"]}')
            text = whole[a:b]
            start = paper.tex.index(text)
            lines = [paper.line(start), paper.line(start + len(text))]
            sub = []
            if 'split' in loc:
                cuts = [m.start() for m in re.finditer(re.escape(loc['split']), text)]
                for n, (x, y) in enumerate(zip(cuts, cuts[1:] + [len(text)]), 1):
                    num = re.match(re.escape(loc['split']) + r'(\d+)', text[x:])
                    sub.append(int(num[1]))
                    frags[f'sub:{step}:{num[1]}'] = paper.prepare(text[x:y])
        frags[f'step:{step}'] = paper.prepare(text)
        steps[step] = dict(env=loc['env'], part=loc['part'], lines=lines, substeps=sub)
    attributions = []
    for key in CONFIG['paper'].get('attributions', []):
        for para in re.split(r'\n\s*\n', paper.tex[paper.tex.index('\\begin{document}'):]):
            if '{' + key + '}' in para and '\\begin{' not in para:
                n = len(attributions)
                frags[f'attr:{n}'] = paper.prepare(para)
                attributions.append(dict(key=key, lines=[paper.line(paper.tex.index(para)),
                                                         paper.line(paper.tex.index(para) + len(para))]))
    for key, b in paper.bib.items():
        frags[f'bib:{key}'] = b['tex']
        inline.add(f'bib:{key}')
    t0 = paper.tex.index('\\begin{tabular}') + len('\\begin{tabular}')
    tab = paper.tex[group(paper.tex, t0):paper.tex.index('\\end{tabular}', t0)]
    hyps = [row.split('&') for row in strip_comments(tab).split('\\\\') if '&' in row]
    for n, (a, b) in enumerate(hyps):
        frags[f'hyp:{n}:0'], frags[f'hyp:{n}:1'] = paper.prepare(a), paper.prepare(b.strip().rstrip(';.'))
        inline |= {f'hyp:{n}:0', f'hyp:{n}:1'}
    conv = re.search(r'\n(Throughout,.*?)\n\s*\n', paper.tex, re.S)[1]
    frags['conventions'] = paper.prepare(conv)
    inline.add('conventions')

    rendered, version = render_all(paper, frags, inline)
    envs = []
    for e in paper.envs:
        key = e['label'] or e['name']
        envs.append(dict(
            kind=e['kind'], label=e['label'], name=e['name'], page=e.get('page'), lines=e['lines'],
            section=e['section'], title=rendered.get(f'arg:{key}'), cite=cite_pairs(e['arg']),
            statement=rendered[f'env:{key}'], summary=rendered[f'sum:{key}'],
            proofs=[dict(html=rendered[f'proof:{key}:{n}'], lines=p['lines']) for n, p in enumerate(e['proofs'])],
            items=[dict(label=i, number=paper.labels[i]['number'], statement=rendered[f'item:{i}'],
                        summary=rendered[f'itemsum:{i}']) for i in e['items']]))
    for step, s in steps.items():
        s['html'] = rendered[f'step:{step}']
        s['substeps'] = [dict(n=n, html=rendered[f'sub:{step}:{n}']) for n in s['substeps']]
    for n, a in enumerate(attributions):
        a['html'] = rendered[f'attr:{n}']
    out = ROOT / 'paper'
    out.mkdir(exist_ok=True)
    shutil.copy(src / 'main.pdf', out / 'main.pdf')
    assets = ROOT / 'assets/katex'
    shutil.rmtree(assets, ignore_errors=True)
    (assets / 'fonts').mkdir(parents=True)
    shutil.copy(KATEX / 'dist/katex.min.css', assets / 'katex.min.css')
    for font in (KATEX / 'dist/fonts').glob('*.woff2'):
        shutil.copy(font, assets / 'fonts' / font.name)
    shutil.copy(KATEX / 'LICENSE', assets / 'LICENSE')
    PAPER.mkdir(parents=True, exist_ok=True)
    shutil.copy(src / CONFIG['paper']['map'], PAPER / 'statement-map.yaml')
    record = dict(
        schema=1, repo=CONFIG['paper']['repo'], commit=CONFIG['paper']['commit'],
        commit_date=git(args.paper.resolve(), 'log', '-1', '--format=%cI', CONFIG['paper']['commit']).strip(),
        pdf=dict(path='paper/main.pdf', sha256=hashlib.sha256((out / 'main.pdf').read_bytes()).hexdigest(),
                 pages=int(re.search(r'Output written on main\.pdf \((\d+) pages', (src / 'main.log').read_text())[1])),
        katex=version,
        source='Rendered from main.tex at the commit with pandoc and KaTeX; numbers and pages from main.aux, '
               'citation numbers from main.bbl.',
        hypotheses=[[rendered[f'hyp:{n}:0'], rendered[f'hyp:{n}:1']] for n in range(len(hyps))],
        conventions=rendered['conventions'],
        bib={k: dict(n=b['n'], author=b['author'], year=b['year'], html=rendered[f'bib:{k}'])
             for k, b in paper.bib.items()},
        title=plain_title(paper.tex),
        sections=[dict(label=x['label'], number=x['number'], title=plain_section(x['title']))
                  for x in paper.sections if x['label']],
        envs=envs, steps=steps, attributions=attributions,
        edges=dependencies(paper))
    (PAPER / 'paper.json').write_text(json.dumps(record, ensure_ascii=False, indent=0) + '\n')
    print(f'Paper {CONFIG["paper"]["commit"][:7]}: {record["pdf"]["pages"]} pages, {len(envs)} environments, '
          f'{len(steps)} proof steps, {len(record["edges"])} printed dependencies, KaTeX {version}.')


if __name__ == '__main__':
    main()
