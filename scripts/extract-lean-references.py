#!/usr/bin/env python3
"""Record Lean's own identifier references for the reader pages.

Reads the .ilean files of a *built* formal checkout whose Lean state is the
pinned commit of site.json: every identifier occurrence that Lean elaborated
to a constant, together with the module and line that declare it, as reported
by Lean itself (scripts/LeanDeclRanges.lean). No name is resolved lexically.
Writes verification/lean-references/references.json and plain source pages
for the project and library files; scripts/link-lean-references.py then adds
the links and hover previews.
"""
from pathlib import Path
import argparse, json, re, shutil

from common import CONFIG, PAGES, REFS, ROOT, all_lean_names, check_formal, comparator_names, git, lean_run, scratch
import leanhl

def utf16_to_index(line, col):
    """Convert an LSP UTF-16 column to a code point index."""
    units = 0
    for i, ch in enumerate(line):
        if units >= col:
            return i
        units += 2 if ord(ch) > 0xFFFF else 1
    return len(line)


PROOF_KEYWORDS = ('theorem', 'lemma', 'instance', 'example')
DECL = re.compile(r'(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public)\s+)*'
                  r'(theorem|lemma|instance|example|def|abbrev|structure|class|inductive|opaque|axiom)\b')


def preview(text_lines, start):
    """Doc comment (at most 4 lines) and declaration (at most 14 lines) starting
    at `start`. Theorems stop at `:=`; definitions keep their body up to a
    blank line or the next top-level command."""
    out, i = [], start - 1
    if i < len(text_lines) and text_lines[i].lstrip().startswith('/--'):
        doc = []
        while i < len(text_lines):
            doc.append(text_lines[i])
            i += 1
            if '-/' in doc[-1]:
                break
        out = doc if len(doc) <= 4 else doc[:3] + ['  …', doc[-1]]
    while i < len(text_lines) and text_lines[i].lstrip().startswith(('include ', 'omit ', '@[')) \
            and not DECL.match(text_lines[i].strip()):
        i += 1
    head = DECL.match(text_lines[i].strip()) if i < len(text_lines) else None
    proof = head is None or head[1] in PROOF_KEYWORDS
    for k, line in enumerate(text_lines[i:i + 14]):
        if k and (not line.strip() or (line[:1].strip() and not line.startswith(('|', ')')))):
            return '\n'.join(out)
        cut = line.find(':=')
        if proof and cut >= 0:
            out.append(line[:cut + 2])
            return '\n'.join(out)
        out.append(line)
        body = line.strip()
        if proof and (body.endswith(' where') or body == 'where'):
            return '\n'.join(out)
    more = i + 14 < len(text_lines) and text_lines[i + 14].strip() and not text_lines[i + 14][:1].strip()
    return '\n'.join(out + (['…'] if more or proof else []))


def checkout_roots(checkout):
    """Module roots of a built checkout: (repo key, source dir, ilean dir, link base).
    Keys without a link base get bundled pages; the others link to GitHub."""
    lake = json.loads((checkout / 'lake-manifest.json').read_text())
    roots = [('formal', checkout, checkout / '.lake/build/lib/lean', None)]
    for pkg in lake['packages']:
        pdir = checkout / '.lake/packages' / pkg['name']
        if git(pdir, 'rev-parse', 'HEAD').strip() != pkg['rev']:
            raise SystemExit(f'package {pkg["name"]} is not at its manifest revision')
        bundled = pkg['name'] == CONFIG['library']['package']
        roots.append(('library' if bundled else pkg['name'], pdir, pdir / '.lake/build/lib/lean',
                      None if bundled else pkg['url'].removesuffix('.git') + '/blob/' + pkg['rev'] + '/'))
    toolchain = (checkout / 'lean-toolchain').read_text().strip()
    tc_dir = Path.home() / '.elan/toolchains' / toolchain.replace('/', '--').replace(':', '---')
    roots.append(('lean4', tc_dir / 'src/lean', tc_dir / 'lib/lean',
                  f'https://github.com/leanprover/lean4/blob/{toolchain.split(":")[1]}/src/'))
    return roots


def read_usages(base, repo, rel, usages, local):
    """Single-line usages of constants in one file, as Lean recorded them."""
    ilean = base[2] / rel.replace('.lean', '.ilean')
    if not ilean.exists():
        return False
    lines = (base[1] / rel).read_text().split('\n')
    found = usages[f'{repo}:{rel}'] = []
    data = json.loads(ilean.read_text())
    local[f'{repo}:{rel}'] = {n: [r[0] + 1, r[2] + 1] for n, r in data['decls'].items()}
    for key, ref in data['references'].items():
        ident = json.loads(key).get('c')
        for l0, c0, l1, c1, *_ in (ref['usages'] if ident else ()):
            if l0 == l1 and l0 < len(lines):
                a, b = utf16_to_index(lines[l0], c0), utf16_to_index(lines[l0], c1)
                found.append((l0 + 1, a, b - a, ident['n']))
    return True


def lean_ranges(checkout, groups, names):
    """Declaring module and line of each name, from Lean, importing `groups` in turn."""
    ranges = {}
    with scratch() as tmp:
        work, mods, out = Path(tmp) / 'names.txt', Path(tmp) / 'modules.txt', Path(tmp) / 'ranges.json'
        for group in groups:
            todo = [n for n in names if n not in ranges]
            work.write_text('\n'.join(todo) + '\n')
            mods.write_text('\n'.join(group) + '\n')
            lean_run(checkout, 'LeanDeclRanges.lean', mods, work, out)
            ranges.update(json.loads(out.read_text()))
    return ranges


def locate(roots, module):
    for key, src, ilean, url in roots:
        if (ilean / (module.replace('.', '/') + '.ilean')).exists():
            return key, module.replace('.', '/') + '.lean'
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, required=True,
                        help='built checkout with the Lean state of the pinned formal commit (lake build)')
    args = parser.parse_args()
    formal = args.formal.resolve()
    head = check_formal(formal)
    pin = CONFIG['formal']['commit']
    toolchain = (formal / 'lean-toolchain').read_text().strip()
    roots = checkout_roots(formal)
    skip = tuple(CONFIG['formal'].get('skip_prefixes', []))
    lib_dir = formal / '.lake/packages' / CONFIG['library']['package']
    linked = {'formal': [f for f in git(formal, 'ls-files', '*.lean').split() if not f.startswith(skip)],
              'library': git(lib_dir, 'ls-files', '*.lean').split()}

    # Pass 1: every single-line usage of a constant, as Lean recorded it.
    usages, local, missing = {}, {}, set()
    for repo, names in linked.items():
        base = next(r for r in roots if r[0] == repo)
        for rel in names:
            if not read_usages(base, repo, rel, usages, local):
                missing.add(f'{repo}:{rel}')

    # Pass 2: Lean itself reports the declaring module and line of each
    # constant, including the names the overview cites directly.
    wanted = set(all_lean_names()) | set(comparator_names(formal))
    names = sorted({u[3] for found in usages.values() for u in found} | wanted)
    # Library files built but not imported by the project resolve in their own environment.
    lib_root = next(r for r in roots if r[0] == 'library')
    built_lib = [rel.removesuffix('.lean').replace('/', '.') for rel in linked['library']
                 if (lib_root[2] / rel.replace('.lean', '.olean')).exists()]
    ranges = lean_ranges(formal, CONFIG['formal']['import_groups'] + [built_lib], names)
    targets, index = [], {}
    for name in names:
        if name in ranges and (owner := locate(roots, ranges[name][0])):
            index[name] = len(targets)
            targets.append([name, owner[0], owner[1], ranges[name][1]])
    absent = sorted(n for n in wanted if n not in index)
    if absent:
        raise SystemExit('names cited by data/overview.json without a declaration: ' + ', '.join(absent))

    # A name the file declares itself refers to that declaration (the
    # standalone challenge and solution files repeat the challenge definitions).
    def resolve(key, name):
        if name in local[key]:
            if (key, name) not in index:
                repo, rel = key.split(':', 1)
                index[key, name] = len(targets)
                targets.append([name, repo, rel, local[key][name][0]])
            return index[key, name]
        return index.get(name)
    files = {}
    for key, found in usages.items():
        spans = {(l, c, n, resolve(key, t)) for l, c, n, t in found}
        files[key] = sorted(sp for sp in spans if sp[3] is not None)
    # The overview links the challenge statements at their place in the
    # challenge file, so each of its declarations gets a target there.
    challenge = 'formal:' + CONFIG['formal']['challenge']['file']
    for name in local.get(challenge, {}):
        resolve(challenge, name)
    unresolved = sorted(n for n in names if n not in index)
    urls = {r[0]: r[3] for r in roots if r[3]}
    sources = {r[0]: r[1] for r in roots}
    previews, cache = {}, {}
    for i, (name, repo, rel, line) in enumerate(targets):
        if (repo, rel) not in cache:
            path = sources[repo] / rel
            cache[repo, rel] = path.read_text().split('\n') if path.exists() else None
        if cache[repo, rel]:
            previews[i] = preview(cache[repo, rel], line)
    decls = {k: v for k, v in local.items() if k.startswith(('formal:', 'library:'))}
    REFS.parent.mkdir(parents=True, exist_ok=True)
    REFS.write_text(json.dumps(dict(
        schema=1, formal_commit=pin, checkout_commit=head, library_commit=CONFIG['library']['commit'],
        toolchain=toolchain,
        source='Usages from the .ilean files of the built checkout; declaration lines from Lean '
               'findDeclarationRanges?. Columns are code points. decls: line ranges of the '
               'declarations of each project and library file, from its .ilean.',
        urls=urls, targets=targets, previews=previews, unresolved=unresolved, decls=decls, files=files),
        ensure_ascii=False, separators=(',', ':')) + '\n')

    labels = {'formal': (CONFIG['formal']['label'], pin),
              'library': (CONFIG['library']['label'], CONFIG['library']['commit'])}
    repos = {'formal': (CONFIG['formal']['repo'], pin), 'library': (CONFIG['library']['repo'], CONFIG['library']['commit'])}
    written = 0
    for repo, names in linked.items():
        shutil.rmtree(ROOT / PAGES[repo], ignore_errors=True)
        src = sources[repo]
        for rel in names:
            if f'{repo}:{rel}' in files:
                dest = ROOT / PAGES[repo] / (rel + '.html')
                dest.parent.mkdir(parents=True, exist_ok=True)
                depth = len(Path(PAGES[repo], rel).parts) - 1
                gh = f'https://github.com/{repos[repo][0]}/blob/{repos[repo][1]}/{rel}'
                dest.write_text(leanhl.page(rel, *labels[repo], (src / rel).read_text().split('\n'), depth, gh))
                written += 1
    print(f'{sum(map(len, files.values()))} references in {len(files)} files to {len(targets)} '
          f'declarations; {len(unresolved)} without a source line; {len(missing)} files without .ilean '
          f'(not built); {written} source pages.')


if __name__ == '__main__':
    main()
