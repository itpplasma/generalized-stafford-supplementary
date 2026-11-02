"""Shared configuration, paths and helpers of the supplementary scripts."""
from pathlib import Path
import html, json, os, subprocess, tempfile

ROOT = Path(__file__).resolve().parent.parent
CONFIG = json.loads((ROOT / 'site.json').read_text())
OVERVIEW = json.loads((ROOT / 'data/overview.json').read_text())
CITATIONS = json.loads((ROOT / 'data/citations.json').read_text())
REFS = ROOT / 'verification/lean-references/references.json'
DAG = ROOT / 'verification/lean-dag/graph.json'
RECORD = ROOT / 'verification/record.json'
# Generated scratch (Lean name lists, raw graphs) goes outside the repository.
CACHE = Path(os.environ.get('SUPPLEMENTARY_CACHE', '/mnt/storage/cache/generalized-stafford-supplementary'))
PAGES = {'formal': CONFIG['formal']['pages'], 'library': CONFIG['library']['pages']}


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True)


def esc(text):
    return html.escape(str(text), quote=False)


def attr(text):
    return html.escape(str(text), quote=True)


def scratch():
    CACHE.mkdir(parents=True, exist_ok=True)
    return tempfile.TemporaryDirectory(dir=CACHE)


def lean_run(formal, script, *args):
    subprocess.run(['lake', 'env', 'lean', '--run', str(ROOT / 'scripts' / script), *map(str, args)],
                   cwd=formal, check=True)


def check_formal(formal):
    """The checkout must have exactly the Lean state of the pinned commit.

    A checkout at a later commit is accepted when no Lean file, lakefile,
    manifest or toolchain differs from the pin; its own head is returned."""
    pin = CONFIG['formal']['commit']
    head = git(formal, 'rev-parse', 'HEAD').strip()
    if head != pin:
        diff = git(formal, 'diff', '--name-only', pin, 'HEAD', '--', *CONFIG['formal']['lean_state']).split()
        if diff:
            raise SystemExit(f'formal checkout {head} differs from pin {pin} in: {", ".join(diff)}')
    dirty = git(formal, 'status', '--porcelain', '--untracked-files=no', '--', *CONFIG['formal']['lean_state'])
    if dirty.strip():
        raise SystemExit('formal checkout has local changes to Lean files:\n' + dirty)
    lib = formal / '.lake/packages' / CONFIG['library']['package']
    if git(lib, 'rev-parse', 'HEAD').strip() != CONFIG['library']['commit']:
        raise SystemExit(f'{CONFIG["library"]["label"]} package differs from the pinned library commit')
    return head


def all_lean_names():
    """Every Lean name the overview data mentions."""
    names = set()
    for group in ('results', 'lemmas', 'formal_only'):
        for item in OVERVIEW[group]:
            for key in ('challenge', 'library', 'lean'):
                if isinstance(item.get(key), list):
                    names.update(item[key])
            names.update(s['decl'] for s in item.get('steps', []))
    for c in CITATIONS['citations'].values():
        names.update(c['lean'])
    return sorted(names)


def comparator_names(formal=None):
    if formal is None:
        return json.loads(RECORD.read_text())['comparator']['theorem_names']
    return json.loads((formal / CONFIG['formal']['comparator']).read_text())['theorem_names']


def rel_href(target, here):
    """Relative link from directory `here` to repository path `target`."""
    rel = os.path.relpath(ROOT / target, here)
    return rel if rel.startswith('.') else './' + rel


# Colour tokens shared by every generated page; light and dark mode.
TOKENS_LIGHT = ('--bg:#fbfaf7;--fg:#1d1d1f;--mute:#5f6368;--line:#dedad2;--card:#ffffff;--soft:#f3f1ec;'
                '--accent:#2d5f9e;--ok:#2f7a4a;--warn:#a06a00;'
                '--hyp:#e6f2ea;--hypk:#2f7a4a;--step:#ffffff;--stepk:#8a8f98;--goal:#ece6f7;--goalk:#5b3fa0;'
                '--dep:#e5eef9;--depk:#2d5f9e;--cited:#fbf0d9;--citedk:#a06a00;--std:#f1f1ef;--stdk:#7b7b74;'
                '--edge:#6d6f73;--hl:#fff0ad')
TOKENS_DARK = ('color-scheme:dark;--bg:#17181a;--fg:#e8e6e1;--mute:#a3a7ad;--line:#3a3c40;--card:#1f2023;'
               '--soft:#232427;--accent:#86aee6;--ok:#7cc797;--warn:#e2b65a;'
               '--hyp:#1e3326;--hypk:#7cc797;--step:#232427;--stepk:#7d828a;--goal:#2c2540;--goalk:#b9a2f0;'
               '--dep:#1d2a3b;--depk:#86aee6;--cited:#3a2f17;--citedk:#e2b65a;--std:#28292b;--stdk:#a19f97;'
               '--edge:#9a9da2;--hl:#4a4220')
TOKENS = (f':root{{{TOKENS_LIGHT}}}'
          f'@media (prefers-color-scheme:dark){{:root:not([data-theme="light"]){{{TOKENS_DARK}}}}}'
          f':root[data-theme="dark"]{{{TOKENS_DARK}}}')

# Base layout shared by the top-level pages.
BASE_CSS = TOKENS + '''
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.5 system-ui,-apple-system,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
main{max-width:1280px;margin:0 auto;padding:18px 16px 64px}
a{color:var(--accent)}code,pre,.mono{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:.86em}
h1{font-size:1.45rem;line-height:1.25;margin:0}h2{font-size:1.08rem;margin:0 0 .5rem}h3{font-size:.98rem;margin:0}
p{margin:.4rem 0}.mute{color:var(--mute)}.small{font-size:.85rem}
nav.top{display:flex;flex-wrap:wrap;gap:.2rem 1rem;font-size:.9rem;margin:0 0 .6rem}
nav.top a{text-decoration:none}nav.top a[aria-current]{color:var(--fg);font-weight:600}
.panel{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:12px 14px}
details>summary{cursor:pointer}details>summary::marker{color:var(--mute)}
pre.lean-src{background:var(--soft);border:1px solid var(--line);border-radius:6px;padding:8px 10px;
margin:.4rem 0;white-space:pre-wrap;overflow-wrap:anywhere;font-size:12.5px;line-height:1.45}
table{border-collapse:collapse;width:100%}td,th{text-align:left;vertical-align:top;padding:.3rem .45rem;border-bottom:1px solid var(--line)}
th{font-weight:600;font-size:.85rem;color:var(--mute)}
.tbl{overflow-x:auto}
.fig{overflow-x:auto}.fig svg{display:block;height:auto;margin:0 auto}
.legend{display:flex;flex-wrap:wrap;gap:.3rem .9rem;font-size:.82rem;margin:.5rem 0;padding:0;list-style:none}
.legend li::before{content:"";display:inline-block;width:.9em;height:.9em;margin-right:.35em;
vertical-align:-.1em;border:1.5px solid var(--k);background:var(--f);border-radius:3px}
a.decl{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:.82em;overflow-wrap:anywhere}
'''
