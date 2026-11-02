#!/usr/bin/env python3
"""Regenerate the site.

Without arguments: render index.html, lean-dag.html and verification/index.html
from the recorded data and link the Lean identifiers (Python 3 and Graphviz).
With --formal PATH (a built checkout with the Lean state of the pinned commit,
see site.json): first re-extract the reference data, the dependency graph and
the verification record from it (elan/Lake on PATH). With --statement-map PATH:
check the Lean names against the paper's statement map (PyYAML).
"""
from pathlib import Path
import argparse, subprocess, sys

HERE = Path(__file__).resolve().parent


def run(script, *args):
    subprocess.run([sys.executable, str(HERE / script), *map(str, args)], check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, help='built checkout with the Lean state of the pinned commit')
    parser.add_argument('--statement-map', type=Path, help="the paper's statement-map.yaml")
    args = parser.parse_args()
    if args.formal:
        run('record-verification.py', '--formal', args.formal)
        run('extract-lean-references.py', '--formal', args.formal)
        run('build-lean-dag.py', '--formal', args.formal)
    else:
        run('build-lean-dag.py')
    run('build-site.py', *(['--statement-map', args.statement_map] if args.statement_map else []))
    run('link-lean-references.py')
