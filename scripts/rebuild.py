#!/usr/bin/env python3
"""Regenerate the site.

Without arguments: render index.html, lean-dag.html and verification/index.html
from the recorded data and link the Lean identifiers (Python 3 with PyYAML,
Graphviz). With --paper PATH (a clone of the paper repository): first build the
paper at the pinned commit and re-extract its environments (latexmk, pandoc,
Node.js with KaTeX). With --formal PATH (a built checkout with the Lean state of
the pinned formal commit): first re-extract the Lean reference data, the
dependency graph and the verification record (elan/Lake on PATH).
"""
from pathlib import Path
import argparse, subprocess, sys

HERE = Path(__file__).resolve().parent


def run(script, *args):
    subprocess.run([sys.executable, str(HERE / script), *map(str, args)], check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, help='built checkout with the Lean state of the pinned commit')
    parser.add_argument('--paper', type=Path, help='clone of the paper repository')
    args = parser.parse_args()
    if args.paper:
        run('paper.py', '--paper', args.paper)
    if args.formal:
        run('record-verification.py', '--formal', args.formal)
        run('extract-lean-references.py', '--formal', args.formal)
        run('build-lean-dag.py', '--formal', args.formal)
    else:
        run('build-lean-dag.py')
    run('build-site.py')
    run('link-lean-references.py')
