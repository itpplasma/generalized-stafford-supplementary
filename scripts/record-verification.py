#!/usr/bin/env python3
"""Record the pins and the formal repository's verification record.

Reads the pinned commit from git (not from the working tree), recomputes the
challenge sha256 and the byte identity of the challenge and solution copies,
and copies the formal repository's docs/verification.md at the commit that
records the pin. Writes verification/record.json and
verification/formal-verification.md. The verifier commands themselves
(scripts/verify.sh, scripts/verify-palomar.sh) are not re-run here; their
results are quoted from the record.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

from common import CONFIG, RECORD, ROOT, check_formal, git


def blob(repo, commit, path):
    return subprocess.check_output(['git', '-C', str(repo), 'show', f'{commit}:{path}'])


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, required=True, help='checkout of the formal repository')
    args = parser.parse_args()
    formal = args.formal.resolve()
    head = check_formal(formal)
    f = CONFIG['formal']
    pin = f['commit']
    rec = f['verification_record']
    if subprocess.run(['git', '-C', str(formal), 'merge-base', '--is-ancestor', pin, rec['commit']]).returncode:
        raise SystemExit('the verification record commit does not descend from the pin')
    changed = git(formal, 'diff', '--name-only', pin, rec['commit'], '--', *f['lean_state']).split()
    if changed:
        raise SystemExit('the verification record commit changes Lean files: ' + ', '.join(changed))

    challenge = blob(formal, pin, f['challenge']['file'])
    got = sha(challenge)
    if got != f['challenge']['sha256']:
        raise SystemExit(f'challenge sha256 at the pin is {got}, expected {f["challenge"]["sha256"]}')
    copies = {
        f['challenge']['copy']: sha(blob(formal, pin, f['challenge']['copy'])) == got,
        f['solution']['copy']: blob(formal, pin, f['solution']['copy']) == blob(formal, pin, f['solution']['file']),
    }
    manifest = json.loads(blob(formal, pin, 'lake-manifest.json'))
    packages = {p['name']: dict(url=p['url'], rev=p['rev']) for p in manifest['packages']}
    if packages[CONFIG['library']['package']]['rev'] != CONFIG['library']['commit']:
        raise SystemExit('lake-manifest.json at the pin does not pin the configured library commit')
    comparator = json.loads(blob(formal, pin, f['comparator']))
    endpoints = blob(formal, pin, 'docs/endpoints.txt').decode().split()
    text = blob(formal, rec['commit'], rec['path']).decode()
    (ROOT / 'verification/formal-verification.md').write_text(text)
    section = re.search(r'## ' + re.escape(rec['section']) + r'\n(.*?)\n## ', text, re.S)[1].strip()
    commands = re.search(r'```sh\n(.*?)```', section, re.S)[1].strip().split('\n')
    # The record names the pin by its abbreviated hash.
    if pin[:7] not in section or got not in section:
        raise SystemExit('the release verification record does not name the pin and the challenge sha256')
    gates = re.search(r'## Gates\n(.*?)\n## ', text, re.S)[1].strip()

    record = dict(
        schema=1,
        formal=dict(repo=f['repo'], commit=pin, commit_date=git(formal, 'log', '-1', '--format=%cI', pin).strip(),
                    toolchain=blob(formal, pin, 'lean-toolchain').decode().strip(),
                    built_checkout_commit=head,
                    built_checkout_note='Built checkout used for the reference data; its Lean files, lakefile, '
                                        'manifest and toolchain are identical to the pin (git diff).'),
        library=dict(repo=CONFIG['library']['repo'], commit=CONFIG['library']['commit']),
        packages=packages,
        challenge=dict(file=f['challenge']['file'], sha256=got, matches_expected=True,
                       identical_copies=copies),
        comparator=dict(file=f['comparator'], **comparator),
        endpoints=dict(file='docs/endpoints.txt', count=len(endpoints)),
        verification_record=dict(path=rec['path'], commit=rec['commit'], note=rec['note'],
                                 sha256=sha(text.encode()), copy='verification/formal-verification.md',
                                 commands=commands, release_record=section, gates=gates),
        checked_here=[
            'challenge sha256 recomputed from the git blob at the pin',
            'challenge and solution copies byte-identical at the pin',
            'library pin in lake-manifest.json at the pin',
            'built checkout has the Lean state of the pin and the pinned library package',
            'verification record commit descends from the pin and changes no Lean file',
        ],
        not_rerun=['scripts/verify.sh', 'scripts/bootstrap-palomar-tools.sh', 'scripts/verify-palomar.sh'],
    )
    RECORD.parent.mkdir(parents=True, exist_ok=True)
    RECORD.write_text(json.dumps(record, indent=1, ensure_ascii=False) + '\n')
    print(f'Recorded pin {pin[:12]}, challenge sha256 {got[:12]}…, '
          f'{len(comparator["theorem_names"])} compared theorems, {len(endpoints)} endpoints.')


if __name__ == '__main__':
    main()
