#!/usr/bin/env python3
"""Replay verified local modules with Lean's bundled checker, one process per module.

Imports are not replayed from an empty environment. For comparison with separate
reference statements and the external nanoda kernel, use Comparator instead.
"""
import argparse
import json
import subprocess
from verify import MODULES as PROOF_MODULES, ROOT, source_hashes

# The entry-only umbrella would select every submodule at once in leanchecker.
MODULES = tuple(m for m in PROOF_MODULES if m != "LeanShadow")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    hashes = source_hashes()
    verified = json.loads((ROOT / 'verification.json').read_text())
    if verified['source_sha256'] != hashes or verified['build_exit_code'] != 0:
        raise SystemExit('Run scripts/verify.py successfully on these sources first')
    record = {'checker': 'Lean bundled leanchecker', 'source_sha256': hashes,
              'scope': 'Local declarations replayed in imported environments; not an independent kernel.',
              'modules': [], 'complete': False}
    if args.resume:
        record = json.loads((ROOT / 'replay-status.json').read_text())
        done = record['modules']
        if record['source_sha256'] != hashes or any(m['exit_code'] for m in done):
            raise SystemExit('Cannot resume a changed or failed replay')
        if [m['module'] for m in done] != list(MODULES[:len(done)]):
            raise SystemExit('Invalid replay prefix')
        if not (ROOT / 'replay.log').is_file():
            raise SystemExit('Missing replay log')
    with (ROOT / 'replay.log').open('a' if args.resume else 'w') as log:
        for module in MODULES[len(record['modules']):]:
            command = ['lake', 'env', 'leanchecker', '--verbose', module]
            print('Replaying ' + module, flush=True)
            result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            log.write('Command: ' + ' '.join(command) + '\n' + result.stdout +
                      'Exit code: ' + str(result.returncode) + '\n\n')
            log.flush()
            record['modules'].append({'module': module, 'command': command, 'exit_code': result.returncode})
            record['exit_code'] = result.returncode
            (ROOT / 'replay-status.json').write_text(json.dumps(record, indent=2) + '\n')
            if result.returncode:
                raise SystemExit(result.returncode)
    if source_hashes() != hashes:
        raise SystemExit('Sources changed during replay')
    record['complete'] = True
    (ROOT / 'replay-status.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'PASS: {len(MODULES)} local modules replayed.')


if __name__ == '__main__':
    main()
