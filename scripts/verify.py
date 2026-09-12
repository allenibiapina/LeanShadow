#!/usr/bin/env python3
"""Build the proof library and audit every local theorem's kernel axioms.

ComparatorChallenges contains reference placeholders and is deliberately outside
this proof-only audit. Run Comparator separately to compare its statements.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCES = [ROOT / 'LeanShadow.lean', *sorted((ROOT / 'LeanShadow').rglob('*.lean'))]
MODULES = tuple(p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.') for p in SOURCES)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def source_hashes():
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCES}


def main():
    expected = set()
    hashes = source_hashes()
    for path in SOURCES:
        source = path.read_text()
        if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s', source, re.MULTILINE):
            raise SystemExit('Forbidden proof shortcut in ' + str(path.relative_to(ROOT)))
        if re.search(r'^import\s+ComparatorChallenges(?:\.|\s)', source, re.MULTILINE):
            raise SystemExit('Proof imports its challenge: ' + str(path.relative_to(ROOT)))
        names = re.findall(r'^theorem\s+(\w+)\b', source, re.MULTILINE)
        namespaces = set(re.findall(r'^namespace\s+(\S+)', source, re.MULTILINE))
        if names and len(namespaces) != 1:
            raise SystemExit('Review theorem namespaces in ' + str(path.relative_to(ROOT)))
        namespace = next(iter(namespaces), '')
        for name in names:
            full = namespace + '.' + name
            if full in expected:
                raise SystemExit('Duplicate theorem: ' + full)
            expected.add(full)
            if '#print axioms ' + full not in source:
                raise SystemExit('Missing axiom report: ' + full)

    config = json.loads((ROOT / 'ComparatorChallenges/LeanShadow.json').read_text())
    required = set(config['theorem_names'])
    if not required <= expected:
        raise SystemExit('Missing main theorem declarations: ' + str(sorted(required - expected)))
    result = subprocess.run(['lake', 'build', 'LeanShadow'], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (ROOT / 'build.log').write_text(result.stdout)
    print(result.stdout, end='')
    if result.returncode:
        raise SystemExit(result.returncode)
    if re.search(r'\b(?:error|warning):', result.stdout):
        raise SystemExit('Build emitted errors or warnings; inspect build.log')
    reports = {}
    for name, raw in re.findall(r"'([\w.]+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        axioms = {v.strip() for v in raw.split(',') if v.strip()}
        if name not in expected:
            continue
        if axioms - ALLOWED:
            raise SystemExit(f'Unexpected axioms in {name}: {sorted(axioms - ALLOWED)}')
        reports[name] = sorted(axioms)
    for name in re.findall(r"'([\w.]+)' does not depend on any axioms", result.stdout):
        if name in expected:
            reports[name] = []
    if set(reports) != expected:
        raise SystemExit('Missing axiom reports: ' + str(sorted(expected - reports.keys())))
    if hashes != source_hashes():
        raise SystemExit('Sources changed during verification; rerun the check')
    record = {
        'status': 'passed',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Proof library only; challenge placeholders are not proofs or proof dependencies.',
        'lean': subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip(),
        'mathlib_commit': 'db584cd6d46c92f209a44c0f1c829460d327499d',
        'build_exit_code': result.returncode,
        'local_module_count': len(SOURCES),
        'local_theorem_count': len(expected),
        'verified_top_level_theorems': sorted(required),
        'source_sha256': hashes,
        'theorem_axioms': reports,
    }
    (ROOT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'PASS: {len(SOURCES)} proof modules, {len(expected)} theorems, '
          f'{len(required)} main results; only standard axioms.')


if __name__ == '__main__':
    main()
