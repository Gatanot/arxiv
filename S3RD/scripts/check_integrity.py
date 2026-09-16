"""Verify distributed files and the source hashes of the recorded Lean audit."""
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    root = Path(__file__).resolve().parents[1]
    expected = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    for name, sha in expected.items():
        path = (root / name).resolve()
        require(path.is_relative_to(root), 'Invalid manifest path: ' + name)
        require(path.is_file(), 'Missing file: ' + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == sha, 'Changed file: ' + name)
    report = json.loads((root / 'reports/lean_report.json').read_text(encoding='utf-8'))
    checks = report['checks']
    sources = {p.stem for p in (root / 'S3RD/lean').glob('*.lean')}
    require(report['status'] == 'PASS' and len(checks) == 19, 'Incomplete Lean audit')
    require({c['module'] for c in checks} == sources, 'Lean module set mismatch')
    for check in checks:
        path = root / 'S3RD/lean' / (check['module'] + '.lean')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == check['sha256'],
                'Proof differs from audit: ' + check['module'])
    print(f'PASS {len(expected)} distributed file hashes and all 19 audited Lean sources')
    print('This checks source identity; run check_lean.py to rebuild the proofs.')


if __name__ == '__main__':
    main()
