#!/usr/bin/env python3
"""Verify unchanged mathematical inputs and rerun the portable release checks."""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
LIBRARY = 'BalancedAssortments'
PACKAGE = 'balanced-assortments'

def check_inputs():
    original = json.loads((ROOT/'docs/release-candidate/source-inventory.json').read_text())['sources']
    paths = {name for name in original if name.endswith('.lean')} | {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}
    actual = {p.relative_to(ROOT).as_posix() for folder in [ROOT/LIBRARY, ROOT/'scripts'] for p in folder.rglob('*.lean')} | {LIBRARY+'.lean'}
    assert {name for name in paths if name.endswith('.lean')} == actual, 'Mathematical input inventory differs from the recorded release'
    for name in sorted(paths):
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == original[name], 'Recorded mathematical input changed: '+name
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    for package in manifest['packages']:
        directory = ROOT/manifest['packagesDir']/package['name']
        head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        assert head == package['rev'], 'Dependency pin differs: '+package['name']
        dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True)
        assert not dirty.strip(), 'Dependency source is modified: '+package['name']
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True)
    assert 'version 4.24.0,' in version and '797c613eb9b6' in version, 'Pinned compiler differs'
    print('UNCHANGED_MATHEMATICAL_INPUTS_PASS files='+str(len(paths)), flush=True)
    return paths

def run(command):
    print('+ '+' '.join(command), flush=True)
    subprocess.run(command, cwd=ROOT, check=True)

def check_checksums(filename):
    for line in (ROOT/filename).read_text().splitlines():
        if not line.strip():
            continue
        expected, relative = line.split(maxsplit=1)
        relative = relative.removeprefix('*')
        path = (ROOT/relative).resolve()
        assert path.is_relative_to(ROOT), 'Checksum path escapes the project'
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, 'Original source checksum differs: '+relative
        print('ORIGINAL_SOURCE_CHECKSUM_PASS '+relative, flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-clean', action='store_true', help='Reuse existing project objects for a local recheck')
    args=parser.parse_args()
    os.chdir(ROOT)
    paths=check_inputs()
    run([sys.executable, 'scripts/check_project.py', '--release'])
    if not args.no_clean:
        run(['lake', 'clean', PACKAGE])
    run(['lake', 'build', LIBRARY])
    run(['lake', 'env', 'lean', '--trust=0', 'scripts/AxiomAudit.lean'])
    run([sys.executable, 'scripts/regressions.py', '--out', '.lake/publication/regressions'])
    check_checksums('paper/SHA256SUMS')
    check_inputs()
    directory=ROOT/'.lake/publication';directory.mkdir(parents=True, exist_ok=True)
    (directory/'result.json').write_text(json.dumps({'status':'PASS','mathematical_inputs':len(paths),'clean_project_build':not args.no_clean,'kernel':'pinned Lean kernel, trust=0','permitted_axioms':['propext','Classical.choice','Quot.sound']}, indent=2)+'\n')
    print('PUBLICATION_VERIFICATION_PASS', flush=True)

if __name__=='__main__':
    main()
