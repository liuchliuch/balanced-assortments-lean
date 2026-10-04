#!/usr/bin/env python3
"""Freeze or verify proof/config/original hashes and read-only dependency pins."""
import argparse,hashlib,json,subprocess,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--verify',action='store_true');p.add_argument('--pins-only',action='store_true');args=p.parse_args()
if args.verify and args.pins_only: p.error('--verify and --pins-only are mutually exclusive')
r=Path(__file__).resolve().parent.parent
inventory=r/'docs/release-candidate/source-inventory.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[r/'BalancedAssortments.lean',*sorted((r/'BalancedAssortments').rglob('*.lean')),
 r/'lean-toolchain',r/'lakefile.toml',r/'lake-manifest.json',r/'STATUS.md',r/'README.md',
 *sorted(p for p in (r/'docs').rglob('*') if 'release-candidate' not in p.parts),
 *sorted((r/'scripts').glob('*.py')),*sorted((r/'scripts').glob('*.sh')),*sorted((r/'scripts').glob('*.lean')),
 *sorted((r/'paper').rglob('*'))]
files=[p for p in files if p.is_file()]
rows={str(p.relative_to(r)):sha(p) for p in files}
manifest=json.loads((r/'lake-manifest.json').read_text());packages=[]
for entry in manifest['packages']:
 d=r/'.lake/packages'/entry['name']
 def git(*a):return subprocess.check_output(['git','-C',str(d),*a],text=True).strip()
 rev=git('rev-parse','HEAD');tree=git('rev-parse','HEAD^{tree}')
 dirty=git('status','--porcelain','--untracked-files=no')
 if rev!=entry['rev'] or dirty:raise SystemExit(f'PIN/WORKTREE MISMATCH: {entry["name"]}: {rev} {dirty}')
 packages.append({'name':entry['name'],'commit':rev,'tree':tree,'tracked_worktree_clean':True})
lean=r/'.toolchain/lean-4.24.0-linux/bin/lean'
if not lean.is_file():
 # Resolve the actual pinned compiler, not the Elan dispatch shim.
 if shutil.which('elan'):
  lean=Path(subprocess.check_output(['elan','which','lean'],cwd=r,text=True).strip())
 else:
  found=shutil.which('lean')
  if not found: raise SystemExit('Lean unavailable: run scripts/bootstrap.sh first')
  lean=Path(found).resolve()
lean=lean.resolve()
toolchain={'version':subprocess.check_output([str(lean),'--version'],text=True).strip(),
 'git_hash':subprocess.check_output([str(lean),'--githash'],text=True).strip(),'lean_binary_sha256':sha(lean)}
if 'version 4.24.0,' not in toolchain['version']:
 raise SystemExit('PINNED LEAN VERSION MISMATCH: '+toolchain['version'])
now={'sources':rows,'packages':packages,'toolchain':toolchain}
if args.pins_only:
 print(json.dumps({'status':'PASS','scope':'current compiler version and tracked dependency pins only; no source freeze or final audit', 'packages':packages,'toolchain':toolchain},indent=2))
 raise SystemExit(0)
if args.verify:
 old=json.loads(inventory.read_text())
 if old!=now:
  changes=[k for k in set(old['sources'])|set(rows) if old['sources'].get(k)!=rows.get(k)]
  raise SystemExit('FROZEN INVENTORY MISMATCH '+repr(changes))
 print(json.dumps({'status':'PASS','source_files':len(rows),'pinned_packages':len(packages),
  'source_inventory_sha256':sha(inventory)},indent=2))
else:
 inventory.parent.mkdir(parents=True,exist_ok=True)
 inventory.write_text(json.dumps(now,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'FROZEN','source_files':len(rows),'pinned_packages':len(packages),
  'source_inventory_sha256':sha(inventory)},indent=2))
