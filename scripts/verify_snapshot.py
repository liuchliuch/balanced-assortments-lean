#!/usr/bin/env python3
"""Bounded, dependency-aware verification of an immutable source snapshot.
This checks all project modules including private/off-namespace declarations.
It is a mechanical check, never a source-semantic completeness certificate.
"""
import argparse, hashlib, json, os, shutil, subprocess, time
from verification_scheduler import run_dag
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--trust-zero',action='store_true');p.add_argument('--jobs',type=int,choices=(1,2),default=1);a=p.parse_args()
r=Path(__file__).resolve().parent.parent; out=Path(a.out).resolve()
if out.exists(): raise SystemExit('Refusing to overwrite existing snapshot')
out.mkdir(parents=True);(out/'logs').mkdir();build=out/'build';build.mkdir()
files=[*sorted((r/'BalancedAssortments').rglob('*.lean')),r/'BalancedAssortments.lean',r/'scripts/AxiomAudit.lean']
mods={'.'.join(f.relative_to(r).with_suffix('').parts):f for f in files if f!=r/'scripts/AxiomAudit.lean'}
# Generate aggregate from the actual source inventory, including newly added modules.
aggregate=''.join(f'import {m}\n' for m in sorted(mods) if m!='BalancedAssortments')
for f in files:
 d=out/f.relative_to(r);d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,d)
(out/'BalancedAssortments.lean').write_text(aggregate)
hashes={str(f.relative_to(out)):hashlib.sha256(f.read_bytes()).hexdigest() for f in out.rglob('*.lean')}
(out/'source-inventory.json').write_text(json.dumps(hashes,indent=2)+'\n')
lean=r/'.toolchain/lean-4.24.0-linux/bin/lean'
if not lean.is_file():
 if shutil.which('elan'):
  lean=Path(subprocess.check_output(['elan','which','lean'],cwd=r,text=True).strip())
 else:
  found=shutil.which('lean')
  if not found: raise SystemExit('Lean unavailable: run scripts/bootstrap.sh first')
  lean=Path(found)
lean=lean.resolve()
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(build),*[str(d) for d in sorted((r/'.lake/packages').glob('*/.lake/build/lib/lean'))]])
deps={}
for m in mods:
 source=(out/Path(*m.split('.')).with_suffix('.lean')).read_text()
 deps[m]=[line.split()[1] for line in source.splitlines() if line.startswith('import ') and line.split()[1] in mods]
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for d in deps[m]:visit(d)
 order.append(m)
for m in sorted(mods):visit(m)
start=time.time()
def compile_module(m):
 src=Path(*m.split('.')).with_suffix('.lean');dst=build/Path(*m.split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 with (out/'logs'/f'{m}.log').open('w') as log:
  code=subprocess.run([str(lean),'-j1',*(['--trust=0'] if a.trust_zero else []),'-o',str(dst),str(src)],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
 return {'status':'PASS' if code==0 else 'FAIL','exit_code':code}
results=run_dag(order,deps,compile_module,a.jobs,lambda m,r: print(m,r['status'],flush=True))
# All compiler jobs have joined before the aggregate-origin audits begin.
allpass=all(x['status']=='PASS' for x in results.values())
if allpass:
 for label,extra in [('origin-axioms',[]),*([('trust-zero',['--trust=0'])] if a.trust_zero else [])]:
  with (out/'logs'/f'{label}.log').open('w') as log:
   code=subprocess.run([str(lean),'-j1',*extra,'scripts/AxiomAudit.lean'],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
  results[label]={'status':'PASS' if code==0 else 'FAIL','exit_code':code}
if not allpass:
 passed=[m for m in order if results[m]['status']=='PASS']
 partial=out/'PartialVerified.lean';partial.write_text(''.join(f'import {m}\n' for m in passed))
 with (out/'logs'/'partial-imports.log').open('w') as log:
  code=subprocess.run([str(lean),'-j1','-o',str(build/'PartialVerified.olean'),'PartialVerified.lean'],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
 if code==0:
  audit=(out/'scripts/AxiomAudit.lean').read_text().replace('import BalancedAssortments\n','import PartialVerified\n',1)
  (out/'scripts/PartialAxiomAudit.lean').write_text(audit)
  for label,extra in [('partial-origin-axioms',[]),*([('partial-trust-zero',['--trust=0'])] if a.trust_zero else [])]:
   with (out/'logs'/f'{label}.log').open('w') as log:
    code=subprocess.run([str(lean),'-j1',*extra,'scripts/PartialAxiomAudit.lean'],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
   results[label]={'status':'PASS' if code==0 else 'FAIL','exit_code':code,'scope':'ONLY successfully rebuilt module closure; not full-project validation'}
 (out/'partial-scope.json').write_text(json.dumps({'modules':passed,'full_project':False},indent=2)+'\n')
report={'results':results,'elapsed_seconds':time.time()-start,'all_mechanical_checks_pass':all(x['status']=='PASS' for x in results.values()),'semantic_completeness_claimed':False,'fresh_module_trust_zero':a.trust_zero,'compiler_jobs':a.jobs}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
raise SystemExit(0 if report['all_mechanical_checks_pass'] else 1)
