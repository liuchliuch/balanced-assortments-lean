#!/usr/bin/env python3
"""Re-elaborate every Examples module and retain hard assertion results.
#guard and throwing #eval IO checks are regression tests, not theorem proofs.
No project olean is overwritten; imported dependencies must already be built.
"""
import argparse, hashlib, json, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--out',default='logs/regressions');a=p.parse_args()
r=Path(__file__).resolve().parent.parent
out=Path(a.out);out=out if out.is_absolute() else r/out
out.mkdir(parents=True,exist_ok=True)
results=[]
for src in sorted((r/'BalancedAssortments').rglob('*Examples.lean')):
 rel=src.relative_to(r);log=out/('.'.join(rel.with_suffix('').parts)+'.log')
 before=hashlib.sha256(src.read_bytes()).hexdigest()
 with log.open('w') as f:
  code=subprocess.run(['lake','env','lean','--trust=0','-j1',str(rel)],cwd=r,stdout=f,stderr=subprocess.STDOUT).returncode
 after=hashlib.sha256(src.read_bytes()).hexdigest()
 status='SOURCE_CHANGED_DURING_CHECK' if before!=after else ('PASS' if code==0 else 'FAIL')
 result={'source':str(rel),'sha256_before':before,'sha256_after':after,'exit_code':code,'status':status,'log':str(log)}
 results.append(result);print(result['source'],result['status'],flush=True)
report={'all_pass':bool(results) and all(x['status']=='PASS' for x in results),'scope':'fresh elaboration of all Examples modules; not all-project proof or semantic acceptance','results':results}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(0 if report['all_pass'] else 1)
