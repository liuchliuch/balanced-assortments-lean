#!/usr/bin/env python3
"""Maintain the aggregate from the complete recursive project module inventory.
Default is read-only; --write regenerates it before a coordinated source freeze.
"""
import argparse
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
r=Path(__file__).resolve().parent.parent
modules=sorted('.'.join(f.relative_to(r).with_suffix('').parts) for f in (r/'BalancedAssortments').rglob('*.lean'))
text=''.join('import '+m+'\n' for m in modules)
aggregate=r/'BalancedAssortments.lean'
if a.write: aggregate.write_text(text)
elif aggregate.read_text()!=text: raise SystemExit('Aggregate differs from recursive inventory; run scripts/update_imports.py --write before freezing')
print(('WROTE' if a.write else 'PASS')+': '+str(len(modules))+' recursively inventoried modules')
