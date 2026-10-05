#!/usr/bin/env python3
"""Hash every accepted project source, regression, verification tool and pinned config."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent.parent
paths={root/'BalancedAssortments.lean',*(root/'BalancedAssortments').rglob('*.lean')}
paths.update(p for p in (root/'scripts').rglob('*') if p.is_file() and p.suffix in {'.lean','.py','.sh','.json'})
paths.update(p for p in (root/'Audit').rglob('*') if p.is_file() and p.suffix in {'.lean','.json'})
paths.update(root/p for p in ('lakefile.toml','lean-toolchain','lake-manifest.json','verification/library-provenance.json'))
for p in sorted(paths): print(hashlib.sha256(p.read_bytes()).hexdigest(),' ',p.relative_to(root),sep='')
