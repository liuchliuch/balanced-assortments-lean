#!/usr/bin/env python3
"""Portable source checkpoint packaging, never a proof-completeness claim.
The final flag checks the frozen inventory first. Development links and caches
are excluded; every other symlink is rejected rather than silently followed.
"""
import argparse, hashlib, os, subprocess, tarfile
from pathlib import Path

EXCLUDED_DIRS={'.lake','.toolchain','.git','__pycache__','.pytest_cache','.mypy_cache'}
EXCLUDED_SUFFIXES={'.olean','.ilean','.o','.trace','.hash','.pyc','.pyo'}

def source_files(root):
    result=[]
    for base,dirs,files in os.walk(root,followlinks=False):
        dirs[:]=sorted(d for d in dirs if d not in EXCLUDED_DIRS)
        for name in dirs+sorted(files):
            p=Path(base)/name
            if p.suffix in EXCLUDED_SUFFIXES: continue
            if p.is_symlink(): raise ValueError(f'Source archive refuses symlink: {p.relative_to(root)}')
            if p.is_file(): result.append(p)
    return sorted(result)

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--final',action='store_true');a=p.parse_args()
    root=Path(__file__).resolve().parent.parent;out=Path(a.out).resolve()
    if out.exists(): raise SystemExit('Refusing to overwrite archive: '+str(out))
    if out.is_relative_to(root): raise SystemExit('Archive destination must be outside project to avoid recursive inclusion')
    if a.final: subprocess.run(['python3',str(root/'scripts/snapshot.py'),'--verify'],cwd=root,check=True)
    files=source_files(root)
    with tarfile.open(out,'w:gz',dereference=False) as archive:
        for f in files: archive.add(f,arcname=str(Path(root.name)/f.relative_to(root)),recursive=False)
    with tarfile.open(out,'r:gz') as archive:
        for member in archive:
            path=Path(member.name)
            if member.issym() or path.is_absolute() or '..' in path.parts:
                raise SystemExit('Invalid archive member: '+member.name)
    print(hashlib.sha256(out.read_bytes()).hexdigest()+'  '+str(out))
    print('Packaged '+str(len(files))+' files; this is a source checkpoint, not a proof-completeness certificate.')

if __name__=='__main__': main()
