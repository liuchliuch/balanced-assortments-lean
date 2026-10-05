#!/usr/bin/env python3
"""Source-only preflight. Kernel/axiom checks remain separate and mandatory."""
from pathlib import Path
import re, sys, json
root = Path(__file__).resolve().parent.parent

def strip_comments_and_strings(text):
    out=[]; i=0; depth=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; i+=2
            elif text.startswith('-/',i): depth-=1; i+=2
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text.startswith('/-',i): depth=1; i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i); i=len(text) if end<0 else end
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\': i+=2
                elif text[i]=='"': i+=1; break
                else: i+=1
            out.append(' ')
        else: out.append(text[i]); i+=1
    return ''.join(out)
production=sorted((root/'BalancedAssortments').rglob('*.lean'))
files=production+[root/'BalancedAssortments.lean']+sorted((root/'scripts').glob('*.lean'))+sorted((root/'Audit').glob('*.lean'))
imports=set(re.findall(r'^import\s+(\S+)\s*$',(root/'BalancedAssortments.lean').read_text(),re.M))
missing=[]; forbidden=[]
for p in files:
    module='.'.join(p.relative_to(root).with_suffix('').parts)
    if p in production and module not in imports: missing.append(module)
    code=strip_comments_and_strings(p.read_text())
    for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide)\b',code):
        rel=p.relative_to(root).as_posix()
        if m.group()=='sorry' and rel in {'Audit/Statements.lean','Audit/NegativeStatements.lean'}: continue
        if m.group()=='axiom' and rel=='Audit/NegativeAxiom.lean': continue
        forbidden.append({'file':str(p.relative_to(root)),'token':m.group(),'line':code[:m.start()].count('\n')+1})
result={'source_modules':len(production),'checked_lean_files':len(files),'not_explicitly_imported_by_aggregate':missing,'forbidden_source_tokens':forbidden,
        'note':'A module count is not a count of completed paper results.'}
print(json.dumps(result,indent=2))
if forbidden or ('--release' in sys.argv and missing): sys.exit(1)
