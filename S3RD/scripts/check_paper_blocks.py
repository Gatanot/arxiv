"""Build the paper appendix from Lean data, checking every zero independently."""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
source = (ROOT/'S3RD'/'lean'/'Blocks.lean').read_text(encoding='utf-8')
names = [f'b{m}_{n}' for m, ns in [(4,[6,10,14]),(5,[6,8,10]),(7,[6,10,14])] for n in ns]
blocks = {}
checks = []
lines = ['# Appendix A. Explicit half-weight blocks', '',
         'Generated from `S3RD/lean/Blocks.lean`; all digits in a column run from top to bottom.',
         'Each list closes cyclically. The direct checker inspects every uncolored vertex.', '']

def verify(cs, weight):
    m,n=len(cs[0]),len(cs)
    assert all(len(c)==m and all(x in range(4) for x in c) for c in cs)
    assert sum(x!=0 for c in cs for x in c)==weight
    zeros=0
    for j in range(n):
        for r in range(m):
            if cs[j][r]:continue
            zeros+=1
            colors={cs[(j-1)%n][r],cs[(j+1)%n][r]}
            colors.update(cs[j][s] for s in (r-1,r+1) if 0<=s<m)
            assert {1,2,3} <= colors, (m,n,r,j,colors)
    return zeros

for name in names:
    match=re.search(r'def '+name+r' : List \(List Nat\) := (\[.*\])',source)
    assert match, name
    cs=ast.literal_eval(match.group(1))
    m,n=map(int,name[1:].split('_'))
    assert len(cs)==n and len(cs[0])==m
    zeros=verify(cs,m*n//2)
    blocks[name]=cs
    checks.append({'name':name,'m':m,'n':n,'weight':m*n//2,'zeros_checked':zeros})
    lines += [f'## B({m},{n})', '', f'Weight: {m*n//2}. Lean certificate: `{name}_pack`.', '',
              '```text',' '.join(''.join(map(str,c)) for c in cs),'```','']

for nameset in [['b4_6','b4_10','b4_14'],['b5_6','b5_8'],['b7_6','b7_10','b7_14']]:
    for a in nameset:
        for b in nameset:
            x,y=blocks[a],blocks[b]
            assert x[0]==y[0] and x[-1]==y[-1]
            verify(x+y,len(x[0])*(len(x)+len(y))//2)

classification=(ROOT/'S3RD'/'lean'/'Classification.lean').read_text(encoding='utf-8')
for name,n,w in [('three4',4,6),('three6',6,9),('three_defect',6,10)]:
    match=re.search(r'theorem '+name+r' :.*?ofColumns (\[.*?\]),\?_⟩',classification,re.S)
    assert match,name
    cs=ast.literal_eval(match.group(1))
    assert len(cs)==n
    checks.append({'name':name,'m':3,'n':n,'weight':w,'zeros_checked':verify(cs,w)})
    blocks[name]=cs
verify(blocks['three_defect']+blocks['three4'],16)
assert blocks['three_defect'][0]==blocks['three4'][0]
assert blocks['three_defect'][-1]==blocks['three4'][-1]

appendix=ROOT/'build'/'reports'/'blocks.md'
appendix.parent.mkdir(parents=True,exist_ok=True)
appendix.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
report={'status':'PASS','scope':'Nine appendix blocks, their permitted ordered joins, and three width-three blocks. This is not a test of all infinite parameters.',
        'appendix_sha256':hashlib.sha256(appendix.read_bytes()).hexdigest(),'checks':checks}
(ROOT/'build'/'reports'/'paper_blocks_report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
print(f'PASS: {len(checks)} blocks; appendix written to {appendix}')
