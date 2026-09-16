"""Independent finite transfer check of the paper's labeled half-weight count.

The general count is proved by color propagation in the paper, not by this test.
No changes to Lean sources are made.
"""
from pathlib import Path
import json

columns=[(0,c,0) for c in (1,2,3)]+[(a,0,b) for a in (1,2,3) for b in (1,2,3)]
states=[(a,b) for a in range(12) for b in range(12)]
index={s:i for i,s in enumerate(states)}

def valid_middle(a,b,c):
    x,y,z=[columns[q] for q in (a,b,c)]
    if any((u==0)==(v==0) for u,v in zip(x,y)):return False
    if any((u==0)==(v==0) for u,v in zip(y,z)):return False
    for r in range(3):
        if y[r]:continue
        colors={x[r],z[r]}|{y[t] for t in (r-1,r+1) if 0<=t<3}
        if not {1,2,3}<=colors:return False
    return True

edges=[(index[a,b],index[b,c]) for a,b in states for c in range(12) if valid_middle(a,b,c)]
# Trace of A^n counts closed walks with a distinguished starting column.
counts=[0]*37
for start in range(144):
    ways=[0]*144;ways[start]=1
    for n in range(1,37):
        nxt=[0]*144
        for a,b in edges:nxt[b]+=ways[a]
        ways=nxt;counts[n]+=ways[start]
checks=[]
for n in range(3,37):
    expected=12*(n%4==0)+12*(n%6==0)
    assert counts[n]==expected,(n,counts[n],expected)
    checks.append({'n':n,'count':counts[n]})
root=Path(__file__).resolve().parents[1]
(root/'build/reports').mkdir(parents=True,exist_ok=True)
(root/'build/reports/width3_counts.json').write_text(json.dumps({
    'status':'PASS','scope':'Finite cross-check for 3<=n<=36 of labeled half-weight colorings; unrestricted support reduction is supplied by the paper and Lean.',
    'states':144,'edges':len(edges),'checks':checks},indent=2)+'\n',encoding='utf-8',newline='\n')
print('PASS: labeled half-weight counts for circumferences 3 through 36.')
