"""Python replica of the Lean enumerator of Grid3/Three/Cert/KeysCore.lean; compares its output with the stored record keys."""
import itertools, re, time, collections
from pathlib import Path
def mult(m,p): return (m//4**p)%4
def mcount(M,p,q): return (M//4**(7*p+q))%4
def sumRow(M,p): return sum(mcount(M,p,q) for q in range(7))
def sumCol(M,q): return sum(mcount(M,p,q) for p in range(7))
def inter(p,q): return ((p+1)&(q+1))!=0
def digit(r,q): return (r//4**q)%4
def valid_type(m): return all(sum(mult(m,p) for p in range(7) if (p+1)&(1<<r))==3 for r in range(3))
def validKey(mL,mR,M):
    return all(inter(p,q) or mcount(M,p,q)==0 for p in range(7) for q in range(7)) and \
           all(sumRow(M,p)<=mult(mL,p) for p in range(7)) and all(sumCol(M,q)<=mult(mR,q) for q in range(7))
def keyMax(mL,mR,M):
    return all((not inter(p,q)) or sumRow(M,p)==mult(mL,p) or sumCol(M,q)==mult(mR,q) for p in range(7) for q in range(7))
def rowOK(p,cap,r): return all(inter(p,q) or digit(r,q)==0 for q in range(7)) and sum(digit(r,q) for q in range(7))<=cap
rowVecs={(p,cap):[r for r in range(16384) if rowOK(p,cap,r)] for p in range(7) for cap in range(4)}
def enumRows(mL,n,p,res):
    if n==0: return [0]
    out=[]
    for r in rowVecs[(p,mult(mL,p))]:
        if all(digit(r,q)<=res[q] for q in range(7)):
            res2=[res[q]-digit(r,q) for q in range(7)]
            out.extend(r+16384*rest for rest in enumRows(mL,n-1,p+1,res2))
    return out
def enumCands(mL,mR): return enumRows(mL,7,0,[mult(mR,q) for q in range(7)])
def enumKeys(mL,mR): return [M for M in enumCands(mL,mR) if keyMax(mL,mR,M)]
if __name__=='__main__':
    types=[m for m in range(16384) if valid_type(m)]
    assert len(types)==39
    data=Path(__file__).resolve().parents[1] / 'Data'
    stored=collections.defaultdict(list)
    for path in sorted(data.glob('C*.lean')):
        for ml,mr,mat in re.findall(r"checkRecord \d+ (\d+) (\d+) (\d+) \d+ \w+ = true", path.read_text()):
            stored[(int(ml),int(mr))].append(int(mat))
    t0=time.time(); tot=0; maxc=0; maxk=0; worst=None
    for a in types:
        for b in types:
            c=enumCands(a,b); k=[M for M in c if keyMax(a,b,M)]
            tot+=len(k); 
            if len(c)>maxc: maxc=len(c); worst=(a,b)
            maxk=max(maxk,len(k))
            assert all(validKey(a,b,M) for M in k)
            if (a,b)==(12288,12288): assert len(k)==1, k; continue
            assert sorted(k)==sorted(stored[(a,b)]), (a,b)
    print('replica matches stored key sets for all 1520 pairs; total maximal keys',tot,'max cands per pair',maxc,worst,'max keys per pair',maxk,'time %.1fs'%(time.time()-t0))
    print('rowVecs sizes', {k:len(v) for k,v in rowVecs.items() if len(v)>1})
