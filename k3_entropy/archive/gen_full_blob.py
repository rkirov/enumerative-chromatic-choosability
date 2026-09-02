import sys, math, time
from indep_orbits import COLS, transition_matchings, is_maximal
import indep_seam as SM
from indep_laws import LAW_COUNTS
import numpy as np
D=108000; SCALE=D//108; E=10**6
def isqrt4(n):
    if n<=0: return 0
    k=int(round(n**0.25))
    while k**4<n: k+=1
    while k>0 and (k-1)**4>=n: k-=1
    return k
def seamrec(li,ri,matching):
    L,R=COLS[li],COLS[ri]; M=SM.Me(L,R,matching)
    cA,cB=LAW_COUNTS[li],LAW_COUNTS[ri]
    aA=np.array(cA,float)/108; aB=np.array(cB,float)/108
    Xf=SM.sinkhorn(M,aA,aB); Rc=np.array(cA)*SCALE; Cc=np.array(cB)*SCALE
    Xi=SM.exactify(Xf,M,Rc,Cc,D)
    if Xi is None: return None
    nr,nc=Xi.shape; toks=[str(nr),str(len(cA))]+[str(x) for x in cA]; ent=[]
    for s in range(nr):
        for t in range(nc):
            v=int(Xi[s,t])
            if v>0:
                num=v*108*(E**4); den=D*cA[s]; k=isqrt4((num+den-1)//den)
                while k**4*den<num: k+=1
                ent.append((s,t,v,k))
    toks.append(str(len(ent)))
    for (s,t,v,k) in ent: toks += [str(s),str(t),str(v),str(k)]
    return " ".join(toks)
CHUNK=1000
seams=[]
for li in range(1,39):
    for ri in range(1,39):
        for mt in transition_matchings(COLS[li],COLS[ri]):
            if is_maximal(COLS[li],COLS[ri],mt): seams.append((li,ri,tuple(mt)))
print(f"total rational seams: {len(seams)}", flush=True)
t0=time.time(); recs=[]; ci=0
for i,(li,ri,mt) in enumerate(seams):
    r=seamrec(li,ri,list(mt))
    if r is not None: recs.append(r)
    if len(recs)==CHUNK:
        open(f"chunk_{ci:03d}.txt","w").write(" ; ".join(recs)); ci+=1; recs=[]
        print(f"  chunk {ci} written ({i+1}/{len(seams)}, {(time.time()-t0)/60:.1f} min)", flush=True)
if recs: open(f"chunk_{ci:03d}.txt","w").write(" ; ".join(recs)); ci+=1
print(f"DONE: {ci} chunks, {(time.time()-t0)/60:.1f} min", flush=True)
