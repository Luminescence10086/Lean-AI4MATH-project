"""(R) 检验: Σ_p E_p >= D − (ω(n)−1), E_p = L_p − ((p−1)v_p(n)+1) >= 0,
   D = Σ_ν min((m_ν−b(ν))₊, ω(ν)−1).  及 TGT/(P_p)/等价核查."""
import random, sys
from math import gcd
from collections import Counter
def factor(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def boundv(n): return 1+sum(e*(p-1) for p,e in factor(n).items())
def vp(n,p):
    e=0
    while n%p==0: n//=p; e+=1
    return e
def lcmlist(xs):
    r=1
    for x in xs: r=r*x//gcd(r,x)
    return r
def check_ess(fam,N):
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    if not all(c>0 for c in cnt): return False
    return all(any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam)
def analyze(fam,n):
    mv=Counter(d for a,d in fam)
    S=sum(min(c,boundv(nu)) for nu,c in mv.items())
    b_n=boundv(n); D=0
    for nu,c in mv.items():
        w=len(factor(nu)); D+=min(max(0,c-boundv(nu)), w-1)
    sumE=0; Pp_ok=True; sumL=0
    for p in factor(n):
        Lp=sum(min(c,(p-1)*vp(nu,p)+1) for nu,c in mv.items() if nu%p==0)
        sumL+=Lp; bp_n=(p-1)*vp(n,p)+1; sumE+=Lp-bp_n
        if Lp<bp_n: Pp_ok=False
    wn=len(factor(n))
    R_ok = sumE >= D-(wn-1)
    TGT = S>=b_n
    return TGT,R_ok,Pp_ok,(S,b_n,D,sumE,wn,sumL)
def covers(n,K,cap=600000):
    full=(1<<n)-1
    aps=[(a,d) for d in [dd for dd in range(1,n+1) if n%dd==0] for a in range(d)]
    masks=[]
    for (a,d) in aps:
        m=0
        for t in range(n//d): m|=1<<((a+t*d)%n)
        masks.append(m)
    out=[]
    def dfs(start,covered,chosen):
        if len(out)>cap: return
        if covered==full: out.append(tuple(chosen)); return
        if len(chosen)>=K: return
        for idx in range(start,len(aps)):
            if masks[idx]&~covered:
                dfs(idx+1,covered|masks[idx],chosen+[idx])
    dfs(0,0,[])
    return aps,out
for (n,K) in [(12,7),(18,7),(24,7),(30,7),(36,8),(48,9)]:
    aps,cv=covers(n,K)
    ntest=0;nR=0;nTGT=0;nPp=0;ex=[];mind=None
    for ch in cv:
        fam=[aps[i] for i in ch]
        if lcmlist([d for a,d in fam])!=n: continue
        if not check_ess(fam,n): continue
        ntest+=1
        TGT,R,Ppok,info=analyze(fam,n)
        S,b_n,D,sumE,wn,sumL=info
        gap=sumE-(D-(wn-1))
        mind=gap if mind is None else min(mind,gap)
        if not R:
            nR+=1
            if len(ex)<3: ex.append((fam,info))
        if not TGT: nTGT+=1
        if not Ppok: nPp+=1
    print(f"[枚举] n={n} K={K}: 全本质 {ntest}; (R)违 {nR}; TGT违 {nTGT}; (P_p)违 {nPp}; min(R缺口)={mind}",flush=True)
    for f,i in ex: print("   (R)反例:",f,"S,b,D,ΣE,ω,ΣL =",i)
