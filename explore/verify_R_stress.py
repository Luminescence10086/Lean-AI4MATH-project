""" (R) 随机压力: n ∈ {84,96,120,180,240,360,420}, 分层随机全本质族.
    (R): Σ_p E_p >= D − (ω(n)−1); 同时核 TGT, (P_p), E_p = spread_p + main_p 分解."""
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
    sumE=0;Pp=True;spread_tot=0;main_tot=0
    for p in factor(n):
        Lp=0; main=0
        levels=sorted({vp(nu,p) for nu in mv if nu%p==0})
        for beta in levels:
            B=(p-1)*beta+1
            grp=[c for nu,c in mv.items() if vp(nu,p)==beta]
            Lp+=sum(min(c,B) for c in grp)
            main+=min(sum(grp),B)
        bp_n=(p-1)*vp(n,p)+1
        if Lp<bp_n: Pp=False
        sumE+=Lp-bp_n
        spread_tot+=Lp-main
        main_tot+=main-bp_n
    wn=len(factor(n))
    R_ok=sumE>=D-(wn-1)
    TGT=S>=b_n
    return TGT,R_ok,Pp,(S,b_n,D,sumE,wn,spread_tot,main_tot)
random.seed(2026)
for N in [84,96,120,180,240,360,420]:
    divs=[d for d in range(2,N+1) if N%d==0]
    ntest=0;nT=0;nR=0;nP=0;best=None
    for trial in range(80000):
        k=random.randint(2,5)
        fam=[];used=set()
        for _ in range(k):
            d=random.choice(divs); a=random.randrange(d)
            cnt=random.randint(1,min(d, max(1,int(1.5*boundv(d)-N//d))))
            for _ in range(cnt):
                aa=(a+random.randrange(d))%d
                if (aa,d) not in used: fam.append((aa,d)); used.add((aa,d))
        fam=list(set(fam))
        covered=set()
        for a,d in fam:
            for t in range(N//d): covered.add((a+t*d)%N)
        G=[c for c in range(N) if c not in covered]
        fam2=fam+[(g,N) for g in G]
        if lcmlist([d for a,d in fam2])!=N: continue
        if not check_ess(fam2,N): continue
        ntest+=1
        TGT,R_ok,Pp,info=analyze(fam2,N)
        if not TGT: nT+=1
        if not R_ok:
            nR+=1
            if best is None: best=(fam2[:12],info)
        if not Pp: nP+=1
    print(f"n={N}: 全本质 {ntest}; TGT违 {nT}; (R)违 {nR}; (P_p)违 {nP}", flush=True)
    if best: print("  (R)反例:",best)
