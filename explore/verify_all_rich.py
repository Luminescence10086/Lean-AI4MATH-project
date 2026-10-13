"""混合差贪心采样器: 重验证 TGT/(R)/(P_p)/(Rp)/(R'') 于多样形状(非补类).
   采样: 随机块 + 贪心用随机差补全覆盖(非仅差-N)."""
import random,sys
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
def rich_sample(N,divs,maxblocks=40):
    """随机块 + 贪心补全(随机差, 优先覆盖未覆盖点)."""
    fam=[]; used=set()
    k=random.randint(1,5)
    for _ in range(k):
        d=random.choice(divs); a=random.randrange(d)
        if (a,d) not in used: fam.append((a,d)); used.add((a,d))
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    for _ in range(maxblocks):
        unc=[x for x in range(N) if cnt[x]==0]
        if not unc: break
        u=random.choice(unc)
        d=random.choice(divs)
        a=u%d
        # 加最多 k2 个该差的块
        for _ in range(random.randint(1,3)):
            aa=(a+random.randrange(d))%d
            if (aa,d) in used: continue
            bm=0
            for t in range(N//d):
                if cnt[(aa+t*d)%N]==0: bm+=1
            if bm==0: continue
            fam.append((aa,d)); used.add((aa,d))
            for t in range(N//d): cnt[(aa+t*d)%N]+=1
    if any(c==0 for c in cnt): return None
    # 全本质检查 + 求私有点
    priv=[]
    for a,d in fam:
        ps={x for t in range(N//d) if cnt[(x:=(a+t*d)%N)]==1}
        priv.append(ps)
    if not all(ps for ps in priv): return None
    return fam
def analyze_full(fam,N):
    mv=Counter(d for a,d in fam)
    # TGT
    S=sum(min(c,boundv(nu)) for nu,c in mv.items())
    TGT=S>=boundv(N)
    # (P_p),(Rp),(R),plus per-p (R'')
    Pp=True;Rp_ok=True;R_ok=True;Rpp=True
    D=0
    for nu,c in mv.items():
        w=len(factor(nu)); D+=min(max(0,c-boundv(nu)), w-1)
    sumL=0; sumE=0
    for p in factor(N):
        alpha=vp(N,p)
        Lp=sum(min(c,(p-1)*vp(nu,p)+1) for nu,c in mv.items() if nu%p==0)
        bp=(p-1)*alpha+1
        if Lp<bp: Pp=False
        t=sum(1 for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
        if Lp+1<bp+t: Rp_ok=False
        sumL+=Lp; sumE+=Lp-bp
        # (R'')
        O=set(vp(nu,p) for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
        Sd={}
        for nu,c in mv.items():
            if nu%p: continue
            b_=vp(nu,p)
            Sd[b_]=Sd.get(b_,0)+min(c,(p-1)*b_+1)
        lhs=sum(v for b_,v in Sd.items() if b_ not in O)
        if lhs<(p-1)*max(0,alpha-sum(O)): Rpp=False
    wn=len(factor(N))
    if sumE<D-(wn-1): R_ok=False
    # 也记录 |O|>=2 非平凡计数
    nontriv=0
    for p in factor(N):
        alpha=vp(N,p)
        O=set(vp(nu,p) for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
        if len(O)>=2 and sum(O)<alpha: nontriv+=1
    return TGT,Pp,Rp_ok,R_ok,Rpp,nontriv
random.seed(8888)
badT=badP=badRp=badR=badRpp=0; tot=0; ntriv=0; ex=[]
for N in [48,60,120,240,360,420,840,1680,2520]:
    divs=[d for d in range(1,N+1) if N%d==0]
    ntest=0
    for trial in range(60000):
        fam=rich_sample(N,divs)
        if fam is None: continue
        if lcmlist([d for a,d in fam])!=N: continue
        ntest+=1; tot+=1
        TGT,Pp,Rp_ok,R_ok,Rpp,nt=analyze_full(fam,N)
        ntriv+=nt
        if not TGT:
            badT+=1
            if len(ex)<3: ex.append(("TGT",N,dict(sorted(Counter(d for a,d in fam).items()))))
        if not Pp:
            badP+=1
            if len(ex)<6: ex.append(("Pp",N,dict(sorted(Counter(d for a,d in fam).items()))))
        if not Rp_ok:
            badRp+=1
            if len(ex)<9: ex.append(("Rp",N,dict(sorted(Counter(d for a,d in fam).items()))))
        if not R_ok:
            badR+=1
            if len(ex)<12: ex.append(("R",N,dict(sorted(Counter(d for a,d in fam).items()))))
        if not Rpp:
            badRpp+=1
            if len(ex)<15: ex.append(("R''",N,dict(sorted(Counter(d for a,d in fam).items()))))
    print(f"[富采样] n={N}: 全本质 {ntest}; |O|>=2非平凡 {nt}",flush=True)
print(f"总计 {tot}; TGT违 {badT}; (P_p)违 {badP}; (Rp)违 {badRp}; (R)违 {badR}; (R'')违 {badRpp}; |O|>=2非平凡 {ntriv}")
for e in ex[:14]: print("  ",e)
