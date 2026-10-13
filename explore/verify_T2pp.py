"""(T'') 搜索: 找 |O|>=2 且 Σ_Oβ < α 的 (实例,p). 同时记录所有 |O|>=2 实例的 Σ_Oβ vs α."""
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
def check_ess(fam,N):
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    if not all(c>0 for c in cnt): return False
    return all(any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam)
def T2pp_scan(fam,n):
    """返回: |O|>=2 的总数, 其中 Σ_Oβ<α 的个数, 最小 Σ_Oβ−α 值"""
    mv=Counter(d for a,d in fam)
    t2=0; bad=0; mind=None; ex=[]
    for p in factor(n):
        alpha=vp(n,p)
        if alpha<2: continue
        O=set()
        for nu,c in mv.items():
            if nu%p==0 and c>boundv(nu): O.add(vp(nu,p))
        if len(O)>=2:
            t2+=1
            d=sum(O)-alpha
            if mind is None or d<mind: mind=d
            if d<0:
                bad+=1
                if len(ex)<3: ex.append((p,alpha,sorted(O),dict(sorted(mv.items()))))
    return t2,bad,mind,ex
# A) 全枚举小 n
def covers(n,K,cap=100000):
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
t2t=0; bt=0; exA=[]
for (n,K) in [(12,7),(18,7),(24,7),(20,7),(28,7),(36,7)]:
    aps,cv=covers(n,K)
    for ch in cv:
        fam=[aps[i] for i in ch]
        if lcmlist([d for a,d in fam])!=n: continue
        if not check_ess(fam,n): continue
        t2,bad,mind,ex=T2pp_scan(fam,n)
        t2t+=t2; bt+=bad
        for e in ex:
            if len(exA)<5: exA.append((n,)+e)
print(f"[全枚举] |O|>=2 的 (实例,p): {t2t}; 其中 Σ_Oβ<α: {bt}")
for e in exA: print("   ",e)
# B) 大 n 随机 (大量)
random.seed(2029)
t2r=0; br=0; exB=[]; glmin=[]
for N in [48,60,84,96,120,180,240,360,420,630,840,1260,1680,2520,3780,5040]:
    divs=[d for d in range(2,N+1) if N%d==0]
    for trial in range(25000):
        k=random.randint(2,7)
        fam=[];used=set()
        for _ in range(k):
            d=random.choice(divs); a=random.randrange(d)
            cnt=random.randint(1,min(d,int(1.8*boundv(d))))
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
        t2,bad,mind,ex=T2pp_scan(fam2,N)
        t2r+=t2; br+=bad
        if mind is not None: glmin.append(mind)
        for e in ex:
            if len(exB)<5: exB.append((N,)+e)
    print(f"[随机] n={N}: 累计 |O|>=2: {t2r}; 违 (T''): {br}; 最小 Σ_Oβ−α = {min(glmin) if glmin else None}",flush=True)
print("总: |O|>=2 的 (实例,p):",t2t+t2r,"; (T'') 违例:",bt+br)
for e in exB: print("   ",e)
