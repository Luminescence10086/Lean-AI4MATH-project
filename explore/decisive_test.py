"""决定性: n=240 非平凡区 + 自由单元6-块 共存搜索 + (V) 检验."""
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
N=240
random.seed(2024)
tot=0; nviol=0; ex=[]; nfree=0
for trial in range(4000000):
    off10=random.sample(range(10),random.randint(6,10))
    off12=random.sample(range(12),random.randint(5,12))
    off6=random.sample(range(6),random.randint(1,4))
    off80=random.sample(range(80),random.randint(5,14))
    fam=[(a,10) for a in off10]+[(a,12) for a in off12]+[(a,6) for a in off6]+[(a,80) for a in off80]
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    unc=[x for x in range(N) if cnt[x]==0]
    if len(unc)>40: continue
    fam2=fam+[(u,N) for u in unc]
    if lcmlist([d for a,d in fam2])!=N: continue
    cnt=[0]*N
    for a,d in fam2:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    if not all(any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam2): continue
    tot+=1
    mv=Counter(d for a,d in fam2); p=2; alpha=4
    O=set(vp(nu,p) for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
    if not(len(O)>=2 and sum(O)<alpha):
        if trial%200000==0: print(f"...trial {trial}: 合法 {tot}, 非平凡 {nfree}",flush=True)
        continue
    nfree+=1
    M=N//(p**alpha)
    for y in range(M):
        Mb=Counter()
        for a,d in fam2:
            if d%p==0:
                mu=d//(p**vp(d,p))
                if (y-a)%mu==0: Mb[vp(d,p)]+=1
        F=sum(min(c,boundv(p**b)) for b,c in Mb.items())
        if F<(p-1)*alpha+1: continue
        v=sum(max(0,min(Mb.get(b,0),boundv(p**b))-(p-1)*b) for b in O)
        if v>1:
            nviol+=1
            if len(ex)<4: ex.append((dict(sorted(mv.items())),sorted(O),y,F,v))
print(f"RESULT: 合法实例 {tot}; 非平凡 {nfree}; (V)违 {nviol}")
for e in ex: print("  ",e)
