"""(U'') 检验: 对一切 F(y) >= (p−1)α+1 的线 y: Σ_{β∈O} min(M_β(y), b(p^β)) <= (p−1)Σ_Oβ + 1.
   另测载体私有线 (L⁺) 版本。"""
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
def eval_family(family):
    M=lcmlist([d for (a,d) in family]) if family else 1
    cnt=[0]*M
    for (a,d) in family:
        for t in range(M//d): cnt[(a+t*d)%M]+=1
    ess=[]
    for (a,d) in family:
        priv={((a+t*d)%M) for t in range(M//d) if cnt[(a+t*d)%M]==1}
        ess.append(priv)
    return ess, M
def U_test(fam,n):
    mv=Counter(d for a,d in fam)
    res=[]
    for p in factor(n):
        alpha=vp(n,p)
        if alpha<2: continue
        M=n//(p**alpha)
        O=set()
        for nu,c in mv.items():
            if nu%p==0 and c>boundv(nu): O.add(vp(nu,p))
        if not O: continue
        target=(p-1)*alpha+1
        thresh=(p-1)*sum(O)+1
        allok=True; anytarget=False; over_lines=[]
        for y in range(M):
            Mb=Counter()
            for a,d in fam:
                if d%p==0:
                    mu=d//(p**vp(d,p))
                    if (y-a)%mu==0: Mb[vp(d,p)]+=1
            F=sum(min(c,boundv(p**b)) for b,c in Mb.items())
            if F>=target:
                anytarget=True
                over=sum(min(Mb.get(b,0),boundv(p**b)) for b in O)
                if over>thresh: allok=False; over_lines.append((y,F,over))
        res.append((p,alpha,sorted(O),allok,anytarget,over_lines[:2]))
    return res
random.seed(4242)
tot=0; nbad=0; ex=[]
for N in [30,42,60,66,70,84,96,120,180,240,360,420]:
    divs=[d for d in range(2,N+1) if N%d==0]
    ntest=0
    for trial in range(30000):
        k=random.randint(2,6)
        fam=[];used=set()
        for _ in range(k):
            d=random.choice(divs); a=random.randrange(d)
            cnt=random.randint(1,min(d,int(1.6*boundv(d))))
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
        ess,_=eval_family(fam2)
        if not all(e for e in ess): continue
        ntest+=1
        for (p,alpha,O,allok,anytarget,ol) in U_test(fam2,N):
            tot+=1
            if not allok:
                nbad+=1
                if len(ex)<5: ex.append((N,p,alpha,O,ol,dict(sorted(Counter(d for a,d in fam2).items()))))
    print(f"[随机] n={N}: 族 {ntest}; 累计 (实例,p) {tot}; (U'')违 {nbad}",flush=True)
print("(U'') 违例:",nbad)
for e in ex: print("  ",e)
