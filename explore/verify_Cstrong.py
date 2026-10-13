"""C-strong 检验: 对载体块 j* (v_p(d)=κ) 的私有点 x, y°=x mod M:
   F(y°) >= (p−1)κ + t_p, t_p = #{ν∋p present: m_ν > b(ν)}.
   若成立 ⟹ (Rp) ⟹ (R) ⟹ TGT."""
import sys
from math import gcd
from collections import Counter
def factor(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def vp(n,p):
    e=0
    while n and n%p==0: n//=p; e+=1
    return e
def boundv(n): return 1+sum(e*(p-1) for p,e in factor(n).items())
def lm(a,b): return a*b//gcd(a,b)
def lcmlist(xs):
    r=1
    for x in xs: r=lm(r,x)
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
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(e for e in ess) else 1
    return ess, essL
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
def cstrong_check(family,p,kap):
    ess,L=eval_family(family)
    mv=Counter(d for a,d in family)
    M=L//(p**kap)
    t_p=sum(1 for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
    carriers=[i for i,(a,d) in enumerate(family) if vp(d,p)==kap]
    if not carriers: return None
    for i in carriers:
        a,d=family[i]
        for x in ess[i]:
            y=x%M
            Mb=Counter()
            for a2,d2 in family:
                if d2%p==0:
                    mu2=d2//(p**vp(d2,p))
                    if (y-a2)%mu2==0: Mb[vp(d2,p)]+=1
            form=sum(min(c,boundv(p**b)) for b,c in Mb.items())
            if form>=(p-1)*kap+t_p: return True
    return False
bad=0;tot=0;ex=[]
for n,K in [(12,7),(18,7),(24,7)]:
    aps,cv=covers(n,K)
    for ch in cv:
        family=[aps[i] for i in ch]
        ess,L=eval_family(family)
        if not all(e for e in ess): continue
        for p in factor(L):
            kap=vp(L,p)
            if kap<2: continue
            r=cstrong_check(family,p,kap)
            if r is None: continue
            tot+=1
            if not r:
                bad+=1
                if len(ex)<4: ex.append((n,p,kap,dict(sorted(Counter(d for a,d in family).items())),family[:12]))
    print(f"[枚举] n={n}: 累计 {tot}, 反例 {bad}",flush=True)
print("C-strong (枚举) 反例:",bad)
for e in ex: print("  ",e)
