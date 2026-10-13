"""验证 (L): max_{y ∉ X} Σ_β min(M_β(y), bound(p^β)) >= bound(p^κ)。
   M_β(y) := #{纯块 j: y ∈ C_j (=a mod μ_j, μ_j = d/p^{v_p(d)}), v_p(d)=β}。
   若成立 ==> (P_p) 一般情形得证（经 (P_p)-LHS ≥ 最优线形式）。"""
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
    ess=[any(cnt[(a+t*d)%M]==1 for t in range(M//d)) for (a,d) in family]
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return all(ess), essL
def covers(n,K,cap=200000):
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

def main():
    bad=[]; tot=0; kappas=Counter()
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ok,L=eval_family(family)
            if not ok: continue
            for p in factor(L):
                kap=vp(L,p)
                if kap<2: continue     # v_p=1 已证；这里压 κ≥2
                M=L//(p**kap)
                X=set()
                for a,d in family:
                    if d%p!=0:
                        mu=d
                        for t in range(M//mu): X.add((a+t*mu)%M)
                if len(X)>=M:
                    bad.append(("X全M",n,p,family)); break
                best=0
                for y in range(M):
                    if y in X: continue
                    Mb=Counter()
                    for a,d in family:
                        if d%p==0:
                            mu=d//(p**vp(d,p))
                            if (y-a)%mu==0: Mb[vp(d,p)]+=1
                    form=sum(min(c,boundv(p**b)) for b,c in Mb.items())
                    if form>best: best=form
                tot+=1; kappas[kap]+=1
                if best<boundv(p**kap):
                    bad.append(("(L)违",n,p,kap,family,best,boundv(p**kap)))
                    break
    print(f"检查 {tot} 个 (实例,p,κ≥2)（κ分布: {dict(sorted(kappas.items()))}）")
    print("(L) 反例:", len(bad))
    for x in bad[:6]: print("   ",x)

if __name__=="__main__":
    main()
