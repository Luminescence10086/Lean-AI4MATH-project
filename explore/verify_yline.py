"""验证一般 κ 的 y*-归约子引理:
   X := split 块(p∤d)的 m-陪集并; y* ∉ X;
   P* := 纯块(p|d) 且 y* ≡ a (mod μ=d/p); M_β := #(P* 中 β=v_p(d)=β 的块数);
   子引理: Σ_β min(M_β, bound(p^β)) >= bound(p^κ)。
   同时报告 P* 覆盖 ℤ/p^κ 的验证 (A_j = a mod p^β 作为 ℤ/p^κ 的类)。"""
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
                kap=vp(L,p); M=L//(p**kap)
                # split 覆盖 mod M
                splitcov=set()
                for a,d in family:
                    if d%p!=0:
                        for t in range(M//d): splitcov.add((a+t*d)%M)
                if len(splitcov)>=M:
                    bad.append(("splits全覆M",n,p,family)); break
                ystar=next(y for y in range(M) if y not in splitcov)
                # P*: 纯块且 y* ∈ coset (y* ≡ a mod mu)
                P=[(a,d) for a,d in family if d%p==0 and (ystar-a)%(d//(p**vp(d,p)))==0]
                # min-形式
                Mb=Counter(vp(d,p) for a,d in P)
                lhs=sum(min(c,boundv(p**b)) for b,c in Mb.items())
                rhs=boundv(p**kap)
                tot+=1
                kappas[kap]+=1
                if lhs<rhs:
                    bad.append(("yline-min违反",n,p,kap,family,ystar,dict(Mb),lhs,rhs)); break
                # 覆盖 ℤ/p^κ 检查
                covered=set()
                for a,d in P:
                    b=vp(d,p)
                    cls=a%(p**b)
                    for t in range(p**kap//(p**b)):
                        covered.add((cls+t*(p**b))%(p**kap))
                if len(covered)!=p**kap:
                    bad.append(("P*未覆盖p^κ",n,p,kap,family,ystar)); break
    print(f"检查 {tot} 个 (实例,p)（κ 分布: {dict(sorted(kappas.items()))}）")
    print("反例:", len(bad))
    for x in bad[:5]: print("   ",x)

if __name__=="__main__":
    main()
