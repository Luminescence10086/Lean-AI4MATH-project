"""检验 (A'): Sigma_{nu: h(nu) > b(nu)+q-1} (n_+(nu)-1)(b(nu)-1) <= Sigma_p (p-1) M_p
   （仅无裂块；若成立则 (D) <= (i)+(A')，其中 (i) 已证：delta_nu <= (n_+-1)(b-1)）。"""
import sys
from math import gcd
from collections import Counter, defaultdict

def factor(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def vp(n,p):
    if n==0: return 0
    e=0
    while n%p==0: n//=p; e+=1
    return e
def boundv(n):
    if n<=1: return 1
    return 1+sum(e*(p-1) for p,e in factor(n).items())
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
    return len(family), ess, essL
def covers(n,K,cap=300000):
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
    bad=[]; tot=0
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            n2=essL
            for q in factor(n2):
                if any(d%q!=0 for a,d in family): continue
                tot+=1
                byd=defaultdict(list)
                for a,d in family: byd[d].append(a%q)
                LHS=0
                for d,reslist in byd.items():
                    h=len(reslist); nu=d//q; b=boundv(nu)
                    npl=len(set(reslist))
                    if h> b+(q-1):
                        LHS += (npl-1)*(b-1)
                primes=set()
                for a,d in family:
                    for p in factor(d): primes.add(p)
                star=0
                for p in primes:
                    V=[0]*q
                    for a,d in family:
                        c=a%q; v=vp(d//q,p)
                        if v>V[c]: V[c]=v
                    star+=(p-1)*(sum(V)-max(V))
                if LHS>star:
                    bad.append((n2,q,family,LHS,star)); print("A' VIOL", bad[-1], flush=True)
    print(f"检查 {tot} 个实例")
    print("(A') 反例:", len(bad))

if __name__=="__main__":
    main()
