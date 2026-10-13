"""检验逐素数紧式与多素组引理:
   (P_p): Sigma_{nu: p|nu} min(m_nu, (p-1)v_p(nu)+1) >= (p-1)v_p(n)+1
   (W):   Sigma_nu (omega(nu)-1)*min(m_nu, b(nu)) >= omega(n)-1
   若两者成立 ==> T23prime（组合论证，见推导）。"""
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
def boundv(n):
    return 1+sum(e*(p-1) for p,e in factor(n).items())
def vp(n,p):
    e=0
    while n and n%p==0: n//=p; e+=1
    return e
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
    badP=[]; badW=[]; tot=0
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ok,L=eval_family(family)
            if not ok: continue
            tot+=1
            m=Counter(d for a,d in family)
            # (P_p)
            for p in factor(L):
                lhs=sum(min(m[nu], (p-1)*vp(nu,p)+1) for nu in m if nu%p==0)
                rhs=(p-1)*vp(L,p)+1
                if lhs<rhs: badP.append((L,p,family,lhs,rhs)); break
            # (W)
            lhsW=sum((len(factor(nu))-1)*min(m[nu],boundv(nu)) for nu in m)
            rhsW=len(factor(L))-1
            if lhsW<rhsW: badW.append((L,family,lhsW,rhsW))
    print(f"检查 {tot} 实例")
    print("(P_p) 反例:", len(badP))
    for x in badP[:5]: print("   ",x)
    print("(W) 反例:", len(badW))
    for x in badW[:5]: print("   ",x)

if __name__=="__main__":
    main()
