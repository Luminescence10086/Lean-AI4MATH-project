"""核对 (P_p) 组合链的缺口:
   已知 Sigma_omega min >= b(n)+omega(n)-1 (由 P_p 加权)。要推 T23prime 需
   Sigma g := Sigma (omega(nu)-1) min(m_nu,b_nu) <= Sigma_omega min - b(n)。
   检验: (i) 该上界是否成立? (ii) 它是否与原目标等价 (即 Sigma g <= Sigma min - (b - (omega-1))
   ... 恒等检查)。打印最紧实例与量值。"""
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
    worst=[]
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ok,L=eval_family(family)
            if not ok: continue
            m=Counter(d for a,d in family)
            minsum=sum(min(m[nu],boundv(nu)) for nu in m)
            b=boundv(L)
            wmin=sum(len(factor(nu))*min(m[nu],boundv(nu)) for nu in m)
            g=sum((len(factor(nu))-1)*min(m[nu],boundv(nu)) for nu in m)
            om=len(factor(L))
            # (i) g <= wmin - b  (需要的上界)
            ub = wmin - b
            if g > ub:
                worst.append((g-ub, "UB-viol", n, family, g, ub, minsum, b, wmin, om))
            # 报告 slack: minsum - b (>=0 为目标), 以及 g-(om-1)
            worst.append((0,"info",n,family,g,om,minsum,b,wmin,0))
    worst.sort(key=lambda x:-x[0])
    print("最紧 (g − (Σω·min − b)) 前 8：")
    for x in worst[:8]:
        d,kind,n,family,g,ub,minsum,b,wmin,om=x
        print(f"  g−UB={d} n={n} g={g} UB={ub} minsum={minsum} b={b} wmin={wmin} fam={family}")

if __name__=="__main__":
    main()
