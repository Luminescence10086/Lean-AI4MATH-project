"""扫描缺陷形式 tightness: margin = (Σ_ν b(ν) − b(n)) − Σ_ν (b(ν)−m_ν)₊。
   打印 margin 最小的实例结构（组数、各组 m_ν/b(ν)/v_p、n）。"""
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
    best=[]
    for n,K in [(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ok,L=eval_family(family)
            if not ok: continue
            m=Counter(d for a,d in family)
            groups=[(nu,c) for nu,c in m.items()]
            bsum=sum(boundv(nu) for nu,c in m.items())
            bL=boundv(L)
            defsum=sum(max(0,boundv(nu)-c) for nu,c in m.items())
            margin=(bsum-bL)-defsum
            if margin<0:
                print("!! 缺陷形式反例:", n, family); return
            best.append((margin,n,L,groups,bsum,bL,defsum))
    best.sort(key=lambda x:x[0])
    print("最紧 8 例：")
    for margin,n,L,groups,bsum,bL,defsum in best[:8]:
        print(f"  margin={margin} n={n} lcmDiff={L} groups={sorted((nu,c,boundv(nu)) for nu,c in groups)} bsum={bsum} b(L)={bL} defsum={defsum}")

if __name__=="__main__":
    main()
