"""更强断言 (L⁺): 存在 β=κ 载体块 j* 及其私有线 y° (=某私有点的 y-坐标):
   F(y°) := Σ_β min(M_β(y°), b(p^β)) >= b(p^κ)。
   （(L⁺) ⟹ (L) ⟹ (P_p) 一般情形。）"""
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
    bad=[]; tot=0
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ess, L = eval_family(family)
            if not all(e for e in ess): continue
            for p in factor(L):
                kap=vp(L,p)
                if kap<2: continue
                M=L//(p**kap)
                # β=κ 载体
                carriers=[i for i,(a,d) in enumerate(family) if vp(d,p)==kap]
                if not carriers: continue
                ok_any=False
                for i in carriers:
                    a,d=family[i]
                    mu=d//(p**vp(d,p))
                    for x in ess[i]:     # 私有点 x mod lcm(...)=L (mod L)
                        # y-坐标 = x mod M
                        y=x%M
                        Mb=Counter()
                        for a2,d2 in family:
                            if d2%p==0:
                                mu2=d2//(p**vp(d2,p))
                                if (y-a2)%mu2==0: Mb[vp(d2,p)]+=1
                        form=sum(min(c,boundv(p**b)) for b,c in Mb.items())
                        if form>=boundv(p**kap): ok_any=True; break
                    if ok_any: break
                tot+=1
                if not ok_any:
                    bad.append((n,p,kap,family))
                    break
    print(f"检查 {tot} 个 (实例,p,κ≥2)")
    print("(L⁺) 反例:", len(bad))
    for x in bad[:6]: print("   ",x)

if __name__=="__main__":
    main()
