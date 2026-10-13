"""验证精确归纳恒等式:
   E_k := F_k - b(p^k) = excess + [(|T|-1)p + min(M1,p) - (p-1)] - Σ_β D_β
   （用 (PC) 实例数值验证恒等式本身 + 各分量统计，寻找 sign 证明的入口）。"""
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
    bad=[]; tot=0; stats=[]
    for n,K in [(12,7),(18,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ess, L = eval_family(family)
            if not all(e for e in ess): continue
            for p in factor(L):
                kapp=vp(L,p)
                if kapp<2: continue
                for i,(a,d) in enumerate(family):
                    if vp(d,p)!=kapp: continue
                    xnext=None
                    for x in ess[i]:
                        xh=x%(p**kapp)
                        cond=True
                        for j,(a2,d2) in enumerate(family):
                            if j==i: continue
                            b2=vp(d2,p)
                            if 1<=b2<=kapp and xh%(p**b2)==a2%(p**b2): cond=False; break
                        if cond: xnext=xh; break
                    if xnext is None: continue
                    # 计数
                    def Mc(b,c):
                        return sum(1 for a2,d2 in family if vp(d2,p)==b and a2%p==c)
                    # 全局 F_κ
                    F=sum(min(Mc(b,None) if False else sum(Mc(b,c) for c in range(p)), boundv(p**b)) for b in range(1,kapp+1))
                    b_rhs=boundv(p**kapp)
                    # 局域
                    m1=len({a2%p for a2,d2 in family if vp(d2,p)==1})
                    T=p-m1
                    locsum=0
                    for c in range(p):
                        # 挖点纤维: 用 b(p^{k-1}) 下界; 其它 needy: p; free(有β=1): 0
                        if c==xnext%p: locsum+=boundv(p**(kapp-1))
                        elif Mc(1,c)==0: locsum+=p
                    excess=locsum-(boundv(p**(kapp-1))+(T-1)*p)
                    M1=sum(Mc(1,c) for c in range(p))
                    sD=0
                    for b in range(2,kapp+1):
                        loc=sum(min(Mc(b,c),boundv(p**(b-1))) for c in range(p))
                        glob=min(sum(Mc(b,c) for c in range(p)),boundv(p**b))
                        sD+=loc-glob
                    E=F-b_rhs
                    pred=excess+((T-1)*p+min(M1,p)-(p-1))-sD
                    tot+=1
                    if E!=pred:
                        bad.append(("恒等式违",n,p,kapp,family,E,pred)); break
                    stats.append((E,T,M1,sD,excess))
                if bad: break
            if bad: break
        if bad: break
    print(f"检查 {tot} 个实例；恒等式违例: {len(bad)}")
    for x in bad[:3]: print("   ",x)
    import statistics
    if stats:
        Es=[s[0] for s in stats]
        print(f"E_κ 分布: min={min(Es)} max={max(Es)} 零占比={sum(1 for e in Es if e==0)}/{len(Es)}")

if __name__=="__main__":
    main()
