"""验证配对不等式 (∗): (|T|-1)p + min(M_1,p) - Σ_β def_β ≥ p-1
   其中 (PC)-κ 实例: 类覆盖 ℤ/p^κ + 挖点; T = 无 β=1 类的纤维集 (含挖点纤维), 
   def_β := max(0, Σ_c min(M'_{β-1}(c), b(p^{β-1})) - min(M_β, b(p^β)))。
   同时验证归纳链的每步数值。"""
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

def analyze(family, p, kapp):
    """构造 (PC) 实例: 取载体 kapp 级块及其私有点线. 返回 per-beta 计数等."""
    ...

def main():
    bad=[]; tot=0
    for n,K in [(12,7),(18,7),(24,7),(30,7),(36,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ess, L = eval_family(family)
            if not all(e for e in ess): continue
            for p in factor(L):
                kapp=vp(L,p)
                if kapp<2: continue
                M=L//(p**kapp)
                # 找载体块 (beta=kapp) 及私有点
                for i,(a,d) in enumerate(family):
                    if vp(d,p)!=kapp: continue
                    for x in ess[i]:
                        xh=x%(p**kapp)
                        # (PC) 实例 = 所有块在 mod p^kappa 的类投影
                        # 每个块 j: 类 A_j mod p^{beta_j} (beta_j=v_p(d_j, p) 若该块 "在线上": 用其投影)
                        # 注意: PC 用块集 = 覆盖 x 的类结构; 做全族的 mod-p^k 投影分析:
                        cnt=Counter()
                        for a2,d2 in family:
                            b2=min(vp(d2,p),kapp)
                            if b2==0: continue
                            cnt[b2]+=1
                        # 检查 x* 是否被其它类覆盖 (PC 条件)
                        cond=True
                        for j,(a2,d2) in enumerate(family):
                            if j==i: continue
                            b2=vp(d2,p)
                            if b2==0 or b2>kapp: continue
                            if xh%(p**b2)==a2%(p**b2): cond=False; break
                        if not cond: continue
                        # 现在是 (PC) 实例: beta=b2 计数下的 min-form; 检查 (PC) 与 (∗)
                        F=sum(min(c,boundv(p**b)) for b,c in cnt.items())
                        if F<boundv(p**kapp): 
                            bad.append(("PC违",n,p,kapp,family)); break
                        # (∗): m1 = 含 beta=1 类的纤维数; T 大小 = p - m1; M_1 = cnt[1]
                        m1=len({a2%p for a2,d2 in family if vp(d2,p)==1})
                        T=p-m1; M1=cnt.get(1,0)
                        # def_beta
                        sdef=0
                        for b in range(2,kapp+1):
                            loc=0
                            for c in range(p):
                                mc=sum(1 for a2,d2 in family if vp(d2,p)==b and a2%p==c)
                                loc+=min(mc,boundv(p**(b-1)))
                            glob=min(cnt.get(b,0),boundv(p**b))
                            sdef+=max(0,loc-glob)
                        star=(T-1)*p+min(M1,p)-sdef
                        tot+=1
                        if star < p-1:
                            bad.append(("(∗)违",n,p,kapp,family,T,M1,sdef,star,p-1)); break
                if bad: break
            if bad: break
        if bad: break
    print(f"检查 {tot} 个 (PC, ∗) 实例")
    print("反例:", len(bad))
    for x in bad[:5]: print("   ",x)

if __name__=="__main__":
    main()
