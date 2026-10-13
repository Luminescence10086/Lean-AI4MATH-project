"""验证 (P_p)-v_p=1 证明的关键步骤：
   取 y* 不被任何 split 块（p∤d）覆盖的最小残留类（mod M）；
   统计"y* ∈ 该纯块 m-陪集 且 该块 p|d"的互异纯块数 ==> 应 >= p。"""
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
    bad=[]; tot=0
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            ok,L=eval_family(family)
            if not ok: continue
            for p in factor(L):
                if vp(L,p)!=1: continue     # 仅 v_p = 1 检验
                M=L//p
                # 覆盖 mod M 检查: y 被 splits(X) 或 至少该类需覆盖
                covM=[set() for _ in range(1)]  # 记录各 mod M 类被 split 覆盖情况
                splitcov=set()
                for a,d in family:
                    if d%p!=0:
                        for t in range(M//d): splitcov.add((a+t*d)%M)
                # 找 y* ∉ splitcov
                if len(splitcov)>=M:
                    bad.append(("splits全覆盖!",n,p,family)); break
                ystar=next(y for y in range(M) if y not in splitcov)
                # 统计: 纯块(p|d) 满足 y* ∈ 其 coset (即 y* ≡ a mod mu, mu=d/p) 的互异块数
                cnt=0
                for a,d in family:
                    if d%p==0:
                        mu=d//p
                        if (ystar-a)%mu==0: cnt+=1
                tot+=1
                if cnt<p:
                    bad.append((n,p,family,ystar,cnt,p)); break
    print(f"检查 {tot} 个 (实例,p, v_p=1)")
    print("反例:", len(bad))
    for x in bad[:5]: print("   ",x)

if __name__=="__main__":
    main()
