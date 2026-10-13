"""检验精确缺口陈述 (D): Sigma_{nu'} max(0, [h-b'-(q-1)]_+ - Sigma_c [b(c)-b']_+ ) <= Sigma_p (p-1) M_p
   （仅无裂块情形；若成立则 (S2*) 得证：每层多余额由实际分布 + M_p 支付）。"""
import sys
from math import gcd
from collections import Counter

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
    bad=[]
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}: {len(cv)} covers", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            n2=essL
            for q in factor(n2):
                if any(d%q!=0 for a,d in family): continue   # 无裂块
                # 每层: h, b', 与分布总和
                D=0
                byd=Counter(d for a,d in family)
                for d,h in byd.items():
                    nu=d//q; bprime=boundv(nu)
                    # 分布 b(c) = #blocks with d 且 res≡c mod q
                    bdist=Counter(a%q for a,dd in family if dd==d)
                    distsum=sum(max(0,c-bprime) for c in bdist.values())
                    D += max(0, max(0,h-bprime-(q-1)) - distsum)
                Ls=[]
                for c in range(q):
                    # fiber: blocks with q|d and res=c -> t-diff d/q, residue (a-c)/q
                    sub=[((a-c)//q, d//q) for a,dd in family if False for (a,d) in [(a,dd)] if dd==0]  # placeholder
                    Ls.append(None)
                # 重新正确计算 Ls
                Ls=[]
                for c in range(q):
                    blocks_in=[((a-c)//q, d//q) for (a,d) in family if d%q==0 and a%q==c]
                    if blocks_in:
                        Ls.append(lcmlist([dd for u,dd in blocks_in]))
                    else:
                        Ls.append(1)
                M=n2//(q**vp(n2,q))
                star=0
                for p in (factor(M) if M>1 else {}):
                    star+=(p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
                star+=(q-1)*(sum(vp(L,q) for L in Ls)-(vp(n2,q)-1))
                if D>star:
                    bad.append((n2,q,family,D,star,Ls)); print("D VIOL", bad[-1], flush=True)
    print("(D) 反例:", len(bad))

if __name__=="__main__":
    main()
