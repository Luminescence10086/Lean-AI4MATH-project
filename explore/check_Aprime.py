"""K=7 深枚举直接验证:
   (A'):  sigma(G) <= card(G) - bound(lcmDiff G)        [一切全本质覆盖]
   (S2*): 无裂块情形: sigma(G) <= Sigma_c sigma(G_c^0) + Sigma_p(p-1)M_p"""
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
def sigma_of(diffs):
    m=Counter(diffs)
    return sum(max(0,c-boundv(nu)) for nu,c in m.items())
def eval_family(family):
    M=lcmlist([d for (a,d) in family]) if family else 1
    cnt=[0]*M
    for (a,d) in family:
        for t in range(M//d): cnt[(a+t*d)%M]+=1
    ess=[any(cnt[(a+t*d)%M]==1 for t in range(M//d)) for (a,d) in family]
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return len(family), ess, essL
def fiber_blocks(family,q,c):
    out=[]
    for (a,d) in family:
        if d%q!=0:
            inv=pow(q%d,-1,d) if d>1 else 0
            u=((a-c)%d)*inv%d if d>1 else 0
            out.append((u,d))
        else:
            if a%q==c:
                dp=d//q; w=((a-c)//q)%dp if dp>1 else 0
                out.append((w, dp if dp>=1 else 1))
    return out
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
    badA=[]; badS2=[]
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}: {len(cv)} covers", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            n2=essL
            sig=sigma_of([d for a,d in family])
            if sig>card-boundv(n2):
                badA.append((n2,card,sig,family)); print("A' VIOL", badA[-1], flush=True)
            for q in factor(n2):
                if any(d%q!=0 for a,d in family): continue   # 只看无裂块
                sigfib=0; Ls=[]
                for c in range(q):
                    fb=fiber_blocks(family,q,c)
                    ca,ce,cl=eval_family(fb)
                    Ls.append(cl); sigfib+=sigma_of([d for (u,d),e in zip(fb,ce) if e])
                M=n2//(q**vp(n2,q))
                star=0
                for p in (factor(M) if M>1 else {}):
                    star+=(p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
                star+=(q-1)*(sum(vp(L,q) for L in Ls)-(vp(n2,q)-1))
                if sig>sigfib+star:
                    badS2.append((n2,q,family,sig,sigfib,star)); print("S2* VIOL", badS2[-1], flush=True)
    print("(A') 直接反例:", len(badA))
    print("(S2*) (无裂块) 反例:", len(badS2))

if __name__=="__main__":
    main()
