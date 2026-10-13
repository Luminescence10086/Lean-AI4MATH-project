"""K=7/8 深枚举复核 (S4): sigma(F) + Sigma(a_i-1) <= Sigma_c sigma(F_c^0) + Sigma_p(p-1)M_p。"""
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
def divs(n): return [d for d in range(1,n+1) if n%d==0]

def eval_family(family):
    M=lcmlist([d for (a,d) in family]) if family else 1
    cnt=[0]*M
    for (a,d) in family:
        for t in range(M//d): cnt[(a+t*d)%M]+=1
    ess=[any(cnt[(a+t*d)%M]==1 for t in range(M//d)) for (a,d) in family]
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return len(family), ess, essL

def sigma_of(diffs):
    m=Counter(diffs)
    return sum(max(0,c-boundv(nu)) for nu,c in m.items())

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

def covers(n,K,cap=400000):
    full=(1<<n)-1
    aps=[(a,d) for d in divs(n) for a in range(d)]
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

def check_family(family, bad):
    card,ess,essL=eval_family(family)
    n=essL
    if not all(ess): return
    sigF=sigma_of([d for a,d in family])
    for q in factor(n):
        sigfiber=0; Ls=[]; Csets={}
        I0=[(idx,(a,d)) for idx,(a,d) in enumerate(family) if d%q!=0]
        for idx,_ in I0: Csets[idx]=set()
        for c in range(q):
            fb=fiber_blocks(family,q,c)
            ca,ce,cl=eval_family(fb)
            Ls.append(cl)
            sigfiber+=sigma_of([d for (u,d),e in zip(fb,ce) if e])
            for (u,d),e in zip(fb,ce):
                if not e: continue
                for idx,(aa,dd) in I0:
                    if dd==d and d>1:
                        inv=pow(q%d,-1,d)
                        if ((aa-c)%d)*inv%d==u: Csets[idx].add(c)
        M=n//(q**vp(n,q))
        star=0
        for p in (factor(M) if M>1 else {}):
            star+=(p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
        star+=(q-1)*(sum(vp(L,q) for L in Ls)-(vp(n,q)-1))
        a={idx:len(s) for idx,s in Csets.items()}
        need=sigF+sum(a[idx]-1 for idx,_ in I0)-star
        if sigfiber<need:
            bad.append((n,q,family,sigfiber,need,sigF,star,{i:sorted(s) for i,s in Csets.items()})); print('VIOL', bad[-1], flush=True)

def main():
    bad=[]
    targets=[(12,7),(18,7),(20,7),(24,7),(28,7),(30,7)]
    for n,K in targets:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}: covers={len(cv)}", flush=True)
        for ch in cv: check_family([aps[i] for i in ch], bad)
    # 手工九块例
    ex=[(0,2),(1,10),(5,10),(7,10),(0,3),(13,30),(19,30),(23,30),(29,30)]
    check_family(ex, bad)
    print("(S4) 深枚举反例:", len(bad))
    for x in bad[:8]: print("   ",x)

if __name__=="__main__":
    main()
