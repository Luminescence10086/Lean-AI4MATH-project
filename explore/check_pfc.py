"""检验 (PFC): 对每根纤维 c: Sigma_{i in I0(c)} (1 - 1/a_i) <= bound(L_c) - 1。
   以及全局基底不等式: Sigma_c exc_c >= bound(n/q) - 1 (equiv (★), 仅作对照)。"""
import sys
from fractions import Fraction
from math import gcd

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
    ess=[]
    for (a,d) in family:
        ess.append(any(cnt[(a+t*d)%M]==1 for t in range(M//d)))
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return len(family), ess, essL

def fiber_blocks(family, q, c):
    out=[]
    for (a,d) in family:
        if d % q != 0:
            inv=pow(q % d, -1, d) if d>1 else 0
            u=((a-c) % d)*inv % d if d>1 else 0
            out.append((u,d))
        else:
            if a % q == c:
                dp=d//q
                w=((a-c)//q) % dp if dp>1 else 0
                out.append((w, dp if dp>=1 else 1))
    return out

def covers(n,K):
    full=(1<<n)-1
    aps=[(a,d) for d in divs(n) for a in range(d)]
    masks=[]
    for (a,d) in aps:
        m=0
        for t in range(n//d): m|=1<<((a+t*d)%n)
        masks.append(m)
    out=[]
    def dfs(start,covered,chosen):
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
    for q in factor(n):
        I0=[(idx,(a,d)) for idx,(a,d) in enumerate(family) if d%q!=0]
        if not I0: continue
        Ls=[]; Csets={idx:set() for idx,_ in I0}
        for c in range(q):
            fb=fiber_blocks(family,q,c)
            ca,ce,cl=eval_family(fb)
            Ls.append(cl)
            for (u,d),e in zip(fb,ce):
                if not e: continue
                for idx,(aa,dd) in I0:
                    if dd==d and d>1:
                        inv=pow(q%d,-1,d)
                        if ((aa-c)%d)*inv%d == u: Csets[idx].add(c)
        a={idx:len(s) for idx,s in Csets.items()}
        exc_tot=Fraction(0)
        for c in range(q):
            pres=[idx for idx in a if c in Csets[idx]]
            lhs=sum(Fraction(1) - Fraction(1,a[idx]) for idx in pres)
            cap=boundv(Ls[c])-1
            if lhs>cap:
                bad['pfc'].append((n,q,c,family,{i:sorted(s) for i,s in Csets.items()},str(lhs),cap,Ls))
            exc_tot += Fraction(cap)-lhs
        M=n//(q**vp(n,q))
        if exc_tot < boundv(n//q)-1:
            bad['base'].append((n,q,family,str(exc_tot),boundv(n//q)-1))

def main():
    bad={'pfc':[], 'base':[]}
    for n,K in [(6,6),(12,6),(18,6),(24,6),(30,6)]:
        aps,cv=covers(n,K)
        for ch in cv: check_family([aps[i] for i in ch], bad)
        print(f"n={n} K={K} done", flush=True)
    print("(PFC) 反例:", len(bad['pfc']))
    for x in bad['pfc'][:6]:
        n,q,c,family,Cs,lhs,cap,Ls=x
        print(f"   n={n} q={q} c={c} family={family}")
        print(f"     C={Cs} lhs={lhs} cap={cap} Ls={Ls}")
    print("全局基底反例:", len(bad['base']))
    for x in bad['base'][:6]: print("   ",x)

if __name__=="__main__":
    main()
