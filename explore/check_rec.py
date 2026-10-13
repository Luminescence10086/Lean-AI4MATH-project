"""检验递归 sigma_rec:
   sigma_rec(F) := max( sigma(F), max_{q | lcmDiff(F)} [ Sigma_c sigma_rec(F_c^0) + Sigma_p(p-1)M_p^(q) - Sigma_{I0}(a_i-1)^(q) ] )
   检验 (C') sigma_rec(F) <= slack(F)  以及  (S5) B'(q) >= sigma(F) 对每个 q。"""
import sys
from math import gcd
from collections import Counter
sys.setrecursionlimit(10000)

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

def sigma_plain(diffs):
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

def decompose(family,q):
    """返回 (sigfibers 用的子族列表, Ls, star, sum_ai_minus1)。子族 = F_c^0（本质片的块）。"""
    subs=[]; Ls=[]; Csets={}
    I0=[(idx,(a,d)) for idx,(a,d) in enumerate(family) if d%q!=0]
    for idx,_ in I0: Csets[idx]=set()
    for c in range(q):
        fb=fiber_blocks(family,q,c)
        ca,ce,cl=eval_family(fb)
        Ls.append(cl)
        sub=[(u,d) for (u,d),e in zip(fb,ce) if e]
        subs.append(sub)
        for (u,d),e in zip(fb,ce):
            if not e: continue
            for idx,(aa,dd) in I0:
                if dd==d and d>1:
                    inv=pow(q%d,-1,d)
                    if ((aa-c)%d)*inv%d==u: Csets[idx].add(c)
    n=lcmlist([d for a,d in family])
    M=n//(q**vp(n,q))
    star=0
    for p in (factor(M) if M>1 else {}):
        star+=(p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
    star+=(q-1)*(sum(vp(L,q) for L in Ls)-(vp(n,q)-1))
    a={idx:len(s) for idx,s in Csets.items()}
    deficit=sum(a[idx]-1 for idx,_ in I0)
    return subs, star-deficit, deficit, star

def sigma_rec(family, depth=0):
    n=lcmlist([d for a,d in family])
    if n<=1: return 0
    s0=sigma_plain([d for a,d in family])
    best=s0
    for q in factor(n):
        subs, net, deficit, star = decompose(family,q)
        val=sum(sigma_rec(sub,depth+1) for sub in subs) + net
        if val>best: best=val
    return best

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
    badC=[]; badS5=[]; tot=0
    for n,K in [(6,6),(12,7),(18,7),(20,7),(24,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}: {len(cv)} covers", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            n2=essL
            slack=card-boundv(n2)
            sr=sigma_rec(family)
            tot+=1
            if sr>slack:
                badC.append((n2,card,sr,slack,family)); print("C' VIOL", badC[-1], flush=True)
            # (S5) 对每个 q
            for q in factor(n2):
                subs,net,deficit,star=decompose(family,q)
                s0=sigma_plain([d for a,d in family])
                val=sum(sigma_rec(s) for s in subs)+net
                if val<s0:
                    badS5.append((n2,q,family,val,s0)); print("S5 VIOL", badS5[-1], flush=True)
    print(f"共 {tot} 个全本质族")
    print("(C') sigma_rec<=slack 反例:", len(badC))
    print("(S5) 反例:", len(badS5))

if __name__=="__main__":
    main()
