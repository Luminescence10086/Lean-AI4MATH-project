"""侦察: 打印含 >=2 个 Case-2 层（同一素 p）的实例结构：层大小 h、b、支撑、v_p、V_p 分布。"""
import sys
from math import gcd
from collections import Counter, defaultdict

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
def covers(n,K,cap=30000):
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
    shown=0
    for n,K in [(12,7),(18,7),(20,7),(24,7),(30,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K} covers={len(cv)}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            n2=essL
            for q in factor(n2):
                if any(d%q!=0 for a,d in family): continue
                byd=defaultdict(list)
                for a,d in family: byd[d].append(a%q)
                primes=set()
                for a,d in family:
                    for p in factor(d): primes.add(p)
                for p in primes:
                    case2=[]
                    for d,reslist in byd.items():
                        h=len(reslist); nu=d//q; b=boundv(nu)
                        if h> b+(q-1) and vp(nu,p)>=1:
                            case2.append((nu,h,b,sorted(set(reslist)),vp(nu,p)))
                    if len(case2)>=2:
                        V=[0]*q
                        for a,d in family:
                            c=a%q; v=vp(d//q,p)
                            if v>V[c]: V[c]=v
                        print(f"  n={n2} q={q} p={p} V={V}")
                        for nu,h,b,sup,vnu in case2:
                            print(f"    nu={nu} h={h} b={b} supp={sup} v_p={vnu} h-b-(q-1)={h-b-(q-1)}")
                        print(f"    family={family}")
                        shown+=1
                        if shown>=8: return
    print("done", shown)

if __name__=="__main__":
    main()
