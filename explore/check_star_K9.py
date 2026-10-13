"""K=9 深枚举：验证 T7 与 (★) 在大 K 下仍成立（含手工构造的 n=30 九块例）。"""
import sys
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

def covers(n,K,limit=None):
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
    if not all(ess): 
        return
    if card<boundv(n): bad['t7'].append((n,card,family))
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
        M=n//(q**vp(n,q))
        star=0
        for p in factor(M) if M>1 else {}:
            star += (p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
        star += (q-1)*(sum(vp(L,q) for L in Ls)-(vp(n,q)-1))
        rhs=sum(len(Csets[idx])-1 for idx,(aa,dd) in I0)
        if star<rhs: bad['star'].append((n,q,family,Csets,star,rhs,Ls))
    return

def main():
    bad={'t7':[], 'star':[]}
    targets=[(6,6),(12,6),(18,6),(24,6),(30,9),(36,7)]
    for n,K in targets:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}: 覆盖数={len(cv)}", flush=True)
        for ch in cv:
            check_family([aps[i] for i in ch], bad)
    print("T7 反例:", len(bad['t7']))
    for x in bad['t7'][:5]: print("  ",x)
    print("(★) 反例:", len(bad['star']))
    for x in bad['star'][:8]:
        n,q,family,Csets,star,rhs,Ls=x
        print(f"   n={n} q={q} family={family}")
        print(f"     star={star} rhs={rhs} C={ {i:sorted(s) for i,s in Csets.items()} } Ls={Ls}")

if __name__=="__main__":
    main()
