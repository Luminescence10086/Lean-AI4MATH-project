"""检验逐素数强化 (★★★_p): (p-1)*M_p >= Sigma_{i in I0, p|d_i} (a_i - 1)  for each p | M."""
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

def minimal_covers(n,K):
    full=(1<<n)-1
    aps=[(a,d) for d in divs(n) for a in range(d)]
    masks=[]
    for (a,d) in aps:
        m=0
        for t in range(n//d): m|=1<<((a+t*d)%n)
        masks.append(m)
    covers=[]
    def dfs(start,covered,chosen):
        if covered==full: covers.append(tuple(chosen)); return
        if len(chosen)>=K: return
        for idx in range(start,len(aps)):
            if masks[idx]&~covered:
                dfs(idx+1,covered|masks[idx],chosen+[idx])
    dfs(0,0,[])
    return aps,covers

def main():
    ns=[int(x) for x in sys.argv[1:]] or [6,12,18,24,30,36]
    bad=[]; tot=0
    for n in ns:
        aps,covers=minimal_covers(n,5)
        for ch in covers:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess) or essL!=n: continue
            for q in factor(n):
                I0=[(idx,(a,d)) for idx,((a,d),e) in enumerate(zip(family,ess)) if d%q!=0]
                if not I0: continue
                # 纤维 + a_i
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
                # 逐素数检验
                for p in (factor(M) if M>1 else {}):
                    lhs=(p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
                    rhs=sum(len(Csets[idx])-1 for idx,(aa,dd) in I0 if dd%p==0)
                    tot+=1
                    if lhs<rhs: bad.append((n,q,p,family,{i:sorted(s) for i,s in Csets.items()},lhs,rhs,Ls))
    print(f"检查 {tot} 个 (实例,p)（全本质裂块）")
    print(f"(★★★_p) 反例: {len(bad)}")
    for x in bad[:8]:
        n,q,p,family,Cs,lhs,rhs,Ls=x
        print(f"    n={n} q={q} p={p} family={family}")
        print(f"      lhs={lhs} rhs={rhs} C={Cs} Ls={Ls}")

if __name__=="__main__":
    main()
