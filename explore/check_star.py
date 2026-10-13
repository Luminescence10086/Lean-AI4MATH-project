"""检验全本质情形裂块步的核心不等式 (★):
   Sigma_p (p-1)*M_p + junksum >= (q-1)*#I0
   其中 (全本质族 F, N=lcmDiff, q|N, I0={q∤d}):
   L_c = lcmDiff(纤维 c 的本质块, t-坐标), M_p = Sigma_c v_p(L_c) - v_p(N/q),
   junksum = Sigma_c #{纤维 c 中非本质块}.
   等价地: card(F) >= bound(N) + [IH-slack 项]（(★) 是不带 slack 的充分条件）。"""
import sys
from itertools import combinations
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
    """family: [(res,diff)] on Z."""
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
    star_bad=[]; t7_bad=[]; tot=0
    for n in ns:
        aps,covers=minimal_covers(n,5)
        for ch in covers:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue          # 只测全本质族
            if essL != n: continue             # lcmDiff=n
            if card<boundv(n): t7_bad.append((n,card,family))
            for q in factor(n):
                I0=[(a,d) for (a,d),e in zip(family,ess) if d%q!=0]
                if not I0: continue            # 裂块情形
                Ls=[]; junksum=0
                for c in range(q):
                    fb=fiber_blocks(family,q,c)
                    ca,ce,cl=eval_family(fb)
                    Ls.append(cl); junksum += ca-sum(ce)
                M={}
                for p in factor(n):
                    s=sum(vp(L,p) for L in Ls)
                    if p==q: M[p]=s-vp(n//1,p)+1
                    else: M[p]=s-vp(n,p)
                    # v_p(N/q) = v_p(N) - [p=q]
                lhs=sum((p-1)*M[p] for p in M)+junksum
                rhs=(q-1)*len(I0)
                if lhs<rhs:
                    star_bad.append((n,q,card,family,junksum,M,lhs,rhs,len(I0)))
                tot+=1
    print(f"检查 {tot} 个 (全本质族, q) 实例（lcmDiff=n, 裂块情形）")
    print(f"T7(card>=bound) 反例: {len(t7_bad)}")
    for x in t7_bad[:5]: print("   ",x)
    print(f"(★) 反例: {len(star_bad)}")
    for x in star_bad[:8]:
        n,q,card,family,junksum,M,lhs,rhs,nI0=x
        print(f"    n={n} q={q} card={card} family={family}")
        print(f"      junksum={junksum} M={M} lhs={lhs} rhs={rhs} (#I0={nI0})")

if __name__=="__main__":
    main()
