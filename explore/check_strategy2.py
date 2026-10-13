"""补全枚举：父族 = 极小覆盖 + 至多 2 个冗余块（d | n）。
   检验 T7 本身、R1（逐纤维 #ess >= bound），以及 T7 裂块步所需的 slack 不等式。"""
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
    ess=[]; priv=[]
    for (a,d) in family:
        ps={((a+t*d)%M) for t in range(M//d) if cnt[(a+t*d)%M]==1}
        priv.append(ps); ess.append(len(ps)>0)
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return len(family), ess, essL, priv

def fiber_blocks(family, p, c):
    out=[]
    for (a,d) in family:
        if d % p != 0:
            inv=pow(p % d, -1, d) if d>1 else 0
            u=((a-c) % d)*inv % d if d>1 else 0
            out.append((u,d))
        else:
            if a % p == c:
                dp=d//p
                w=((a-c)//p) % dp if dp>1 else 0
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
    ns=[int(x) for x in sys.argv[1:]] or [6,12,18,24,30]
    extra_max=2
    t7_bad=[]; r1_bad=[]; parts=[]
    tot=0
    for n in ns:
        aps,covers=minimal_covers(n,5)
        allidx=range(len(aps))
        for ch in covers:
            base=set(ch)
            rest=[i for i in allidx if i not in base]
            for k in range(extra_max+1):
                for extra in combinations(rest,k):
                    family=[aps[i] for i in list(ch)+list(extra)]
                    card,ess,essL,priv=eval_family(family)
                    N=essL
                    if card<boundv(N):
                        t7_bad.append((n,card,boundv(N),family,ess))
                    for p in factor(N):
                        I0e=[(a,d) for (a,d),e in zip(family,ess) if e and d%p!=0]
                        E0=len(I0e)
                        asum=0
                        B=0; junksum=0; eps=0; cardsum=0
                        fibersets=[]
                        for c in range(p):
                            fb=fiber_blocks(family,p,c)
                            fibersets.append(fb)
                            ca,ce,cl,cp=eval_family(fb)
                            cardsum+=ca; B+=boundv(cl); junksum+=ca-sum(ce); eps+=sum(ce)-boundv(cl)
                            if sum(ce)<boundv(cl):
                                r1_bad.append((n,p,c,family,ess,ce,cl,fb))
                        # a_i：本质裂块在几根纤维里"片本质"
                        for (a,d) in I0e:
                            cnt_f=0
                            for c in range(p):
                                fb=fibersets[c]
                                ca,ce,cl,cp=eval_family(fb)
                                for (u,nu),e in zip(fb,ce):
                                    # 找该块在纤维 c 的片
                                    if nu==d and ((a-c) % d)*pow(p % d,-1,d) % d == u:
                                        if e: cnt_f+=1; break
                            asum+=cnt_f
                        N0=sum(1 for (a,d),e in zip(family,ess) if not e and d%p!=0)
                        N1=sum(1 for (a,d),e in zip(family,ess) if not e and d%p==0)
                        rhs=(p-1)*(E0+N0)-(B-boundv(N))
                        if junksum+eps < rhs:
                            parts.append((n,p,family,ess,junksum,eps,rhs,E0,N0,N1,asum,B,boundv(N)))
                        tot+=1
    print(f"检查 {tot} 个 (family,p) 实例（父族=极小覆盖+≤2冗余）")
    print(f"T7 反例: {len(t7_bad)}")
    for x in t7_bad[:5]: print("   ",x)
    print(f"R1 反例: {len(r1_bad)}")
    for x in r1_bad[:5]:
        n,p,c,family,ess,ce,cl,fb=x
        print(f"    n={n} p={p} c={c} parent={family} parent_ess={ess}")
        print(f"      fiber={fb} fiber_ess={ce} lcm={cl} bound={boundv(cl)}")
    print(f"裂块步 slack 缺口 (junksum+eps < rhs): {len(parts)}")
    for x in parts[:5]:
        n,p,family,ess,junksum,eps,rhs,E0,N0,N1,asum,B,bN=x
        print(f"    n={n} p={p} family={family} ess={ess}")
        print(f"      junksum={junksum} eps={eps} rhs={rhs} E0={E0} N0={N0} N1={N1} asum={asum} B={B} boundN={bN}")

if __name__=="__main__":
    main()
