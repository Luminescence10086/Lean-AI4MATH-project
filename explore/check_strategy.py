"""验证 T7 裂块步证明策略的两个子断言（对真实可实现的纤维系统）：
   R1: 对每根纤维 c： #ess(F_c) >= bound(essLcm F_c)   [即 card >= bound + #junk]
   R2: 计数条件 Sigma_c #junk(F_c) >= (p-1)#I0 - (B - bound N)
"""
import sys
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

def enumerate_covers(n,K):
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

def eval_family(family):
    """family: list of (res, diff) APs in Z. Returns (card, ess list, essLcm, private sets)."""
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
    """把 family 按 mod p 纤维 c 分解成 t-坐标 AP 表 [(u, nu)]。"""
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

def main():
    ns=[int(x) for x in sys.argv[1:]] or [6,12,18,24,30]
    r1_bad=[]; r2_bad=[]; tot=0
    for n in ns:
        aps,covers=enumerate_covers(n,6)
        for ch in covers:
            family=[aps[i] for i in ch]
            card,ess,essL,priv=eval_family(family)
            N=essL
            for p in factor(N):
                I0=[(a,d) for (a,d),e in zip(family,ess) if e and d%p!=0]      # 本质裂块
                I1=[(a,d) for (a,d),e in zip(family,ess) if e and d%p==0]
                N0=sum(1 for (a,d),e in zip(family,ess) if not e and d%p!=0)    # 非本质裂块
                N1=sum(1 for (a,d),e in zip(family,ess) if not e and d%p==0)
                rho0=N0+N1; E0=len(I0)
                # a_i：本质裂块的本质片数
                asum=0
                for (a,d) in I0:
                    fibers=set()
                    for c in range(p):
                        fb=fiber_blocks([(a,d)],p,c)
                        ca,ce,cl,cp=eval_family(fb)
                        if any(ce): fibers.add(c)
                    asum+=len(fibers)
                B=0; junksum=0
                for c in range(p):
                    fb=fiber_blocks(family,p,c)
                    ca,ce,cl,cp=eval_family(fb)
                    B+=boundv(cl)
                    junksum+=ca-sum(ce)
                    if sum(ce) < boundv(cl):   # R1 违规
                        r1_bad.append((n,p,c,family,ess,ce,cl,fb))
                rhs=(p-1)*E0-(B-boundv(N))
                if junksum < rhs:              # R2 违规
                    r2_bad.append((n,p,family,ess,junksum,rhs,N0,N1,E0,asum,B,boundv(N)))
                tot+=1
    print(f"检查 {tot} 个 (cover,p) 实例")
    print(f"R1 违规: {len(r1_bad)}")
    for x in r1_bad[:6]:
        n,p,c,family,ess,ce,cl,fb=x
        print(f"  n={n} p={p} c={c} family={family} ess={ess} fiber_ess={ce} lcm={cl} bound={boundv(cl)} fiber={fb}")
    print(f"R2 违规: {len(r2_bad)}")
    for x in r2_bad[:6]:
        n,p,family,ess,junksum,rhs,N0,N1,E0,asum,B,bN=x
        print(f"  n={n} p={p} family={family} junksum={junksum} rhs={rhs} N0={N0} N1={N1} E0={E0} asum={asum} B={B} boundN={bN}")

if __name__=="__main__":
    main()
