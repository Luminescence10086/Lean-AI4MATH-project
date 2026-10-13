"""检验 (★★): Sigma_{p|M} (p-1)*S_p >= Sigma_{I0}(a_i - 1),  S_p = Sigma_c v_p(L_c) - max_c v_p(L_c).
   若成立则 (★) 成立（因 M_p >= S_p，载体摊派），且 (★★) 是纯纤维-关联命题。"""
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
    ns=[int(x) for x in sys.argv[1:]] or [6,12,18,24,30,36,48]
    bad_ss=[]; bad_star=[]; tot=0
    for n in ns:
        aps,covers=minimal_covers(n,5)
        for ch in covers:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess) or essL!=n: continue
            for q in factor(n):
                I0=[(a,d) for (a,d),e in zip(family,ess) if d%q!=0]
                if not I0: continue
                # 纤维 + a_i（块 i 的本质片所在纤维集）
                Ls=[]; Csets=[set() for _ in family]
                for c in range(q):
                    fb=fiber_blocks(family,q,c)
                    ca,ce,cl=eval_family(fb)
                    Ls.append(cl)
                    # 把 fb 的块映射回原块：I0 块按 (u,d) 匹配，I1 块按纯块
                    for (u,d),e in zip(fb,ce):
                        if not e: continue
                        if d % 1==0 and d in [dd for (aa,dd) in family if dd%q!=0]:
                            # 可能是 I0 片：找出匹配的 I0 块
                            for idx,(aa,dd) in enumerate(family):
                                if dd%q!=0 and dd==d:
                                    # 检查是否是这个块的片：u == ((aa-c)*inv(q,d))%d
                                    if d>1:
                                        inv=pow(q%d,-1,d)
                                        if ((aa-c)%d)*inv%d == u: Csets[idx].add(c)
                        # I1 纯块：t-差 d = dd/q
                        for idx,(aa,dd) in enumerate(family):
                            if dd%q==0 and aa%q==c and dd//q==d:
                                dp=d
                                w=((aa-c)//q)%dp if dp>1 else 0
                                if w==u: Csets[idx].add(c)
                asum=sum(len(Csets[idx]) for idx,(aa,dd) in enumerate(family) if dd%q!=0)
                rhs=sum(len(Csets[idx])-1 for idx,(aa,dd) in enumerate(family) if dd%q!=0)
                M=n//(q**vp(n,q))
                ss=0; star=0
                for p in factor(M) if M>1 else {}:
                    sv=[vp(L,p) for L in Ls]
                    S=max(0, sum(sv)-max(sv)) if sv else 0
                    ss += (p-1)*S
                    star += (p-1)*(sum(sv)-vp(M,p))
                tot+=1
                if ss<rhs: bad_ss.append((n,q,family,Csets,rhs,ss,Ls))
                if star<rhs: bad_star.append((n,q,family,rhs,star,Ls))
    print(f"检查 {tot} 个 (全本质裂块, q) 实例")
    print(f"(★★) [S_p 和减最大版] 反例: {len(bad_ss)}")
    for x in bad_ss[:6]:
        n,q,family,Csets,rhs,ss,Ls=x
        print(f"    n={n} q={q} family={family} rhs={rhs} ss={ss} Ls={Ls}")
        print(f"      C_sets={[(i, sorted(c)) for i,c in enumerate(Csets) if c]}")
    print(f"(★) 原版 反例: {len(bad_star)}")
    for x in bad_star[:6]:
        n,q,family,rhs,star,Ls=x
        print(f"    n={n} q={q} family={family} rhs={rhs} star={star} Ls={Ls}")

if __name__=="__main__":
    main()
