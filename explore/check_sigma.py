"""检验候选 sigma := Sigma_nu [m_nu - bound(nu)]_+ （同差块组松弛）:
   (S1) sigma(F) <= slack(F) = card - bound(lcmDiff)            [全本质族]
   (S2) 无裂块情形: sigma(F) <= Sigma_c sigma(F_c^0)
   (S3) 裂块情形: Sigma_c sigma(F_c^0) >= [Sigma(a_i-1) - Sigma_p(p-1)M_p]_+"""
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
    ess=[]
    for (a,d) in family:
        ess.append(any(cnt[(a+t*d)%M]==1 for t in range(M//d)))
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return len(family), ess, essL

def sigma_of(diffs):
    """sigma := Sigma_nu [m_nu - bound(nu)]_+ (diffs = 块差列表, 即 F_c^0 或全族的差)."""
    m=Counter(diffs)
    return sum(max(0, c-boundv(nu)) for nu,c in m.items())

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
    sigF=sigma_of([d for a,d in family])
    # (S1)
    if sigF> card-boundv(n):
        bad['S1'].append((n,card,sigF,family))
    for q in factor(n):
        # 纤维系统与 sigma(F_c^0)
        sigfiber=0; Ls=[]; Csets={}
        I0=[(idx,(a,d)) for idx,(a,d) in enumerate(family) if d%q!=0]
        for idx,_ in I0: Csets[idx]=set()
        for c in range(q):
            fb=fiber_blocks(family,q,c)
            ca,ce,cl=eval_family(fb)
            Ls.append(cl)
            sigfiber += sigma_of([d for (u,d),e in zip(fb,ce) if e])
            for (u,d),e in zip(fb,ce):
                if not e: continue
                for idx,(aa,dd) in I0:
                    if dd==d and d>1:
                        inv=pow(q%d,-1,d)
                        if ((aa-c)%d)*inv%d==u: Csets[idx].add(c)
        if not I0:   # 无裂块 (S2)
            if sigF>sigfiber:
                bad['S2'].append((n,q,family,sigF,sigfiber))
        else:        # 裂块 (S3)
            M=n//(q**vp(n,q))
            star=0
            for p in (factor(M) if M>1 else {}):
                star += (p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
            star += (q-1)*(sum(vp(L,q) for L in Ls)-(vp(n,q)-1))
            a={idx:len(s) for idx,s in Csets.items()}
            deficit=sum(a[idx]-1 for idx,_ in I0)-star
            if sigfiber < max(0,deficit):
                bad['S3'].append((n,q,family,{i:sorted(s) for i,s in Csets.items()},sigfiber,deficit,Ls))

def main():
    bad={'S1':[],'S2':[],'S3':[]}
    for n,K in [(6,6),(12,6),(18,6),(24,6),(30,6)]:
        aps,cv=covers(n,K)
        for ch in cv: check_family([aps[i] for i in ch], bad)
        print(f"n={n} K={K} done", flush=True)
    print("(S1) 反例:", len(bad['S1']))
    for x in bad['S1'][:5]: print("   ",x)
    print("(S2) 反例:", len(bad['S2']))
    for x in bad['S2'][:5]: print("   ",x)
    print("(S3) 反例:", len(bad['S3']))
    for x in bad['S3'][:6]: print("   ",x)

if __name__=="__main__":
    main()

# ---- 追加检验 (S2*) 与 (S4) ----
def main2():
    bad={'S2s':[],'S4':[],'S1':[]}
    for n,K in [(6,6),(12,6),(18,6),(24,6),(30,6)]:
        aps,cv=covers(n,K)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            nn=essL
            sigF=sigma_of([d for a,d in family])
            if sigF>card-boundv(nn): bad['S1'].append((nn,card,sigF,family))
            for q in factor(nn):
                sigfiber=0; Ls=[]; Csets={}
                I0=[(idx,(a,d)) for idx,(a,d) in enumerate(family) if d%q!=0]
                for idx,_ in I0: Csets[idx]=set()
                for c in range(q):
                    fb=fiber_blocks(family,q,c)
                    ca,ce,cl=eval_family(fb)
                    Ls.append(cl)
                    sigfiber += sigma_of([d for (u,d),e in zip(fb,ce) if e])
                    for (u,d),e in zip(fb,ce):
                        if not e: continue
                        for idx,(aa,dd) in I0:
                            if dd==d and d>1:
                                inv=pow(q%d,-1,d)
                                if ((aa-c)%d)*inv%d==u: Csets[idx].add(c)
                M=nn//(q**vp(nn,q))
                star=0
                for p in (factor(M) if M>1 else {}):
                    star += (p-1)*(sum(vp(L,p) for L in Ls)-vp(M,p))
                star += (q-1)*(sum(vp(L,q) for L in Ls)-(vp(nn,q)-1))
                if not I0:  # (S2*): star + sigfiber >= sigF
                    if star+sigfiber < sigF:
                        bad['S2s'].append((nn,q,family,star,sigfiber,sigF,card))
                else:       # (S4): sigfiber >= sigF + Sigma(a_i-1) - star
                    a={idx:len(s) for idx,s in Csets.items()}
                    need=sigF+sum(a[idx]-1 for idx,_ in I0)-star
                    if sigfiber < need:
                        bad['S4'].append((nn,q,family,sigfiber,need,sigF,star,{i:sorted(s) for i,s in Csets.items()}))
    print("(S1) 反例:", len(bad['S1']))
    print("(S2*) 反例:", len(bad['S2s']))
    for x in bad['S2s'][:6]: print("   ",x)
    print("(S4) 反例:", len(bad['S4']))
    for x in bad['S4'][:6]: print("   ",x)

if __name__=="__main__":
    import sys as _s
    if '--s2' in _s.argv: main2()
