"""检验 (PQ): 对全本质覆盖 F (lcmDiff = n), 对每个素 p | n, 投影 mod n'=n/p:
     π(AP(a,d)) = AP(a mod d', d'),  d' = d/p 若 p|d 否则 d      (d' | n' 恒成立)
   F' := {π(B)} 去重. 断言:
     (PQ)  Σ_ν min(m_ν, b(ν)) ≥ Σ_ν' min(m'_ν', b(ν')) + (p−1)
   同时报告: 投影覆盖 ℤ/n' 是否成立; Σmin(F') ≥ b(n') 是否成立(应成立, 由 IH).
   PQ 成立 ⟹ T²³′ 对 ω(n) 归纳: 投影取极小覆盖保持全本质, 用 IH 即得."""
import random, sys
from math import gcd
from collections import Counter

def factor(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def boundv(n): return 1+sum(e*(p-1) for p,e in factor(n).items())
def lcmlist(xs):
    r=1
    for x in xs: r=r*x//gcd(r,x)
    return r
def sigmin(mv):  # Σ min(m_ν, b(ν))
    return sum(min(c,boundv(nu)) for nu,c in mv.items())

def check_ess(fam,N):
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    if not all(c>0 for c in cnt): return False
    return all(any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam)

def covers_Zn(fam, N):
    covered=set()
    for a,d in fam:
        for t in range(N//d): covered.add((a+t*d)%N)
    return len(covered)==N

def project(fam, p):
    out=set()
    for a,d in fam:
        if d % p == 0:
            dp=d//p
            out.add((a % dp, dp))
        else:
            out.add((a % d, d))
    return sorted(out)

def pq_test(fam, n, verbose=False):
    """返回 (bad_list, info)"""
    if lcmlist([d for a,d in fam])!=n: return None,None
    mv=Counter(d for a,d in fam)
    S=sigmin(mv)
    bad=[]
    info=[]
    for p in factor(n):
        np_=n//p
        Fp=project(fam,p)
        if not covers_Zn(Fp, np_):
            bad.append(("投影不覆盖",p)); continue
        mvp=Counter(d for a,d in Fp)
        Sp=sigmin(mvp)
        ok_ih = Sp >= boundv(np_)
        ok_pq = S >= Sp + (p-1)
        info.append((p, S, Sp, boundv(np_), ok_ih, ok_pq))
        if not ok_pq: bad.append(("PQ违",p,S,Sp))
        if not ok_ih: bad.append(("IH违",p,Sp,boundv(np_)))
    return bad, info

# ---------- 1) 小 n 全枚举 (K ≤ 7) ----------
def small_enum():
    def covers(n,K,cap=400000):
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
    todo=[(12,7),(18,7),(24,7),(30,7)]
    for (n,K) in todo:
        aps,cv=covers(n,K)
        ntest=0; nbad=0; ex=[]
        for ch in cv:
            fam=[aps[i] for i in ch]
            if not check_ess(fam,n): continue
            bad,info=pq_test(fam,n)
            if bad is None: continue
            ntest+=1
            if bad:
                nbad+=1
                if len(ex)<3: ex.append((fam,bad))
        print(f"[全枚举] n={n} K={K}: 全本质族 {ntest}; PQ/IH 违 {nbad}", flush=True)
        for f,b in ex: print("   ",f,b)

# ---------- 2) 大 n 随机分层 ----------
def random_stress():
    random.seed(11)
    for N in [84, 96, 120, 180, 240]:
        divs=[d for d in range(1,N+1) if N%d==0]
        ntest=0; nbad=0; ex=[]
        for trial in range(120000):
            if ntest>=60000: break
            k=random.randint(2,4)
            fam=[]; used=set()
            for _ in range(k):
                d=random.choice([x for x in divs if x>=2])
                a=random.randrange(d)
                mcount=random.randint(1,min(d, max(1,int(1.2*boundv(d)-N//d))))
                for _ in range(mcount):
                    aa=(a+random.randrange(d))%d
                    if aa not in used:
                        fam.append((aa,d)); used.add(aa)
            fam=list(set(fam))
            covered=set()
            for a,d in fam:
                for t in range(N//d): covered.add((a+t*d)%N)
            G=[c for c in range(N) if c not in covered]
            fam2=fam+[(g,N) for g in G]
            if not check_ess(fam2,N): continue
            bad,info=pq_test(fam2,N)
            if bad is None: continue
            ntest+=1
            if bad:
                nbad+=1
                if len(ex)<3: ex.append((fam2,bad))
        print(f"[随机] n={N}: 全本质族 {ntest}; PQ/IH 违 {nbad}", flush=True)
        for f,b in ex: print("   ",f[:12],"...",b)

if __name__=="__main__":
    which=sys.argv[1] if len(sys.argv)>1 else "both"
    if which in ("small","both"): small_enum()
    if which in ("random","both"): random_stress()
