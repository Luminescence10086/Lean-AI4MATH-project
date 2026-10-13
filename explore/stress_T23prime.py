"""对抗性压力测试 T23prime（σ ≤ card − bound(lcmDiff)）于高 n：
   分层构造: 选若干"层" (d_i 与类子集)，加补类整流块，检验 覆盖/全本质/T23prime。
   n ∈ {84, 96, 120, 180}，各随机 30 万次。"""
import random
from math import gcd
from collections import Counter

def factor(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def boundv(n):
    return 1+sum(e*(p-1) for p,e in factor(n).items())
def lm(a,b): return a*b//gcd(a,b)
def lcmlist(xs):
    r=1
    for x in xs: r=lm(r,x)
    return r

def check(fam, N):
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    if not all(c>0 for c in cnt): return None
    ess=[any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam]
    if not all(ess): return None
    L=lcmlist([d for a,d in fam])
    card=len(fam)
    m=Counter(d for a,d in fam)
    sig=sum(max(0,c-boundv(nu)) for nu,c in m.items())
    return card, L, sig, card-boundv(L)

def main():
    random.seed(7)
    worst={}
    for N in [84, 96, 120, 180]:
        divs=[d for d in range(1,N+1) if N%d==0]
        best=None
        for trial in range(300000):
            k=random.randint(2,4)
            fam=[]
            used=set()
            for _ in range(k):
                d=random.choice([x for x in divs if x>=2])
                a=random.randrange(d)
                # 该层取至多 d 个类（子集）
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
            r=check(fam2,N)
            if r is None: continue
            card,L,sig,slack=r
            margin=slack-sig
            if best is None or margin<best[0]:
                best=(margin,card,L,sig,slack,list(fam))
            if margin<0:
                print(f"!! T23prime 反例 n={N}: card={card} σ={sig} slack={slack}")
                print("   family=",fam2)
                return
        if best: print(f"n={N}: 最紧 (slack−σ)={best[0]}  card={best[1]} lcmDiff={best[2]} σ={best[3]}")
    print("pressure: T23prime survived all tiers")

if __name__=="__main__":
    main()
