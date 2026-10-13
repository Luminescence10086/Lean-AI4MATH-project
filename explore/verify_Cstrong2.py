"""C-strong 随机压力 + 精化: 线上可见的 over-full 组.
   C-strong: F(y°) >= (p−1)κ + t_p.
   C-ref:    F(y°) >= (p−1)κ + 1 + #{over-full ν∋p: y° ∈ C_j of ν 的某块}.  (y° ∈ μ-陪集)"""
import random,sys
from math import gcd
from collections import Counter
exec(open("verify_Cstrong.py").read().split('bad=0;tot=0;ex=[]')[0])
def cstrong_line(family,p,kap):
    """返回 (ok_strong, ok_ref, info): 对载体私有线."""
    ess,L=eval_family(family)
    mv=Counter(d for a,d in family)
    M=L//(p**kap)
    t_p=sum(1 for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
    carriers=[i for i,(a,d) in enumerate(family) if vp(d,p)==kap]
    best=None
    for i in carriers:
        a,d=family[i]
        for x in ess[i]:
            y=x%M
            Mb=Counter()
            vis=set()
            for a2,d2 in family:
                if d2%p==0:
                    mu2=d2//(p**vp(d2,p))
                    if (y-a2)%mu2==0:
                        Mb[vp(d2,p)]+=1
                        if mv[d2]>boundv(d2): vis.add(d2)
            form=sum(min(c,boundv(p**b)) for b,c in Mb.items())
            ok_s = form >= (p-1)*kap+t_p
            ok_r = form >= (p-1)*kap+1+len(vis)
            cand=(ok_s,ok_r,form,len(vis),t_p)
            if best is None or cand<best: best=cand
            if ok_s and ok_r: return best
    return best
random.seed(31)
tot=0;ns=0;nr=0;ex=[]
for N in [30,42,60,66,70,84,96,120,180,240]:
    divs=[d for d in range(2,N+1) if N%d==0]
    for trial in range(30000):
        k=random.randint(2,6)
        fam=[];used=set()
        for _ in range(k):
            d=random.choice(divs); a=random.randrange(d)
            cnt=random.randint(1,min(d,int(1.6*boundv(d))))
            for _ in range(cnt):
                aa=(a+random.randrange(d))%d
                if (aa,d) not in used: fam.append((aa,d)); used.add((aa,d))
        fam=list(set(fam))
        covered=set()
        for a,d in fam:
            for t in range(N//d): covered.add((a+t*d)%N)
        G=[c for c in range(N) if c not in covered]
        fam2=fam+[(g,N) for g in G]
        if lcmlist([d for a,d in fam2])!=N: continue
        ess,L=eval_family(fam2)
        if not all(e for e in ess): continue
        for p in factor(L):
            kap=vp(L,p)
            if kap<2: continue
            r=cstrong_line(fam2,p,kap)
            if r is None: continue
            tot+=1
            if not r[0]:
                ns+=1
                if len(ex)<4: ex.append(("C-strong",N,p,kap,r,dict(sorted(Counter(d for a,d in fam2).items()))))
            if not r[1]:
                nr+=1
                if len(ex)<8: ex.append(("C-ref",N,p,kap,r,dict(sorted(Counter(d for a,d in fam2).items()))))
    print(f"[随机] n={N}: 累计 {tot}; C-strong违 {ns}; C-ref违 {nr}",flush=True)
print("总:",tot,"C-strong违",ns,"C-ref违",nr)
for e in ex: print("  ",e)
