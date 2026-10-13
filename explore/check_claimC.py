"""检验 Claim C: 全本质 F、lcmDiff = q^k M (q∤M)、∃i: q∤d_i  ==>  |F| >= bound(M) + q - 1。
   并核对手工 n=30 九块例。"""
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

def check(n,K,bad):
    aps,cv=covers(n,K)
    for ch in cv:
        family=[aps[i] for i in ch]
        card,ess,essL=eval_family(family)
        if not all(ess) or essL!=n: continue
        for q in factor(n):
            if not any(d%q!=0 for (a,d) in family): continue   # 裂块情形
            M=n//(q**vp(n,q))
            if card < boundv(M)+q-1:
                bad.append((n,q,card,family,boundv(M)+q-1))
    return len(cv)

def main():
    bad=[]
    for n,K in [(6,6),(12,6),(18,6),(24,6),(30,6),(36,7)]:
        c=check(n,K,bad)
        print(f"n={n} K={K} done (covers={c})", flush=True)
    print("Claim C 反例:", len(bad))
    for x in bad[:8]:
        n,q,card,family,tgt=x
        print(f"   n={n} q={q} card={card} need={tgt} family={family}")
    # 手工九块例
    ex=[(0,2),(1,10),(5,10),(7,10),(0,3),(13,30),(19,30),(23,30),(29,30)]
    card,ess,essL=eval_family(ex)
    print(f"\n手工例: card={card} all_ess={all(ess)} lcmDiff={essL} ")
    print(f"  覆盖检查:", all(any((x%30-a)%d==0 for a,d in ex) for x in range(30)))
    for q in factor(essL):
        M=essL//(q**vp(essL,q))
        print(f"  q={q}: 裂块? {any(d%q!=0 for a,d in ex)}: card={card} vs bound(M)+q-1={boundv(M)+q-1}")

if __name__=="__main__":
    main()
