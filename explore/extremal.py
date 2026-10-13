"""打印每个 essLcm 下的极小 card 覆盖族结构（找 T7 紧例的形状）。"""
import sys
from math import gcd

def factor(n):
    f = {}
    d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d,0)+1; n//=d
        d += 1
    if n > 1: f[n] = f.get(n,0)+1
    return f

def boundv(n):
    if n <= 1: return 1
    return 1 + sum(e*(p-1) for p,e in factor(n).items())

def lm(a,b): return a*b//gcd(a,b)
def lcmlist(xs):
    r=1
    for x in xs: r=lm(r,x)
    return r
def divs(n): return [d for d in range(1,n+1) if n%d==0]

def enumerate_covers(n, K):
    full=(1<<n)-1
    aps=[(a,d) for d in divs(n) for a in range(d)]
    masks=[]
    for (a,d) in aps:
        m=0
        for t in range(n//d): m |= 1<<((a+t*d)%n)
        masks.append(m)
    covers=[]
    def dfs(start, covered, chosen):
        if covered==full: covers.append(tuple(chosen)); return
        if len(chosen)>=K: return
        for idx in range(start,len(aps)):
            if masks[idx] & ~covered:
                dfs(idx+1, covered|masks[idx], chosen+[idx])
    dfs(0,0,[])
    return aps, covers

def evaluate(n, family):
    cnt=[0]*n
    for (a,d) in family:
        for t in range(n//d): cnt[(a+t*d)%n]+=1
    ess=[any(cnt[(a+t*d)%n]==1 for t in range(n//d)) for (a,d) in family]
    card=len(family)
    rho=card-sum(ess)
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return card,rho,essL,ess

def main():
    for n in [int(x) for x in sys.argv[1:]] or [6,12,18,24,30]:
        aps, covers = enumerate_covers(n, 6)
        best={}   # essLcm -> (card, family, ess)
        for ch in covers:
            family=[aps[i] for i in ch]
            card,rho,essL,ess=evaluate(n,family)
            key=essL
            if key not in best or card<best[key][0]:
                best[key]=(card,family,ess)
        print(f"=== n={n} ===")
        for essL in sorted(best):
            card,family,ess=best[essL]
            fs=" ".join(f"{a}%{d}{'' if e else '(junk)'}" for (a,d),e in zip(family,ess))
            tag = "TIGHT" if card==boundv(essL) else f"slack{card-boundv(essL)}"
            print(f"  essLcm={essL:3d} bound={boundv(essL):2d} card={card:2d} {tag}: {fs}")

if __name__=="__main__":
    main()
