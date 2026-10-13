"""判定: 是否会出现两个 Case-2 层 nu != nu' 同时 p|nu, p|nu' 且支撑纤维集相交（相对某 argmax c* 后仍重叠）。
   若无 ==> (A''-p) 的单层论证即足够（逐纤维 V_p(c) 只被一个 Case-2 层"高值"占用）。
   若有，打印最紧实例以供分析。"""
import sys
from math import gcd
from collections import Counter, defaultdict

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
def eval_family(family):
    M=lcmlist([d for (a,d) in family]) if family else 1
    cnt=[0]*M
    for (a,d) in family:
        for t in range(M//d): cnt[(a+t*d)%M]+=1
    ess=[any(cnt[(a+t*d)%M]==1 for t in range(M//d)) for (a,d) in family]
    essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
    return len(family), ess, essL
def covers(n,K,cap=60000):
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

def main():
    overlaps=[]; tot=0
    for n,K in [(36,7),(40,7),(44,7),(48,7),(60,7)]:
        aps,cv=covers(n,K)
        print(f"n={n} K={K}", flush=True)
        for ch in cv:
            family=[aps[i] for i in ch]
            card,ess,essL=eval_family(family)
            if not all(ess): continue
            n2=essL
            for q in factor(n2):
                if any(d%q!=0 for a,d in family): continue
                tot+=1
                byd=defaultdict(list)
                for a,d in family: byd[d].append(a%q)
                primes=set()
                for a,d in family:
                    for p in factor(d): primes.add(p)
                for p in primes:
                    V=[0]*q
                    for a,d in family:
                        c=a%q; v=vp(d//q,p)
                        if v>V[c]: V[c]=v
                    vmax=max(V)
                    cstars=[c for c in range(q) if V[c]==vmax]
                    # Case-2 层 (含 p 部分)
                    case2={}
                    for d,reslist in byd.items():
                        h=len(reslist); nu=d//q; b=boundv(nu)
                        if h> b+(q-1) and vp(nu,p)>=1:
                            case2[nu]=set(reslist)
                    # 对每个 c*，看剔除后是否仍有两层重叠
                    for cstar in cstars:
                        T={nu:(s-{cstar}) for nu,s in case2.items()}
                        nus=list(T.keys())
                        for i in range(len(nus)):
                            for j in range(i+1,len(nus)):
                                if T[nus[i]] & T[nus[j]]:
                                    overlaps.append((n2,q,p,cstar,nus[i],nus[j],sorted(T[nus[i]]),sorted(T[nus[j]]),family))
                                    break
                            else:
                                continue
                            break
    print(f"检查 {tot} 实例")
    print("多重叠事例数:", len(overlaps))
    for x in overlaps[:6]:
        n2,q,p,cstar,a,b,Ta,Tb,fam=x
        print(f"   n={n2} q={q} p={p} c*={cstar} nu={a},{b} T={Ta},{Tb} fam={fam}")

if __name__=="__main__":
    main()
