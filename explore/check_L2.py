"""验证结构引理 L2：
   覆盖族、n=essLcm、p|n 素数、i 本质且 p∤d_i  ==>  块 i 的私有点恰落在一个 mod p 纤维里。
   同时输出违例（若有）与统计。"""
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

def main():
    ns=[int(x) for x in sys.argv[1:]] or [6,12,18,24,30,36,48,60]
    bad=[]
    stats={}
    for n in ns:
        aps,covers=enumerate_covers(n,6)
        for ch in covers:
            family=[aps[i] for i in ch]
            M=lcmlist([d for (a,d) in family])   # 私有点在 mod M 下判定
            cnt=[0]*M
            for (a,d) in family:
                for t in range(M//d): cnt[(a+t*d)%M]+=1
            ess=[]
            priv={}   # i -> set of private residues mod M
            for i,(a,d) in enumerate(family):
                ps={((a+t*d)%M) for t in range(M//d) if cnt[(a+t*d)%M]==1}
                priv[i]=ps
                ess.append(len(ps)>0)
            essL=lcmlist([d for (a,d),e in zip(family,ess) if e]) if any(ess) else 1
            for p in factor(essL):          # p | essLcm
                for i,(a,d) in enumerate(family):
                    if ess[i] and d%p!=0:
                        fibs={(x%p) for x in priv[i]}
                        key=(len(fibs), a, d, tuple(sorted(family)), tuple(ess))
                        if len(fibs)!=1:
                            bad.append((n,p,i,a,d,fibs,sorted(family),ess,essL))
                        stats[len(fibs)]=stats.get(len(fibs),0)+1
    print("纤维数分布 (a_i 值 -> 出现次数):", dict(sorted(stats.items())))
    if bad:
        print(f"L2 反例 {len(bad)} 个：")
        for n,p,i,a,d,fibs,fam,ess,essL in bad[:10]:
            print(f"  n={n} p={p} block{i}={a}%{d} fibers={fibs} essLcm={essL} family={fam} ess={ess}")
    else:
        print("无 L2 反例 ✓")

if __name__=="__main__":
    main()
