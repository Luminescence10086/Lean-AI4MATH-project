"""验证 Q_m = p: 普通(无挖点)类覆盖 of Z/p^m 的最小 F = Σ_β min(M_β, b(p^β))。
   枚举所有类覆盖（类 mod p^β, β=1..m）小规模。"""
import itertools
from math import gcd
def factor(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def boundv(n): return 1+sum(e*(p-1) for p,e in factor(n).items())

def minF(p,m,cap=8):
    N=p**m
    # 所有类: (a, beta) a< p^beta
    classes=[(a,b) for b in range(1,m+1) for a in range(p**b)]
    best=None; bestc=None
    # DFS over subsets with cap size
    def covers(class_set):
        covered=set()
        for a,b in class_set:
            for t in range(N//(p**b)): covered.add((a+t*(p**b))%N)
        return len(covered)==N
    for k in range(1,cap+1):
        for combo in itertools.combinations(classes,k):
            if covers(combo):
                from collections import Counter
                Mb=Counter(b for a,b in combo)
                F=sum(min(c,boundv(p**b)) for b,c in Mb.items())
                if best is None or F<best:
                    best=F; bestc=combo
        if best is not None and k>=p: break   # p 个 mod p 类已可覆盖, 不必更大
        if best is not None: break
    return best,bestc

for p,m in [(2,1),(2,2),(2,3),(3,1),(3,2),(5,1),(5,2)]:
    N=p**m
    if N>64: 
        print(f"p={p} m={m} (N={N} 跳过)"); continue
    b,c=minF(p,m,cap=min(6,N))
    print(f"p={p} m={m}: Q={b} (期望 p={p})  例={c}")
