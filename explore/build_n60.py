"""构造 n=60 的两 Case-2 层实例：A = 6 类 mod 12, B = 7 类 mod 20, G = 补类 mod 60。
   检验: 覆盖 / 全本质 / Case-2(h(6)>5, h(10)>6) / (A') 与 (A''-p=2) 的真值。"""
import itertools
from math import gcd
from collections import Counter

def boundv(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return 1+sum(e*(p-1) for p,e in f.items())
def vp(n,p):
    e=0
    while n and n%p==0: n//=p; e+=1
    return e

def eval_family(family, N):
    cnt=[0]*N
    for a,d in family:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    ess=[any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in family]
    cover=all(c>0 for c in cnt)
    return cover, ess

best=None
import random
random.seed(1)
N=60
for trial in range(200000):
    A=random.sample(range(12),6)
    B=random.sample(range(20),7)
    fam=[(a,12) for a in A]+[(b,20) for b in B]
    covered=set()
    for a,d in fam:
        for t in range(N//d): covered.add((a+t*d)%N)
    G=[c for c in range(N) if c not in covered]
    fam2=fam+[(g,60) for g in G]
    cover,ess=eval_family(fam2,N)
    if cover and all(ess):
        # Case-2: q=2 拆 d: nu = d/2
        h6=len(A); h10=len(B)
        c2_6=(h6> boundv(6)+2-1); c2_10=(h10> boundv(10)+2-1)
        if c2_6 and c2_10:
            best=(A,B,G,fam2,cover,ess,h6,h10,c2_6,c2_10)
            break
if best:
    A,B,G,fam2,cover,ess,h6,h10,c26,c210=best
    print("找到两 Case-2 层实例!")
    print("  A(6类 mod12)=",sorted(A),"  B(7类 mod20)=",sorted(B),"  |G|=",len(G))
    print(f"  h(6)={h6} > b(6)+1={boundv(6)+1} ✓ Cf2={c26};  h(10)={h10} > b(10)+1={boundv(10)+1} ✓ Cf2={c210}")
    print("  cover=",cover," all-essential=",all(ess))
    # 纤维 (q=2): I0 (2∤d): 无(d=12,20,60 全偶) ==> case (a) ✓
    Ls=[]
    for c in range(2):
        sub=[((a-c)//2, d//2) for a,d in fam2 if a%2==c]
        L=1
        for u,d in sub: L=L*d//gcd(L,d)
        Ls.append(L)
    print("  纤维 lcmDiff:",Ls)
    V2=[0,0]
    for a,d in fam2:
        c=a%2; v=vp(d//2,2)
        if v>V2[c]: V2[c]=v
    M2=sum(V2)-max(V2)
    print(f"  V_2={V2} M_2={M2}")
    # (A''-p=2): Sigma_{Case-2,p|nu} v_2(nu)(n_+-1) <= M_2 ?
    def nplus(classes, mod, q):
        return len(set(c%q for c in classes))
    np6=nplus(A,12,2); np10=nplus(B,20,2)
    lhs=vp(6,2)*(np6-1)+vp(10,2)*(np10-1)
    print(f"  (A''-p): LHS={lhs} (np6={np6},np10={np10}) vs M_2={M2}  ==> {'反例!' if lhs>M2 else '成立'}")
    # (A'): Sigma (n_+-1)(b-1) vs Sigma_p(p-1)M_p
    claim=(np6-1)*(boundv(6)-1)+(np10-1)*(boundv(10)-1)
    star=0
    for p in [2,3,5]:
        V=[0,0]
        for a,d in fam2:
            c=a%2; v=vp(d//2,p)
            if v>V[c]: V[c]=v
        star+=(p-1)*(sum(V)-max(V))
    print(f"  (A'): claim={claim} vs Sigma(p-1)M_p={star}  ==> {'反例!' if claim>star else '成立'}")
    print("  族:",fam2)
else:
    print("随机搜索未找到：200000 次试验")
