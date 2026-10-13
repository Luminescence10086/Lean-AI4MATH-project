"""记录 n=60 关键实例（对 (D)/(A') 路线为反例，对 (S5)/(TGT) 为通过例）并输出精确数据。"""
from math import gcd
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
N=60
A=list(range(6)); B=list(range(8))
fam=[(a,12) for a in A]+[(b,20) for b in B]
covered=set()
for a,d in fam:
    for t in range(N//d): covered.add((a+t*d)%N)
G=[c for c in range(N) if c not in covered]
fam2=fam+[(g,60) for g in G]
cnt=[0]*N
for a,d in fam2:
    for t in range(N//d): cnt[(a+t*d)%N]+=1
ess=[any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam2]
print("=== n=60 关键实例 ===")
print("A(6类 mod12):",A,"  B(8类 mod20):",B,"  |G|:",len(G),"(补类 mod 60)")
print("card =",len(fam2),"  cover =",all(c>0 for c in cnt),"  all-essential =",all(ess))
print("lcmDiff =",60)
print("σ(F) =", max(0,6-boundv(12))+max(0,8-boundv(20))+max(0,len(G)-boundv(60)),
      " b(12)=",boundv(12)," b(20)=",boundv(20)," b(60)=",boundv(60))
print("slack = card - bound(60) =",len(fam2)-boundv(60))
# 纤维
for c in range(2):
    sub=sorted(set((a-c)//2 for a,d in fam2 if a%2==c for _ in [0]))
    print(f" fiber {c}: t-差集合(部分统计) n={len([1 for a,d in fam2 if a%2==c])}")
Ls=[]
for c in range(2):
    L=1
    for a,d in fam2:
        if a%2==c:
            dd=d//2; L=L*dd//gcd(L,dd)
    Ls.append(L)
print(" Ls =",Ls)
V={p:[0,0] for p in [2,3,5]}
for a,d in fam2:
    c=a%2
    for p in [2,3,5]:
        v=vp(d//2,p)
        if v>V[p][c]: V[p][c]=v
print(" V_p:",{p:V[p] for p in V})
print(" Σ(p-1)M_p =",sum((p-1)*(sum(V[p])-max(V[p])) for p in V))
# δ 分解（对 (D) 路线的反例性）
for d,lab in [(12,"nu=6"),(20,"nu=10"),(60,"nu=30")]:
    h=sum(1 for a,dd in fam2 if dd==d)
    nu=d//2; b=boundv(nu)
    bd=[0,0]
    for a,dd in fam2:
        if dd==d: bd[a%2]+=1
    dist=sum(max(0,x-b) for x in bd)
    X=max(0,h-b-1)
    print(f" {lab}: h={h} b={b} 分布={bd} X={X} D={dist} δ={max(0,X-dist)}")
