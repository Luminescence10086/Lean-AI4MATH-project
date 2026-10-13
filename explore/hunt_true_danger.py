"""真·危险区搜索 v2 (修 randint): n ∈ {112,...,560}: 浅层1,2 过载 + 深层4 补全, lcm 强制."""
import random,sys
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
def vp(n,p):
    e=0
    while n%p==0: n//=p; e+=1
    return e
def lcmlist(xs):
    r=1
    for x in xs: r=r*x//gcd(r,x)
    return r
def chain(fam,N):
    mv=Counter(d for a,d in fam)
    S=sum(min(c,boundv(nu)) for nu,c in mv.items())
    res={"TGT":S>=boundv(N)}
    D=sum(min(max(0,c-boundv(nu)),len(factor(nu))-1) for nu,c in mv.items())
    sumE=0; res["Pp"]=res["Rp"]=res["Rpp"]=True
    for p in factor(N):
        alpha=vp(N,p)
        Lp=sum(min(c,(p-1)*vp(nu,p)+1) for nu,c in mv.items() if nu%p==0)
        bp=(p-1)*alpha+1
        if Lp<bp: res["Pp"]=False
        t=sum(1 for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
        if Lp+1<bp+t: res["Rp"]=False
        sumE+=Lp-bp
        O=set(vp(nu,p) for nu,c in mv.items() if nu%p==0 and c>boundv(nu))
        Sd={}
        for nu,c in mv.items():
            if nu%p: continue
            b_=vp(nu,p); Sd[b_]=Sd.get(b_,0)+min(c,(p-1)*b_+1)
        lhs=sum(v for b_,v in Sd.items() if b_ not in O)
        if lhs<(p-1)*max(0,alpha-sum(O)): res["Rpp"]=False
    res["R"]=sumE>=D-(len(factor(N))-1)
    return res
random.seed(7777)
tot=0; t2viol=0; bads=Counter(); ex=[]
for N in [112,176,208,240,304,368,560,784,880]:
    divs=[d for d in range(2,N+1) if N%d==0]
    l1=[d for d in divs if vp(d,2)==1]
    l2=[d for d in divs if vp(d,2)==2]
    l4=[d for d in divs if vp(d,2)>=4]
    if not l1 or not l2 or not l4: continue
    ntest=0
    for trial in range(500000):
        d1=random.choice(l1); d2=random.choice(l2); d4=random.choice(l4)
        lo1=boundv(d1)+1; hi1=min(d1,boundv(d1)+3)
        lo2=boundv(d2)+1; hi2=min(d2,boundv(d2)+3)
        if lo1>hi1 or lo2>hi2: continue
        c1=random.randint(lo1,hi1); c2=random.randint(lo2,hi2)
        fam=[(a,d1) for a in random.sample(range(d1),c1)]+[(a,d2) for a in random.sample(range(d2),c2)]
        cnt=[0]*N
        for a,d in fam:
            for t in range(N//d): cnt[(a+t*d)%N]+=1
        for _ in range(20):
            unc=[x for x in range(N) if cnt[x]==0]
            if not unc: break
            a=random.choice(unc)%d4
            if (a,d4) in fam: continue
            fam.append((a,d4))
            for t in range(N//d4): cnt[(a+t*d4)%N]+=1
        if any(c==0 for c in cnt): continue
        if lcmlist([d for a,d in fam])!=N: continue
        cnt=[0]*N
        for a,d in fam:
            for t in range(N//d): cnt[(a+t*d)%N]+=1
        if not all(any(cnt[(a+t*d)%N]==1 for t in range(N//d)) for a,d in fam): continue
        ntest+=1; tot+=1
        res=chain(fam,N)
        mv=Counter(d for a,d in fam)
        O=set(vp(nu,2) for nu,c in mv.items() if nu%2==0 and c>boundv(nu))
        if len(O)>=2 and sum(O)<vp(N,2):
            t2viol+=1
            if len(ex)<5: ex.append((N,dict(sorted(mv.items())),sorted(O),res))
        for k,v in res.items():
            if not v: bads[k]+=1
    print(f"n={N}: 真·lcm 全本质 {ntest}; 累计 (T'')违 {t2viol}; 链违 {dict(bads)}",flush=True)
print(f"总 {tot}; (T'')违 {t2viol}; 链违 {dict(bads)}")
for e in ex: print("  ",e)
