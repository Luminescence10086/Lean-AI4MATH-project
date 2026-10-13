"""植入私有点采样器: 按构造保证全本质.
   1) 随机 s 个差; 2) 随机 s 个互异私有点 x_i; 3) a_i := x_i mod d_i, 校验 x_j mod d_i != a_i (j≠i); 
   4) 补全覆盖(可含共享私有点的块? 不: 仅用满足避开所有私有点的块)."""
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
def planted(N,divs):
    s=random.randint(2,8)
    xs=random.sample(range(N),min(s,N))
    fam=[]
    for i in range(s):
        d=random.choice(divs)
        a=xs[i]%d
        ok=True
        for j in range(s):
            if j==i: continue
            if xs[j]%d==a: ok=False; break
        if not ok: continue
        fam.append((a,d))
    if not fam: return None
    # 贪心补: 只用避开全部私有点的块. 私有点集 = 上面 xs 中真正被唯一覆盖的? 保守: 全部 xs 前 len(fam) 个
    privset=set(xs[:len(fam)])
    cnt=[0]*N
    for a,d in fam:
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    for _ in range(30):
        unc=[x for x in range(N) if cnt[x]==0]
        if not unc: break
        u=random.choice(unc)
        d=random.choice(divs)
        a=u%d
        # 避开 privset
        if any(x%d==a for x in privset): continue
        added=False
        for t in range(N//d):
            if cnt[(a+t*d)%N]==0: added=True; break
        if not added: continue
        fam.append((a,d))
        for t in range(N//d): cnt[(a+t*d)%N]+=1
    if any(c==0 for c in cnt): return None
    # 校验全本质
    for a,d in fam:
        if not any(cnt[(a+t*d)%N]==1 for t in range(N//d)): return None
    return fam
def chain_check(fam,N):
    mv=Counter(d for a,d in fam)
    S=sum(min(c,boundv(nu)) for nu,c in mv.items())
    res={"TGT":S>=boundv(N)}
    D=sum(min(max(0,c-boundv(nu)),len(factor(nu))-1) for nu,c in mv.items())
    sumE=0
    res["Pp"]=True; res["Rp"]=True; res["Rpp"]=True
    nontriv=0
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
        if len(O)>=2 and sum(O)<alpha: nontriv+=1
    res["R"]=sumE>=D-(len(factor(N))-1)
    return res,nontriv
random.seed(424242)
tot=0; bads=Counter(); ntriv=0; ex=[]
for N in [48,60,72,84,96,120,180,240,360,420,720,840,1260,1680]:
    divs=[d for d in range(2,N+1) if N%d==0]
    ntest=0
    for trial in range(120000):
        fam=planted(N,divs)
        if fam is None: continue
        if lcmlist([d for a,d in fam])!=N: continue
        ntest+=1; tot+=1
        res,nt=chain_check(fam,N)
        ntriv+=nt
        for k,v in res.items():
            if not v:
                bads[k]+=1
                if len(ex)<10: ex.append((k,N,dict(sorted(Counter(d for a,d in fam).items()))))
    print(f"[植入] n={N}: 全本质 {ntest}; 累计违 {dict(bads)}",flush=True)
print(f"总计 {tot}; 违例 {dict(bads)}; |O|>=2 非平凡 {ntriv}")
for e in ex: print("  ",e)
