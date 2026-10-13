"""逐层配对检验 (PL-ℓ): 对 (PC) 实例的全树, 按根层 ℓ 分组:
     PROV_ℓ := Σ_{depth(X)=ℓ−1} prov_X  ≥  LOSS_ℓ := Σ_{depth(X)+β=ℓ, β≥2} D^X_β
   其中 prov_X := M_1(X) + Σ_c τ_c − b(p^{κ_X}) (全节点; 叶: prov = F − τ),
   τ_c := 0 若 c 被单个类完全覆盖(free), 否则 b(p^{κ_c}) 若 c 是挖点链, 否则 p。
   望远镜恒等: E_root = Σ_ℓ PROV_ℓ − Σ_ℓ LOSS_ℓ (精确), 且 PROV_1 ≥ 0。
   若 (PL-ℓ) 对一切 ℓ≥2 成立 ⟹ E_root ≥ 0 得证。"""
import sys
sys.setrecursionlimit(100000)

def factor(n):
    f={}; d=2; m=n
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def boundv(n): return 1+sum(e*(p-1) for p,e in factor(n).items())

def enum_pc(p, kappa, maxsize=None, cap=200000):
    """枚举 Z/p^κ 的类覆盖 family(类=(beta,a), beta∈[1,κ]) 且含挖点 A*={x*}:
       x* 仅被点类 A* 覆盖。返回 (classes, covers)。"""
    classes=[]
    for beta in range(1,kappa+1):
        for a in range(p**beta):
            classes.append((beta,a))
    N=p**kappa
    masks=[]
    for (beta,a) in classes:
        m=0
        for x in range(N):
            if x % p**beta == a % p**beta: m |= 1<<x
        masks.append(m)
    full=(1<<N)-1
    out=[]
    def dfs(start, covered, chosen):
        if len(out)>cap: return
        if covered==full:
            out.append(tuple(chosen)); return
        if maxsize and len(chosen)>=maxsize: return
        # 剪枝: 剩余类即使全加也盖不满 -> 剪
        for idx in range(start,len(classes)):
            if masks[idx] & ~covered:
                dfs(idx+1, covered|masks[idx], chosen+[idx])
    dfs(0,0,[])
    return classes, out

def is_puncture(classes, ch):
    """找 A*=(κ,a*) 点类使 x*=a* 不被其它类覆盖"""
    fam=[classes[i] for i in ch]
    for (beta,a) in fam:
        if beta!=KAPPA: continue
        xstar=a
        ok=True
        for (b2,a2) in fam:
            if (b2,a2)==(beta,a): continue
            if xstar % p**b2 == a2 % p**b2: ok=False; break
        if ok: return xstar
    return None

def analyze(p, kappa, classes, ch):
    """返回 (viol, info): 检查 (PL-ℓ) 与恒等式; viol 非空 = 反例。"""
    fam=set(classes[i] for i in ch)
    N=p**kappa
    xstar=is_puncture(classes, ch)
    if xstar is None: return None
    b_of={m: boundv(p**m) for m in range(0,kappa+2)}
    def in_fam(beta,a): return (beta,a) in fam
    def Xcoset(t, X):  # 深度 t 纤维: X∈[0,p^t)
        return X
    def M_of(t, X, beta):  # M_β(X): root-level t+β 类且 coset ⊆ X
        lvl=t+beta
        if lvl>kappa: return 0
        return sum(1 for x in range(p**lvl) if (lvl,x) in fam and x % (p**t) == X % (p**t))
    def free_cover(t, X):
        # ∃ 类(β,a), β≤t, coset ⊇ X (即 a ≡ X mod p^β)
        for beta in range(1,t+1):
            if (beta, X % (p**beta)) in fam: return True
        return False
    def contains_x(t, X): return xstar % (p**t) == X % (p**t)
    # 节点遍历: 自底向上
    nodes={}  # (t,X) -> dict
    for t in range(kappa-1,-1,-1):
        for X in range(p**t):
            kX=kappa-t
            M1=M_of(t,X,1)
            free=free_cover(t,X)
            if free: tau=0
            elif contains_x(t,X): tau=b_of[kX]      # 挖点链
            else: tau=p
            F=sum(min(M_of(t,X,b), b_of[b]) for b in range(1,kX+1))
            E=F-tau
            nodes[(t,X)]=dict(M1=M1,free=free,tau=tau,F=F,E=E,kX=kX)
    # children 的 tau 与 D
    prov={}; loss={}
    for l in range(1,kappa+1): loss[l]=0
    for (t,X),nd in nodes.items():
        kX=nd['kX']
        if kX>=2:
            stau=0
            children=[]
            for c in range(p):
                chX=X + c*(p**t)   # 深度 t+1 的纤维 (mod p^{t+1})
                children.append(chX)
                stau+=nodes[(t+1,chX)]['tau']
            provX=nd['M1']+stau-nd['tau']
            prov[(t,X)]=provX
            # sanity: provX == E − ΣE_c + ΣD
            sE=sum(nodes[(t+1,chX)]['E'] for chX in children)
            sD=0
            for b in range(2,kX+1):
                loc=0
                for chX in children:
                    # child 内层 β−1 = M_{β−1}(child)
                    loc+=min(M_of(t+1,chX,b-1), b_of[b-1])
                glob=min(M_of(t,X,b), b_of[b])
                D=loc-glob
                sD+=D
                l=t+b
                if l<=kappa: loss[l]+=D
            if provX != nd['E']-sE+sD:
                return (("prov残差违",p,kappa,ch,t,X,provX,nd['E'],sE,sD), None)
        else:
            prov[(t,X)]=nd['E']
    # 逐层
    PROV={l:0 for l in range(1,kappa+1)}
    for (t,X),v in prov.items(): PROV[t+1]+=v
    viol=[]
    violPL=0
    for l in range(2,kappa+1):
        if PROV[l] < loss[l]:
            violPL+=1
    # 望远镜恒等
    Er=nodes[(0,0)]['F']-b_of[kappa]
    tot=sum(PROV.values())-sum(loss.values())
    if Er!=tot: viol.append(("望远镜违",Er,tot))
    if Er<0: viol.append(("E_root<0",Er,0))
    if PROV[1]<0: viol.append(("PROV_1<0",PROV[1],0))
    # 前缀和瀑布不变量
    pref=[]; s=0
    for l in range(1,kappa+1):
        s+=PROV[l]-loss[l]; pref.append(s)
    minpref=min(pref)
    if minpref<0: viol.append(("PREFIX",minpref,pref))
    return (viol, dict(E=Er, PROV=PROV, loss=loss, pref=pref, violPL=violPL,
                       nodes={k:v for k,v in nodes.items()}, prov=prov))

if __name__=="__main__":
    global p, KAPPA
    tasks=[(2,2,7),(2,3,8),(2,4,9),(3,2,7),(3,3,9),(5,2,8)]
    for (p,KAPPA,maxK) in tasks:
        classes,covers=enum_pc(p,KAPPA,maxsize=maxK)
        print(f"p={p} κ={KAPPA}: 覆盖数 {len(covers)}", flush=True)
        nbad=0; npc=0; EXAMPLES=[]; nPL=0
        for ch in covers:
            r=analyze(p,KAPPA,classes,ch)
            if r is None: continue
            npc+=1
            viol,info=r
            if info: nPL+=info['violPL']
            if viol:
                nbad+=1
                if len(EXAMPLES)<2: EXAMPLES.append((ch,viol,info))
        print(f"   (PC)实例 {npc}; 反例 {nbad}; 违 PL-ℓ 的层-实例数 {nPL}", flush=True)
        for ch,viol,info in EXAMPLES:
            fam=[classes[i] for i in ch]
            print("   反例 ch=",fam)
            print("     viol=",viol[:3])
            if info:
                print("     PROV=",info['PROV'],"loss=",info['loss'],"E=",info['E'],"pref=",info['pref'])
                print("     nodes:")
                for (t,X),v in sorted(info['nodes'].items()):
                    if v['kX']>=2 or t>=KAPPA-2:
                        print("      t=%d X=%d τ=%d M1=%d free=%s kX=%d F=%d E=%d prov=%d"%(
                            t,X,v['tau'],v['M1'],v['free'],v['kX'],v['F'],v['E'],info['prov'].get((t,X),v['E'])))
