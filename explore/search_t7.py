"""穷举搜索：覆盖系统 (a_i mod d_i 覆盖 Z，d_i | n) 的本质部分与 T7/T'' 类不等式。

目标：
1) 找 T7（card >= bound(essLcm)）的反例；
2) 采集 slack = card + rho - bound(essLcm) 的结构数据（用于设计势函数 Phi）。
"""
import sys
from math import gcd

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def boundv(n):
    if n <= 1:
        return 1
    return 1 + sum(e * (p - 1) for p, e in factor(n).items())

def lm(a, b):
    return a * b // gcd(a, b)

def lcmlist(xs):
    r = 1
    for x in xs:
        r = lm(r, x)
    return r

def divs(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def enumerate_covers(n, K):
    """枚举所有"每个加入的块至少贡献一个新剩余类"的子族（含所有极小覆盖），大小 <= K。"""
    full = (1 << n) - 1
    aps = [(a, d) for d in divs(n) for a in range(d)]
    masks = []
    for (a, d) in aps:
        m = 0
        for t in range(n // d):
            m |= 1 << ((a + t * d) % n)
        masks.append(m)
    covers = []
    def dfs(start, covered, chosen):
        if covered == full:
            covers.append(tuple(chosen))
            return
        if len(chosen) >= K:
            return
        for idx in range(start, len(aps)):
            if masks[idx] & ~covered:
                dfs(idx + 1, covered | masks[idx], chosen + [idx])
    dfs(0, 0, [])
    return aps, covers

def evaluate(n, family):
    cnt = [0] * n
    for (a, d) in family:
        for t in range(n // d):
            cnt[(a + t * d) % n] += 1
    ess = []
    for (a, d) in family:
        ess.append(any(cnt[(a + t * d) % n] == 1 for t in range(n // d)))
    card = len(family)
    rho = card - sum(ess)
    essL = lcmlist([d for (a, d), e in zip(family, ess) if e]) if any(ess) else 1
    return card, rho, essL, ess

def main():
    ns = [int(x) for x in sys.argv[1:]] or [6, 8, 12, 16, 18, 20, 24, 30, 36]
    for n in ns:
        K = 6
        aps, covers = enumerate_covers(n, K)
        t7_bad = []       # card < bound(essLcm)
        tpp_bad = []      # card + rho < bound(essLcm)
        min_slack = {}    # (essLcm) -> min over covers of card+rho-bound
        min_card = {}     # (essLcm) -> min card
        for ch in covers:
            family = [aps[i] for i in ch]
            card, rho, essL, ess = evaluate(n, family)
            b = boundv(essL)
            if card < b:
                t7_bad.append((card, rho, essL, family, ess))
            if card + rho < b:
                tpp_bad.append((card, rho, essL, family, ess))
            s = card + rho - b
            if essL not in min_slack or s < min_slack[essL]:
                min_slack[essL] = s
            if essL not in min_card or card < min_card[essL]:
                min_card[essL] = card
        print(f"=== n={n}  covers(<= {K})={len(covers)} ===")
        if t7_bad:
            print("  T7 反例:")
            for card, rho, essL, family, ess in t7_bad[:5]:
                print(f"    card={card} rho={rho} essLcm={essL} bound={boundv(essL)} family={family} ess={ess}")
        if tpp_bad:
            print("  T'' 反例 (!!):")
            for card, rho, essL, family, ess in tpp_bad[:5]:
                print(f"    card={card} rho={rho} essLcm={essL} bound={boundv(essL)} family={family}")
        # 关键统计：对每个 essLcm，min card 与 bound 比较（T7 只在"无 junk 也能达到"时紧）
        for essL in sorted(min_card):
            print(f"  essLcm={essL:4d} bound={boundv(essL):3d} minCard={min_card[essL]:3d} minSlack={min_slack[essL]:3d}")

if __name__ == "__main__":
    main()
