"""Explicit certificates for the line-lemma audit; n always comes from lcmlist."""
from collections import Counter
from math import gcd
import json


def lcmlist(xs):
    n = 1
    for x in xs:
        n = n * x // gcd(n, x)
    return n


def vp(n, p):
    b = 0
    while n % p == 0:
        n //= p
        b += 1
    return b


def factor(n):
    out = {}
    p = 2
    while p * p <= n:
        if n % p == 0:
            out[p] = vp(n, p)
            n //= p ** out[p]
        p += 1
    if n > 1:
        out[n] = 1
    return out


def bound(n):
    return 1 + sum((p - 1) * b for p, b in factor(n).items())


def audit(fam, p=2):
    n = lcmlist(d for a, d in fam)
    cnt = [sum(x % d == a % d for a, d in fam) for x in range(n)]
    private = [next((x for x in range(n) if x % d == a % d and cnt[x] == 1), None)
               for a, d in fam]
    assert min(cnt) >= 1 and all(x is not None for x in private)
    alpha = vp(n, p)
    groups = Counter(d for a, d in fam)
    O = sorted({vp(d, p) for d, m in groups.items() if d % p == 0 and m > bound(d)})
    lines = []
    for y in range(n // p ** alpha):
        M = Counter(vp(d, p) for a, d in fam
                    if d % p == 0 and (y - a) % (d // p ** vp(d, p)) == 0)
        F = sum(min(m, (p - 1) * b + 1) for b, m in M.items())
        sat = [b for b in O if M[b] >= (p - 1) * b + 1]
        if F >= (p - 1) * alpha + 1:
            lines.append(dict(y=y, M=dict(sorted(M.items())), F=F, saturated=sat))
    deep = sum(min(m, (p - 1) * alpha + 1)
               for d, m in groups.items() if vp(d, p) == alpha)
    result = dict(n=n, p=p, alpha=alpha, family=fam, private=private,
                  census=dict(sorted(groups.items())), O=O, sumO=sum(O),
                  achieved_lines=lines, deep_census=deep,
                  deep_target=(p - 1) * alpha + 1)
    result['TGT'] = sum(min(m, bound(d)) for d, m in groups.items()) >= bound(n)
    result['Rp'] = all(sum(min(m, (q - 1) * vp(d, q) + 1)
                          for d, m in groups.items() if d % q == 0)
                       >= (q - 1) * vp(n, q) + sum(d % q == 0 and m > bound(d)
                                                 for d, m in groups.items())
                       for q in factor(n))
    result['Pp'] = True
    result['Rpp'] = True
    sumE = 0
    for q in factor(n):
        aq = vp(n, q)
        Lq = sum(min(m, (q - 1) * vp(d, q) + 1) for d, m in groups.items() if d % q == 0)
        sumE += Lq - ((q - 1) * aq + 1)
        Oq = {vp(d, q) for d, m in groups.items() if d % q == 0 and m > bound(d)}
        Sq = sum(min(m, (q - 1) * vp(d, q) + 1)
                 for d, m in groups.items() if d % q == 0 and vp(d, q) not in Oq)
        result['Pp'] &= Lq >= (q - 1) * aq + 1
        result['Rpp'] &= Sq >= (q - 1) * max(0, aq - sum(Oq))
    D = sum(min(max(0, m - bound(d)), len(factor(d)) - 1) for d, m in groups.items())
    result['R'] = sumE >= D - (len(factor(n)) - 1)
    return result


if __name__ == '__main__':
    base = ([(a, 10) for a in [7, 2, 4, 3, 9, 8, 5, 6]]
            + [(a, 12) for a in [11, 7, 2, 9, 5, 1, 4, 0, 10]]
            + [(a, 120) for a in [20, 30, 51, 80, 90, 111]])
    audit(base)
    # Two disjoint copies, on residues 0 and 1 mod 3; the third residue
    # is partitioned by a binary prefix tree with depth 4.
    lifted = [(c + 3 * a, 3 * d) for c in [0, 1] for a, d in base]
    lifted += [(2 + 3 * a, 3 * d) for a, d in [(0, 2), (1, 4), (3, 8), (7, 16), (15, 16)]]
    result = audit(lifted)
    assert result['n'] == 720 and result['O'] == [1, 2]
    bad = [line for line in result['achieved_lines'] if len(line['saturated']) > 1]
    assert bad and result['sumO'] < result['alpha']
    assert result['deep_census'] < result['deep_target']
    assert all(result[k] for k in ['TGT', 'Pp', 'Rp', 'Rpp', 'R'])
    variant = lifted[:-1] + [(15, 16)]
    result_b = audit(variant)
    bad_b = [line for line in result_b['achieved_lines']
             if line['M'].get(result_b['alpha'], 0) > 0 and len(line['saturated']) > 1]
    assert result_b['sumO'] < result_b['alpha'] and bad_b
    assert all(result_b[k] for k in ['TGT', 'Pp', 'Rp', 'Rpp', 'R'])
    with open('explore/sigma_route_counterexample.json', 'w', encoding='utf-8') as output:
        json.dump(result, output, indent=2, ensure_ascii=False)
    with open('explore/sigma_route_counterexample_B.json', 'w', encoding='utf-8') as output:
        json.dump(result_b, output, indent=2, ensure_ascii=False)
    for name, r in [('A/V/deep', result), ('B', result_b)]:
        print(name, json.dumps({k: r[k] for k in ['n', 'alpha', 'census', 'O', 'sumO', 'deep_census', 'TGT', 'Pp', 'Rp', 'Rpp', 'R']}))
        print('y=6:', next(line for line in r['achieved_lines'] if line['y'] == 6))
