"""Independent private-point stars for old Pp/Rp; no matching algorithm.
Actual lcm and private witnesses are checked for every cover.
"""
from collections import Counter
from pathlib import Path
from random import Random
import json
from audit_sigma_route import lcmlist, factor, vp, bound
import verify_matching_path as samples


def setup(family):
    n = lcmlist(d for a, d in family)
    covers = [[i for i, (a, d) in enumerate(family) if x % d == a % d] for x in range(n)]
    assert all(covers)
    private = {}
    for x, indices in enumerate(covers):
        if len(indices) == 1:
            private.setdefault(indices[0], x)
    assert len(private) == len(family)
    coords = [(p, t) for p, alpha in factor(n).items() for t in range(alpha)]
    vectors = {tuple(x // p**t % p for p, t in coords): x for x in range(n)}
    assert len(vectors) == n
    return n, covers, private, coords, vectors


def star(family, data, carrier, chosen_coords):
    n, covers, private, coords, vectors = data
    x = private[carrier]
    base = [x // p**t % p for p, t in coords]
    chosen = {}
    for v in chosen_coords:
        p, t = coords[v]
        assert t < vp(family[carrier][1], p)
        for z in range(p):
            if z == base[v]:
                continue
            y = base.copy()
            y[v] = z
            point = vectors[tuple(y)]
            assert carrier not in covers[point]
            j = covers[point][0]
            assert vp(family[j][1], p) > t
            assert family[j][0] // p**t % p == z
            assert j not in chosen.values()
            chosen[(v, z)] = j
    assert carrier not in chosen.values()
    return chosen


def certificate(family, check_digits=False):
    data = setup(family)
    n, covers, private, coords, vectors = data
    census = Counter(d for a, d in family)
    results = {}
    for p, alpha in factor(n).items():
        carrier = next(i for i, (a, d) in enumerate(family) if vp(d, p) == alpha)
        selected = star(family, data, carrier, [v for v, (q, t) in enumerate(coords) if q == p])
        stars = set(selected.values())
        W = alpha * (p - 1)
        assert len(stars) == W
        used = Counter(family[i][1] for i in stars)
        for d, count in used.items():
            assert d % p == 0 and count <= vp(d, p) * (p - 1)
        pp = stars | {carrier}
        assert len(pp) == W + 1
        for d, count in Counter(family[i][1] for i in pp).items():
            assert count <= min(census[d], vp(d, p) * (p - 1) + 1)
        overfull = [d for d, count in census.items() if d % p == 0 and count > bound(d)]
        anchors = {next(i for i, (a, di) in enumerate(family) if di == d and i not in stars)
                   for d in overfull}
        rp = stars | anchors
        assert len(rp) == W + len(overfull)
        for d, count in Counter(family[i][1] for i in rp).items():
            assert count <= min(census[d], vp(d, p) * (p - 1) + 1)
        results[p] = dict(carrier=carrier, private_point=private[carrier],
                          star_blocks=sorted(stars), pp_selected=sorted(pp),
                          rp_selected=sorted(rp), overfull_groups=overfull)
    return dict(n=n, blocks=len(family), prime_certificates=results)


def main():
    named = json.loads(Path('explore/matching_path_certificates.json').read_text(encoding='utf-8'))
    report = dict(named={}, exhaustive={}, random_covers=0, large_true_lcm_cases=0)
    for name, data in named.items():
        report['named'][name] = certificate(data['family'])
    # A legal exact partition with two incomparable difference groups, no d=n block.
    n80 = [(a, 16) for a in range(0, 16, 2)] + [(a, 10) for a in range(1, 10, 2)]
    report['n80'] = certificate(n80)
    data = setup(n80)
    budgets = []
    for i, (a, d) in enumerate(n80):
        chosen = star(n80, data, i, [v for v, (p, t) in enumerate(data[3]) if t < vp(d, p)])
        used = set(chosen.values())
        unused_groups = {di for j, (aj, di) in enumerate(n80) if j not in used}
        budgets.append(dict(carrier_difference=d, star_size=len(used),
                            unused_groups=len(unused_groups), budget=len(used)+len(unused_groups)))
    assert data[0] == 80 and bound(80) == 9 and max(x['budget'] for x in budgets) == 7
    report['n80_single_carrier_budget'] = budgets
    # Arithmetic implication counterexample, explicitly NOT a legal covering family.
    m, d = 3, 6
    lp = {p: min(m, (p-1)*vp(d, p)+1) for p in factor(d)}
    assert all(lp[p] >= (p-1)*vp(d,p)+1 for p in lp)
    assert min(m, bound(d)) == 3 < bound(d) == 4
    report['arithmetic_only_counterexample'] = dict(n=6, census={'6': 3}, Lp=lp,
                                                   D=0, H=2, sumE=0, legal_cover=False)
    samples.certificate = certificate
    for n in [6, 12, 18, 24]:
        report['exhaustive'][str(n)] = samples.exhaustive(n, 7)
        print('exhaustive', n, report['exhaustive'][str(n)], flush=True)
    rng = Random(20261013)
    for N in [60,84,120,180,240,360,720,1680]:
        for gen in [samples.random_exact_partition, samples.rich_cover]:
            for _ in range(20):
                out = certificate(gen(N,rng))
                report['random_covers'] += 1
                report['large_true_lcm_cases'] += out['n'] >= 60 and out['blocks'] >= 7
    Path('explore/old_route_star_report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),
                                                       encoding='utf-8')
    print('passed:', sum(report['exhaustive'].values()), 'small covers;',
          report['random_covers'], 'random covers;', report['large_true_lcm_cases'], 'large true lcm cases')
    print('n80 single-carrier budget maximum:', max(x['budget'] for x in budgets), '<', bound(80))


if __name__ == '__main__':
    main()
