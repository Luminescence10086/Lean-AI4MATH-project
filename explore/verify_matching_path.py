"""Verify digit semantics and explicit slot-to-block certificates after path design.

Uses actual lcmlist, exhaustive K=7 small cases, and multiple large-case shapes.
Finite checks are diagnostics, not a proof of the general matching theorem.
"""
from collections import Counter
from pathlib import Path
from random import Random
import json
from audit_sigma_route import lcmlist, factor, vp, bound


def certificate(family, check_digits=False):
    n = lcmlist(d for a, d in family)
    masks = [sum(1 << x for x in range(a % d, n, d)) for a, d in family]
    full = (1 << n) - 1
    counts = [sum((mask >> x) & 1 for mask in masks) for x in range(n)]
    assert min(counts) > 0
    assert all(any(counts[x] == 1 for x in range(a % d, n, d)) for a, d in family)
    coordinates = [(p, t) for p, alpha in factor(n).items() for t in range(alpha)]
    slots = [(p, t, k) for p, t in coordinates for k in range(p - 1)]
    supports = [{(p, t) for p, t in coordinates if t < vp(d, p)} for a, d in family]
    assert len(slots) == bound(n) - 1
    for (a, d), support in zip(family, supports):
        assert sum(p - 1 for p, t in support) == bound(d) - 1
        if check_digits:
            for x in range(n):
                same_digits = all(x // p ** t % p == a // p ** t % p for p, t in support)
                assert same_digits == (x % d == a % d)
    if check_digits:
        # Injection of all residues into the coordinate product, whose size is n.
        assert len({tuple(x // p ** t % p for p, t in coordinates) for x in range(n)}) == n

    adjacency = [[i for i, support in enumerate(supports) if (p, t) in support]
                 for p, t, k in slots]
    matched_block = {}

    def augment(slot, seen):
        for block in adjacency[slot]:
            if block in seen:
                continue
            seen.add(block)
            if block not in matched_block or augment(matched_block[block], seen):
                matched_block[block] = slot
                return True
        return False

    for slot in range(len(slots)):
        assert augment(slot, set()), ('unsaturated slot', n, family, slots[slot])
    assert len(matched_block) == len(slots)
    assert len(set(matched_block.values())) == len(slots)
    anchor = next(i for i in range(len(family)) if i not in matched_block)
    selected = set(matched_block) | {anchor}
    selected_counts = Counter(family[i][1] for i in selected)
    matched_counts = Counter(family[i][1] for i in matched_block)
    group_counts = Counter(d for a, d in family)
    for d, m in group_counts.items():
        assert matched_counts[d] <= bound(d) - 1
        assert selected_counts[d] <= min(m, bound(d))
    assert len(selected) == bound(n)
    for block, slot in matched_block.items():
        assert slots[slot][:2] in supports[block]
    return dict(n=n, family=family, slots=slots,
                matching=[dict(slot=slots[s], block=i) for i, s in sorted(matched_block.items())],
                anchor=anchor, selected=sorted(selected), bound=bound(n),
                selected_census=dict(sorted(selected_counts.items())))


def exhaustive(n, K):
    aps = [(a, d) for d in range(1, n + 1) if n % d == 0 for a in range(d)]
    masks = [sum(1 << x for x in range(a, n, d)) for a, d in aps]
    full = (1 << n) - 1
    count = 0

    def search(chosen, covered, forbidden):
        nonlocal count
        if covered == full:
            certificate([aps[i] for i in chosen])
            count += 1
            return
        if len(chosen) == K:
            return
        # An uncovered point must be covered in every completion. Branches are
        # disjoint by forbidding earlier options for that point in later branches.
        uncovered = [x for x in range(n) if not (covered >> x) & 1]
        options = min(([i for i, mask in enumerate(masks)
                        if i not in forbidden and (mask >> x) & 1] for x in uncovered), key=len)
        forbidden_here = set(forbidden)
        for i in options:
            if masks[i] & ~covered:
                new_chosen = chosen + [i]
                # Once a chosen block has no private point, later additions cannot restore it.
                irredundant = True
                for j in new_chosen:
                    others = 0
                    for k in new_chosen:
                        if k != j:
                            others |= masks[k]
                    if not masks[j] & ~others:
                        irredundant = False
                        break
                if irredundant:
                    search(new_chosen, covered | masks[i], forbidden_here | {i})
            forbidden_here.add(i)

    search([], 0, set())
    return count


def random_exact_partition(N, rng):
    family = [(0, 1)]
    for _ in range(rng.randint(10, 35)):
        expandable = [(i, p) for i, (a, d) in enumerate(family)
                      for p in factor(N // d)]
        if not expandable:
            break
        i, p = rng.choice(expandable)
        a, d = family.pop(i)
        family.extend((a + k * d, p * d) for k in range(p))
    return family


def rich_cover(N, rng):
    divisors = [d for d in range(2, N + 1) if N % d == 0]
    family = []
    for _ in range(rng.randint(4, 12)):
        d = rng.choice(divisors)
        a = rng.randrange(d)
        if (a, d) not in family:
            family.append((a, d))
    covered = {x for a, d in family for x in range(a, N, d)}
    family.extend((x, N) for x in range(N) if x not in covered)
    # Delete redundant blocks one by one; never discard all initially nonessential
    # blocks simultaneously (that operation need not preserve coverage).
    counts = [sum(x % d == a for a, d in family) for x in range(N)]
    order = list(range(len(family)))
    rng.shuffle(order)
    removed = set()
    for i in order:
        a, d = family[i]
        points = range(a, N, d)
        if all(counts[x] > 1 for x in points):
            removed.add(i)
            for x in points:
                counts[x] -= 1
    return [block for i, block in enumerate(family) if i not in removed]


def main():
    report = dict(exhaustive={}, named=[], exact_partitions=0, rich_covers=0,
                  large_true_lcm_cases=0, maximum_true_lcm=1)
    for n in [6, 12, 18, 24]:
        count = exhaustive(n, 7)
        report['exhaustive'][str(n)] = dict(K=7, legal_covers=count)
        print('exhaustive', n, 'K=7:', count, flush=True)

    named = {}
    for name, path in [('n720_A', 'sigma_route_counterexample.json'),
                       ('n720_B', 'sigma_route_counterexample_B.json')]:
        family = json.loads(Path('explore', path).read_text(encoding='utf-8'))['family']
        named[name] = certificate(family, check_digits=True)
    n60 = [(a, 12) for a in range(6)] + [(a, 20) for a in range(8)]
    covered = {x for a, d in n60 for x in range(a, 60, d)}
    n60 += [(x, 60) for x in range(60) if x not in covered]
    named['n60'] = certificate(n60, check_digits=True)
    n240 = ([(a, 10) for a in [0, 1, 2, 3, 5, 6, 8, 9]]
            + [(a, 12) for a in [0, 1, 4, 5, 8, 9]]
            + [(a, 80) for a in [7, 14, 27, 34, 47, 54, 67, 74]])
    named['n240'] = certificate(n240, check_digits=True)
    report['named'] = {name: dict(n=c['n'], clauses=len(c['family']), slots=len(c['slots']),
                                selected=len(c['selected'])) for name, c in named.items()}

    rng = Random(20261010)
    for N in [60, 120, 240, 336, 480, 720, 840, 1680]:
        for kind, sampler in [('exact_partitions', random_exact_partition), ('rich_covers', rich_cover)]:
            for trial in range(80):
                family = sampler(N, rng)
                c = certificate(family, check_digits=trial < 2)
                report[kind] += 1
                if c['n'] >= 60 and len(family) >= 7:
                    report['large_true_lcm_cases'] += 1
                report['maximum_true_lcm'] = max(report['maximum_true_lcm'], c['n'])
        print('pressure modulus', N, 'actual lcm recomputed for every family', flush=True)
    Path('explore/matching_path_certificates.json').write_text(
        json.dumps(named, indent=2, ensure_ascii=False), encoding='utf-8')
    Path('explore/matching_path_report.json').write_text(
        json.dumps(report, indent=2, ensure_ascii=False), encoding='utf-8')
    print(json.dumps(report, ensure_ascii=False, indent=2), flush=True)


if __name__ == '__main__':
    main()
