"""Elementary alternating-search certificates; no Hall/deficiency library.
Finite diagnostics are not a Lean formalization of the accompanying paper proofs.
"""
from collections import Counter, deque
from itertools import product
from pathlib import Path
from random import Random
import json

from audit_sigma_route import lcmlist, factor, vp, bound
import verify_matching_path as prior_samples


def search(start, adjacency, left_match, right_match):
    left_seen, right_parent = {start}, {}
    todo = deque([start])
    while todo:
        left = todo.popleft()
        for right in adjacency[left]:
            if right in right_parent:
                continue
            right_parent[right] = left
            if right not in right_match:
                cursor = right
                while True:
                    slot = right_parent[cursor]
                    previous = left_match.get(slot)
                    left_match[slot] = cursor
                    right_match[cursor] = slot
                    if previous is None:
                        return True, left_seen, set(right_parent)
                    cursor = previous
            slot = right_match[right]
            if slot not in left_seen:
                left_seen.add(slot)
                todo.append(slot)
    return False, left_seen, set(right_parent)


def local_assignment(q, owners, uses, values, T, N, right_match):
    touched = {owners[s] for s in T}
    assert N == {i for i, support in enumerate(uses) if support & touched}
    forbidden = {v: set() for v in touched}
    for i in N:
        assert i in right_match and right_match[i] in T
        v = owners[right_match[i]]
        assert v in uses[i]
        forbidden[v].add(values[i][v])
    fresh = {}
    for v in touched:
        assert len(forbidden[v]) <= owners.count(v) < q[v]
        fresh[v] = next(z for z in range(q[v]) if z not in forbidden[v])
    assert all(any(fresh[v] != values[i][v] for v in uses[i] & touched) for i in N)
    assert all(not (support & touched) for i, support in enumerate(uses) if i not in N)
    return fresh


def certificate(family, check_digits=False):
    n = lcmlist(d for a, d in family)
    counts = [sum(x % d == a % d for a, d in family) for x in range(n)]
    assert min(counts) > 0
    assert all(any(counts[x] == 1 for x in range(a % d, n, d)) for a, d in family)
    variables = [(p, t) for p, alpha in factor(n).items() for t in range(alpha)]
    q = [p for p, t in variables]
    owners = [v for v, p in enumerate(q) for _ in range(p - 1)]
    uses = [{v for v, (p, t) in enumerate(variables) if t < vp(d, p)} for a, d in family]
    values = [[a // p**t % p for p, t in variables] for a, d in family]
    adjacency = [[i for i, support in enumerate(uses) if owner in support] for owner in owners]
    assert all(adjacency)
    left_match, right_match = {}, {}
    for start in range(len(owners)):
        ok, T, N = search(start, adjacency, left_match, right_match)
        if not ok:
            fresh = local_assignment(q, owners, uses, values, T, N, right_match)
            raise AssertionError(('unexpected local assignment in minimal cover', n, T, N, fresh))
    assert len(left_match) == len(owners) == bound(n) - 1
    assert len(right_match) == len(set(left_match.values()))
    anchor = next(i for i in range(len(family)) if i not in right_match)
    selected = set(right_match) | {anchor}
    group_counts = Counter(d for a, d in family)
    selected_counts = Counter(family[i][1] for i in selected)
    for d, m in group_counts.items():
        assert selected_counts[d] <= min(m, bound(d))
    if check_digits:
        for i, (a, d) in enumerate(family):
            for x in range(n):
                same = all(x // variables[v][0]**variables[v][1] % q[v] == values[i][v]
                           for v in uses[i])
                assert same == (x % d == a % d)
    assert len(selected) == bound(n)
    return dict(n=n, blocks=len(family), slots=len(owners), anchor=anchor,
                selected=sorted(selected), selected_census=dict(sorted(selected_counts.items())))


def check_failure_mechanism():
    # Satisfiable examples where there are too few clauses to saturate all slots.
    cases = [([2, 2, 2], [{0, 1}, {1, 2}], [[0, 0, 0], [0, 0, 0]]),
             ([3, 2], [{0, 1}], [[1, 0]]),
             ([2, 2, 2], [{0, 1}, {2}], [[0, 0, 0], [0, 0, 1]])]
    for q, uses, values in cases:
        owners = [v for v, size in enumerate(q) for _ in range(size - 1)]
        adjacency = [[i for i, support in enumerate(uses) if owner in support] for owner in owners]
        left_match, right_match = {}, {}
        for start in range(len(owners)):
            ok, T, N = search(start, adjacency, left_match, right_match)
            if not ok:
                assert N
                fresh = local_assignment(q, owners, uses, values, T, N, right_match)
                x = next(x for x in product(*(range(size) for size in q))
                         if all(any(x[v] != values[i][v] for v in support)
                                for i, support in enumerate(uses) if i not in N))
                merged = list(x)
                for v, z in fresh.items():
                    merged[v] = z
                assert all(any(merged[v] != values[i][v] for v in support)
                           for i, support in enumerate(uses))
                break
        else:
            raise AssertionError('Expected a failed search')
    return len(cases)


def subsets(items):
    items = list(items)
    for mask in range(1 << len(items)):
        yield {items[k] for k in range(len(items)) if mask >> k & 1}


def representatives(edges):
    """The two-case finite induction from paper proof II, not augmenting search."""
    I = set(edges)
    if not I:
        return {}
    for J in subsets(I):
        if not J or J == I:
            continue
        U = set().union(*(edges[i] for i in J))
        if len(U) == len(J):
            first = representatives({i: edges[i] for i in J})
            rest = representatives({i: edges[i] - U for i in I - J})
            return first | rest
    i = min(I)
    e = min(edges[i])
    rest = representatives({j: edges[j] - {e} for j in I - {i}})
    return {i: e} | rest


def check_inductive_route():
    saturated, positive_deficit = 0, 0
    for graph in range(1 << 9):
        edges = {i: {j for j in range(3) if graph >> (3*i+j) & 1} for i in range(3)}
        def neighborhood(T):
            return set().union(*(edges[i] for i in T)) if T else set()
        all_T = list(subsets(edges))
        if all(len(neighborhood(T)) >= len(T) for T in all_T):
            match = representatives(edges)
            assert len(match) == len(set(match.values())) == 3
            assert all(match[i] in edges[i] for i in edges)
            saturated += 1
        elif all(edges.values()):
            T = max(all_T, key=lambda T: len(T) - len(neighborhood(T)))
            N = neighborhood(T)
            assert N and len(T) > len(N)
            inverse = {j: {i for i in T if j in edges[i]} for j in N}
            assert all(len(set().union(*(inverse[j] for j in J))) >= len(J)
                       for J in subsets(N) if J)
            match = representatives(inverse)
            assert len(match) == len(set(match.values())) == len(N)
            assert all(match[j] in inverse[j] for j in N)
            positive_deficit += 1
    return dict(graphs=512, full_slot_matches=saturated, positive_deficit_matches=positive_deficit)


def main():
    report = dict(failure_mechanism_cases=check_failure_mechanism(),
                  inductive_route_graphs=check_inductive_route(), named={}, exhaustive={},
                  exact_partitions=0, mixed_covers=0, large_true_lcm_cases=0)
    named = json.loads(Path('explore/matching_path_certificates.json').read_text(encoding='utf-8'))
    for name, data in named.items():
        report['named'][name] = certificate(data['family'], check_digits=True)
    # Reuse only the existing sample generators; all matching checks use this new implementation.
    prior_samples.certificate = certificate
    for n in [6, 12, 18, 24]:
        report['exhaustive'][str(n)] = dict(K=7, covers=prior_samples.exhaustive(n, 7))
        print('exhaustive', n, report['exhaustive'][str(n)], flush=True)
    rng = Random(20261013)
    for N in [60, 84, 120, 180, 240, 360, 720, 1680]:
        for generator, key in [(prior_samples.random_exact_partition, 'exact_partitions'),
                               (prior_samples.rich_cover, 'mixed_covers')]:
            for _ in range(20):
                result = certificate(generator(N, rng))
                report[key] += 1
                report['large_true_lcm_cases'] += result['n'] >= 60 and result['blocks'] >= 7
    Path('explore/elementary_matching_report.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(report, ensure_ascii=False, indent=2), flush=True)


if __name__ == '__main__':
    main()
