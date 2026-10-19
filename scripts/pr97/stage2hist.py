#!/usr/bin/env python3
"""The whole-projector histogram of the PR97 node and its stage-2 moments (stdlib only).

Usage: stage2hist.py DATA_JSON OUT_JSON

DATA_JSON is generate.py's output, the data `emit_lean.py` turns into `M8/Local/Data`. The
script mirrors the Lean node of `M8/Global`:
* the slot compiler `Dag.compile` of `M8/Local/Compile.lean`, on the DAG of `M8/Local/Witness.lean`;
* the frames of the two stages along every local register (`M8/Global/StageFrames.lean`);
* the node's wires, lifts and sinks (`M8/Global/Node.lean`, `NodeFrames.lean`).
Every move of the framed node between distinct nested frames `A ≤ B` is one edge program
`Exchange.program (B - A)`, and in stage 2 one reversed child `F_{r f}` of rank
`r = rank B - rank A`. The histogram counts these edges by rank, over the whole node.

It writes the histogram and checks its rank mass against `calls_node_le`
(`s₀ = 57403754177`). It then reports the moments
`μ₁ = Σ_r (n_r/W)(r/m)` and `μ_τ = Σ_r (n_r/W)(r/m)^τ` with `W = 108516254`, `m = 529`, and the
largest saving `a` with `μ_{1-a} < 1`.
"""
import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations

H = 23
M = H * H
TRIP = list(combinations(range(H), 3))
TID = {T: i for i, T in enumerate(TRIP)}
S0 = 57403754177


def rank_mod(vecs, p):
    """rank of integer vectors modulo the prime p"""
    rows = [[x % p for x in v] for v in vecs]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [x * inv % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def rank_exact(vecs):
    """rank over the rationals; two large primes bound it from below and must agree with the
    exact Gaussian elimination"""
    rows = [[Fraction(x) for x in v] for v in vecs]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(r + 1, len(rows)):
            if rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def tvec(S):
    return [1 if z in S else 0 for z in range(H)]


def supp_triples(sp):
    """the triples of a support, as in `Supp.mem` (`M8/Local/Kernel.lean`)"""
    if sp[0] == 'leaf':
        return [TRIP[sp[1]]]
    if sp[0] == 'two':
        x, y, Z = sp[1], sp[2], sp[3]
        return [tuple(sorted((x, y, z))) for z in range(H) if Z >> z & 1]
    # 'one': point c and generate.py's 22x22 rank-relative pair mask
    c, P22 = sp[1], sp[2]
    rk_inv = [u for u in range(H) if u != c]
    out = []
    for i in range(22):
        for j in range(i + 1, 22):
            if P22 >> (22 * i + j) & 1:
                out.append(tuple(sorted((c, rk_inv[i], rk_inv[j]))))
    return out


def frame_rank(triples, cache):
    key = frozenset(triples)
    if key not in cache:
        vecs = [tvec(S) for S in triples]
        r1 = rank_mod(vecs, (1 << 61) - 1)
        r2 = rank_mod(vecs, (1 << 31) - 1)
        assert r1 == r2, ('rank disagreement', triples)
        cache[key] = r1
    return cache[key]


def load(path):
    D = json.load(open(path))
    N, v = D['N'], D['v']
    nodes = D['nodes']
    assert len(nodes) == N and all(nodes[n]['id'] == n for n in range(N))
    # roots in canonical order (emit_lean.py): outputs 3·TID[T] + T.index(c), then centres
    roots = [None] * (3 * len(TRIP) + H)
    for q in D['roots']:
        if 'out' in q:
            c, T = q['out']
            j = 3 * TID[tuple(T)] + T.index(c)
        else:
            j = 3 * len(TRIP) + q['ret']
        assert roots[j] is None
        roots[j] = q
    assert all(roots)
    return D, N, v, nodes, roots


def compile_lean(N, v, nodes, roots):
    """`Dag.compile` of `M8/Local/Compile.lean`, step by step"""
    def arg(n, pos):
        r = nodes[n]
        return (r['args'][1] if pos else r['args'][0]) if 'args' in r else 0

    def link(n):
        L = nodes[n].get('link')
        return (L['operand'] == 1, L['user'], L['pos'] == 1) if L else None

    linked = set()
    for n in range(N):
        L = link(n)
        if L:
            linked.add(('gate', L[1], L[2]))
    gate_uses = defaultdict(list)
    for t in range(v, N):
        for pos in (False, True):
            gate_uses[arg(t, pos)].append(('gate', t, pos))
    root_uses = defaultdict(list)
    for r, q in enumerate(roots):
        root_uses[q['node']].append(('root', r))

    def free_uses(y):
        return [u for u in gate_uses[y] + root_uses[y] if u not in linked]

    nxt = 0
    pend = {}
    ops = []
    reads = []

    def assign(s, u):
        pend[u] = s
        if u[0] == 'root':
            reads.append((s, u[1]))

    def serve(node, piv, us):
        nonlocal nxt
        if not us:
            return
        assign(piv, us[0])
        for u in us[1:]:
            assign(nxt, u)
            ops.append(('copy', piv, nxt, node))
            nxt += 1

    for n in range(N):
        if n < v:
            s = nxt
            nxt += 1
            ops.append(('src', s, n))
            serve(n, s, free_uses(n))
        else:
            sa = pend.get(('gate', n, False), 0)
            sb = pend.get(('gate', n, True), 0)
            L = link(n)
            if L:
                o, t, pos = L
                piv, oth = (sa, sb) if o else (sb, sa)
                ops.append(('add', piv, oth, n))
                assign(oth, ('gate', t, pos))
                serve(n, piv, free_uses(n))
            else:
                ops.append(('add', sa, sb, n))
                serve(n, sa, free_uses(n))
    return nxt, ops, reads, pend


def slots_of(op):
    if op[0] == 'src':
        return [op[1]]
    return [op[1], op[2]]


def node_of(op):
    return op[2] if op[0] == 'src' else op[3]


def steps(ranks):
    """the moves along a chain of nested frames, given by their ranks"""
    out = []
    for a, b in zip(ranks, ranks[1:]):
        assert b >= a, ('decreasing chain', ranks)
        if b > a:
            out.append(b - a)
    return out


def main(data_path, out_path):
    D, N, v, nodes, roots = load(data_path)
    R, ops, reads, pend = compile_lean(N, v, nodes, roots)
    assert R == D['R'] == 28866, R
    cache = {}
    dim = [frame_rank(supp_triples(nodes[n]['supp']), cache) for n in range(N)]
    assert all(dim[n] == 1 for n in range(v))
    star = [frame_rank([S for S in TRIP if c in S], cache) for c in range(H)]
    # the read slot of each root (`slotOf j = compile.pend (.root j)`)
    root_slot = [pend[('root', j)] for j in range(len(roots))]
    nout = 3 * len(TRIP)
    root_frames = defaultdict(list)
    for j, s in enumerate(root_slot):
        root_frames[s].append(star[j - nout] if j >= nout else H - 1)
    # stage one along each side slot: 0, the compute frames, the root frames, then 1
    chain_nodes = defaultdict(list)
    for op in ops:
        for s in slots_of(op):
            chain_nodes[s].append(node_of(op))
    local = Counter()
    for s in range(R):
        ranks = [0] + [dim[n] for n in chain_nodes[s]] + root_frames[s] + [H]
        local.update(steps(ranks))
    assert sum(r * c for r, c in local.items()) == H * R
    hist = Counter()
    for _stage in range(2):
        # side slots: the local moves, and the exterior move `0 → (1-P) ⊗ 1` (stage two) or the
        # sink `1 ⊗ Q → 1` (stage one), of rank m - h
        for r, c in local.items():
            hist[r] += v * c
        hist[M - H] += v * R
        # centre temporaries: one move of the star frame's rank
        for c in range(H):
            hist[star[c]] += v
    # data pairs: X S T climbs 1 → 23 → 507 → 529, Y S T climbs 0 → 22 → 506 → 528
    NP = v * v
    hist[H - 1] += 2 * NP
    hist[(H - 1) ** 2] += NP
    hist[H - 1] += 2 * NP
    hist[(H - 1) ** 2] += NP
    # correction temporaries: 1 → 1 - P ⊗ Q
    hist[1] += NP
    W = 2 * NP + 2 * v * R
    s = sum(r * c for r, c in hist.items())
    assert W == 108516254 and s == S0, (W, s)
    edges = sum(hist.values())
    mu1 = Fraction(s, W * M)

    def mu(a):
        return sum(c / W * (r / M) ** (1 - a) for r, c in hist.items())

    lo, hi = 0.0, 0.01
    for _ in range(100):
        mid = (lo + hi) / 2
        if mu(mid) < 1:
            lo = mid
        else:
            hi = mid
    out = {
        'source': D['source'],
        'W': W, 'm': M, 'rankMass': s, 'edges': edges,
        'histogram': sorted([r, c] for r, c in hist.items()),
        'localSteps': sorted([r, c] for r, c in local.items()),
        'starRanks': star,
        'mu1': [mu1.numerator, mu1.denominator],
        'aStar': lo,
    }
    with open(out_path, 'w') as fh:
        json.dump(out, fh, indent=1)
    print('slots', R, 'ops', len(ops), 'edges', edges, 'rank mass', s)
    print('local steps', sorted(local.items()))
    print('star ranks', set(star))
    print('histogram', sorted(hist.items()))
    print('mu1 = %d/%d = %.12f' % (mu1.numerator, mu1.denominator, float(mu1)))
    print('a* (mu_{1-a} = 1) = %.10e' % lo)
    for a in (9.69e-5, 9.695e-5, 9.699e-5):
        print('a = %.4e: 1 - mu_tau = %.4e' % (a, 1 - mu(a)))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
