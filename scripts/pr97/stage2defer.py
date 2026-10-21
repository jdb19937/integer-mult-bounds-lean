#!/usr/bin/env python3
"""The structural design-B frames of the PR97 node: deferred readouts, V starts and late copies
(stdlib only).

Usage: stage2defer.py PR97_DIR [OUT_JSON]

PR97_DIR is upstream's `references/partial-gauge/pr97/` at `463113d6` (the pins of
`stage2designb.py`). The schedule is upstream's design-B word (`deferred_23.json.gz`); its frames
are replaced by frames whose rank and nondegeneracy are theorems:
* `('lift', c, M, r)`: `Frames.liftFrame c M r`, the root complement of the outputs `{c} ∪ p`,
  `p ∈ M`, and of the centre `c` when `r`; rank `(22 if r else 23) − dimC c M`;
* `('plain', n)`: the plain frame `span(n)`; `('line', S)`: the line of `t_S`; `0` and `1`;
* `('out', T)`: the hyperplane `t_T^⊥`; `('ret', c)`: the star frame of `c`.

The node frames are B2's (`stage2lift.py`): a node is lifted when upstream lifts it and every
root it reaches along slot successors has one centre. The other frames are unions of these root
sets, kept when they have one centre and replaced otherwise:
* a late-copy frame `C = W(⋃ roots of the remaining users)` by the node's own frame;
* a V start `s_i = ⋂_{i' ≥ i}` (first node frame of the `i'`-th V slot of the leaf `S`) by the
  line of `t_S`;
* a deferred readout frame, by the reverse recursion over the readout order
  `σ_u = F₀(u) ∩ ⋂_{T ∈ targets(u)} t_T^⊥ ∩ ⋂_T σ_{next_T(u)}`, with `next_T(u)` the next kept
  slot reading `y_T`, by `0` (such a slot is read before the kept ones).
A union has one centre `c` when every output triple contains `c` and every centre is `c`.

The script checks every nesting along every slot chain, every `y_T` chain (`0`, the kept `σ_u` in
readout order, `t_T^⊥`) and every `X_S` chain (`⟨t_S⟩`, the V starts, `1`) by the combinatorial
rules that the Lean lemmas prove (`liftFrame_nest`, `liftFrame_hyper`, `liftFrame_star`,
`frameOf_lift`), with plain-to-plain steps by exact span inclusion. It then builds the histogram as
`stage2designb.py` does, checks the rank mass `s₀`, and reports `a*`, the rational τ-moment
certificate at the largest `a` on the `10⁻⁷` grid below `q_τ = 1 − 1/10⁸`, and the retune.
"""
import math
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations

import stage2designb as dbm

H = dbm.H
M = dbm.M
P31 = 2 ** 31 - 1
QT = dbm.QT


class Echelon:
    """row echelon basis mod a prime; ranks of 0/1 triple rows are exact (minors below 3^(23/2))"""

    def __init__(self):
        self.rows = []
        self.piv = []

    def reduce(self, r):
        r = [x % P31 for x in r]
        for pc, b in zip(self.piv, self.rows):
            c = r[pc]
            if c:
                r = [(x - c * y) % P31 for x, y in zip(r, b)]
        return r

    def insert(self, r):
        r = self.reduce(r)
        pc = next((i for i, x in enumerate(r) if x), None)
        if pc is None:
            return False
        inv = pow(r[pc], P31 - 2, P31)
        r = [x * inv % P31 for x in r]
        for i, b in enumerate(self.rows):
            if b[pc]:
                self.rows[i] = [(x - b[pc] * y) % P31 for x, y in zip(b, r)]
        self.rows.append(r)
        self.piv.append(pc)
        return True

    def contains(self, r):
        return not any(self.reduce(r))


def trow(T):
    return [int(q in T) for q in range(H)]


def pair_rank(pairs):
    """points on edges less bipartite components (`Frames.dimC`)"""
    adj = defaultdict(list)
    for u, w in pairs:
        adj[u].append(w)
        adj[w].append(u)
    side, bip = {}, 0
    for v0 in adj:
        if v0 in side:
            continue
        side[v0] = 0
        stack, ok = [v0], True
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in side:
                    side[y] = 1 - side[x]
                    stack.append(y)
                elif side[y] == side[x]:
                    ok = False
        bip += ok
    return len(adj) - bip


class Side:
    """the side DAG, its slot successors and the roots every node reaches (upstream numbering)"""

    def __init__(self, W):
        self.trip = list(combinations(range(H), 3))
        self.args = {int(n): (tuple(a) if a else None) for n, a in W['args'].items()}
        self.act = sorted(self.args)
        self.sup = {}
        for n in self.act:
            if self.args[n] is None:
                self.sup[n] = 1 << (n - 1)
            else:
                a, b = self.args[n]
                self.sup[n] = self.sup[a] | self.sup[b]
        self.outputs = {(c, tuple(T)): n for c, T, n in W['outputs']}
        self.retained = {c: n for c, n in W['retained']}
        self.mL = {x: (y, k) for x, y, k in W['links']}
        self.j = {int(n) for n in W['j']}
        self.late = {int(n): (list(e), list(l)) for n, (e, l) in W['late'].items()}
        self.bas, self.dn = {}, {}
        for n in self.act:
            if self.args[n] is None:
                self.bas[n] = (n - 1,)
                self.dn[n] = 1
                continue
            a, b = self.args[n]
            E, keep = Echelon(), []
            for i in self.bas[a] + self.bas[b]:
                if len(keep) == H:
                    break
                if E.insert(trow(self.trip[i])):
                    keep.append(i)
            self.bas[n] = tuple(keep)
            self.dn[n] = len(keep)
        key = lambda n: (self.dn[n], n)
        self.users = {n: [] for n in self.act}
        for n in sorted(self.act, key=key):
            if self.args[n]:
                for pos, x in enumerate(self.args[n]):
                    self.users[x].append(('gate', n, pos))
        for (c, T), n in sorted(self.outputs.items()):
            self.users[n].append(('out', (c, T)))
        for c, n in sorted(self.retained.items()):
            self.users[n].append(('ret', c))
        linked = {r: x for x, r in self.mL.items()}
        succ = {n: set() for n in self.act}
        droots = {n: set() for n in self.act}

        def to(n, use):
            if use[0] == 'gate':
                succ[n].add(use[1])
            else:
                droots[n].add(rootkey(use))

        for n in self.act:
            for k, u in enumerate(self.users[n]):
                if (n, k) not in linked:
                    to(n, u)
            if n in self.mL:
                y, k = self.mL[n]
                to(n, self.users[y][k])
        self.reach = {}
        for n in sorted(self.act, key=key, reverse=True):
            s = set(droots[n])
            for t in succ[n]:
                s |= self.reach[t]
            self.reach[n] = frozenset(s)

    def supp(self, n):
        return [self.trip[i] for i in range(len(self.trip)) if self.sup[n] >> i & 1]


def rootkey(u):
    return ('out', u[1][0], tuple(u[1][1])) if u[0] == 'out' else ('ret', u[1])


P61 = 2 ** 61 - 1
MULTI = False
NODES_MULTI = False


def rvec(k):
    return trow(k[2]) if k[0] == 'out' else [8 if q == k[1] else 1 for q in range(H)]


def rank_basis(keys):
    E, B = Echelon(), []
    for k in sorted(keys):
        if E.insert(rvec(k)):
            B.append(k)
    return E, B


def gdet_nonzero(B):
    """det of the 9G-Gram of B mod 2^61 - 1 (numbers only)"""
    vs = [rvec(k) for k in B]
    Mx = [[(9 * sum(a * b for a, b in zip(x, y)) - sum(x) * sum(y)) % P61 for y in vs] for x in vs]
    n = len(Mx)
    for c in range(n):
        piv = next((i for i in range(c, n) if Mx[i][c]), None)
        if piv is None:
            return False
        Mx[c], Mx[piv] = Mx[piv], Mx[c]
        inv = pow(Mx[c][c], P61 - 2, P61)
        for i in range(c + 1, n):
            f = Mx[i][c] * inv % P61
            if f:
                Mx[i] = [(a - f * b) % P61 for a, b in zip(Mx[i], Mx[c])]
    return True


def as_keys(fr):
    return roots_of(fr) if fr[0] == 'lift' else fr[1]


def join(keys, multi=None):
    """the frame of a set of root keys of one centre (with MULTI, any nondegenerate set), or None"""
    cs = {k[1] for k in keys}
    if len(cs) != 1:
        if not (MULTI if multi is None else multi) or not keys or -1 in cs:
            return None
        _, B = rank_basis(keys)
        return ('roots', frozenset(keys)) if gdet_nonzero(B) else None
    (c,) = cs
    pairs = frozenset(tuple(q for q in k[2] if q != c) for k in keys if k[0] == 'out')
    return ('lift', c, pairs, any(k[0] == 'ret' for k in keys))


def roots_of(fr):
    """the root keys of a lift frame"""
    if fr[0] == 'roots':
        return set(fr[1])
    _, c, pairs, r = fr
    ks = {('out', c, tuple(sorted((c,) + p))) for p in pairs}
    return ks | ({('ret', c)} if r else set())


def f2_targets(S):
    """the targets `y_T` whose coefficient of slot s's garbage is odd: the transpose sweep of the
    compiled operations over 𝔽₂ applied to the root reads"""
    cov = [set() for _ in range(S.R)]
    for s, (c, T) in S.out.items():
        cov[s] ^= {S.tid[T]}
    for s, c in S.ret.items():
        cov[s] ^= {t for t, T in enumerate(S.trip) if c in T}
    for op in reversed(S.ops):
        if op[0] == 'add':
            cov[op[2]] ^= cov[op[1]]
        elif op[0] == 'fan':
            for g in op[2]:
                cov[op[1]] ^= cov[g]
    return cov


class Frames:
    def __init__(self, G, S):
        self.G, self.S = G, S
        self.node = {}
        for n in G.act:
            if G.args[n] is not None and n in G.j:
                fr = join(G.reach[n], NODES_MULTI)
                self.node[n] = fr if fr else ('plain', n)
            else:
                self.node[n] = ('plain', n)
        self.late = {}
        for n0, (_e, lt) in G.late.items():
            for i in range(len(lt)):
                keys = set()
                for k in lt[i:]:
                    rs = self.use_roots(n0, k)
                    keys = keys | rs if keys is not None and rs is not None else None
                fr = join(keys) if keys else None
                self.late[n0, tuple(lt[i:])] = fr if fr else self.node[n0]
        self.vstart = {}
        for n, us in S.xs:
            keys = set()
            for i in reversed(range(len(us))):
                hl = S.hold[us[i]]
                if len(hl) > 1:
                    fr = self.node[hl[1]]
                    keys = keys | roots_of(fr) if fr[0] in ('lift', 'roots') and keys is not None else None
                fr = join(keys) if keys else None
                self.vstart[us[i]] = fr if fr else ('line', G.trip[n - 1])
        cov = f2_targets(S)
        self.targets = cov
        self.sigma = {}
        last = {}
        for s in reversed(S.readout):
            f0 = self.frame(self.start_key(s))
            fr = None
            if f0[0] in ('lift', 'roots'):
                c0 = f0[1] if f0[0] == 'lift' else None
                keys = set(roots_of(f0)) | {('out', c0 if c0 in S.trip[t] else
                                             (min(S.trip[t]) if MULTI else -1), S.trip[t])
                                            for t in cov[s]}
                for t in cov[s]:
                    if t in last:
                        keys |= roots_of(self.sigma[last[t]])
                fr = join(keys)
            if fr:
                self.sigma[s] = fr
                for t in cov[s]:
                    last[t] = s

    def use_roots(self, n0, k):
        u = self.G.users[n0][k]
        if u[0] != 'gate':
            return {rootkey(u)}
        fr = self.node[u[1]]
        return roots_of(fr) if fr[0] in ('lift', 'roots') else None

    def start_key(self, s):
        S, G = self.S, self.G
        n0 = S.hold[s][0]
        if G.args[n0] is None:
            return ('v', s)
        k = S.start[s][2]
        dec = G.late.get(n0)
        if dec is None or k in dec[0]:
            return ('n', n0)
        lt = dec[1]
        return ('c', n0, tuple(lt[lt.index(k):]))

    def chain_keys(self, s):
        S, G = self.S, self.G
        ch = [('sigma', s), self.start_key(s)]
        for idx, n in enumerate(S.hold[s]):
            if idx > 0:
                ch.append(('n', n))
            if G.args[n] is not None and S.pivslot.get(n) == s and n in G.late:
                lt = G.late[n][1]
                for i in range(len(lt) - 1):
                    ch.append(('c', n, tuple(lt[i:])))
        if s in S.out:
            ch.append(('out', S.out[s][1]))
        if s in S.ret:
            ch.append(('ret', S.ret[s]))
        ch.append(('one',))
        return ch

    def frame(self, key):
        k = key[0]
        if k == 'sigma':
            return self.sigma.get(key[1], ('zero',))
        if k == 'v':
            return self.vstart[key[1]]
        if k == 'n':
            return self.node[key[1]]
        if k == 'c':
            return self.late[key[1], key[2]]
        return key

    def dim(self, fr):
        k = fr[0]
        if k == 'zero':
            return 0
        if k == 'one':
            return H
        if k in ('out', 'ret'):
            return H - 1
        if k == 'line':
            return 1
        if k == 'plain':
            return self.G.dn[fr[1]]
        if k == 'roots':
            return H - len(rank_basis(fr[1])[1])
        _, c, pairs, r = fr
        return (H - 1 if r else H) - pair_rank(pairs)

    def nested(self, A, B):
        """A ≤ B by the rules the Lean lemmas prove (multi-centre frames by span inclusion)"""
        if A == B or A[0] == 'zero' or B[0] == 'one':
            return True
        if 'roots' in (A[0], B[0]):
            if A[0] in ('lift', 'roots'):
                E, _ = rank_basis(as_keys(A))
                if B[0] in ('lift', 'roots'):
                    return all(E.contains(rvec(k)) for k in as_keys(B))
                if B[0] == 'out':
                    return E.contains(trow(B[1]))
                if B[0] == 'ret':
                    return E.contains(rvec(('ret', B[1])))
                return False
            if A[0] in ('plain', 'line'):
                trips = self.G.supp(A[1]) if A[0] == 'plain' else [A[1]]
                return all(len(set(T) & set(k[2])) == 1 if k[0] == 'out' else k[1] in T
                           for T in trips for k in B[1])
            return False
        if A[0] == 'lift':
            _, c, pairs, r = A
            if B[0] == 'lift':
                return B[1] == c and B[2] <= pairs and (r or not B[3])
            if B[0] == 'out':
                return c in B[1] and tuple(q for q in B[1] if q != c) in pairs
            if B[0] == 'ret':
                return B[1] == c and r
            return False
        if A[0] in ('plain', 'line'):
            trips = self.G.supp(A[1]) if A[0] == 'plain' else [A[1]]
            if B[0] == 'lift':
                _, c, pairs, r = B
                pts = {q for p in pairs for q in p}
                return all(c in T and not (set(T) - {c}) & pts for T in trips)
            if B[0] == 'out':
                return all(len(set(T) & set(B[1])) == 1 for T in trips)
            if B[0] == 'ret':
                return all(B[1] in T for T in trips)
            if B[0] == 'plain':
                E = Echelon()
                for i in self.G.bas[B[1]]:
                    E.insert(trow(self.G.trip[i]))
                return all(E.contains(trow(T)) for T in trips)
        return False


def main(pr97_dir, out_path=None, mode=None):
    global MULTI, NODES_MULTI
    MULTI = mode in ('--multi', '--multi-nodes')
    NODES_MULTI = mode == '--multi-nodes'
    W = dbm.read(pr97_dir, 'witness_23.json.gz')
    D = dbm.read(pr97_dir, 'deferred_23.json.gz')
    S = dbm.Schedule(W, D)
    S.start = D['start']
    S.out = {s: (c, tuple(T)) for s, c, T in D['out']}
    S.ret = {s: c for s, c in D['ret']}
    G = Side(W)
    F = Frames(G, S)
    lifted = sum(fr[0] in ('lift', 'roots') for n, fr in F.node.items() if G.args[n] is not None)
    print('computed frames: sigma', sum(fr[0] == 'roots' for fr in F.sigma.values()),
          'V', sum(fr[0] == 'roots' for fr in F.vstart.values()),
          'late', sum(fr[0] == 'roots' for fr in F.late.values()),
          'nodes', sum(fr[0] == 'roots' for fr in F.node.values()))
    print('lifted nodes', lifted, 'kept sigma', len(F.sigma), 'of', len(S.readout),
          'lifted V starts', sum(fr[0] in ('lift', 'roots') for fr in F.vstart.values()), 'of', len(F.vstart),
          'lifted late frames', sum(fr[0] in ('lift', 'roots') for fr in F.late.values()), 'of', len(F.late))
    aux = Counter()
    for s in range(S.R):
        frs = [F.frame(k) for k in F.chain_keys(s)]
        for A, B in zip(frs, frs[1:]):
            assert F.nested(A, B), ('slot chain', s, A, B)
        ds = [F.dim(fr) for fr in frs]
        aux.update(dbm.steps(ds))
    readers = defaultdict(list)
    for s in S.readout:
        if s in F.sigma:
            for t in F.targets[s]:
                readers[t].append(s)
    data = Counter()
    for t in range(S.v):
        frs = [('zero',)] + [F.sigma[s] for s in readers[t]] + [('out', S.trip[t])]
        for A, B in zip(frs, frs[1:]):
            assert F.nested(A, B), ('y chain', t, A, B)
        ds = [F.dim(fr) for fr in frs]
        ds = [d for i, d in enumerate(ds) if i == 0 or d != ds[i - 1]]
        data.update(dbm.steps(ds))
    for n, us in S.xs:
        frs = [('line', G.trip[n - 1])] + [F.vstart[s] for s in us] + [('one',)]
        for A, B in zip(frs, frs[1:]):
            assert F.nested(A, B), ('x chain', n, A, B)
        ds = [F.dim(fr) for fr in frs]
        ds = [d for i, d in enumerate(ds) if i == 0 or d != ds[i - 1]]
        data.update(dbm.steps(ds))
    f = [F.dim(F.frame(('sigma', s))) for s in range(S.R)]
    hist = Counter()
    for _stage in range(2):
        for r, c in aux.items():
            hist[r] += S.v * c
        for r, c in data.items():
            hist[r] += S.v * c
        hist[H - 1] += S.v * H
        for s in range(S.R):
            hist[M - H + f[s]] += S.v
    N = S.v * S.v
    hist[(H - 1) ** 2] += 2 * N
    hist[1] += N
    Wd = 2 * N + 2 * S.v * S.R
    s0 = sum(r * c for r, c in hist.items())
    assert Wd == 108516254 and s0 == dbm.S0 and max(hist) < M, (Wd, s0)

    def mu(a):
        return sum(c / Wd * (r / M) ** (1 - a) for r, c in hist.items())

    lo, hi = 0.0, 0.01
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if mu(mid) < 1 else (lo, mid)
    k = math.floor(lo * 10 ** 7)
    while dbm.tau_bound(hist, Wd, Fraction(k, 10 ** 7)) >= QT:
        k -= 1
    a = Fraction(k, 10 ** 7)
    tb = dbm.tau_bound(hist, Wd, a)
    one_tau2 = (1 - dbm.THETA) * a + dbm.THETA * dbm.A_LEAF
    lam = Fraction(math.floor(one_tau2 * 10 ** 11), 10 ** 11)
    lam1 = lam - Fraction(1, 10 ** 11)
    kappa = math.floor(dbm.EPS * lam1 * 2 ** 46)
    print('all chains nest; rank mass', s0, 'sum dim sigma', sum(f))
    print('histogram', sorted(hist.items()))
    print('a* = %.10e' % lo)
    print('tau-moment bound at a = %s: slack below q_tau %.3e' % (a, float(QT - tb)))
    print('1 - tau2 = %s, 1 - lambda = %s, 1 - lambda\' = %s' % (one_tau2, lam, lam1))
    print('kappa = %d/2^46 = 2^%.4f' % (kappa, math.log2(kappa / 2 ** 46)))
    if out_path:
        import json
        with open(out_path, 'w') as fh:
            json.dump({'source': {'upstream': dbm.UPSTREAM, 'sha256': dbm.PINS}, 'W': Wd, 'm': M,
                       'rankMass': s0, 'histogram': sorted([r, c] for r, c in hist.items()),
                       'aStar': lo, 'a': [a.numerator, a.denominator], 'kappa': kappa}, fh, indent=1)


if __name__ == '__main__':
    main(*sys.argv[1:])
