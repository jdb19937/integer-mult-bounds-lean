#!/usr/bin/env python3
"""The design-B whole-projector histogram of the PR97 node and its stage-2 moments (stdlib only).

Usage: stage2designb.py PR97_DIR [OUT_JSON]

PR97_DIR is upstream's `references/partial-gauge/pr97/` at
`463113d675af7410ac91d53a4fed51ec6494eb9a`; the SHA-256 of every file read is pinned below
(they are the pins of its `SOURCE.json`). The design-B word is Swapnil Jain's round-seven
schedule (`deferred_23.json.gz`): late copies, V leaves on the data wires `X_S`, and readouts of
the slot garbage deferred to frames `σ_u`. Its frame dimensions are upstream's data (node frames,
late-copy intersections, the bases of `σ_u` and of the V-leaf starts); nothing here re-derives
the geometry, which the Lean checks must establish.

Per stage (stage two is the complement time-reversal of stage one) and each of the `v`
invocations, every move between nested frames is one whole child of its rank:
* every side slot: the steps of its chain `σ_u, start, nodes, late-copy frames, root, 1` (`aux`),
  and its exterior `E₁ = I − (I − σ_u) ⊗ Q` (stage one) or `E₂ = (I−P) ⊗ I + P ⊗ σ_u` (stage
  two), of rank `m − h + dim σ_u`;
* every target `y_T`: its chain `0`, the deferred levels, `t_T^⊥`; every leaf `X_S`: its chain
  `⟨t_S⟩`, the V-gate frames, `1` (`data`);
* every centre temporary: one move of rank `h − 1`.
Per data pair: two connectors `(I−P) ⊗ (I−Q)` of rank `(h−1)²` and one rank-one correction.

The script checks the per-invocation `aux` and `data` histograms against upstream's receipt
(`bit-ledger-result.json`) and the rank mass against `s₀ = 57403754177`, then reports
`q₁ = s₀/(W m)`, the saving `a*` with `μ_{1−a*} = 1`, the rational τ-moment certificate of
`stage2cert.py` at `a = 1240/10⁷` (below `q_τ = 1 − 1/10⁸`), and the retune it implies:
`1 − τ₂ = (1−θ) a + θ a_leaf` at `θ = 1/1000`, `a_leaf = 3734039/10¹²`, the layer exponents
`λ`, `λ'` on the `10⁻¹¹` grid just above `τ₂`, and `κ = ⌊ε (1−λ') 2⁴⁶⌋ / 2⁴⁶` at `ε = 31/64`.
"""
import gzip
import hashlib
import json
import math
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations

UPSTREAM = '463113d675af7410ac91d53a4fed51ec6494eb9a'
PINS = {
    'witness_23.json.gz': 'b2486aa2bb222bacea6e52162a3920780e45dd8edc5d7cb03eabea336a1c6588',
    'deferred_23.json.gz': '8c38e947ff9e021e308000dd82bb5e2194eb265d8b75194e22ce783d3e75317c',
    'bit-ledger-result.json': 'c3dd79e5e6d72e49d8d1be2d4d9ad808cd7d24b7a725190d24100cbd3644394a',
}
H = 23
M = H * H
S0 = 57403754177
A = Fraction(1240, 10 ** 7)
QT = 1 - Fraction(1, 10 ** 8)
THETA = Fraction(1, 1000)
A_LEAF = Fraction(3734039, 10 ** 12)
EPS = Fraction(31, 64)


def read(d, name):
    path = d.rstrip('/') + '/' + name
    with open(path, 'rb') as fh:
        raw = fh.read()
    assert hashlib.sha256(raw).hexdigest() == PINS[name], ('pin mismatch', name)
    return json.loads(gzip.decompress(raw) if name.endswith('.gz') else raw)


class Schedule:
    """the design-B schedule: slot chains as frame keys, with upstream's dimensions"""

    def __init__(self, W, D):
        assert W['h'] == D['h'] == H
        self.R = D['R']
        self.trip = list(combinations(range(H), 3))
        self.v = len(self.trip)
        self.tid = {T: i for i, T in enumerate(self.trip)}
        self.args = {int(n): a for n, a in W['args'].items()}
        self.ops = D['ops']
        self.hold = D['hold']
        self.start = D['start']
        self.out = {s: (c, tuple(T)) for s, c, T in D['out']}
        self.ret = {s: c for s, c in D['ret']}
        self.readout = D['readout_order']
        self.f = [0] * self.R
        for s, B in zip(D['readout_order'], D['sigma']):
            self.f[s] = len(B)
        self.vdim = {s: len(B) for s, B in zip(D['vleaf_slots'], D['vleaf_start'])}
        self.xs = D['xs_order']
        self.node_dims = {n: d for n, d in D['node_dims']}
        self.late_dims = {(n, tuple(lt)): d for n, lt, d in D['late_dims']}
        self.late = {int(n): (e, l) for n, (e, l) in W['late'].items()}
        self.pivslot = {o[3]: o[1] for o in self.ops if o[0] == 'add'}

    def start_dim(self, s):
        n0 = self.hold[s][0]
        if self.args[n0] is None:
            return self.vdim[s]
        k = self.start[s][2]
        dec = self.late.get(n0)
        if dec is None or k in dec[0]:
            return self.node_dims[n0]
        lt = dec[1]
        return self.late_dims[n0, tuple(lt[lt.index(k):])]

    def chain(self, s):
        """the frame dimensions along slot s in time order"""
        ds = [self.f[s], self.start_dim(s)]
        for i, n in enumerate(self.hold[s]):
            if i > 0:
                ds.append(self.node_dims[n])
            if self.args[n] is not None and self.pivslot.get(n) == s and n in self.late:
                lt = self.late[n][1]
                for j in range(len(lt) - 1):
                    ds.append(self.late_dims[n, tuple(lt[j:])])
        if s in self.out or s in self.ret:
            ds.append(H - 1)
        ds.append(H)
        return ds

    def targets(self):
        """the targets `y_T` whose coefficient of slot s's garbage is nonzero over ℤ (the transpose
        sweep of the compiled operations applied to the root reads)"""
        cov = [Counter() for _ in range(self.R)]
        for s, (c, T) in self.out.items():
            cov[s][self.tid[T]] += 1
        for s, c in self.ret.items():
            for t, T in enumerate(self.trip):
                if c in T:
                    cov[s][t] += 1
        for op in reversed(self.ops):
            if op[0] == 'add':
                cov[op[2]].update(cov[op[1]])
            elif op[0] == 'fan':
                for g in op[2]:
                    cov[op[1]].update(cov[g])
        return [{t for t, x in c.items() if x} for c in cov]


def steps(ds):
    out = []
    for a, b in zip(ds, ds[1:]):
        assert b >= a, ('decreasing chain', ds)
        if b > a:
            out.append(b - a)
    return out


def histogram(S):
    aux = Counter()
    for s in range(S.R):
        aux.update(steps(S.chain(s)))
    assert sum(r * c for r, c in aux.items()) == sum(H - f for f in S.f)
    tg = S.targets()
    lev = defaultdict(set)
    for s in S.readout:
        for t in tg[s]:
            lev[t].add(S.f[s])
    data = Counter()
    for t in range(S.v):
        data.update(steps(sorted({0, H - 1} | lev[t])))
    for _n, us in S.xs:
        ds = [1] + [S.vdim[s] for s in us] + [H]
        data.update(steps([d for i, d in enumerate(ds) if i == 0 or d != ds[i - 1]]))
    hist = Counter()
    for _stage in range(2):
        for r, c in aux.items():
            hist[r] += S.v * c
        for r, c in data.items():
            hist[r] += S.v * c
        hist[H - 1] += S.v * H
        for s in range(S.R):
            hist[M - H + S.f[s]] += S.v
    N = S.v * S.v
    hist[(H - 1) ** 2] += 2 * N
    hist[1] += N
    return aux, data, hist, 2 * N + 2 * S.v * S.R


def tau_bound(hist, W, a):
    """`stage2cert.py`'s rational upper bound on `Σ_r (n_r/W)(r/m)^(1-a)`"""
    tot = Fraction(0)
    for r, c in hist.items():
        L = Fraction(math.ceil(math.log(M / r) * 10 ** 9) + 1, 10 ** 9)
        y = a * L
        assert 0 <= y <= 1
        tot += Fraction(c, W) * Fraction(r, M) * (1 + y + y * y / 2 + Fraction(2, 9) * y ** 3)
    return tot


def main(pr97_dir, out_path=None):
    W = read(pr97_dir, 'witness_23.json.gz')
    D = read(pr97_dir, 'deferred_23.json.gz')
    rec = read(pr97_dir, 'bit-ledger-result.json')
    S = Schedule(W, D)
    aux, data, hist, Wd = histogram(S)
    up = rec['rank_histograms']
    assert aux == Counter({int(r): c for r, c in up['aux'].items()}), 'aux histogram'
    assert data == Counter({int(r): c for r, c in up['data'].items()}), 'data histogram'
    s = sum(r * c for r, c in hist.items())
    assert Wd == 108516254 and s == S0, (Wd, s)
    assert max(hist) < M
    q1 = Fraction(s, Wd * M)

    def mu(a):
        return sum(c / Wd * (r / M) ** (1 - a) for r, c in hist.items())

    lo, hi = 0.0, 0.01
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if mu(mid) < 1 else (lo, mid)
    tb = tau_bound(hist, Wd, A)
    assert tb < QT and q1 < 1
    one_tau2 = (1 - THETA) * A + THETA * A_LEAF
    lam = Fraction(math.floor(one_tau2 * 10 ** 11), 10 ** 11)
    assert lam < one_tau2
    lam1 = lam - Fraction(1, 10 ** 11)
    kappa = math.floor(EPS * lam1 * 2 ** 46)
    print('slots', S.R, 'deferred', len(S.readout), 'sum dim sigma', sum(S.f))
    print('aux and data histograms match the receipt; rank mass', s)
    print('histogram', sorted(hist.items()))
    print('q1 = %d/%d' % (q1.numerator, q1.denominator))
    print('a* = %.10e' % lo)
    print('tau-moment bound at a = %s: %.15f, slack below q_tau %.3e' % (A, float(tb), float(QT - tb)))
    print('1 - tau2 = %s' % one_tau2)
    print('1 - lambda = %s, 1 - lambda\' = %s' % (lam, lam1))
    print('kappa = %d/2^46 = 2^%.4f' % (kappa, math.log2(kappa / 2 ** 46)))
    if out_path:
        out = {
            'source': {'upstream': UPSTREAM, 'sha256': PINS},
            'W': Wd, 'm': M, 'rankMass': s,
            'histogram': sorted([r, c] for r, c in hist.items()),
            'aux': sorted([r, c] for r, c in aux.items()),
            'data': sorted([r, c] for r, c in data.items()),
            'mu1': [q1.numerator, q1.denominator],
            'aStar': lo,
            'kappa': kappa,
        }
        with open(out_path, 'w') as fh:
            json.dump(out, fh, indent=1)


if __name__ == '__main__':
    main(*sys.argv[1:])
