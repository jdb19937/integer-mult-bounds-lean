"""Reader for the pinned PR97 round-seven witness (stdlib only).

The witness is Swapnil Jain's `witness_23.json.gz`, pinned in upstream
`references/partial-gauge/pr97/` (see `SOURCE.json` there). This module reads it, checks its
DAG, renumbers the active nodes in compile order and recovers the use order that the witness's
links refer to.

Conventions:
* points are `0..h-1`; triples are the `C(h,3)` subsets in lexicographic order;
* old node ids are the witness's (`1..v` are the leaves, leaf `i` is triple `i-1`);
* new node ids are positions in compile order: nodes sorted by (dimension of the span of their
  support, old id). Leaves get new ids `0..v-1`, equal to their triple index.
"""
import gzip
import hashlib
import json
from itertools import combinations

PRIME = (1 << 61) - 1   # ranks mod PRIME are exact: 0/1 rows of weight 3 have minors < 3^12


def sha256(path):
    with open(path, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def rank_mod(rows, p=PRIME):
    """rank of integer rows mod p (Gaussian elimination)."""
    piv = {}
    r = 0
    for row in rows:
        v = [x % p for x in row]
        for c, (prow, inv) in sorted(piv.items()):
            if v[c]:
                f = v[c] * inv % p
                v = [(a - f * b) % p for a, b in zip(v, prow)]
        lead = next((c for c, x in enumerate(v) if x), None)
        if lead is not None:
            piv[lead] = (v, pow(v[lead], p - 2, p))
            r += 1
    return r


class Witness:
    def __init__(self, path):
        with gzip.open(path, 'rt') as fh:
            self.raw = W = json.load(fh)
        self.h = h = W['h']
        self.trip = list(combinations(range(h), 3))
        self.v = v = len(self.trip)
        self.tid = {T: i for i, T in enumerate(self.trip)}
        self.args = {int(n): (tuple(a) if a else None) for n, a in W['args'].items()}
        for n, a in self.args.items():
            if a is None:
                assert 1 <= n <= v and tuple(W['leaf'][str(n)]) == self.trip[n - 1]
            else:
                assert all(x < n and x in self.args for x in a)
        # supports as bitsets over triples (old ids)
        self.sup = {}
        for n in sorted(self.args):
            a = self.args[n]
            if a is None:
                self.sup[n] = 1 << (n - 1)
            else:
                x, y = a
                assert not self.sup[x] & self.sup[y], 'overlapping supports'
                self.sup[n] = self.sup[x] | self.sup[y]
        self.outputs = [(c, tuple(T), n) for c, T, n in W['outputs']]
        self.retained = [(c, n) for c, n in W['retained']]
        self.links = {x: (y, k) for x, y, k in W['links']}
        self._dims()
        self._renumber()
        self._users()

    def support_triples(self, n):
        s = self.sup[n]
        return [i for i in range(self.v) if s >> i & 1]

    def _dims(self):
        """dimension of the span of the support triples of every node (exact)."""
        h = self.h
        self.dim = {}
        rows = [[int(q in T) for q in range(h)] for T in self.trip]
        for n in sorted(self.args):
            self.dim[n] = rank_mod([rows[i] for i in self.support_triples(n)])

    def _renumber(self):
        self.order = sorted(self.args, key=lambda n: (self.dim[n], n))
        self.new = {n: i for i, n in enumerate(self.order)}
        assert all(self.new[n] == n - 1 for n in range(1, self.v + 1)), 'leaves first'

    def _users(self):
        """the use list of every node, in the witness's order: gate uses by (dim, id) of the
        user, then outputs, then retained (old ids)."""
        users = {n: [] for n in self.args}
        for n in self.order:
            a = self.args[n]
            if a:
                for pos, x in enumerate(a):
                    users[x].append(('gate', n, pos))
        for c, T, n in sorted(self.outputs):
            users[n].append(('out', (c, T)))
        for c, n in sorted(self.retained):
            users[n].append(('ret', c))
        self.users = users
