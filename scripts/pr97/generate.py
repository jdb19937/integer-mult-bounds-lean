#!/usr/bin/env python3
"""Generate the PR97 local-word data for `IntegerMultBounds/MathlibTM2/M8/` (stdlib only).

Usage: generate.py PR97_DIR OUT_JSON

PR97_DIR is upstream's `references/partial-gauge/pr97/` (pinned in its `SOURCE.json`); it must
contain `witness_23.json.gz`. OUT_JSON receives the renumbered DAG, the support records, the
links in target form, the roots and the link relations, plus the statistics checked below.

Everything written here is re-checked in Lean; this script also runs the same local checks and
the complete F2 replay of the plain word, so a bad witness fails here first.
"""
import json
import sys
from collections import Counter
from fractions import Fraction

import witness as wit


# ----------------------------------------------------------------------------- pair masks
def rk(c, u):
    """rank of point u among the points other than c."""
    assert u != c
    return u if u < c else u - 1


def pbit(c, u, w):
    """bit of the pair {u, w} (both != c) in the 22x22 upper-triangle layout relative to c."""
    a, b = sorted((rk(c, u), rk(c, w)))
    assert a < b
    return 22 * a + b


def pairmask(c, pairs):
    m = 0
    for u, w in pairs:
        m |= 1 << pbit(c, u, w)
    return m


def all_pairs(h, c):
    pts = [u for u in range(h) if u != c]
    return pairmask(c, [(u, w) for i, u in enumerate(pts) for w in pts[i + 1:]])


# ----------------------------------------------------------------------------- compile
def compile_plain(W):
    """the plain compile (no deferral, copies right after their node), in old ids.
    Returns ops [('src', slot, n) | ('add', piv, oth, n) | ('copy', piv, f, n)], the root reads
    [(slot, ('out', (c, T)) | ('ret', c))] and the slot count."""
    linked = {(y, k) for x, (y, k) in W.links.items()}
    edge = {}
    ops = []
    reads = []
    nslots = 0

    def assign(s, n, k):
        u = W.users[n][k]
        if u[0] == 'gate':
            edge[u[1], u[2]] = s
        else:
            reads.append((s, u))

    for n in W.order:
        a = W.args[n]
        if a is None:
            piv = nslots
            nslots += 1
            ops.append(('src', piv, n))
        else:
            x, y = a
            sa, sb = edge.pop((n, 0)), edge.pop((n, 1))
            if n in W.links and W.links[n][0] == x:
                sa, sb = sb, sa
            piv, oth = sa, sb
            ops.append(('add', piv, oth, n))
            if n in W.links:
                ly, lk = W.links[n]
                assign(oth, ly, lk)
        ks = [k for k in range(len(W.users[n])) if (n, k) not in linked]
        assert ks, ('node without a free use', n)
        for k in ks[1:]:
            f = nslots
            nslots += 1
            ops.append(('copy', piv, f, n))
            assign(f, n, k)
        assign(piv, n, ks[0])
    assert not edge
    return ops, reads, nslots


def replay_f2(W, ops, reads, R):
    """complete F2 replay of the plain local word on all basis vectors: start readouts with the
    adjoint masks, sources, ops, root reads, inverse ops, sources. Returns True on y += x with
    x and every side slot restored."""
    v = W.v
    tid = W.tid
    readT = []
    for s, u in reads:
        Ts = [tid[u[1][1]]] if u[0] == 'out' else [t for t, T in enumerate(W.trip) if u[1] in T]
        readT.append((s, Ts))
    cov = [set() for _ in range(R)]
    for s, Ts in readT:
        for t in Ts:
            cov[s] ^= {t}
    for o in reversed(ops):
        if o[0] == 'add':
            cov[o[2]] ^= cov[o[1]]
        elif o[0] == 'copy':
            cov[o[1]] ^= cov[o[2]]
    size = 2 * v + R
    bits = [1 << i for i in range(size)]
    Y = lambda t: v + t
    A = lambda s: 2 * v + s
    for s in range(R):
        for t in cov[s]:
            bits[Y(t)] ^= bits[A(s)]
    src = [(o[1], o[2]) for o in ops if o[0] == 'src']
    for s, n in src:
        bits[A(s)] ^= bits[n - 1]
    for o in ops:
        if o[0] == 'add':
            bits[A(o[1])] ^= bits[A(o[2])]
        elif o[0] == 'copy':
            bits[A(o[2])] ^= bits[A(o[1])]
    for s, Ts in readT:
        for t in Ts:
            bits[Y(t)] ^= bits[A(s)]
    for o in reversed(ops):
        if o[0] == 'add':
            bits[A(o[1])] ^= bits[A(o[2])]
        elif o[0] == 'copy':
            bits[A(o[2])] ^= bits[A(o[1])]
    for s, n in src:
        bits[A(s)] ^= bits[n - 1]
    return all(bits[i] == ((1 << i) ^ (1 << (i - v)) if v <= i < 2 * v else 1 << i)
               for i in range(size))


# ----------------------------------------------------------------------------- records
def support_record(W, n):
    """('leaf', triple) | ('two', x, y, Zmask) | ('one', c, Pmask)."""
    T = W.support_triples(n)
    common = set(W.trip[T[0]])
    for i in T[1:]:
        common &= set(W.trip[i])
    if len(common) == 3:
        return ('leaf', T[0])
    if len(common) == 2:
        x, y = sorted(common)
        Z = 0
        for i in T:
            (z,) = set(W.trip[i]) - common
            Z |= 1 << z
        return ('two', x, y, Z)
    assert len(common) == 1, ('support without a common point', n)
    (c,) = common
    return ('one', c, pairmask(c, [tuple(sorted(set(W.trip[i]) - {c})) for i in T]))


def rel_mask(W, rec, c):
    """the pair mask of a support record relative to a point c of all its triples, or None."""
    if rec[0] == 'leaf':
        S = W.trip[rec[1]]
        if c not in S:
            return None
        u, w = [x for x in S if x != c]
        return 1 << pbit(c, u, w)
    if rec[0] == 'two':
        _, x, y, Z = rec
        if c not in (x, y):
            return None
        o = y if c == x else x
        return pairmask(c, [(o, z) for z in range(W.h) if Z >> z & 1])
    _, cc, P = rec
    return P if cc == c else None


def points(rec, W):
    if rec[0] == 'leaf':
        return set(W.trip[rec[1]])
    if rec[0] == 'two':
        return {rec[1], rec[2]}
    return {rec[1]}


def odd_path(h, c, Pt, u, w):
    """a path of odd length from u to w in the pair graph Pt (relative to c), or None. Its
    alternating sum of edge vectors is e_u + e_w, so the triple {c, u, w} lies in the span."""
    pts = [x for x in range(h) if x != c]
    adj = {x: [y for y in pts if y != x and Pt >> pbit(c, x, y) & 1] for x in pts}
    start = (u, 0)
    prev = {start: None}
    queue = [start]
    while queue:
        x, par = queue.pop(0)
        if x == w and par == 1:
            path = []
            node = (x, par)
            while node is not None:
                path.append(node[0])
                node = prev[node]
            return path[::-1]
        for y in adj[x]:
            nxt = (y, 1 - par)
            if nxt not in prev:
                prev[nxt] = (x, par)
                queue.append(nxt)
    return None


def main(pr97_dir, out_path):
    path = pr97_dir.rstrip('/') + '/witness_23.json.gz'
    W = wit.Witness(path)
    new = W.new
    N, v, h = len(W.order), W.v, W.h
    stats = Counter()

    # compile and replay
    ops, reads, R = compile_plain(W)
    stats['slots'] = R
    stats['ops'] = len(ops)
    assert replay_f2(W, ops, reads, R), 'plain word is not y += x'

    # supports
    sup = {n: support_record(W, n) for n in W.order}
    stats.update(Counter('support_' + r[0] for r in sup.values()))

    # node records in new ids
    nodes = []
    linkedFrom = {}
    for n, (y, k) in W.links.items():
        u = W.users[y][k]
        assert u[0] == 'gate'
        linkedFrom[new[u[1]], u[2]] = new[n]
    for n in W.order:
        i = new[n]
        a = W.args[n]
        rec = {'id': i}
        if a is None:
            rec['leaf'] = n - 1
        else:
            rec['args'] = [new[a[0]], new[a[1]]]
            assert new[a[0]] < i and new[a[1]] < i
            if n in W.links:
                y, k = W.links[n]
                u = W.users[y][k]
                rec['link'] = {'operand': a.index(y), 'user': new[u[1]], 'pos': u[2]}
                assert new[n] < new[u[1]], 'link not timed'
            for pos in (0, 1):
                if (i, pos) in linkedFrom:
                    rec.setdefault('linkedFrom', {})[str(pos)] = linkedFrom[i, pos]
        s = sup[n]
        rec['supp'] = list(s)
        nodes.append(rec)
    # a free (non-linked) use witness per node
    linked = {(y, k) for x, (y, k) in W.links.items()}
    for n in W.order:
        ks = [k for k in range(len(W.users[n])) if (n, k) not in linked]
        u = W.users[n][ks[0]]
        nodes[new[n]]['free'] = (['gate', new[u[1]], u[2]] if u[0] == 'gate'
                                 else ['out', u[1][0], list(u[1][1])] if u[0] == 'out'
                                 else ['ret', u[1]])

    # local checks (mirror of the Lean checks)
    for rec in nodes:
        if 'args' not in rec:
            continue
        s = rec['supp']
        sa, sb = (nodes[j]['supp'] for j in rec['args'])
        if s[0] == 'two':
            _, x, y, Z = s
            Za = Zb = None
            for name, t in (('a', sa), ('b', sb)):
                if t[0] == 'two':
                    assert (t[1], t[2]) == (x, y)
                    z = t[3]
                else:
                    S = W.trip[t[1]]
                    assert x in S and y in S
                    (zz,) = set(S) - {x, y}
                    z = 1 << zz
                if name == 'a':
                    Za = z
                else:
                    Zb = z
            assert Za & Zb == 0 and Za | Zb == Z
            stats['check_two'] += 1
        else:
            _, c, P = s
            Pa, Pb = rel_mask(W, tuple(sa), c), rel_mask(W, tuple(sb), c)
            assert Pa is not None and Pb is not None and Pa & Pb == 0 and Pa | Pb == P
            stats['check_one'] += 1
            stats['conv_two'] += (sa[0] == 'two') + (sb[0] == 'two')
    # roots
    roots = []
    for c, T, n in W.outputs:
        rec = nodes[new[n]]['supp']
        a, b = [x for x in T if x != c]
        want = pairmask(c, [(u, w) for u in range(h) for w in range(u + 1, h)
                            if c not in (u, w) and not {u, w} & {a, b}])
        assert rel_mask(W, tuple(rec), c) == want
        roots.append({'node': new[n], 'out': [c, list(T)]})
    for c, n in W.retained:
        rec = nodes[new[n]]['supp']
        assert rel_mask(W, tuple(rec), c) == all_pairs(h, c)
        roots.append({'node': new[n], 'ret': c})
    # links
    relations = 0
    for rec in nodes:
        if 'link' not in rec:
            continue
        L = rec['link']
        t = nodes[L['user']]
        y = rec['args'][L['operand']]
        assert t['args'][L['pos']] == y
        assert t['linkedFrom'][str(L['pos'])] == rec['id']
        st, sn = tuple(t['supp']), tuple(rec['supp'])
        cs = sorted(points(st, W) & points(sn, W))
        assert cs, 'link without a common point'
        c = cs[0]
        Pt, Pn = rel_mask(W, st, c), rel_mask(W, sn, c)
        if Pn & ~Pt == 0:
            stats['link_inclusion'] += 1
            continue
        rels = []
        extra = Pn & ~Pt
        pts = [x for x in range(h) if x != c]
        for i, u in enumerate(pts):
            for w in pts[i + 1:]:
                if extra >> pbit(c, u, w) & 1:
                    walk = odd_path(h, c, Pt, u, w)
                    assert walk is not None, 'link span fails'
                    rels.append(walk)
                    stats['path_len_%d' % (len(walk) - 1)] += 1
        L['point'] = c
        L['relations'] = rels
        relations += len(rels)
        stats['link_relations'] += 1
    stats['relations'] = relations
    # counts
    stats['N'] = N
    stats['v'] = v
    stats['roots'] = len(roots)
    stats['links'] = len(W.links)
    assert R == N - v + len(roots) - len(W.links)
    out = {
        'source': {'witness': path, 'sha256': wit.sha256(path)},
        'h': h, 'v': v, 'N': N, 'R': R,
        'nodes': nodes, 'roots': roots, 'stats': dict(stats),
    }
    with open(out_path, 'w') as fh:
        json.dump(out, fh, separators=(',', ':'))
    print(json.dumps(dict(stats), indent=1))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
