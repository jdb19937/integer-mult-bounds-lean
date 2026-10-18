#!/usr/bin/env python3
"""Emit the port certificates of the compressed nine-stage PR589 geometry.

For each of the 111 live ports, upstream's `research/e8-bit-carrier-skeleton/code/nine/geometry.py`
(PR #386, as parameterised by PR #545's `adapt.py` for punctured words) builds a Weyl element `g_t`
by reflections over the 120 E8 lines of `bitE8-r865.json.gz`, with `g_t` mapping line 0 to the port's
line up to sign. The complement columns `A_t = g_t[:, 1:]` are an orthonormal basis of the line's
orthogonal space. This script recomputes `g_t` exactly in the same order and writes the line and
twice the complement columns (integers) to `Nine/PortData.lean`; Lean's kernel checks the
orthonormality equations (`PortCertificate.Checked`).

usage: generate_pr589_ports.py WORD.json.gz LINES120.json.gz [--expect GEOMETRY.json]

WORD is the pinned PR589 word (`research/e8-bit-p111-tuned/tune/bitE8mut-p111-tuned.json.gz`);
LINES120 is `research/e8-bit-carrier-skeleton/data/bit/bitE8-r865.json.gz`. `--expect` compares the
complement columns with an upstream `GEOMETRY.json` emitted for the same word.
"""
import argparse, gzip, hashlib, json
from fractions import Fraction
from pathlib import Path

WORD_SHA256 = 'e3e301e62bc2b41dbf1ceac0acf3d35824ebeab1848c5a2142d4577b109da52f'
LINES_SHA256 = '1fb726ea3818fe0837cceb0dd22a71a0814f064e5e781628104610d6468e0e55'
OUT = Path('IntegerMultBounds/Networks/Certificates/PR589/Nine/PortData.lean')
NS = 'IntegerMultBounds.Networks.Certificates.PR589.Nine'


def load(path, sha):
    raw = Path(path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == sha, path
    return json.loads(gzip.decompress(raw))


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
            for i in range(len(a))]


def eye(n):
    return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]


def weyl(lines):
    """geometry.py's breadth-first reflection walk from line 0."""
    n = len(lines)
    ip = lambda u, v: Fraction(sum(x * y for x, y in zip(u, v)), 2)
    gs = {0: eye(8)}
    todo = [0]
    while todo:
        more = []
        for i in todo:
            for j in range(n):
                if j in gs or abs(ip(lines[i], lines[j])) != 1:
                    continue
                d = ([x - y for x, y in zip(lines[i], lines[j])] if ip(lines[i], lines[j]) == 1
                     else [x + y for x, y in zip(lines[i], lines[j])])
                dd = sum(x * x for x in d)
                r = [[Fraction(int(a == b)) - Fraction(2 * d[a] * d[b], dd) for b in range(8)]
                     for a in range(8)]
                gs[j] = matmul(r, gs[i])
                more.append(j)
        todo = more
    assert len(gs) == n
    return gs


def vec(xs):
    return '![' + ', '.join(str(x) for x in xs) + ']'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('word')
    ap.add_argument('lines120')
    ap.add_argument('--expect', type=Path)
    a = ap.parse_args()
    w = load(a.word, WORD_SHA256)
    src = load(a.lines120, LINES_SHA256)
    assert (w['h'], w['v'], w['form']) == (8, 111, '<x,y>/2') and len(src['lines']) == 120
    lines = src['lines']
    live = w['ports_geom']
    assert len(live) == 111 and all(w['lines'][t] == lines[p] for t, p in enumerate(live))
    gs = weyl(lines)
    I = eye(8)
    ports = []
    for t, p in enumerate(live):
        g, q = gs[p], lines[p]
        assert matmul([list(r) for r in zip(*g)], g) == I
        image = [sum(g[i][k] * lines[0][k] for k in range(8)) for i in range(8)]
        assert image == q or image == [-x for x in q]
        A = [row[1:] for row in g]
        twice = [[2 * x for x in row] for row in A]
        assert all(x.denominator == 1 for row in twice for x in row)
        twice = [[int(x) for x in row] for row in twice]
        assert sum(x * x for x in q) == 4
        for k in range(7):
            for l in range(7):
                assert sum(twice[i][k] * twice[i][l] for i in range(8)) == 4 * (k == l)
        for i in range(8):
            for j in range(8):
                assert sum(twice[i][k] * twice[j][k] for k in range(7)) + q[i] * q[j] == 4 * (i == j)
        assert all(sum(q[i] * twice[i][k] for i in range(8)) == 0 for k in range(7))
        ports.append((q, twice))
    if a.expect:
        geo = json.loads(a.expect.read_text())
        assert len(geo['ports']) == 111
        for t, (q, twice) in enumerate(ports):
            e = geo['ports'][t]
            assert e['q'] == q
            assert [[2 * Fraction(x) for x in row] for row in e['complement_columns']] == twice
        print('complement columns agree with', a.expect)
    body = []
    for t, (q, twice) in enumerate(ports):
        body.append(f'  ⟨{vec(q)}, ![' + ', '.join(vec(row) for row in twice) + ']⟩')
    text = ('module\n\npublic import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortFrame\n\n'
            '/-! The 111 port certificates of the compressed nine-stage geometry, in port order: each\n'
            "port's line and twice its complement columns. Generated by\n"
            'scripts/generate_pr589_ports.py from the pinned PR589 word and the 120 E8 lines of\n'
            'upstream\'s `bitE8-r865.json.gz`; the kernel checks every certificate. -/\n'
            f'@[expose] public section\nnamespace {NS}\n\n'
            'def ports : List PortCertificate := [\n' + ',\n'.join(body) + ']\n\n'
            'theorem ports_length : ports.length = 111 := by decide +kernel\n\n'
            'theorem ports_checked : ∀ c ∈ ports, c.Checked := by decide +kernel\n\n'
            f'end {NS}\n')
    OUT.write_text(text)
    print('wrote', OUT, len(ports), 'ports')


if __name__ == '__main__':
    main()
