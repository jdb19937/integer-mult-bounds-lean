#!/usr/bin/env python3
"""The rational moment certificate of the stage-2 histogram (stdlib only).

Usage: stage2cert.py HIST_JSON

HIST_JSON is stage2hist.py's output. With `τ* = 1 - a`, `a = 969/10^7`, the τ-moment is
`Σ_r (n_r/W)(r/m)^τ* = Σ_r (n_r/W)(r/m) exp(a log(m/r))`. For each rank `r` the script picks a
rational `L_r > log(m/r)`, at 10⁻⁹ above, certified by an exponential series of `k_r` terms:
`m/r < Σ_{i<k_r} L_r^i / i!`. With `exp x ≤ 1 + x + x²/2 + 2x³/9` on `[0, 1]`, the rational sum
`Σ_r (n_r/W)(r/m)(1 + y_r + y_r²/2 + 2y_r³/9)`, `y_r = a L_r`, must stay below
`q_τ = 1 - 2/10^8`. The script prints the bounds as Lean literals and the slack.
"""
import json
import math
import sys
from fractions import Fraction
from math import factorial

A = Fraction(969, 10 ** 7)
QT = 1 - Fraction(2, 10 ** 8)


def series(L, k):
    return sum(L ** i / factorial(i) for i in range(k))


def main(path):
    H = json.load(open(path))
    hist = [tuple(x) for x in H['histogram']]
    W, m = H['W'], H['m']
    total = Fraction(0)
    mu1 = Fraction(0)
    rows = []
    for r, c in hist:
        L = Fraction(math.ceil(math.log(m / r) * 10 ** 9) + 1, 10 ** 9)
        k = 1
        while not series(L, k) > Fraction(m, r):
            k += 1
        y = A * L
        assert 0 <= y <= 1
        total += Fraction(c, W) * Fraction(r, m) * (1 + y + y * y / 2 + Fraction(2, 9) * y ** 3)
        mu1 += Fraction(c, W) * Fraction(r, m)
        rows.append((r, c, L, k))
    assert total < QT and mu1 < 1
    print('-- (rank, count, log bound numerator over 10^9, series terms)')
    for r, c, L, k in rows:
        print('(%d, %d, %d, %d)' % (r, c, L * 10 ** 9, k))
    print('q1 = %d/%d' % (mu1.numerator, mu1.denominator))
    print('tau-moment bound %.15f, slack below q_tau %.3e' % (float(total), float(QT - total)))


if __name__ == '__main__':
    main(sys.argv[1])
