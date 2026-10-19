#!/usr/bin/env python3
"""The S6 retune: the cost chain at the PR97 stage-1 exponent.

With the supplier seam pointed at the PR97 network (`apply_seam.py --supplier=pr97`), this sets
the cost chain's exponent and saving:

* `Parameters.tau = 1 - 3734039/10^12` (`M8/Global/Branching97`);
* `CompactInterim.lam = 1 - 35/10^7`, `lam' = 1 - 33/10^7`, `kappa = 111364923/2^46`;
* `Cost.Total.tot_kappa_eq`: `totKappa = 115755209/(10^12 * 2^38)`;
* the stated saving of `mulInTime` and its callers, and their documentation.

The binding margin is the layout margin `ε c (1-τ)`, with slack below `2^-46`. Every replacement
must match exactly once, so the script fails loudly on a changed upstream text.

usage: retune.py [--dry-run]
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRY = '--dry-run' in sys.argv

KAPPA_OLD, KAPPA_NEW = '88279', '111364923'

EDITS = {
    'IntegerMultBounds/Parameters.lean': [
        ('def tau : ℝ := 1 - 296 / 10 ^ 11', 'def tau : ℝ := 1 - 3734039 / 10 ^ 12'),
    ],
    'IntegerMultBounds/MathlibTM2/Cost/CompactInterimParameters.lean': [
        ('def lam : ℝ := 1-28/(10^10:ℝ)', 'def lam : ℝ := 1-35/(10^7:ℝ)'),
        ("def lam' : ℝ := 1-23/(2^33:ℝ)", "def lam' : ℝ := 1-33/(10^7:ℝ)"),
        ('rounded down to `2^-46`, about `2^-29.57`.', 'rounded down to `2^-46`, about `2^-19.27`.'),
        ('def kappa : ℝ := 88279/(2^46:ℝ)', 'def kappa : ℝ := 111364923/(2^46:ℝ)'),
    ],
    'IntegerMultBounds/MathlibTM2/Cost/Total.lean': [
        ('Exponents: `τ = 1 - 296/10¹¹`', 'Exponents: `τ = 1 - 3734039/10¹²`'),
        ('theorem tot_kappa_eq : totKappa = 1147 / (10 ^ 11 * 2 ^ 35) := by',
         'theorem tot_kappa_eq : totKappa = 115755209 / (10 ^ 12 * 2 ^ 38) := by'),
    ],
    'IntegerMultBounds/MathlibTM2/Theorem.lean': [
        ('saving `88279 · 2^-46`', 'saving `111364923 · 2^-46`'),
        ('and `1-τ = 296 · 10^-11`, about\n`2^-29.57`.', 'and `1-τ = 3734039 · 10^-12`,\nabout `2^-19.27`.'),
        ('theorem mulInTime : MulInTime (88279 / 2 ^ 46 : ℝ) :=', 'theorem mulInTime : MulInTime (111364923 / 2 ^ 46 : ℝ) :='),
        ('theorem saving_gt : 10 * (2 ^ 33 : ℝ)⁻¹ < 88279 / 2 ^ 46 := by norm_num',
         'theorem saving_gt : 10 * (2 ^ 33 : ℝ)⁻¹ < 111364923 / 2 ^ 46 := by norm_num'),
    ],
}

# Files whose every `88279/2^46` literal is the saving of the cost chain.
KAPPA_FILES = [
    'IntegerMultBounds/MathlibTM2/Fast/CompactFinalR.lean',
    'IntegerMultBounds/MathlibTM2/Fast/CompactMainDispatch.lean',
    'IntegerMultBounds/MathlibTM2/DFT/DFTCheck.lean',
    'CompletedProofCheck.lean',
]

changes = {}
for rel, pairs in EDITS.items():
    p = ROOT / rel
    t = p.read_text()
    for old, new in pairs:
        n = t.count(old)
        if n != 1 and t.count(new) == 1:
            continue  # already applied
        if n != 1:
            sys.exit(f'{rel}: expected one occurrence of {old!r}, found {n}')
        t = t.replace(old, new)
    changes[p] = t
for rel in KAPPA_FILES:
    p = ROOT / rel
    t = p.read_text()
    t = t.replace(f'{KAPPA_OLD} / 2 ^ 46', f'{KAPPA_NEW} / 2 ^ 46').replace(f'{KAPPA_OLD}/2^46', f'{KAPPA_NEW}/2^46')
    t = t.replace(f'{KAPPA_OLD} · 2^-46', f'{KAPPA_NEW} · 2^-46')
    changes[p] = t

for p, t in changes.items():
    old = p.read_text()
    n = sum(1 for a, b in zip(old.split('\n'), t.split('\n')) if a != b)
    print(f'{p.relative_to(ROOT)}: {n} lines')
    if not DRY and old != t:
        p.write_text(t)
left = [str(p.relative_to(ROOT)) for p, t in changes.items() if KAPPA_OLD in t]
if left:
    print('88279 remains in:', ', '.join(left))
print('dry run' if DRY else 'applied')
