#!/usr/bin/env python3
"""The S6 supplier seam.

The cost chain consumes the binary interchanges through `BinaryRadixEqualShared`,
`BinaryInterchangeRun` (with `BinaryInterchangeBudget`) and the exponent `Parameters.tau`. This
script makes those names a seam and gives Shared50's implementation its own names:

* Kenny's three modules move to `Shared50BinaryRadixEqualShared`, `Shared50BinaryInterchangeRun`
  and `Shared50BinaryInterchangeBudget`, and the Shared50 supplier modules
  (`shared50_supplier_modules.txt`) refer to them;
* the Shared50 supplier modules use Shared50's own exponent `Shared50Parameters.tau`, and
  `Shared50RecursiveBudgetBound.tau_range` in place of `exponent_range`;
* new seam modules at the three old paths re-export the Shared50 supplier and restate its two
  uniform bounds at `Parameters.tau`; `Shared50RecursiveBudgetBound.exponent_range` states the
  range of `Parameters.tau`.

Consumers (Host, Cost, Fast, Node and the compact gadgets) are not edited. The script is
idempotent: rerun it after an upstream merge. Files that use `Parameters.tau` outside the supplier
list and outside the known consumers are reported for a decision.

usage: apply_seam.py [--dry-run] [--supplier=m8|pr97]

The chosen supplier is kept in `supplier.txt`; `m8` points the seams at the M8 machine on
Shared50 as a bit network (`M8/Machine/Shared50Network`). The `shared50` choice, Kenny's own
machine, was retired with its modules (`docs/retired-shared50-machine.md`).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / 'IntegerMultBounds'
MACHINE = PKG / 'Machine'
DRY = '--dry-run' in sys.argv
MARK = '-- S6 supplier seam'

MOVES = {
    'BinaryRadixEqualShared': 'Shared50BinaryRadixEqualShared',
    'BinaryInterchangeRun': 'Shared50BinaryInterchangeRun',
    'BinaryInterchangeBudget': 'Shared50BinaryInterchangeBudget',
}

changes = {}  # path -> (old, new)


def read(p):
    if p in changes:
        return changes[p][1]
    return p.read_text() if p.exists() else None


def write(p, new):
    old = changes[p][0] if p in changes else (p.read_text() if p.exists() else None)
    if old != new:
        changes[p] = (old, new)


def module_path(mod):
    return ROOT / (mod.replace('.', '/') + '.lean')


def rename_supplier_names(text):
    for old, new in MOVES.items():
        text = re.sub(r'(?<![\w])' + old + r'\b', new, text)
    return text


SUPPLIER_RANGE = ('/-- The range of the supplier exponent `Parameters.tau` of the cost chain. -/\n'
                  'theorem exponent_range : 0 < Parameters.tau ∧ Parameters.tau < 1 := by\n'
                  '  norm_num [Parameters.tau]\n')


def rename_tau(text):
    keep = SUPPLIER_RANGE in text
    text = text.replace(SUPPLIER_RANGE, '@@S6_SUPPLIER_RANGE@@')
    text = re.sub(r'(?<![\w])((?:IntegerMultBounds\.)?)Parameters\.tau\b', r'\1Shared50Parameters.tau', text)
    text = text.replace('Shared50RecursiveBudgetBound.exponent_range', 'Shared50RecursiveBudgetBound.tau_range')
    if keep:
        text = text.replace('@@S6_SUPPLIER_RANGE@@', SUPPLIER_RANGE)
    return text


def is_seam(p):
    t = p.read_text() if p.exists() else ''
    return MARK in t


# 1. Move Kenny's implementations (from the old path, whenever it holds an implementation).
for old, new in MOVES.items():
    src, dst = MACHINE / (old + '.lean'), MACHINE / (new + '.lean')
    if src.exists() and not is_seam(src):
        write(dst, rename_supplier_names(src.read_text()))

# 2. The Shared50 supplier modules: names of the moved modules and Shared50's own exponent.
supplier = [l.strip() for l in (Path(__file__).parent / 'shared50_supplier_modules.txt').read_text().split()]
supplier = [m for m in supplier if m.split('.')[-1] not in MOVES] + \
    ['IntegerMultBounds.Machine.' + n for n in MOVES.values()]
for mod in supplier:
    p = module_path(mod)
    t = read(p)
    if t is None:
        continue
    write(p, rename_tau(rename_supplier_names(t)))

# 3. Shared50's exponent and its range.
p = PKG / 'Shared50Parameters.lean'
t = read(p)
if 'def tau : ℝ' not in t:
    t = t.replace('noncomputable section\n',
                  'noncomputable section\n\n/-- The width exponent certified for the Shared50 node. -/\n'
                  'def tau : ℝ := 1 - 296 / 10 ^ 11\n', 1)
    write(p, t)
p = MACHINE / 'Shared50RecursiveBudgetBound.lean'
t = read(p)
t = re.sub(r'theorem exponent_range : 0 < Shared50Parameters\.tau', 'theorem tau_range : 0 < Shared50Parameters.tau', t)
t = re.sub(r'(?<![\w.])exponent_range\.', 'tau_range.', t)
if SUPPLIER_RANGE not in t:
    t = t.replace('theorem exponent_saving', SUPPLIER_RANGE + '\ntheorem exponent_saving', 1)
write(p, t)

# 4. The seam modules at the old paths.
def public_names(text):
    names = []
    for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(def|abbrev|theorem|lemma) ([\w\']+)', text, flags=re.M):
        names.append(m.group(2))
    return [n for n in dict.fromkeys(names) if n != 'uniform_bound']


def statement(text, name):
    m = re.search(r'^theorem ' + name + r' ?(.*?) := by', text, flags=re.M | re.S)
    return m.group(1)


M8 = 'IntegerMultBounds.MathlibTM2.M8.Machine'
SUPPLIER_FILE = Path(__file__).parent / 'supplier.txt'
supplier_arg = [a.split('=', 1)[1] for a in sys.argv if a.startswith('--supplier=')]
supplier_choice = supplier_arg[0] if supplier_arg else (
    SUPPLIER_FILE.read_text().strip() if SUPPLIER_FILE.exists() else 'pr97')
assert supplier_choice in ('m8', 'pr97'), supplier_choice

if supplier_choice == 'm8':
    net_doc = 'the M8 machine on Shared50 as a bit network (`M8.Machine.Shared50Network.net`)'
    net_term = M8 + '.Shared50Network.net'
    net_import = 'public import ' + M8 + '.Shared50Network\n'
    tau_proof = ('  change ' + M8 + '.Shared50Network.network.tau = Parameters.tau\n'
                 '  rw [' + M8 + '.Shared50Network.network_tau]\n'
                 '  norm_num [Shared50Parameters.tau, Parameters.tau]')
    tau_word = 'the network exponent `Shared50Parameters.tau`'
else:
    G = 'IntegerMultBounds.MathlibTM2.M8.Global'
    net_doc = 'the M8 machine on the PR97 node (`M8.Global.pr97`)'
    net_term = '⟨' + G + '.pr97, ' + G + '.runs_pr97.supports⟩'
    net_import = 'public import ' + G + '.Instance\n'
    tau_proof = ('  change ' + G + '.pr97.tau = Parameters.tau\n'
                 '  rw [' + G + '.pr97_tau]\n'
                 '  norm_num [' + G + '.Branching97.tau, ' + G + '.Branching97.saving, Parameters.tau]')
    tau_word = 'the PR97 exponent `Global.Branching97.tau`'
impl_mod = {'radix': M8 + '.BinaryRadixEqualShared', 'run': M8 + '.BinaryInterchangeRun',
            'budget': M8 + '.BinaryInterchangeBudget'}
impl_ns = {'radix': M8 + '.BinaryRadixEqualShared', 'run': M8 + '.BinaryInterchangeRun'}
tau_text = 'BudgetBound.tau'
if supplier_choice == 'm8':
    radix_doc = ('is the M8 machine on Shared50 as a bit network (`M8.Machine.Shared50Network.net`); its\n'
                 'exponent, the network exponent `Shared50Parameters.tau`, is the exponent `Parameters.tau` of\n'
                 'the cost chain (`supplier_tau`), at which `uniform_bound` is stated.')
    run_doc = ('The supplier is the M8 machine on Shared50 as a bit network\n'
               '(`M8.Machine.BinaryInterchangeRun`).')
else:
    radix_doc = ('is ' + net_doc + '; its exponent, ' + tau_word + ', is the exponent\n'
                 '`Parameters.tau` of the cost chain (`supplier_tau`), at which `uniform_bound` is stated.')
    run_doc = 'The supplier is ' + net_doc + '.'
extra_import = net_import
instance_decl = ('/-- The network of the supplier machine. -/\n'
                 'noncomputable instance supplierNet : ' + M8 + '.Net := ' + net_term + '\n\n')
tau_lhs = M8 + '.BudgetBound.tau'
texts = {k: (ROOT / (v.replace('.', '/') + '.lean')).read_text() for k, v in impl_mod.items()}

radix, run, budget = texts['radix'], texts['run'], texts['budget']

seam_radix = f"""module

{MARK}
public import {impl_mod['radix']}
{extra_import}
/-!
# The equal-width radix interchange of the cost chain

The cost chain uses the supplier's equal-width radix interchange under these names. The supplier
{radix_doc}
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryRadixEqualShared

{instance_decl}export {impl_ns['radix']} ({' '.join(public_names(radix))})

theorem supplier_tau : {tau_lhs} = Parameters.tau := by
{tau_proof}

theorem uniform_bound {statement(radix, 'uniform_bound').replace(tau_text, 'Parameters.tau')} := by
  rw [← supplier_tau]
  exact {impl_ns['radix']}.uniform_bound

end IntegerMultBounds.Machine.BinaryRadixEqualShared
"""

seam_run = f"""module

{MARK}
public import IntegerMultBounds.Machine.BinaryRadixEqualShared
public import {impl_mod['run']}

/-!
# The rectangular interchange of the cost chain

The cost chain uses the supplier's width-selecting rectangular interchange under these names.
{run_doc}
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryInterchangeRun

export {impl_ns['run']} ({' '.join(public_names(run))})

end IntegerMultBounds.Machine.BinaryInterchangeRun
"""

seam_budget = f"""module

{MARK}
public import IntegerMultBounds.Machine.BinaryInterchangeRun
public import IntegerMultBounds.Machine.BinaryRadixEqualShared
public import {impl_mod['budget']}

/-!
# The time bound of the rectangular interchange

The supplier's uniform time bound at the exponent `Parameters.tau` of the cost chain.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryInterchangeRun

theorem uniform_bound {statement(budget, 'uniform_bound').replace(tau_text, 'Parameters.tau')} := by
  rw [← BinaryRadixEqualShared.supplier_tau]
  exact {impl_ns['run']}.uniform_bound

end IntegerMultBounds.Machine.BinaryInterchangeRun
"""

write(MACHINE / 'BinaryRadixEqualShared.lean', seam_radix)
write(MACHINE / 'BinaryInterchangeRun.lean', seam_run)
write(MACHINE / 'BinaryInterchangeBudget.lean', seam_budget)

# 5. Report unclassified uses of `Parameters.tau`.
consumers_ok = ('IntegerMultBounds/MathlibTM2/', 'IntegerMultBounds/Parameters.lean')
supplier_paths = {module_path(m) for m in supplier}
unclassified = []
for f in PKG.rglob('*.lean'):
    if '/M8/' in str(f) or f in supplier_paths or str(f.relative_to(ROOT)).startswith(consumers_ok):
        continue
    if f.stem in MOVES:
        continue
    t = read(f)
    if re.search(r'(?<![\w])(?:IntegerMultBounds\.)?Parameters\.tau\b', t):
        unclassified.append(str(f.relative_to(ROOT)))

import difflib


def changed(o, n):
    return sum(1 for l in difflib.unified_diff(o.split('\n'), n.split('\n'), lineterm='', n=0)
               if l.startswith('-') and not l.startswith('---'))


moved_from = {MACHINE / (new + '.lean'): MACHINE / (old + '.lean') for old, new in MOVES.items()}
edited, edited_lines, moved, seams = 0, 0, 0, 0
for p, (old, new) in sorted(changes.items()):
    if p in moved_from:
        d = changed(moved_from[p].read_text() if not is_seam(moved_from[p]) else new, new)
        print(f'move {moved_from[p].relative_to(ROOT)} -> {p.name}  ({d} lines renamed)')
        edited_lines += d
        moved += 1
    elif p.stem in MOVES and p.parent == MACHINE:
        print(f'seam {p.relative_to(ROOT)}  ({len(new.splitlines())} lines)')
        seams += 1
    else:
        d = changed(old or '', new)
        edited += 1
        edited_lines += d
        print(f'edit {p.relative_to(ROOT)}  ({d} lines)')
print(f'{edited} files edited in place, {moved} moved, {seams} seam modules; {edited_lines} existing lines changed')
print('consumers of Parameters.tau outside MathlibTM2 (unchanged, supplier exponent):')
for u in sorted(unclassified):
    print('  ', u)
print('supplier:', supplier_choice)
if not DRY:
    for p, (old, new) in changes.items():
        p.write_text(new)
    SUPPLIER_FILE.write_text(supplier_choice + '\n')
    print('applied')
