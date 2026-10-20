#!/usr/bin/env python3
"""Emit the symbolic register snapshots used by the T16 local-word action certificate.

Reads the committed native event modules (Trace/Forward*.lean), derives the backward events
exactly as `Trace.backwardEvents` does, erases both to their rational scalar gates exactly as
`Trace.erase` does, runs them symbolically over sparse rational rows, and writes the rows that
differ from the identity after each piece of the 25 event chunks. Lean's kernel checks every
emitted snapshot; nothing here is trusted.
"""
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TRACE = ROOT / 'IntegerMultBounds/Networks/Certificates/T16/Trace'
NS = 'IntegerMultBounds.Networks.Certificates.T16.Trace'
GROUPS = 25
CHUNK = 1024
# Peak memory of one piece check in GB, fitted on single-piece checks (within 0.15 GB on all 25):
# per 10^4 terms of written rows, of source rows read and of the two snapshots, and per 10^3
# events. Pieces are cut where the prediction would pass TARGET.
BASE, ROW_GB, SOURCE_GB, EVENT_GB, SNAP_GB = -0.542, 0.518e-4, 1.027e-4, 0.271e-3, 0.378e-4
TARGET = 3.8
PER_MODULE = 5


def events(prefix):
    out = []
    for k in range(GROUPS):
        text = (TRACE / f'{prefix}{k}.lean').read_text()
        blocks = re.findall(r'def \w+Events(\d+) : List Event := \[(.*?)\]\ntheorem', text, re.S)
        for _, body in sorted(blocks, key=lambda b: int(b[0])):
            out += [line.strip().rstrip(',') for line in body.strip().split('\n')]
    return out


def parse(e):
    """A scalar event as `(op, args)`; any other event as `(None, e)`."""
    m = re.match(r'\.scalar \(\.(\w+) (.*)\)$', e)
    if not m:
        return (None, e)
    return (m.group(1), [int(x) for x in re.findall(r'-?\d+', m.group(2))])


def dual(e):
    """`Scalar.dual`: an add exchanges target and source and negates, a scale inverts."""
    op, a = e
    if op == 'add':
        return ('add', [a[1], a[0], -a[2], a[3], a[4]])
    if op == 'scale':
        return ('scale', [a[0], a[2], a[1], a[3]])
    return e


def transpose(e):
    """`Event.transpose`: a center transfer `t += c x` becomes `c += t x`."""
    op, a = e
    if op == 'add':
        return ('add', [a[1], a[0], a[2], a[3], a[4]])
    return dual(e)


CENTER_START = 12551
CENTER_LENGTH = 26


def center_dual(es):
    """`Trace.centerDual` on one center block."""
    if len(es) >= 3 and es[0][0] == 'clear' and es[1][0] == 'copy':
        (_, (c, f)), (_, (_, s, _)), center, rest = es[0], es[1], es[2], es[3:]
        return ([dual(rest[-1])] if rest else []) + [transpose(e) for e in rest[:-1]] + \
            [dual(center), ('add', [s, c, -1, 1, f]), ('clear', [c, f])]
    return [dual(e) for e in es]


def program(prefix):
    """The events of `forwardEvents` or `backwardEvents`."""
    fwd = [parse(e) for e in events('Forward')]
    if prefix == 'Forward':
        return fwd
    end = CENTER_START + 8 * CENTER_LENGTH
    blocks = [center_dual(fwd[CENTER_START + CENTER_LENGTH * k:CENTER_START + CENTER_LENGTH * (k + 1)])
              for k in range(8)]
    return [dual(e) for e in fwd[:CENTER_START]] + sum(blocks, []) + [dual(e) for e in fwd[end:]]


def gates(es):
    """The erased gates `(target, [(source, coefficient)])`, as `Scalar.gate`."""
    out = []
    for op, args in es:
        if op is None:
            continue
        if op == 'add':
            t, s, n, d, _ = args
            out.append((t, [(s, Fraction(n, d))]))
        elif op == 'scale':
            t, n, d, _ = args
            out.append((t, [(t, Fraction(n, d) - 1)]))
        elif op == 'clear':
            t, _ = args
            out.append((t, [(t, Fraction(-1))]))
        elif op == 'copy':
            t, s, _ = args
            out.append((t, [(t, Fraction(-1)), (s, Fraction(1))]))
        else:
            raise ValueError(op)
    return out


def snapshots(prefix):
    """Split the events into pieces whose checks are predicted to stay under TARGET GB. Returns
    the cut lengths inside each chunk, the number of cuts in each piece but the last, and the
    changed rows after each piece."""
    es = program(prefix)
    rows = {i: {i: Fraction(1)} for i in range(712)}
    changed = lambda: {r: dict(v) for r, v in rows.items() if v != {r: Fraction(1)}}
    size = 0  # terms of the changed rows
    starts, result = [], []
    start, work, snap_in = 0, 0.0, 0
    for i, e in enumerate(es):
        step = EVENT_GB
        new = None
        for t, terms in gates([e]):
            step += SOURCE_GB * sum(len(rows[s]) for s, _ in terms)
            new = dict(rows[t])
            for s, c in terms:
                for j, a in rows[s].items():
                    new[j] = new.get(j, 0) + c * a
            new = (t, {j: a for j, a in new.items() if a != 0})
            step += ROW_GB * len(new[1])
        if i > start and BASE + work + step + SNAP_GB * (snap_in + size) > TARGET:
            starts.append(i)
            result.append(changed())
            start, work, snap_in = i, 0.0, size
        if new:
            t, row = new
            old = 0 if rows[t] == {t: Fraction(1)} else len(rows[t])
            rows[t] = row
            size += (0 if row == {t: Fraction(1)} else len(row)) - old
        work += step
    result.append(changed())
    cuts, sizes, count = [], [], 0
    for k in range(GROUPS):
        inner = [i - CHUNK * k for i in starts if CHUNK * k < i < CHUNK * (k + 1)]
        cuts.append([b - a for a, b in zip([0] + inner, inner)])
        # Cuts of this chunk: one before the first inner start, one after each.
        for j in range(len(inner) + 1):
            first = CHUNK * k + ([0] + inner)[j]
            if first in starts:
                sizes.append(count)
                count = 0
            count += 1
    return cuts, sizes, result


PIECE_TERMS = 600
SCALE = 2 ** 17  # `Symbolic.scale`


def entry(i, row):
    flat = ', '.join(f'{j}, {int(c < 0)}, {int(abs(c) * SCALE)}' for j, c in sorted(row.items()))
    return f'  .row {i} [{flat}]'


HEADER = ('module\n\npublic import {imp}\n\n'
          '/-! Generated by scripts/generate_t16_action.py. {doc} -/\n'
          '@[expose] public section\nnamespace ' + NS + '\n\nopen Symbolic\n\n')


def main():
    text = HEADER.format(imp=NS + '.Symbolic', doc='Storage format for symbolic register rows.')
    # Natural literals: each integer literal in the rows costs the elaborator a typeclass search.
    text += ('/-- One stored row: its register and flat `(source, sign, magnitude)` triples of scaled\n'
             'coefficients, sign `1` for a negative coefficient. -/\n'
             'inductive StoredRow where\n  | row (register : ℕ) (terms : List ℕ)\n\n'
             '/-- Decode flat triples. -/\n'
             'def decodeTerms : List ℕ → Row\n'
             '  | j :: s :: n :: rest => (j, if s = 0 then (n : ℤ) else -(n : ℤ)) :: decodeTerms rest\n'
             '  | _ => []\n\n'
             'def StoredRow.decode : StoredRow → ℕ × Row\n'
             '  | .row i terms => (i, decodeTerms terms)\n\n'
             '/-- The identity trie with the listed rows replaced. -/\n'
             'def snapshotTrie (rows : List StoredRow) : Trie :=\n'
             '  (rows.map StoredRow.decode).foldl (fun T p => T.put p.1 p.2) (Trie.init 10 0 1)\n\n')
    text += 'end ' + NS + '\n'
    (TRACE / 'ActionFormat.lean').write_text(text)
    written = {'ActionFormat.lean'}

    def write(file, text):
        (TRACE / file).write_text(text)
        written.add(file)

    for prefix, name in [('Forward', 'forward'), ('Backward', 'backward')]:
        chunks = 'forwardChunks' if prefix == 'Forward' else 'backwardChunks'
        source = NS + ('.Forward' if prefix == 'Forward' else '.BackwardChunks')
        cuts, sizes, snaps = snapshots(prefix)
        write(f'Action{prefix}Pieces.lean',
              HEADER.format(imp=NS + '.Pieces\npublic import ' + source,
                            doc=f'The {name} chunks regrouped into pieces of bounded kernel memory.')
              .replace('open Symbolic\n\n', '')
              + f'def {name}Cuts : List (List ℕ) :=\n  [' + ', '.join(
                  '[' + ', '.join(map(str, c)) + ']' for c in cuts) + ']\n\n'
              + f'def {name}Sizes : List ℕ := [' + ', '.join(map(str, sizes)) + ']\n\n'
              + f'def {name}Pieces : List (List Event) := pieces {name}Cuts {name}Sizes {chunks}\n\n'
              + f'theorem {name}Pieces_length : {name}Pieces.length = {len(snaps)} := by\n  decide +kernel\n\n'
              + 'end ' + NS + '\n')
        # `names[k]` is the snapshot before piece `k`; a piece without gates reuses the last one.
        names, modules = ['[]'], [[]]
        for k, snap in enumerate(snaps, 1):
            if snap is None:
                names.append(names[-1])
                modules.append(modules[-1])
                continue
            body = HEADER.format(imp=NS + '.ActionFormat',
                                 doc=f'{prefix} symbolic rows after piece {k - 1}, as overrides of the\n'
                                 'identity trie.')
            pieces, cur, size = [], [], 0
            for i in sorted(snap):
                if cur and size + len(snap[i]) > PIECE_TERMS:
                    pieces.append(cur)
                    cur, size = [], 0
                cur.append(i)
                size += len(snap[i])
            if cur:
                pieces.append(cur)
            for p, ks in enumerate(pieces):
                body += (f'def {name}Snapshot{k}Piece{p} : List StoredRow := [\n'
                         + ',\n'.join(entry(i, snap[i]) for i in ks) + ']\n\n')
            body += (f'def {name}Snapshot{k} : List StoredRow :=\n  '
                     + ' ++ '.join(f'{name}Snapshot{k}Piece{p}' for p in range(len(pieces))) + '\n\n')
            body += 'end ' + NS + '\n'
            write(f'Action{prefix}Rows{k}.lean', body)
            names.append(f'{name}Snapshot{k}')
            modules.append([f'Action{prefix}Rows{k}'])
        # Reach checks: each module imports the rows it names and the previous module of its
        # orientation, so at most one check per orientation runs at a time (each about 4 GB).
        n = len(snaps)
        groups = [range(j, min(j + PER_MODULE, n)) for j in range(0, n, PER_MODULE)]
        for g, ks in enumerate(groups):
            imps = sorted({m for k in ks for m in modules[k] + modules[k + 1]},
                          key=lambda m: int(m.split('Rows')[1]))
            imps = ([f'Action{prefix}{g - 1}'] if g else []) + imps
            body = HEADER.format(imp='\npublic import '.join([NS + '.' + m for m in imps]
                                                             + [NS + f'.Action{prefix}Pieces']),
                                 doc=f'The kernel checks that {name} pieces {ks[0]} to {ks[-1]} reach their rows.')
            for k in ks:
                body += (f'theorem {name}_reach{k} :\n'
                         f'    symRun (snapshotTrie {names[k]}) (erase ({name}Pieces.getD {k} [])) =\n'
                         f'      some (snapshotTrie {names[k + 1]}) := by\n  decide +kernel\n\n')
            body += 'end ' + NS + '\n'
            write(f'Action{prefix}{g}.lean', body)
        body = HEADER.format(imp='\npublic import '.join(NS + f'.Action{prefix}{g}' for g in range(len(groups))),
                             doc=f'The {name} rows before each piece, and every piece check.')
        body += (f'def {name}Snapshots : List (List StoredRow) :=\n  [' + ', '.join(names) + ']\n\n'
                 f'theorem {name}_reach : ∀ k < {n},\n'
                 f'    symRun (snapshotTrie ({name}Snapshots.getD k [])) (erase ({name}Pieces.getD k [])) =\n'
                 f'      some (snapshotTrie ({name}Snapshots.getD (k + 1) [])) := by\n'
                 '  intro k hk\n  match k, hk with\n'
                 + ''.join(f'  | {k}, _ => exact {name}_reach{k}\n' for k in range(n))
                 + f'  | _ + {n}, h => exact absurd h (by omega)\n\n')
        body += 'end ' + NS + '\n'
        write(f'Action{prefix}.lean', body)
    for f in TRACE.glob('Action*.lean'):
        if f.name not in written and f.name != 'Action.lean':
            f.unlink()


if __name__ == '__main__':
    main()
