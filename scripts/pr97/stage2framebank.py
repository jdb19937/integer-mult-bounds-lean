#!/usr/bin/env python3
"""Emit the shared computed-root bank for the pinned design-B schedule.

Usage: stage2framebank.py PR97_DIR OUTPUT_JSON [--multi-nodes] [--lean-root REPO_ROOT]

The schedule and witness are SHA-256 checked by stage2designb.read. Bases are
untrusted: Lean's RootCheck.basisOk must validate every emitted record. A basis
is shared by all frames that select the same independent root vectors. Its
generators include every represented root and every adjacent computed basis
needed by a chain; the exact residual check therefore certifies these spans
once, independently of how often the frame occurs in the schedule.
"""
import argparse
import json
from pathlib import Path

import stage2defer as df


def code(key):
    if key[0] == 'ret':
        return 32768 + key[1]
    a, b, c = key[2]
    return a + 32 * b + 1024 * c


def reconstruct(source, multi_nodes):
    df.MULTI = True
    df.NODES_MULTI = multi_nodes
    W = df.dbm.read(str(source), 'witness_23.json.gz')
    D = df.dbm.read(str(source), 'deferred_23.json.gz')
    schedule = df.dbm.Schedule(W, D)
    graph = df.Side(W)
    frames = df.Frames(graph, schedule)
    return graph, schedule, frames


def collect(graph, schedule, frames):
    # Root labels attached to identical output triples denote the same vector.
    # Deduplicate those vectors before selecting a basis, deterministically.
    records, occurrences = {}, {}
    cache = {}

    def register(frame):
        if frame[0] != 'roots':
            return None
        roots = frozenset(frame[1])
        if roots not in cache:
            vectors = {}
            for key in sorted(roots):
                vectors.setdefault(code(key), key)
            keys = [vectors[k] for k in sorted(vectors)]
            _, basis = df.rank_basis(keys)
            chosen = tuple(code(k) for k in basis)
            cache[roots] = chosen
            entry = records.setdefault(chosen, set())
            entry.update(vectors)
        return cache[roots]

    def occurrence(kind, key, frame):
        basis = register(frame)
        if basis is not None:
            occurrences[kind, key] = basis

    for n, frame in sorted(frames.node.items()):
        occurrence('node', n, frame)
    for s, frame in sorted(frames.sigma.items()):
        occurrence('sigma', s, frame)
    for s, frame in sorted(frames.vstart.items()):
        occurrence('vstart', s, frame)
    for key, frame in sorted(frames.late.items()):
        occurrence('late', key, frame)

    chains = []
    for s in range(schedule.R):
        chains.append(('slot', s, [frames.frame(k) for k in frames.chain_keys(s)]))
    readers = [[] for _ in range(schedule.v)]
    for s in schedule.readout:
        if s in frames.sigma:
            for t in sorted(frames.targets[s]):
                readers[t].append(s)
    for t in range(schedule.v):
        chains.append(('y', t, [('zero',)] + [frames.sigma[s] for s in readers[t]] +
                       [('out', schedule.trip[t])]))
    for n, uses in schedule.xs:
        chains.append(('x', n, [('line', graph.trip[n - 1])] +
                       [frames.vstart[s] for s in uses] + [('one',)]))

    edges = set()
    runs = []
    for kind, wire, chain in chains:
        run = []
        for frame in chain:
            basis = register(frame)
            if basis is None:
                if run:
                    runs.append((kind, wire, run))
                    run = []
            else:
                if run:
                    a = run[-1]
                    records[a].update(basis)
                    edges.add((a, basis))
                run.append(basis)
        if run:
            runs.append((kind, wire, run))

    bases = sorted(records)
    indices = {basis: i for i, basis in enumerate(bases)}
    return {
        'records': [{'basis': list(basis), 'generators': sorted(records[basis])} for basis in bases],
        'occurrences': [[kind, key, indices[basis]] for (kind, key), basis in sorted(occurrences.items())],
        'computedRuns': [[kind, wire, [indices[basis] for basis in run]] for kind, wire, run in runs],
        'edges': sorted([indices[a], indices[b]] for a, b in edges),
    }


def compact_bank(result):
    """Share equivalent modular spans; exact Lean checks remain authoritative."""
    canonical, records, remap = {}, [], []
    for record in result['records']:
        echelon = df.Echelon()
        for k in record['basis']:
            vector = ([8 if q == k - 32768 else 1 for q in range(df.H)] if k >= 32768 else
                      [int(q in (k % 32, (k // 32) % 32, k // 1024)) for q in range(df.H)])
            assert echelon.insert(vector)
        key = tuple(tuple(row) for _, row in sorted(zip(echelon.piv, echelon.rows)))
        if key not in canonical:
            canonical[key] = len(records)
            records.append({'basis': record['basis'], 'generators': set()})
        index = canonical[key]
        records[index]['generators'].update(record['generators'])
        remap.append(index)
    edges = sorted({(remap[a], remap[b]) for a, b in result['edges']})
    for a, b in edges:
        records[a]['generators'].update(records[b]['basis'])
    result['records'] = [{'basis': r['basis'], 'generators': sorted(r['generators'])} for r in records]
    result['edges'] = [list(edge) for edge in edges]
    for row in result['occurrences']:
        row[2] = remap[row[2]]
    for row in result['computedRuns']:
        row[2] = [remap[i] for i in row[2]]
    return result


def vector(k):
    if k >= 32768:
        return [8 if q == k - 32768 else 1 for q in range(df.H)]
    return [int(q in (k % 32, (k // 32) % 32, k // 1024)) for q in range(df.H)]


def inverse_witness(basis):
    """Untrusted Bareiss inverse, normalized to keep kernel integers small."""
    from functools import reduce
    from math import gcd
    vectors = [vector(k) for k in basis]
    gram = [[9 * sum(a * b for a, b in zip(x, y)) - sum(x) * sum(y)
             for y in vectors] for x in vectors]
    n = len(basis)
    rows = [row + [int(i == j) for j in range(n)] for i, row in enumerate(gram)]
    previous = 1
    for k in range(n):
        pivot = next(i for i in range(k, n) if rows[i][k])
        rows[k], rows[pivot] = rows[pivot], rows[k]
        pr = rows[k]
        value = pr[k]
        rows = [row if i == k else [(value * x - row[k] * y) // previous
                for x, y in zip(row, pr)] for i, row in enumerate(rows)]
        previous = value
    inverse = [row[n:] for row in rows]
    common = reduce(gcd, [previous] + [x for row in inverse for x in row], 0)
    if previous < 0:
        common = -common
    scale = previous // common
    inverse = [[x // common for x in row] for row in inverse]
    assert scale and all(sum(gram[i][k] * inverse[k][j] for k in range(n)) ==
                         (scale if i == j else 0) for i in range(n) for j in range(n))
    return scale, inverse


def emit_sample(result, index, path, batch_size=16):
    """Emit a profiling check; the complete generator uses the same split."""
    record = result['records'][index]
    scale, inverse = inverse_witness(record['basis'])
    chunks = [record['generators'][i:i + batch_size]
              for i in range(0, len(record['generators']), batch_size)]
    text = ['module', 'import IntegerMultBounds.MathlibTM2.M8.Frames.RootBankCheck',
            'open IntegerMultBounds.MathlibTM2.M8.Frames.RootBank']
    for i, chunk in enumerate(chunks):
        text.append(f'def chunk{i} : List Nat := {chunk}')
    names = '[' + ', '.join(f'chunk{i}' for i in range(len(chunks))) + ']'
    text.append(f'def sample : Record := ⟨{record["basis"]}, {names}.flatten, {scale}, {inverse}⟩')
    text.append('theorem matrix_checked : sample.matrixCheck = true := by decide +kernel')
    for i in range(len(chunks)):
        text.append(f'theorem chunk{i}_checked : sample.generatorCheck chunk{i} = true := by decide +kernel')
    facts = ', '.join(f'chunk{i}_checked' for i in range(len(chunks)))
    text.append('theorem sample_checked : sample.check = true :=')
    text.append(f'  Record.check_of_chunks sample {names} rfl matrix_checked (by')
    text.append(f'    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, {facts}, Bool.true_and])')
    Path(path).write_text('\n\n'.join(text) + '\n')
    return scale, len(chunks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--multi-nodes', action='store_true')
    parser.add_argument('--lean-root', type=Path, help='also emit the Lean data and kernel checks')
    parser.add_argument('--signed-output', type=Path, help='also reconstruct the complete signed wire chains')
    args = parser.parse_args()
    graph, schedule, frames = reconstruct(args.source, args.multi_nodes)
    result = compact_bank(collect(graph, schedule, frames))
    result['source'] = {'upstream': df.dbm.UPSTREAM, 'sha256': df.dbm.PINS,
                        'multiNodes': args.multi_nodes}
    args.output.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print('records', len(result['records']), 'occurrences', len(result['occurrences']),
          'computed runs', len(result['computedRuns']), 'edges', len(result['edges']),
          'bytes', args.output.stat().st_size, flush=True)
    if args.signed_output is not None:
        signed = collect_signed(graph, schedule, frames, result)
        args.signed_output.write_text(json.dumps(signed, separators=(',', ':')) + '\n')
        print('complete signed chains', len(signed['fullChains']), 'additional spans',
              len(signed['records']) - signed['parentCount'], flush=True)
    if args.lean_root is not None:
        emit_bank(result, args.lean_root)
        emit_runs(result, args.lean_root)


def emit_bank(result, destination, per_module=64, batch_size=16):
    """Emit narrow data/check modules and one balanced lookup bank."""
    import hashlib
    assert result['source']['upstream'] == df.dbm.UPSTREAM
    assert result['source']['sha256'] == df.dbm.PINS
    prefix = 'IntegerMultBounds.MathlibTM2.M8.Frames.Computed'
    directory = Path(destination) / 'IntegerMultBounds/MathlibTM2/M8/Frames/Computed'
    (directory / 'Data').mkdir(parents=True, exist_ok=True)
    (directory / 'Checks').mkdir(parents=True, exist_ok=True)
    snapshot = hashlib.sha256(json.dumps(result, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    note = (f'/-! Generated by scripts/pr97/stage2framebank.py from upstream {df.dbm.UPSTREAM}.\n'
            f'Witness SHA-256 {df.dbm.PINS["witness_23.json.gz"]};\n'
            f'schedule SHA-256 {df.dbm.PINS["deferred_23.json.gz"]}.\n'
            f'Canonical frame-bank SHA-256 {snapshot}.\n'
            'All frame data and inverse witnesses are untrusted until their kernel checks pass. -/\n')
    namespace = 'IntegerMultBounds.MathlibTM2.M8.Frames.Computed'
    opening = f'\n{note}\n@[expose] public section\nnamespace {namespace}\nopen RootBank Local\n'
    closing = f'\nend {namespace}\n'

    def tree(values):
        if len(values) == 1:
            return values[0]
        mid = len(values) // 2
        return f'.node ({tree(values[:mid])}) ({tree(values[mid:])})'

    count = len(result['records'])
    width = 1 << max(0, (count - 1).bit_length())
    # A fixed module width keeps import paths stable as records are added.
    assert per_module > 0 and per_module & (per_module - 1) == 0
    width = max(per_module, width)
    data_modules, check_modules, chunk_names, chunk_facts = [], [], [], []
    for start in range(0, width, per_module):
        number = start // per_module
        module = f'Bank{number:03d}'
        data_modules.append(f'{prefix}.Data.{module}')
        check_modules.append(f'{prefix}.Checks.{module}')
        data = ['module', 'public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBankCheck', opening]
        checks = ['module', f'public import {prefix}.Data.{module}', opening]
        leaves, facts = [], []
        for index in range(start, min(start + per_module, count)):
            record = result['records'][index]
            scale, inverse = inverse_witness(record['basis'])
            name = f'entry{index:05d}'
            chunks = [record['generators'][i:i + batch_size]
                      for i in range(0, len(record['generators']), batch_size)]
            names = []
            for j, values in enumerate(chunks):
                part = f'{name}g{j:03d}'
                names.append(part)
                data.append(f'def {part} : List Nat := {values}')
            parts = '[' + ', '.join(names) + ']'
            data.append(f'def {name} : RootBank.Record :=\n'
                        f'  ⟨{record["basis"]}, {parts}.flatten, {scale}, {inverse}⟩')
            checks.append(f'theorem {name}_matrix : {name}.matrixCheck = true := by decide +kernel')
            gen_facts = []
            for part in names:
                fact = f'{part}_checked'
                gen_facts.append(fact)
                checks.append(f'theorem {fact} : {name}.generatorCheck {part} = true := by decide +kernel')
            checks.append(f'theorem {name}_checked : {name}.check = true :=\n'
                          f'  RootBank.Record.check_of_chunks {name} {parts} rfl {name}_matrix (by\n'
                          '    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, '
                          + ', '.join(gen_facts) + ', Bool.true_and])')
            leaves.append(f'.leaf {name}')
            facts.append(f'{name}_checked')
        if len(leaves) < per_module:
            data.append(f'def padding{number:03d} : RootBank.Record := ⟨[], [], 1, []⟩')
            checks.append(f'theorem padding{number:03d}_checked : padding{number:03d}.check = true := by decide +kernel')
            facts.append(f'padding{number:03d}_checked')
            leaves += [f'.leaf padding{number:03d}'] * (per_module - len(leaves))
        chunk = f'bank{number:03d}'
        chunk_fact = f'{chunk}_checked'
        chunk_names.append(chunk)
        chunk_facts.append(chunk_fact)
        data.append(f'def {chunk} : Tree RootBank.Record := {tree(leaves)}')
        checks.append(f'theorem {chunk_fact} : RootBank.bankCheck {chunk} = true := by\n'
                      f'  simp only [{chunk}, RootBank.bankCheck, ' + ', '.join(facts) + ', Bool.true_and]')
        (directory / 'Data' / f'{module}.lean').write_text('\n\n'.join(data) + closing)
        (directory / 'Checks' / f'{module}.lean').write_text('\n\n'.join(checks) + closing)
        if number % 32 == 0:
            print('emitted records', min(start + per_module, count), 'of', count, flush=True)
    data = ['module'] + [f'public import {m}' for m in data_modules] + [opening]
    data.append(f'def bank : Tree RootBank.Record := {tree(chunk_names)}')
    data.append(f'def bankWidth : Nat := {width}')
    data.append(f'def bankSize : Nat := {count}')
    data.append('noncomputable def bankEntry (i : Nat) : RootBank.Record := bank.get bankWidth i')
    (directory / 'Data.lean').write_text('\n\n'.join(data) + closing)
    checks = ['module', f'public import {prefix}.Data'] + [f'public import {m}' for m in check_modules] + [opening]
    checks.append('theorem bank_checked : RootBank.bankCheck bank = true := by\n'
                  '  simp only [bank, RootBank.bankCheck, ' + ', '.join(chunk_facts) + ', Bool.true_and]')
    checks.append('theorem bankEntry_checked (i : Nat) : (bankEntry i).check = true :=\n'
                  '  RootBank.bankCheck_get bank bankWidth i bank_checked')
    (directory / 'Checks.lean').write_text('\n\n'.join(checks) + closing)
    properties = ['module', f'public import {prefix}.Data', opening]
    properties.append('theorem bank_perfect : bank.Perfect bankWidth :=\n'
                      '  Tree.perfect_of_perfectB bank bankWidth (by decide +kernel)')
    properties.append('theorem bank_nonempty :\n'
                      '    Tree.all (fun _ (entry : RootBank.Record) => Nat.blt 0 entry.basis.length)\n'
                      '      (fun _ => true) bankSize bank 0 bankWidth = true := by decide +kernel')
    properties.append('theorem basis_length_pos (i : Nat) (hi : i < bankSize) :\n'
                      '    0 < (bankEntry i).basis.length := by\n'
                      '  have hiw : i < bankWidth := hi.trans_le (by decide +kernel)\n'
                      '  have h := Tree.all_get (fun _ (entry : RootBank.Record) => Nat.blt 0 entry.basis.length)\n'
                      '    (fun _ => true) bankSize bank bankWidth 0 bank_perfect bank_nonempty i hiw\n'
                      '    (by simpa only [Nat.zero_add] using hi)\n'
                      '  exact Nat.blt_eq.mp h')
    (directory / 'Properties.lean').write_text('\n\n'.join(properties) + closing)
    print('emitted', count, 'certified-record obligations in', len(data_modules), 'modules;',
          'bank digest', snapshot, flush=True)


def emit_runs(result, destination, per_module=128):
    """Certify every distinct consecutive computed section of a wire chain."""
    import hashlib
    prefix = 'IntegerMultBounds.MathlibTM2.M8.Frames.Computed'
    directory = Path(destination) / 'IntegerMultBounds/MathlibTM2/M8/Frames/Computed'
    (directory / 'Runs').mkdir(parents=True, exist_ok=True)
    snapshot = hashlib.sha256(json.dumps(result, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    namespace = 'IntegerMultBounds.MathlibTM2.M8.Frames.Computed'
    note = (f'/-! Generated by scripts/pr97/stage2framebank.py; pinned upstream {df.dbm.UPSTREAM}.\n'
            f'Frame-bank SHA-256 {snapshot}. These are computed sections of the\n'
            'wire chains; the intervening plain and one-centre frames are separate obligations. -/\n')
    opening = f'\n{note}\n@[expose] public section\nnamespace {namespace}\n'
    closing = f'\nend {namespace}\n'
    runs = sorted({tuple(row[2]) for row in result['computedRuns']})
    data_modules, check_modules, parts, facts = [], [], [], []
    for start in range(0, len(runs), per_module):
        module = f'Runs{start // per_module:03d}'
        data_modules.append(f'{prefix}.Runs.{module}')
        check_modules.append(f'{prefix}.Checks.{module}')
        data = ['module', 'public import Mathlib.Init', opening]
        checks = ['module', f'public import {prefix}.Runs.{module}', f'public import {prefix}.Data', opening]
        names, checked = [], []
        for i in range(start, min(start + per_module, len(runs))):
            name = f'run{i:05d}'
            names.append(name)
            checked.append(f'{name}_checked')
            data.append(f'def {name} : List Nat := {list(runs[i])}')
            checks.append(f'theorem {name}_checked : RootBank.chainCheck bankEntry bankSize {name} = true := by decide +kernel')
        part = f'runs{start // per_module:03d}'
        parts.append(part)
        facts.append(f'{part}_checked')
        data.append(f'def {part} : List (List Nat) := [' + ', '.join(names) + ']')
        checks.append(f'theorem {part}_checked : RootBank.chainsCheck bankEntry bankSize {part} = true := by\n'
                      f'  simp only [RootBank.chainsCheck, {part}, List.all_cons, List.all_nil, '
                      + ', '.join(checked) + ', Bool.true_and]')
        (directory / 'Runs' / f'{module}.lean').write_text('\n\n'.join(data) + closing)
        (directory / 'Checks' / f'{module}.lean').write_text('\n\n'.join(checks) + closing)
    data = ['module'] + [f'public import {m}' for m in data_modules] + [opening]
    all_parts = '[' + ', '.join(parts) + ']'
    data.append(f'def runs : List (List Nat) := {all_parts}.flatten')
    (directory / 'Runs.lean').write_text('\n\n'.join(data) + closing)
    checks = ['module', f'public import {prefix}.Runs'] + [f'public import {m}' for m in check_modules] + [opening]
    checks.append('theorem runs_checked : RootBank.chainsCheck bankEntry bankSize runs = true := by\n'
                  '  rw [runs, RootBank.chainsCheck_flatten]\n'
                  '  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, '
                  + ', '.join(facts) + ', Bool.true_and]')
    (directory / 'RunChecks.lean').write_text('\n\n'.join(checks) + closing)
    semantic = ['module', f'public import {prefix}.Checks', f'public import {prefix}.RunChecks',
                'public import IntegerMultBounds.MathlibTM2.M8.Frames.RootMoves',
                f'public import {prefix}.Properties', opening]
    semantic.append('theorem entry_idem (i : Nat) : (bankEntry i).frame * (bankEntry i).frame = (bankEntry i).frame :=\n'
                    '  RootBank.Record.idem (bankEntry i) (bankEntry_checked i)')
    semantic.append('theorem entry_rank (i : Nat) : (bankEntry i).frame.rank = 23 - (bankEntry i).basis.length :=\n'
                    '  RootBank.Record.rank (bankEntry i) (bankEntry_checked i)')
    semantic.append('theorem entry_rank_lt (i : Nat) (hi : i < bankSize) : (bankEntry i).frame.rank < 23 := by\n'
                    '  rw [entry_rank]\n'
                    '  have h := basis_length_pos i hi\n'
                    '  omega')
    semantic.append('theorem entry_bounded (i : Nat) : Height.Bounded (bankEntry i).frame (2 * 10 ^ 200) :=\n'
                    '  RootBank.Record.bounded (bankEntry i) (bankEntry_checked i)')
    semantic.append('theorem run_pairwise (ids : List Nat) (h : ids ∈ runs) :\n'
                    '    (ids.map fun i => (bankEntry i).frame).Pairwise Nested :=\n'
                    '  RootBank.chainsCheck_pairwise bankEntry bankSize (fun i _ => bankEntry_checked i) runs runs_checked ids h')
    semantic.append('theorem run_moment {M : Type} [AddCommMonoid M] (φ : Nat → M)\n'
                    '    (ids : List Nat) (h : ids ∈ runs) :\n'
                    '    Global.chainMoment φ (ids.map fun i => (bankEntry i).frame) =\n'
                    '      ((RootBank.rankSteps bankEntry ids).map φ).sum :=\n'
                    '  RootBank.chainMoment_rankSteps φ bankEntry bankSize (fun i _ => bankEntry_checked i) ids\n'
                    '    (List.all_eq_true.mp runs_checked ids h)')
    (directory / 'Facts.lean').write_text('\n\n'.join(semantic) + closing)
    print('emitted', len(runs), 'distinct computed chain sections', flush=True)


def collect_signed(graph, schedule, frames, seed):
    """Complete wire descriptions, sharing the already certified root bank.

Only new spans become new records. Signed relations are checked independently
of the geometric construction: spans require exact generator residuals and
positive-to-negative steps require exact G-orthogonality. Thus no claim about
the untrusted modular basis selection is needed by the circuit's soundness.
"""
    from collections import Counter
    records = [dict(basis=list(r['basis']), generators=list(r['generators'])) for r in seed['records']]
    spaces, by_basis = {}, {}

    def space_of(basis):
        basis = tuple(basis)
        if basis not in by_basis:
            e = df.Echelon()
            for k in basis:
                assert e.insert(vector(k))
            by_basis[basis] = (tuple(tuple(row) for _, row in sorted(zip(e.piv, e.rows))), e)
        return by_basis[basis]

    for i, entry in enumerate(records):
        key, _ = space_of(entry['basis'])
        assert key not in spaces
        spaces[key] = i

    def freeze(key):
        return tuple(freeze(x) for x in key) if isinstance(key, list) else key

    containers = {'node': frames.node, 'sigma': frames.sigma,
                  'vstart': frames.vstart, 'late': frames.late}
    described = {}
    for kind, key, i in seed['occurrences']:
        frame = containers[kind][freeze(key)]
        assert frame[0] == 'roots'
        described[frame] = (3, i)

    def register(codes, rank=None):
        e, basis = df.Echelon(), []
        for k in codes:
            if e.insert(vector(k)):
                basis.append(k)
            if rank is not None and len(basis) == rank:
                break
        if rank is not None:
            assert len(basis) == rank
        key = tuple(tuple(row) for _, row in sorted(zip(e.piv, e.rows)))
        if key not in spaces:
            spaces[key] = len(records)
            records.append({'basis': basis, 'generators': list(basis)})
            by_basis[tuple(basis)] = (key, e)
        return spaces[key]

    def describe(frame):
        if frame in described:
            return described[frame]
        kind = frame[0]
        if kind == 'zero':
            value = (0, 0)
        elif kind == 'one':
            value = (1, 0)
        elif kind == 'plain':
            value = (2, register([code(('out', 0, graph.trip[i])) for i in graph.bas[frame[1]]]))
        elif kind == 'line':
            value = (2, register([code(('out', 0, frame[1]))]))
        elif kind == 'lift':
            rank = df.H - frames.dim(frame)
            value = ((1, 0) if rank == 0 else (0, 0) if rank == df.H else
                     (3, register(sorted({code(k) for k in df.roots_of(frame)}), rank)))
        elif kind == 'out':
            value = (3, register([code(('out', 0, frame[1]))]))
        elif kind == 'ret':
            value = (3, register([32768 + frame[1]]))
        else:
            raise ValueError(('unregistered frame', kind))
        described[frame] = value
        return value

    def dimension(frame):
        tag, i = frame
        return 0 if tag == 0 else df.H if tag == 1 else (
            len(records[i]['basis']) if tag == 2 else df.H - len(records[i]['basis']))

    def contained(a, b):
        _, e = space_of(records[a]['basis'])
        return all(e.contains(vector(k)) for k in records[b]['basis'])

    def nested(a, b):
        if a[0] == 0 or b[0] == 1:
            return True
        if a[0] == b[0] == 2:
            return contained(b[1], a[1])
        if a[0] == b[0] == 3:
            return contained(a[1], b[1])
        if a[0] == 2 and b[0] == 3:
            return all(9 * sum(x * y for x, y in zip(vector(u), vector(v))) ==
                       sum(vector(u)) * sum(vector(v))
                       for u in records[a[1]]['basis'] for v in records[b[1]]['basis'])
        return False

    aux, data = Counter(), Counter()
    chains, sigma = [], []

    def add_chain(kind, wire, raw, counter):
        chain = [describe(frame) for frame in raw]
        dims = [dimension(frame) for frame in chain]
        assert all(nested(a, b) for a, b in zip(chain, chain[1:])), (kind, wire)
        assert all(a <= b for a, b in zip(dims, dims[1:])), (kind, wire, dims)
        counter.update(b - a for a, b in zip(dims, dims[1:]) if a != b)
        chains.append([kind, wire, chain])

    for s in range(schedule.R):
        add_chain('slot', s, [frames.frame(k) for k in frames.chain_keys(s)], aux)
        sigma.append(describe(frames.frame(('sigma', s))))
    readers = [[] for _ in range(schedule.v)]
    for s in schedule.readout:
        if s in frames.sigma:
            for t in sorted(frames.targets[s]):
                readers[t].append(s)
    for t in range(schedule.v):
        add_chain('y', t, [('zero',)] + [frames.sigma[s] for s in readers[t]] +
                  [('out', schedule.trip[t])], data)
    for n, uses in schedule.xs:
        add_chain('x', n, [('line', graph.trip[n - 1])] +
                  [frames.vstart[s] for s in uses] + [('one',)], data)
    histogram = Counter()
    for rank, multiplicity in (aux + data).items():
        histogram[rank] += 2 * schedule.v * multiplicity
    histogram[df.H - 1] += 2 * schedule.v * df.H
    for frame in sigma:
        histogram[df.M - df.H + dimension(frame)] += 2 * schedule.v
    pairs = schedule.v * schedule.v
    histogram[(df.H - 1) ** 2] += 2 * pairs
    histogram[1] += pairs
    assert sum(rank * count for rank, count in histogram.items()) == df.dbm.S0
    assert max(histogram) < df.M
    # Every source rank remains the certified basis length, regardless of
    # which representative of a modular span the constructor selected.
    for frame, value in described.items():
        assert dimension(value) == frames.dim(frame), (frame, value)
    return {
        'source': dict(seed['source'], parentBankCount=len(seed['records'])),
        'records': records,
        'parentCount': len(seed['records']),
        'fullChains': chains,
        'sigma': sigma,
        'nodeFrames': [[n, describe(frame)] for n, frame in sorted(frames.node.items())],
        'nodeOrder': sorted(graph.act, key=lambda n: (graph.dn[n], n)),
        'vstartFrames': [[s, describe(frame)] for s, frame in sorted(frames.vstart.items())],
        'lateFrames': [[n, list(uses), described[frame]]
                       for (n, uses), frame in sorted(frames.late.items()) if frame in described],
        'readoutOrder': list(schedule.readout),
        'starts': schedule.start,
        'auxHistogram': sorted([r, c] for r, c in aux.items()),
        'dataHistogram': sorted([r, c] for r, c in data.items()),
        'histogram': sorted([r, c] for r, c in histogram.items()),
    }


if __name__ == '__main__':
    main()
