#!/usr/bin/env python3
"""Replay frame-chain alignment with the design-B compiler (untrusted).

The scalar semantics and chain geometry are proved separately in Lean. This
replay detects mismatches in numbering, readout order and frame assignment;
it does not replace the pending Lean proof connecting those two parts.
"""
import argparse
import json
from itertools import combinations
from pathlib import Path

import designbword
import stage2designb
from stage2defer import f2_targets


def check_alignment(result, compiled, targets):
    slot = dict(compiled['slotMap'])
    upstream = {v: k for k, v in slot.items()}
    node = dict(compiled['nodeMap'])
    node_frame = {node[n]: tuple(frame) for n, frame in result['nodeFrames']}
    expected = {
        (kind, slot[wire] if kind == 'slot' else node[wire] if kind == 'x' else wire):
            [tuple(frame) for frame in chain]
        for kind, wire, chain in result['fullChains']}
    traces = {key: [chain[0]] for key, chain in expected.items()}
    start = {slot[i]: tuple(chain[1]) for kind, i, chain in result['fullChains'] if kind == 'slot'}
    sigma = {slot[i]: tuple(frame) for i, frame in enumerate(result['sigma'])}
    sources = {op[1]: op for op in compiled['ops'] if op[0] == 'src'}
    deferred = set(compiled['deferred'])
    # Fallback-zero readouts must precede all retained nonzero readouts.
    readout_order = sorted(compiled['deferred'], key=lambda p: sigma[p] != (0, 0))

    def trace_op(op, last=False):
        if last:
            frame = (1, 0)
        elif op[0] in ['src', 'copy']:
            frame = start[op[1] if op[0] == 'src' else op[2]]
        else:
            frame = node_frame[op[3]]
        keys = ([('slot', op[1]), ('x', op[2])] if op[0] == 'src' else
                [('slot', op[1]), ('slot', op[2])])
        for key in keys:
            traces[key].append(frame)

    def readouts(slots):
        for p in slots:
            for t in sorted(targets[upstream[p]]):
                traces['slot', p].append(sigma[p])
                traces['y', t].append(sigma[p])

    readouts(p for p in range(len(slot)) if p not in deferred)
    early = [sources[p] for p in compiled['earlySources']]
    late = [sources[p] for p in compiled['lateSources']]
    for op in early + compiled['first']:
        trace_op(op)
    basis = {tuple(entry['basis']): i for i, entry in enumerate(result['records'])}
    triples = list(combinations(range(23), 3))
    leaf_count = len(triples)
    for c in range(23):
        p = compiled['rootSlots'][3 * leaf_count + c]
        traces['slot', p].append((3, basis[32768 + c,]))
        for t, triple in enumerate(triples):
            if c in triple:
                traces['y', t].append((0, 0))
    readouts(readout_order)
    for op in late + compiled['rest']:
        trace_op(op)
    for j in range(3 * leaf_count):
        t = j // 3
        p = compiled['rootSlots'][j]
        a, b, c = triples[t]
        frame = (3, basis[a + 32 * b + 1024 * c,])
        traces['slot', p].append(frame)
        traces['y', t].append(frame)
    for op in reversed(early + late + compiled['first'] + compiled['rest']):
        trace_op(op, True)

    def compress(frames):
        return [frame for i, frame in enumerate(frames) if i == 0 or frame != frames[i - 1]]

    failures = [key for key, chain in traces.items() if compress(chain) != compress(expected[key])]
    assert not failures, ('frame-chain alignment', failures[:10], len(failures))
    return {'wireChains': len(traces), 'readoutOrder': readout_order,
            'zeroReadouts': sum(sigma[p] == (0, 0) for p in deferred)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('dag_data', type=Path)
    parser.add_argument('signed_snapshot', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    witness = stage2designb.read(str(args.source), 'witness_23.json.gz')
    deferred = stage2designb.read(str(args.source), 'deferred_23.json.gz')
    schedule = stage2designb.Schedule(witness, deferred)
    compiled = designbword.main(str(args.source), str(args.dag_data))
    result = check_alignment(json.loads(args.signed_snapshot.read_text()), compiled, f2_targets(schedule))
    if args.output:
        args.output.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print('Aligned', result['wireChains'], 'wire chains;', result['zeroReadouts'],
          'zero-frame readouts moved to the start of the deferred block.')


if __name__ == '__main__':
    main()
