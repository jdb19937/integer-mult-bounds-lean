#!/usr/bin/env python3
"""Generate finite tape placements or rewind/clear adapters; Lean checks all claims."""
import argparse
import json
from pathlib import Path
from generate_lean_sequence import identifier, render as render_sequence


def slots_checked(slots, tapes):
    if type(tapes) is not int or tapes <= 0 or not isinstance(slots, list) or not slots:
        raise ValueError('positive tape count and nonempty slots required')
    if any(type(slot) is not int or not 0 <= slot < tapes for slot in slots):
        raise ValueError('slot outside bank')
    if len(set(slots)) != len(slots):
        raise ValueError('duplicate slots')


def render(manifest):
    if manifest.get('version') != 1:
        raise ValueError('unsupported version')
    namespace = manifest['namespace']
    for part in namespace.split('.'):
        identifier(part, 'namespace')
    if manifest['kind'] == 'cleanup':
        return cleanup(manifest)
    if manifest['kind'] != 'placement':
        raise ValueError('unknown adapter kind')
    lines = ['module', '', 'public import IntegerMultBounds.Schoenhage.CertifiedBinOf', '',
             '/-! Generated finite placements. Do not edit; regenerate from the manifest. -/',
             '@[expose] public section', f'namespace {namespace}',
             'open IntegerMultBounds.Machine IntegerMultBounds.Schoenhage',
             'open IntegerMultBounds.Schoenhage.CertifiedSequence',
             'open IntegerMultBounds.Schoenhage.LayoutGenSetup',
             'open IntegerMultBounds.Resampling.Script', 'noncomputable section', '']
    names = set()
    for case in manifest['cases']:
        name = identifier(case['name'], 'name')
        if name in names:
            raise ValueError('duplicate name')
        names.add(name)
        tapes, slots = case['tapes'], case['slots']
        slots_checked(slots, tapes)
        if len(slots) != 5:
            raise ValueError('the binOf kernel requires five slots')
        vector = ', '.join(map(str, slots))
        args = f'(value : ℕ) (bank : Fin {tapes} → WTape)'
        ready = f'(ready : bank ∘ {name}Slots = bbank value emp emp)'
        finish = f'Function.update bank {slots[1]} (reg (bin value))'
        lines += [f'def {name}Slots : Fin 5 → Fin {tapes} := ![{vector}]',
                  f'theorem {name}_injective : Function.Injective {name}Slots := by decide',
                  f'def {name}Program : Cmd 0 {tapes} := binOf.map {name}Slots {name}_injective', '',
                  f'def {name}Certificate {args} {ready} :=',
                  f'  ofRuns (placed_update {name}Slots {name}_injective bank ready 1',
                  '    (reg (bin value)) (runs_binOf_update value))', '',
                  f'def {name}Cost (value : ℕ) : ℕ := (ofRuns (runs_binOf_update value)).bound', '',
                  f'theorem {name}_runs {args} {ready} :',
                  f'    Runs {name}Program bank (· = {finish}) ({name}Cost value) :=',
                  f'  ({name}Certificate value bank ready).runs', '',
                  f'theorem {name}_hoare {args} {ready} :',
                  f'    HoareTime (compile (by decide) {name}Program).2',
                  f'      (· = enc bank) (· = enc ({finish})) ({name}Cost value) :=',
                  f'  ({name}Certificate value bank ready).hoare (by decide)', '']
    return '\n'.join(lines + ['end', f'end {namespace}', ''])


def cleanup(manifest):
    name = identifier(manifest['name'], 'name')
    tapes, rewind, scratch = manifest['tapes'], manifest['rewind'], manifest['clear']
    slots_checked([rewind] + scratch, tapes)
    if not scratch:
        raise ValueError('at least one clear slot required')
    current = 'bank'
    stages = [dict(command=f'rewind {rewind}', proof=f'runs_rewind (a := 0) {rewind} bank')]
    current = f'Function.update bank {rewind} ⟨[], (bank {rewind}).left.reverse ++ (bank {rewind}).right⟩'
    for slot in scratch:
        stages.append(dict(command=f'clear {slot}', proof=f'runs_clear (a := 0) {slot} ({current})'))
        current = f'Function.update ({current}) {slot} emp'
    spec = dict(version=1, namespace=manifest['namespace'], imports=[], cases=[])
    spec['imports'] = ['IntegerMultBounds.Schoenhage.TapeBank']
    spec['cases'] = [dict(name=name, alphabet=0, tapes=tapes, binders=f'(bank : Fin {tapes} → WTape)',
                          arguments='bank', input='bank', output=current, stages=stages)]
    source = render_sequence(spec)
    namespace = manifest['namespace']
    scratch_list = '[' + ', '.join(map(str, scratch)) + ']'
    cost = f'clen (bank {rewind}).left + 2' + ''.join(f' + (2 * clen (bank {slot}).words + 2)' for slot in scratch) + f' + {len(scratch)}'
    unfold = ', '.join([f'{name}Cost', f'{name}Certificate', 'Block.then', 'ofRuns'] +
                       [f'{name}Stage{index}' for index in range(len(stages))])
    source += f'''
namespace {namespace}
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.CertifiedSequence

theorem {name}_original_cost (bank : Fin {tapes} → WTape) :
    {name}Cost bank = {cost} := by
  simp [{unfold}]
  omega

theorem {name}_bank (bank : Fin {tapes} → WTape) :
    ({name}Certificate bank).output = fun tape =>
      if tape ∈ ({scratch_list} : List (Fin {tapes})) then emp
      else if tape = {rewind} then ⟨[], (bank {rewind}).left.reverse ++ (bank {rewind}).right⟩
      else bank tape := by
  rw [{name}_output]
  change ({scratch_list} : List (Fin {tapes})).foldl
    (fun current slot => Function.update current slot emp)
    (Function.update bank {rewind} ⟨[], (bank {rewind}).left.reverse ++ (bank {rewind}).right⟩) = _
  rw [TapeBank.clear_fold]
  unfold TapeBank.cleared
  funext tape
  simp only [Function.update_apply]

end {namespace}
'''
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    try:
        source = render(json.loads(args.manifest.read_text()))
        if args.check:
            if not args.output.exists() or args.output.read_text() != source:
                parser.error('generated output is stale')
        else:
            args.output.write_text(source)
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
