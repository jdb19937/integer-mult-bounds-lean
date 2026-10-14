#!/usr/bin/env python3
"""Guarded positive checks, axiom audit, and corrupted-adapter rejection tests."""
import json
from pathlib import Path
import sys
import tempfile

from verify_pilot import ROOT, check

sys.path.insert(0, str(ROOT / 'scripts'))
from generate_lean_adapter import render


def main():
    folder = ROOT / 'IntegerMultBounds/Schoenhage'
    sources = {}
    for manifest, module in [('layout_placements', 'LayoutPlacementGenerated'), ('twist_cleanup', 'TwistCleanupGenerated')]:
        source = render(json.loads((ROOT / f'scripts/proofgen/{manifest}.json').read_text()))
        if source != (folder / f'{module}.lean').read_text():
            raise RuntimeError(f'{module} is stale')
        sources[module] = source
    for module in ['TapeBank', 'CertifiedPlacement', 'CertifiedBinOf', 'LayoutPlacementGenerated', 'TwistCleanupGenerated']:
        check(folder / f'{module}.lean', output=ROOT / f'.lake/build/lib/lean/IntegerMultBounds/Schoenhage/{module}.olean')
    check(folder / 'LayoutAdapterPilot.lean')
    placements, cleanup = sources['LayoutPlacementGenerated'], sources['TwistCleanupGenerated']
    corruptions = {
        'AliasedSlots': placements.replace('![34, 44, 45, 46, 10]', '![34, 44, 44, 46, 10]', 1),
        'WrongOutputTape': placements.replace('Function.update bank 44', 'Function.update bank 43'),
        'UnclearedTape': cleanup.replace('[11, 12, 13, 14]', '[11, 12, 13, 14, 15]'),
        'UnpaidCleanup': cleanup.replace('clen (bank 17).left + 2', 'clen (bank 17).left + 1'),
    }
    with tempfile.TemporaryDirectory(prefix='adapter-check-', dir=ROOT / 'scripts/proofgen') as temporary:
        for name, source in corruptions.items():
            assert source not in sources.values(), f'{name}: mutation did not apply'
            path = Path(temporary) / f'{name}.lean'
            path.write_text(source)
            check(path, reject=True)
    print('Adapter checks, transitive axiom audit, and four corruption tests passed.')


if __name__ == '__main__':
    main()
