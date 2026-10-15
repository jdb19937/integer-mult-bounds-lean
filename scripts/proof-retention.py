#!/usr/bin/env python3
"""Inventory modules removable from the completed proof's import graph.

This is an import-dependency audit, not a declaration-use analysis or a deletion
command. The public Mathlib entry point and focused checks are protected too.
"""
import argparse
import collections
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
THEOREM = 'IntegerMultBounds.MathlibTM2.Theorem'
PUBLIC_ROOTS = ('IntegerMultBounds.MathlibTM2', 'FastPathCheck',
                'MathlibTM2Check', 'CompletedProofCheck')


def imports(source):
    """Read import commands, ignoring nested comments and string contents."""
    clean = []
    i, depth, quoted = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
                clean.append(' ')
            else:
                clean.append('\n' if char == '\n' else ' ')
                i += 1
        elif quoted:
            if char == '\\':
                i += 2
            else:
                quoted = char != '"'
                clean.append('\n' if char == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            clean.append(' ')
            i += 2
        elif pair == '--':
            end = source.find('\n', i)
            i = len(source) if end == -1 else end
        elif char == '"':
            quoted = True
            clean.append(' ')
            i += 1
        else:
            clean.append(char)
            i += 1
    result = set()
    for line in ''.join(clean).splitlines():
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)$', line)
        if match:
            result.update(name for name in match.group(1).split()
                          if name == 'IntegerMultBounds' or name.startswith('IntegerMultBounds.'))
    return result


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        if module not in graph:
            raise ValueError(f'Missing local module: {module}')
        seen.add(module)
        pending.extend(graph[module])
    return seen


def module_path(module):
    return module.replace('.', '/') + '.lean'


def inventory(root=ROOT):
    paths = sorted((root / 'IntegerMultBounds').rglob('*.lean')) + sorted(root.glob('*.lean'))
    files = {str(path.relative_to(root))[:-5].replace('/', '.'): path for path in paths}
    sources = {module: path.read_text() for module, path in files.items()}
    graph = {module: imports(source) for module, source in sources.items()}
    proof = closure(graph, [THEOREM])
    public = closure(graph, PUBLIC_ROOTS)
    package = {module for module in graph if module.startswith('IntegerMultBounds.')}
    candidates = package - public
    # No retained module may have an import into the proposed removal set.
    incoming = {(m, dep) for m in public for dep in graph[m] if dep in candidates}
    if incoming:
        raise ValueError(f'Retained imports into candidate set: {sorted(incoming)}')

    def stats(modules):
        return {'modules': len(modules),
                'lines': sum(len(sources[m].splitlines()) for m in modules),
                'by_directory': dict(sorted(collections.Counter(
                    module_path(m).rsplit('/', 1)[0] for m in modules).items()))}

    # Legacy check files are outside the primary verification surface, but
    # their direct imports must be retired or retained when a purge is made.
    legacy_checks = {}
    legacy_roots = set()
    for path in sorted((root / 'scripts' / 'proofgen').glob('*Audit.lean')):
        direct = imports(path.read_text())
        legacy_roots.update(direct)
        used = direct & candidates
        if used:
            legacy_checks[str(path.relative_to(root))] = sorted(map(module_path, used))
    legacy_extra = closure(graph, legacy_roots) - public
    conservative = candidates - legacy_extra

    return {
        'theorem_root': THEOREM,
        'protected_roots': list(PUBLIC_ROOTS),
        'scope': 'Import closure only; candidates may still support the stronger native target.',
        'primary_proof': stats(proof),
        'public_compatibility_extra': stats((public - proof) & package),
        'candidates': stats(candidates),
        'legacy_audit_extra': stats(legacy_extra),
        'conservative_candidates': stats(conservative),
        'retain_for_proof': sorted(map(module_path, proof)),
        'retain_for_public_compatibility': sorted(map(module_path, (public - proof) & package)),
        'candidate_files': sorted(map(module_path, candidates)),
        'retain_for_legacy_audits': sorted(map(module_path, legacy_extra)),
        'conservative_candidate_files': sorted(map(module_path, conservative)),
        'legacy_check_imports': legacy_checks,
        'aggregate_root': 'IntegerMultBounds.lean must be pruned before candidate files are removed.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, help='write a reproducible JSON inventory')
    parser.add_argument('--check', action='store_true', help='compare an existing manifest without editing')
    args = parser.parse_args()
    if args.check and not args.manifest:
        parser.error('--check requires --manifest')
    data = inventory()
    rendered = json.dumps(data, indent=2, ensure_ascii=False) + '\n'
    if args.manifest:
        if args.check:
            if not args.manifest.exists() or args.manifest.read_text() != rendered:
                parser.exit(1, 'Proof-retention manifest is out of date.\n')
        else:
            args.manifest.write_text(rendered)
    for key in ('primary_proof', 'public_compatibility_extra', 'candidates',
                'legacy_audit_extra', 'conservative_candidates'):
        info = data[key]
        print(f'{key}: {info["modules"]} modules, {info["lines"]:,} lines')


if __name__ == '__main__':
    main()
