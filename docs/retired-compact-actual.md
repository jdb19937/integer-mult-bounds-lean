# Retired native actual-multiplier stage wrappers

On 2026-10-15, 16 unused `Machine/CompactActual*` modules were removed,
totaling 1,317 source lines. They instantiated the superseded native stage
machinery with actual multiplier parameters, readiness conditions, pair
schedules, inverse schedules and cost allowances.

The [exact manifest](retired-compact-actual.json) records the files and recovery
baseline `7415d773d14212c68b523979aaac6db9dc0ba542`. Recover individual files
and their root imports from that revision if the native route is resumed.

## Boundary

All 16 files were conservative removal candidates. Reverse import traversal
required no additional deletions. The completed theorem, public compatibility
interfaces and legacy focused audits have identical import closures after
removal. Reusable circuit/frame mathematics and the Mathlib host proof remain.

The aggregate root and component catalog no longer list these files. The
native plan marks the removed padding milestone retired and removes the
retired stage rows; it does not count the removed theorem as a current result.
No retained Lean proof body, theorem statement or proof limit was changed.

## Validation

The complete local import graph has no missing modules. Protected import
closures were compared before and after removal and are identical.

- Six retention-audit tests passed.
- Manifest consistency passed on an isolated snapshot containing exactly the
  intended cleanup, excluding concurrent proof-optimization edits.
- Plan regeneration and whitespace checks passed.
- Guarded library build passed: 6,907 jobs, 31.1 GiB peak combined RSS.
- Library-wide axiom audit passed for 143,876 declarations, allowing only the
  three standard axioms; peak RSS was 4,823.2 MiB.
