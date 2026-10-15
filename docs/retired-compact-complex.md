# Retired native CompactComplex controller

On 2026-10-15 the superseded native controller was removed from the active
checkout: 426 controller modules and 209 unused transitive importers, totaling
635 modules and 109,973 source lines. The exact list and recovery baseline
`ce0fac83` are in [retired-compact-complex.json](retired-compact-complex.json).

## Boundary

The 426-file seed is the intersection of the audited conservative candidate
set with `Machine/CompactComplex*`. It excludes the two similarly named
modules used by the completed proof. Reverse import traversal adds 209
legacy wrappers that cannot remain buildable after their dependencies are
removed, including old role/phase/normalization adapters and the former
native stream-arithmetic integration theorem.

All 635 files were outside the transitive imports of the completed theorem,
the public Mathlib compatibility facade, the focused theorem checks and the
three legacy proof-generation audits. Every surviving source was checked for
imports into the removal set; the all-components root was pruned accordingly.
No retained proof body, theorem statement or proof limit was changed.
The independent Gaussian butterfly residue bridge and the contributed host
proof remain available.

## Documentation and recovery

The component index no longer lists removed files as current components.
Section 5 now catalogs surviving components; its removed milestones are
marked retired rather than complete. The prior detailed native-controller
plan and its invariants are preserved in commit `ce0fac83`, together with the
source files. This also removes stale README claims that the old controller
is still the current path to the general sub-n-log-n result.

To resume that stronger-exponent development, recover the manifest-listed
files and the relevant root imports from `ce0fac83`, then reconcile them with
the current library and rerun the guarded checks. Restoring the entire old
checkout over newer work is unnecessary.

## Validation

The completed theorem, its protected import closure, public compatibility
modules and legacy focused audit dependencies are unchanged. The remaining
retention manifest is regenerated after removal.

- Entire surviving local import graph: no missing modules.
- Protected theorem closure: unchanged at 1,989 modules and 532,699 lines.
- Retention audit tests: 6 passed, including transitive dependent retirement and rejection of protected removals.
- Existing proof-generation adapter/generator tests: 11 passed.
- Plan regeneration, retention manifest consistency and whitespace checks: passed.
- Fresh guarded library build: passed, 6,923 jobs, 5.0 GiB peak combined RSS.
- Independent completed-proof axiom audit: passed for 109,860 declarations, allowing only the three standard axioms.

A further run of the library-wide audit and all focused Lean audits was queued
after the fresh build. At commit time it was waiting for a separate guarded
profiling snapshot build to release the mandatory shared lock; these additional
results are not claimed here. The existing CI proof-integrity checks remain
enabled, and all their dependencies are retained.
