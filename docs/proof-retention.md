# Proof retention and purge candidates

The completed Mathlib proof is the primary route. This audit identifies what
can be removed from that route while retaining the public Mathlib entry point,
the original simulation bridge, and the existing focused checks. It does not
delete proof files or assert that excluded work has no value for the stronger
`83/10^12` target.

The baseline is commit `9c30e6ab`. The authoritative per-file lists are in
[proof-retention.json](proof-retention.json), generated from local Lean imports
by [proof-retention.py](../scripts/proof-retention.py).

## What the completed proof still needs

| Retention set | Lean modules | Source lines |
| --- | ---: | ---: |
| Transitive imports of `MathlibTM2.Theorem` | 1,989 | 532,699 |
| Additional public compatibility and integration modules | 26 | 4,984 |
| Additional dependencies of the legacy focused audits | 242 | 59,104 |
| Conservative removal candidates, preserving all those checks | 1,515 | 198,928 |

The 1,989-module proof closure includes 895 modules in the `Machine` namespace,
696 network/certificate modules, 63 Schönhage–Strassen modules, and 241 Mathlib
host-proof modules. In particular the original binary interchange, network
rank/control certificates, arithmetic primitives, fast scalar multiplication,
fixed-point mathematics and resampling estimates remain dependencies. Whole
`Machine`, `Networks`, `Schoenhage`, `NLogN` or `Resampling` directories cannot
be deleted.

An import closure is conservative: an imported module may contain unused
declarations, but removing it requires a separate import-minimization or
declaration-level analysis. This audit does not classify individual declarations
inside retained files as dead.

## First conservative batch

The exact 1,515-file set is `conservative_candidate_files` in the manifest.
None is imported transitively by the final theorem, the public Mathlib entry
point, `FastPathCheck`, `MathlibTM2Check`, `CompletedProofCheck`, or the three
legacy `scripts/proofgen/*Audit.lean` checks.

| Candidate family | Files | Lines | Role |
| --- | ---: | ---: | --- |
| `Machine/CompactComplex*` | 426 | 84,348 | Old native recursive controller, event schedule, bank/ledger invariants and root assembly. |
| `Machine/CompactNative*` | 57 | 7,165 | Native role/control/phase lifecycle adapters. |
| `Machine/ActivePrefix*` | 205 | 18,373 | Native active-prefix control assembly outside the retained interchange proof. |
| Other native `Machine` candidates | 768 | 78,294 | Further reservation, padding, layout, phase and assembly work; use the exact manifest rather than a directory glob. |
| Other directories | 59 | 10,748 | Unused milestone bundles, alternate network semantics and remaining old transform/resampling wrappers. |

These are safe candidates for the **completed result**, subject to replacing
the all-components root import list and updating the corresponding legacy
documentation. Many are substantive work toward the stronger compact-control
target. Their deletion would retire that development from the active checkout;
Git history preserves the baseline for recovery.

## Optional second batch

There are another 242 modules outside the public completed-proof closure, but
the legacy adapter, chirp or recovery audits still import them transitively.
They are listed in `retain_for_legacy_audits`. Together the two batches contain
1,757 modules and 258,032 lines.

Deleting this second batch requires retiring or adapting those legacy checks
and their generators as one change. The manifest lists their direct candidate
imports under `legacy_check_imports`:

- `scripts/proofgen/ChirpAudit.lean`: 11 direct imports.
- `scripts/proofgen/ProofReuseAudit.lean`: 5 direct imports.
- `scripts/proofgen/RecoveryInstallAudit.lean`: 36 direct imports.

Seven generated/pilot modules are already outside the all-components root:
`CertifiedBinOf`, `CertifiedPlacement`, `LayoutAdapterPilot`,
`LayoutPlacementGenerated`, `LayoutSequenceGenerated`, `LayoutSequencePilot`
and `TwistCleanupGenerated`, all under `Schoenhage`. They belong to the legacy
audit closure; being absent from the root is not enough to delete them without
handling those checks.

## Purge boundary and validation

`IntegerMultBounds.lean` currently imports the legacy components explicitly.
Removing candidate files without pruning that aggregator would break the main
build and `AxiomAudit`. A removal change must keep the retained import closure,
keep every proof-integrity check on the surviving code, regenerate plan status,
and update legacy documentation and generator references. The first batch
requires no retirement of a focused audit.

`CompletedProofCheck.lean` imports `MathlibTM2.Theorem` directly, without the
all-components aggregator or optional compatibility facade. It proves the
unconditional statement is available and audits every imported project
declaration for the same three permitted standard axioms. It passed for
109,860 declarations, with 4,278.7 MiB peak RSS, and is now included in CI.
No proof source or proof limit was changed by this audit.

Reproduce the inventory and its checks with:

```sh
python3 -m unittest discover -s scripts -p test_proof_retention.py
python3 scripts/proof-retention.py --manifest docs/proof-retention.json --check
python3 scripts/check-lean-safe.py CompletedProofCheck.lean
```

To refresh the inventory after import changes, omit `--check`. The script only
writes the requested manifest; it never removes Lean files. Parser tests cover
nested comments and strings, multiple imports, transitive dependency diamonds,
cycles, and missing imports.
