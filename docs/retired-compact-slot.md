# Retired native compact slot pipeline

On 2026-10-19, 20 modules of the native compact slot pipeline were removed,
totaling 2,112 source lines. The Mathlib TM2 compact slot XOR replaced them in
`Node/CompactBasisSlot.lean`.

The removed modules built the thirteen native descriptor headers, ran the
native compact runtime program on the encoded records, and cleared the headers
again. They also proved the costs of these steps. Six `Machine/ActivePrefixStage*` modules (the
all-width runtime stage run, endpoint, dispatch and singleton budgets) had no other importer
and went with them.

The [exact manifest](retired-compact-slot.json) records the files and recovery
baseline `b96c2df9a3e182100eac167977b028282c1765b3`. Recover individual files
and their root imports from that revision if the native route is resumed.

## Replacement

`compactBasisSlot_exec` now runs `cxSlotProg` in three phases:

- **Setup** (`Node/CompactSetup.lean`) fills the index fields, masks,
  counters and interchange headers from the unary descriptor registers.
- **Core** (`cxCore`) moves the records by the gadget passes, the key pass,
  the repair and the fix pass.
- **Cleanup** restores every register except the stream.

`Node/CompactSlotCost.lean` bounds the cost by
`O(M (L + B) max(1, (k - 1) guard)^τ)`, where `M` is the number of records, `L`
the index length and `B` the record length. The bad repair records are paid by
the late repair density.

The basis chain now takes `CompactLayoutPacked layout rows D` in place of
`1 < k → Packed (compactSlotComputedInputs …) D`. Unlike before, the condition
is required for width one too. `Cost/CompactSlotPacking.lean` derives it from
the actual multiplier sizes, as `compactCaller_runtime_eventually_packed` did
for the native condition.

The compact control check audits the new contracts in place of the removed ones:

- `cxSlotRun_exec`
- `CxData.OK.slotRun_cost_le`
- `compactBasisSlot_exec`
- `compactBasisSlotCost_le`
- `compactSlotPacked_of_dyadic`
- `compactCaller_slot_eventually_packed`

## Validation

- Guarded library build passed: 11,940 jobs.
- `AxiomAudit.lean` passed for 101,567 declarations.
- `CompletedProofCheck.lean` passed for 6 declarations.
- `CompactControlCheck.lean` passed for 540 contracts.

`scripts/proof-retention.py` was not rerun. It already fails at the baseline,
because its development roots name the removed `Schoenhage` layout pilots.
