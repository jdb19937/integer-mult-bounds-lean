import IntegerMultBounds.MathlibTM2.Cost.CompactSwap
import IntegerMultBounds.MathlibTM2.Node.CompactRotParity
import IntegerMultBounds.MathlibTM2.Cost.CompactStageExec
import IntegerMultBounds.MathlibTM2.Node.CompactGeometry
import IntegerMultBounds.MathlibTM2.Cost.CompactRuntime
import IntegerMultBounds.MathlibTM2.Cost.CompactParameters
import IntegerMultBounds.MathlibTM2.Node.CompactRotRuntime
import IntegerMultBounds.MathlibTM2.Node.CompactGeometryRecursive
import IntegerMultBounds.MathlibTM2.Node.CompactEncoding
import IntegerMultBounds.MathlibTM2.Node.CompactSlotXor
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecArithmetic
import IntegerMultBounds.MathlibTM2.Cost.CompactSlotXor
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecPieces
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecRows
import IntegerMultBounds.MathlibTM2.Fast.CompactSynSel
import IntegerMultBounds.MathlibTM2.Node.CompactEncodingOffset
import Lean.Util.CollectAxioms

/-! Focused integrity audit for the compact-control host primitives.
These are prepared execution contracts, not an improved layer or multiplier theorem. -/

open Lean in
run_cmd do
  let names := #[
    ``IntegerMultBounds.MathlibTM2.Node.compactSwap_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactParityPack_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactParityWord_binSyms,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSwapCost_le_volume,
    ``IntegerMultBounds.MathlibTM2.Node.compactNativeProg_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactEarlyProg_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactLateProg_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactStageWords_length_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactStageBankSize_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactEarlyProg_exec_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLateProg_exec_le,
    ``IntegerMultBounds.MathlibTM2.Node.compactNative_destination_rank,
    ``IntegerMultBounds.MathlibTM2.Node.compactNative_result_entry,
    ``IntegerMultBounds.MathlibTM2.Node.compactRuntimeProg_exec,
    ``IntegerMultBounds.MathlibTM2.Node.CompactRecursiveLayout.child,
    ``IntegerMultBounds.MathlibTM2.Node.compactRecursiveNative_serialized_rank,
    ``IntegerMultBounds.MathlibTM2.Node.compactEncoding_exists,
    ``IntegerMultBounds.MathlibTM2.Node.compactEncoding_runtime_result,
    ``IntegerMultBounds.MathlibTM2.Node.compactSlotXor_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntimeProg_exec_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntimePacked_of_dyadic,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactCeil,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactReserveCounts,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSlotXorCost_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSlotXor_exec_le,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactReservedPieces,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactSynRec,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactRowReserve,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservedPcs_ok,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservedPcs_exp_sum,
    ``IntegerMultBounds.MathlibTM2.Node.compactOffsetArray_encZ,
    ``IntegerMultBounds.MathlibTM2.Node.compactOffsetArray_encZ_pullM,
    ``IntegerMultBounds.MathlibTM2.Node.compactOffset_volume]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"Compact-control host axiom audit passed for {names.size} contracts."
