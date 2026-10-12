module

public import IntegerMultBounds.Machine.ArbitrarySliceStepBudget
public import IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics
public import IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun
public import IntegerMultBounds.Machine.ArbitraryWidthPieces
public import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
public import IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange
public import IntegerMultBounds.Machine.BinaryDescriptorDivision
public import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
public import IntegerMultBounds.Machine.BinaryDivide
public import IntegerMultBounds.Machine.BinaryInterchangeBudget
public import IntegerMultBounds.Machine.BinaryRadixRangePrepare
public import IntegerMultBounds.Machine.CyclicRowNormalized
public import IntegerMultBounds.Machine.FiniteReturnDispatch
public import IntegerMultBounds.Machine.RadixDigitMoveBlockExecution
public import IntegerMultBounds.Machine.RadixRangePadding
public import IntegerMultBounds.Machine.RadixRangePaddingExecution
public import IntegerMultBounds.Machine.RecursiveCallProtocol
public import IntegerMultBounds.Machine.RecursiveChildPrepare
public import IntegerMultBounds.Machine.RecursiveDescriptorDivision
public import IntegerMultBounds.Machine.RecursiveDigitRoleBank
public import IntegerMultBounds.Machine.RecursiveHeaderRestore
public import IntegerMultBounds.Machine.RecursiveInterchangeVolume
public import IntegerMultBounds.Machine.RecursiveRowPadding
public import IntegerMultBounds.Machine.RecursiveRowsNode
public import IntegerMultBounds.Machine.RecursiveViewedAction
public import IntegerMultBounds.Machine.RoleArrayCall
public import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
public import IntegerMultBounds.Machine.Shared50RecursiveBasePermutation
public import IntegerMultBounds.Machine.Shared50RecursiveBudgetBound
public import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation
public import IntegerMultBounds.Machine.Shared50RecursiveDepth
public import IntegerMultBounds.Machine.Shared50RecursiveInduction
public import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
public import IntegerMultBounds.Machine.Shared50RecursiveSegments
public import IntegerMultBounds.Machine.StackPop
public import IntegerMultBounds.Machine.StackPush
public import IntegerMultBounds.Networks.AffineFieldSegments
public import IntegerMultBounds.Networks.Shared50ModularControl
public import IntegerMultBounds.Swap.LowerTriangular
public import IntegerMultBounds.Swap.Modular
public import IntegerMultBounds.Swap.PivotRank
public import IntegerMultBounds.Swap.Recurrence

/-! Section 4 milestones: each states one sub-problem of the faster
interchange (plan/04-faster-interchange-address.md) in a single theorem. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)

/-- Lemma 4.4 on tapes: from the six original headers, one fixed machine
transposes the radix payload for every width, including zero, restoring all
other tapes, within `C · volume · max(1, width)^τ` steps. -/
theorem runs_uniform : ∃ C : ℝ, 0 < C ∧ ∀ {t : ℕ} (caller : Tapes t prime)
    (headers : Fin 6 → Fin t) (source : Fin t) (d : Descriptor) (hs : Fin 6 → List Bool),
    d.Positive → RecursiveDimensionBank.Headers d hs →
    (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) →
    (∀ i, caller.head (headers i) = 1) →
    ∀ (x : Fin (volume prime d) → ZMod 2), caller.tape source = sourceWord x →
    caller.head source = 0 →
    HoareTime (program headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) (cost d hs) ∧
    (cost d hs : ℝ) ≤ C*(volume prime d : ℝ)*((max 1 d.width : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound
  exact ⟨C,hC,fun caller headers source d hs hp hv ht hh x hf hhead =>
    ⟨runs caller headers source d hs hp hv ht hh x hf hhead,hbound d hs hp hv⟩⟩

end
end IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun

namespace IntegerMultBounds.Machine.BinaryInterchangeRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

/-- The binary interchange on tapes: from five original binary headers, one
fixed machine returns the exact rectangular transpose for all adjacent widths,
including zero, restoring every other tape and head, within
`C · rectangular volume · max(1, h, d)^τ` steps. -/
theorem runs_uniform : ∃ C : ℝ, 0 < C ∧ ∀ {t : ℕ} (caller : Tapes t prime)
    (focus : Fin 5 → Fin t) (payload : Fin t) (hi : Function.Injective focus)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool), h ≤ d+1 → d ≤ h+1 →
    (∀ i, Counter.value (hs i) = values P G B h d i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) → 0 < P → 0 < G → 0 < B →
    (∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i)) →
    (∀ i, caller.head (focus i) = 1) →
    ∀ (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool),
    caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) →
    caller.head payload = 0 →
    HoareTime (program focus payload hi) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (cost P G B h d hs) ∧
    (cost P G B h d hs : ℝ) ≤
      C*(BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℝ)*
        ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound
  exact ⟨C,hC,fun caller focus payload hi P G B h d hs hhd hdh hv hc hP hG hB htapes hheads x ht hh =>
    ⟨runs caller focus payload hi P G B h d hs hhd hdh hv hc hP hG hB htapes hheads x ht hh,
      hbound P G B h d hs hP hG hB hhd hdh hv hc⟩⟩

end
end IntegerMultBounds.Machine.BinaryInterchangeRun

namespace IntegerMultBounds.Machine.RecursiveDigitRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveShiftRoleBank (common source updated)

/-- The single-digit base case on tapes: at width one the clean machine on the
permanent role bank replaces the selected role by the exact node transpose,
retaining headers and auxiliaries, within `coefficient · volume` steps. -/
theorem realizes_transpose {t u : ℕ} {v : Descriptor} (hw : v.width = 1) (wire : Fin t)
    (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head wire = 0) (ht : roles.tape wire = source x)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) wire)
      (fun w => w = CleanSubbank.bank (common roles hs aux))
      (fun w => w = CleanSubbank.bank (common (updated roles wire
        (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs aux))
      (coefficient*volume prime v) := by
  rw [← Shared50RecursiveBasePermutation.array_transpose hw x]
  exact realizes hw wire roles hs aux x hh ht hv hpos

end
end IntegerMultBounds.Machine.RecursiveDigitRoleBank

namespace IntegerMultBounds.Swap.Recurrence

/-- The recurrence gives F(k) <= K (m^k)^tau, the power-digit piece sum is O(e^tau), and the row, row-range and radix padding bounds hold. -/
theorem interchange_arithmetic :
    (type_of% @IntegerMultBounds.Swap.Recurrence.power_width_bound) ∧
    (type_of% @IntegerMultBounds.Swap.Recurrence.swap_recurrence) ∧
    (type_of% @IntegerMultBounds.Swap.Recurrence.digit_sum_le) ∧
    (type_of% @IntegerMultBounds.Swap.Recurrence.pieces_le) ∧
    (type_of% @IntegerMultBounds.Swap.Recurrence.row_padding) ∧
    (type_of% @IntegerMultBounds.Swap.Recurrence.row_range) ∧
    (type_of% @IntegerMultBounds.Swap.Recurrence.radixWidth_spec) :=
  ⟨@IntegerMultBounds.Swap.Recurrence.power_width_bound, @IntegerMultBounds.Swap.Recurrence.swap_recurrence, @IntegerMultBounds.Swap.Recurrence.digit_sum_le, @IntegerMultBounds.Swap.Recurrence.pieces_le, @IntegerMultBounds.Swap.Recurrence.row_padding, @IntegerMultBounds.Swap.Recurrence.row_range, @IntegerMultBounds.Swap.Recurrence.radixWidth_spec⟩

end IntegerMultBounds.Swap.Recurrence

namespace IntegerMultBounds.Swap.Modular

/-- Every rational matrix factors as E1 Pi E2 with lower-triangular factors and rank A pivots, and for the fixed Shared50 edge set the chosen odd prime gives, at every q^b, shear programs H <- H + A D with exactly rank A interchanges and certified coefficients. -/
theorem certified_factor_shear :
    (type_of% @IntegerMultBounds.Swap.PivotRank.exists_factorization_rank) ∧
    (type_of% @IntegerMultBounds.Swap.LowerTriangular.factorization) ∧
    (type_of% @IntegerMultBounds.Swap.Modular.exists_prime_shear) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50ModularControl.chosen_edge_specs) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50ModularControl.interchanges_exact) :=
  ⟨@IntegerMultBounds.Swap.PivotRank.exists_factorization_rank, @IntegerMultBounds.Swap.LowerTriangular.factorization, @IntegerMultBounds.Swap.Modular.exists_prime_shear, @IntegerMultBounds.Networks.Shared50ModularControl.chosen_edge_specs, @IntegerMultBounds.Networks.Shared50ModularControl.interchanges_exact⟩

end IntegerMultBounds.Swap.Modular

namespace IntegerMultBounds.Machine.Shared50RecursiveSegments

/-- The certified shear programs on tapes: every nonrecursive segment runs on the
role bank with its exact field action in `coefficient · volume` steps, splitting a
program yields only its own nonrecursive instructions, the programs use exactly
`s` interchanges, and the recursive depth contract executes those interchanges. -/
theorem realizes_shear :
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveSegments.realizes) ∧
    (type_of% @IntegerMultBounds.Networks.AffineFieldSegments.split_run_spec) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50ModularControl.interchanges_exact) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveInduction.contract) :=
  ⟨@IntegerMultBounds.Machine.Shared50RecursiveSegments.realizes, @IntegerMultBounds.Networks.AffineFieldSegments.split_run_spec, @IntegerMultBounds.Networks.Shared50ModularControl.interchanges_exact, @IntegerMultBounds.Machine.Shared50RecursiveInduction.contract⟩

end IntegerMultBounds.Machine.Shared50RecursiveSegments

namespace IntegerMultBounds.Machine.RecursivePrimitives

/-- Cyclic role split/merge, counted stack push/pop, descriptor-stack roundtrip, descriptor division and finite return dispatch have exact word-level results: role words, restored older stacks, canonical quotient and decoded return state. -/
theorem word_semantics :
    (type_of% @IntegerMultBounds.Machine.BinaryDescriptorDivision.divide_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip.roundtrip_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.FiniteReturnDispatch.dispatch_exact) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryDivide.div_correct) :=
  ⟨@IntegerMultBounds.Machine.BinaryDescriptorDivision.divide_hoare, @IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip.roundtrip_hoare, @IntegerMultBounds.Machine.FiniteReturnDispatch.dispatch_exact, @IntegerMultBounds.Machine.BinaryDivide.div_correct⟩

end IntegerMultBounds.Machine.RecursivePrimitives

namespace IntegerMultBounds.Machine.RecursivePrimitives

/-- The fixed machines for normalized cyclic role split and merge, counted stack push and pop, descriptor-stack roundtrip, role-array call parking, clean descriptor division and finite return dispatch each meet their exact bank contract within linear cost. -/
theorem machines_hoare :
    (type_of% @IntegerMultBounds.Machine.CyclicRowNormalized.split_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CyclicRowNormalized.merge_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.StackPush.push_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.StackPop.pop_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip.roundtrip_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RoleArrayCall.call_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryDescriptorDivision.divide_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.FiniteReturnDispatch.dispatch_hoare) :=
  ⟨@IntegerMultBounds.Machine.CyclicRowNormalized.split_hoare, @IntegerMultBounds.Machine.CyclicRowNormalized.merge_hoare, @IntegerMultBounds.Machine.StackPush.push_hoare, @IntegerMultBounds.Machine.StackPop.pop_hoare, @IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip.roundtrip_hoare, @IntegerMultBounds.Machine.RoleArrayCall.call_hoare, @IntegerMultBounds.Machine.BinaryDescriptorDivision.divide_hoare, @IntegerMultBounds.Machine.FiniteReturnDispatch.dispatch_hoare⟩

end IntegerMultBounds.Machine.RecursivePrimitives

namespace IntegerMultBounds.Machine.RecursiveNodeOperations

/-- Node row split into roles, selected shifts and H/D scalings through coordinate views, and the permuted merge act on the logical node array exactly as the corresponding field operations. -/
theorem array_semantics :
    (type_of% @IntegerMultBounds.Machine.RecursiveViewedAction.realizes_array) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowsNode.entry_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowsNode.exit_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveSegments.realizes) :=
  ⟨@IntegerMultBounds.Machine.RecursiveViewedAction.realizes_array, @IntegerMultBounds.Machine.RecursiveRowsNode.entry_hoare, @IntegerMultBounds.Machine.RecursiveRowsNode.exit_hoare, @IntegerMultBounds.Machine.Shared50RecursiveSegments.realizes⟩

end IntegerMultBounds.Machine.RecursiveNodeOperations

namespace IntegerMultBounds.Machine.RecursiveNodeOperations

/-- The node operations on tapes: node entry (save headers, split rows), any selected
shift or H/D scaling through coordinate views, and node exit (restore headers,
permuted merge) each meet their exact bank contract, and entry and exit cost
linear parent volume. -/
theorem realizes :
    (type_of% @IntegerMultBounds.Machine.RecursiveRowsNode.entry_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowsNode.exit_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveViewedAction.realizes_array) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowsNode.entry_cost_linear) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowsNode.exit_cost_linear) :=
  ⟨@IntegerMultBounds.Machine.RecursiveRowsNode.entry_hoare, @IntegerMultBounds.Machine.RecursiveRowsNode.exit_hoare, @IntegerMultBounds.Machine.RecursiveViewedAction.realizes_array, @IntegerMultBounds.Machine.RecursiveRowsNode.entry_cost_linear, @IntegerMultBounds.Machine.RecursiveRowsNode.exit_cost_linear⟩

end IntegerMultBounds.Machine.RecursiveNodeOperations

namespace IntegerMultBounds.Machine.RecursiveInterchangeVolume

/-- Along any child path the prepared child headers are the canonical child layout, logical volume divides exactly by the role count, and all descriptor stack, division and header costs are at most a constant times the child's logical volume. -/
theorem call_cost_absorbed :
    (type_of% @IntegerMultBounds.Machine.RecursiveInterchangeVolume.Path.original_chunks) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveInterchangeVolume.Path.volume_div) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveDescriptorDivision.cost_le_child_volume) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveDescriptorDivision.divide_hoare_linear) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveChildPrepare.prepares) :=
  ⟨@IntegerMultBounds.Machine.RecursiveInterchangeVolume.Path.original_chunks, @IntegerMultBounds.Machine.RecursiveInterchangeVolume.Path.volume_div, @IntegerMultBounds.Machine.RecursiveDescriptorDivision.cost_le_child_volume, @IntegerMultBounds.Machine.RecursiveDescriptorDivision.divide_hoare_linear, @IntegerMultBounds.Machine.RecursiveChildPrepare.prepares⟩

end IntegerMultBounds.Machine.RecursiveInterchangeVolume

namespace IntegerMultBounds.Machine.RecursiveCallProtocol

/-- The call protocol on tapes: the entry block parks arrays, saves parent headers
and PC and installs the child headers, the recovery block restores the parent
bank, and the header-frame restore is linear in volume. -/
theorem roundtrip :
    (type_of% @IntegerMultBounds.Machine.RecursiveCallProtocol.enters) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveCallProtocol.recovers) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveHeaderRestore.restore_hoare_linear) :=
  ⟨@IntegerMultBounds.Machine.RecursiveCallProtocol.enters, @IntegerMultBounds.Machine.RecursiveCallProtocol.recovers, @IntegerMultBounds.Machine.RecursiveHeaderRestore.restore_hoare_linear⟩

end IntegerMultBounds.Machine.RecursiveCallProtocol

namespace IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose

/-- At every power width the node pre/child/post decomposition composes to the full binary transpose, and the certified recursive budget at depth k is at most constant * V * (125000^depth)^tau. -/
theorem recursive_transpose_budget :
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveBudgetBound.power_width_bound) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose.transpose_all) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveChildPermutation.child_spec) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveDepth.selected_volume) :=
  ⟨@IntegerMultBounds.Machine.Shared50RecursiveBudgetBound.power_width_bound, @IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose.transpose_all, @IntegerMultBounds.Machine.Shared50RecursiveChildPermutation.child_spec, @IntegerMultBounds.Machine.Shared50RecursiveDepth.selected_volume⟩

end IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose

namespace IntegerMultBounds.Machine.RadixRangePadding

/-- Zero-padding rows or both chunk ranges, transposing and cropping back gives exactly the original transpose, and the ordered radix digit movement (join/separate) agrees with the joined transpose layout. -/
theorem padding_semantics :
    (type_of% @IntegerMultBounds.Machine.RadixRangePadding.crop_transpose_pad) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowPadding.cropArray_transpose_padArray) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveRowPadding.crop_permute_pad) ∧
    (type_of% @IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics.exchange_join_transpose_separate) :=
  ⟨@IntegerMultBounds.Machine.RadixRangePadding.crop_transpose_pad, @IntegerMultBounds.Machine.RecursiveRowPadding.cropArray_transpose_padArray, @IntegerMultBounds.Machine.RecursiveRowPadding.crop_permute_pad, @IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics.exchange_join_transpose_separate⟩

end IntegerMultBounds.Machine.RadixRangePadding

namespace IntegerMultBounds.Machine.BinaryRadixRangePrepare

/-- Given a padded radix-range transpose contract, the prepare, transpose and finish machines together return exactly the original binary-range transpose with all generated metadata erased in linear padded-volume time, and the row padding/cropping and radix digit-movement machines meet their exact contracts. -/
theorem pad_transpose_crop_hoare :
    (type_of% @IntegerMultBounds.Machine.BinaryRadixRangePrepare.prepare_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryRadixRangePrepare.finish_transpose_pad_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RadixRangePaddingExecution.crop_transpose_pad_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RowPaddingConstructedAlphabet.pad_bits_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RowPaddingConstructedAlphabet.crop_bits_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RadixDigitMoveBlockExecution.forward_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RadixDigitMoveBlockExecution.backward_hoare) :=
  ⟨@IntegerMultBounds.Machine.BinaryRadixRangePrepare.prepare_hoare, @IntegerMultBounds.Machine.BinaryRadixRangePrepare.finish_transpose_pad_hoare, @IntegerMultBounds.Machine.RadixRangePaddingExecution.crop_transpose_pad_hoare, @IntegerMultBounds.Machine.RowPaddingConstructedAlphabet.pad_bits_hoare, @IntegerMultBounds.Machine.RowPaddingConstructedAlphabet.crop_bits_hoare, @IntegerMultBounds.Machine.RadixDigitMoveBlockExecution.forward_hoare, @IntegerMultBounds.Machine.RadixDigitMoveBlockExecution.backward_hoare⟩

end IntegerMultBounds.Machine.BinaryRadixRangePrepare

namespace IntegerMultBounds.Machine.ArbitraryWidthPieces

/-- The base-125000 power pieces of width e (slice windows, high exchange/join, elementary fallback) compose to the full radix transpose, and their slice-step budgets total at most constant * V * e^tau. -/
theorem pieces_transpose_budget :
    (type_of% @IntegerMultBounds.Machine.ArbitrarySliceStepBudget.sum_bound) ∧
    (type_of% @IntegerMultBounds.Machine.ArbitraryWidthPieces.pieces_swap) ∧
    (type_of% @IntegerMultBounds.Machine.ArbitraryWidthPieces.runWindows_full) ∧
    (type_of% @IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose.array_entry) ∧
    (type_of% @IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics.exchange_join_transpose_separate) :=
  ⟨@IntegerMultBounds.Machine.ArbitrarySliceStepBudget.sum_bound, @IntegerMultBounds.Machine.ArbitraryWidthPieces.pieces_swap, @IntegerMultBounds.Machine.ArbitraryWidthPieces.runWindows_full, @IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose.array_entry, @IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics.exchange_join_transpose_separate⟩

end IntegerMultBounds.Machine.ArbitraryWidthPieces

namespace IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange

/-- Equal- and adjacent-width binary transposes decompose exactly into padded radix-range transposes and high-block movements, and one constant C bounds the wrapper cost by C * rectangular volume * max(1,h,d)^tau. -/
theorem decomposition_bound :
    (type_of% @IntegerMultBounds.Machine.BinaryInterchangeRun.uniform_bound) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange.longH_eq_transpose) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange.longD_eq_transpose) ∧
    (type_of% @IntegerMultBounds.Machine.RadixRangePadding.crop_transpose_pad) :=
  ⟨@IntegerMultBounds.Machine.BinaryInterchangeRun.uniform_bound, @IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange.longH_eq_transpose, @IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange.longD_eq_transpose, @IntegerMultBounds.Machine.RadixRangePadding.crop_transpose_pad⟩

end IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange
