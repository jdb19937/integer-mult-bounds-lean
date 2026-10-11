import IntegerMultBounds.Machine.CompactComplexActualBasisCoordinates
import IntegerMultBounds.Machine.ActivePrefixStageUnselectedFrame
import IntegerMultBounds.Machine.CompactComplexEndpointCoordinates

/-! Actual native row destinations act on the original recursive node
coordinates and preserve every surrounding global address spectator. -/
namespace IntegerMultBounds.Machine.CompactComplexActualBasisSlice
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactComplexNonleafChildAddress (address insert axis axisIndex)
open CompactComplexEndpointCoordinates (rowCoordinates)
open ActivePrefixStageNativePairCoordinates (start)
open CompactAllAxisPhaseDispatch (count edge)
variable {sh : Shape}

/-- Recover the original global address directly from its physical native row
start. This includes every compact/slack/back bit, independent of the codec. -/
theorem native_row_coordinate (d : ActivePrefixStageFullData.Inputs sh)
    (r : Fin (ActivePrefixStageTripleWords.count d)) (t : Fin sh.bits) :
    rowCoordinates sh (start d r) t=
      Networks.BinaryRowColumns.scalar (Nat.testBit r.val t.rev.val) := by
  have hp : 0<sh.payload := by have hr := d.hrecord; omega
  have h := CompactComplexEndpointCoordinates.rank_bit
    (rowCoordinates sh (start d r)) t.rev.val t.rev.isLt
  simpa only [rowCoordinates,FlatCoordinateLayout.rank_coordinates,Fin.val_mk,
    start,Nat.mul_div_cancel _ hp,Nat.testBit_mod_two_pow,t.rev.isLt,decide_true,
    Bool.true_and,ButterflyAxisWalsh.coordinate,Fin.eta,Fin.rev_rev] using h.symm

section Node
variable {left k : ℕ} (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (m ell p : ℕ) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

abbrev nativeInput := NativePolynomialStageShape.inputs
  (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm

theorem native_slots : (nativeInput rho visit ha pair m ell p hG hGK hm).stage.slots=25^3 := rfl

/-- The selected node address at the computed output row is the literal
ambient basis map applied in each column to the original node address. -/
theorem node_destination (pc : Fin count)
    (r : Fin (ActivePrefixStageTripleWords.count (nativeInput rho visit ha pair m ell p hG hGK hm))) :
    address rho visit (rowCoordinates (NativePolynomialStageShape.shape sh ell p)
      (start (nativeInput rho visit ha pair m ell p hG hGK hm)
        (ActivePrefixStageNativePairCoordinates.run (nativeInput rho visit ha pair m ell p hG hGK hm)
          (CompactNativeConjugatedPhase.ops (nativeInput rho visit ha pair m ell p hG hGK hm) (native_slots rho visit ha pair m ell p hG hGK hm) pc) r)))=
    fun column => CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
      (address rho visit (rowCoordinates (NativePolynomialStageShape.shape sh ell p)
        (start (nativeInput rho visit ha pair m ell p hG hGK hm) r)) column) := by
  funext column
  have h := CompactComplexActualBasisCoordinates.destination_coordinates
    (nativeInput rho visit ha pair m ell p hG hGK hm) (native_slots rho visit ha pair m ell p hG hGK hm) pc r column
  dsimp only [nativeInput] at h
  erw [CompactComplexEndpointCoordinates.native_node_address,
    CompactComplexEndpointCoordinates.native_node_address] at h
  exact h

/-- The entire surrounding global address frame is unchanged by the actual
basis word, including unused positions between selected node coordinates. -/
theorem node_spectator (pc : Fin count)
    (r : Fin (ActivePrefixStageTripleWords.count (nativeInput rho visit ha pair m ell p hG hGK hm)))
    (t : Fin sh.bits) (ht : ¬∃ i,axis rho visit i=t) :
    rowCoordinates (NativePolynomialStageShape.shape sh ell p)
      (start (nativeInput rho visit ha pair m ell p hG hGK hm)
        (ActivePrefixStageNativePairCoordinates.run (nativeInput rho visit ha pair m ell p hG hGK hm)
          (CompactNativeConjugatedPhase.ops (nativeInput rho visit ha pair m ell p hG hGK hm) (native_slots rho visit ha pair m ell p hG hGK hm) pc) r)) t=
    rowCoordinates (NativePolynomialStageShape.shape sh ell p)
      (start (nativeInput rho visit ha pair m ell p hG hGK hm) r) t := by
  erw [native_row_coordinate,native_row_coordinate]
  apply congrArg Networks.BinaryRowColumns.scalar
  apply ActivePrefixStageUnselectedFrame.native_bit_unselected
  rintro ⟨slot,col,he⟩
  apply ht
  let high : Fin (arity^k) := ActivePrefixStageRuntimeOrdinal.reverseAxis col
  refine ⟨axisIndex slot high,?_⟩
  apply Fin.rev_injective
  apply Fin.ext
  simp only [axis,ButterflyAxisWalsh.coordinate,Fin.rev_rev,Fin.val_mk]
  rw [←CompactComplexEndpointCoordinates.node_position rho visit ha pair slot high]
  have hr : ActivePrefixStageRuntimeOrdinal.reverseAxis high=col := by
    apply Fin.ext
    change arity^k-(arity^k-col.val-1)-1=col.val
    have hc := col.isLt
    change col.val<arity^k at hc
    omega
  erw [ActivePrefixStageRuntimeOrdinal.original_position,hr]
  change t.rev.val=sh.H+sh.B+
    ActivePrefixStageGeometry.slotLow (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) slot+
    ((CompactBinaryBasisSchedule.stage (node rho visit ha) pair).rho+col.val*sh.chunk) at he
  omega

/-- The whole actual destination address is the original address with exactly
the node's selected coordinates replaced by the ambient basis transform. -/
theorem node_row_destination (pc : Fin count)
    (r : Fin (ActivePrefixStageTripleWords.count (nativeInput rho visit ha pair m ell p hG hGK hm))) :
    rowCoordinates (NativePolynomialStageShape.shape sh ell p)
      (start (nativeInput rho visit ha pair m ell p hG hGK hm)
        (ActivePrefixStageNativePairCoordinates.run (nativeInput rho visit ha pair m ell p hG hGK hm)
          (CompactNativeConjugatedPhase.ops (nativeInput rho visit ha pair m ell p hG hGK hm)
            (native_slots rho visit ha pair m ell p hG hGK hm) pc) r))=
    insert rho visit
      (rowCoordinates (NativePolynomialStageShape.shape sh ell p)
        (start (nativeInput rho visit ha pair m ell p hG hGK hm) r))
      (fun column => CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
        (address rho visit (rowCoordinates (NativePolynomialStageShape.shape sh ell p)
          (start (nativeInput rho visit ha pair m ell p hG hGK hm) r)) column)) := by
  funext t
  by_cases ht : ∃ i,axis rho visit i=t
  · obtain ⟨i,rfl⟩ := ht
    have hs : Function.Surjective (fun z : Fin arity × Fin (arity^k) => axisIndex z.1 z.2) :=
      (finProdFinEquiv.trans (finCongr (by rw [pow_succ,Nat.mul_comm]))).surjective
    obtain ⟨⟨slot,column⟩,rfl⟩ := hs i
    erw [CompactComplexNonleafChildAddress.insert_axis]
    have h := congrFun (congrFun (node_destination rho visit ha pair m ell p hG hGK hm pc r) column) slot
    exact h
  · erw [CompactComplexNonleafChildAddress.insert_frame rho visit _ _ t ht]
    exact node_spectator rho visit ha pair m ell p hG hGK hm pc r t ht

end Node
end
end IntegerMultBounds.Machine.CompactComplexActualBasisSlice
