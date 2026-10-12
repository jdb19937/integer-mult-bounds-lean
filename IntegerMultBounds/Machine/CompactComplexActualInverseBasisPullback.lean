module

public import IntegerMultBounds.Machine.CompactComplexActualBasisPullback

/-! The original reverse basis word pulls stored coefficients back through
the forward ambient coordinate map. The forward-child-reverse calculation
therefore returns the original residual factor at the unchanged address. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualInverseBasisPullback
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactComplexNonleafChildAddress (address insert)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray)
open CompactComplexActualBasisCoordinates (coefficientIndex)
open CompactComplexActualBasisSlice (nativeInput native_slots)
open CompactComplexActualBasisPullback (nativeRow nativeField)
open CompactAllAxisPhaseDispatch (count edge)
open RecursiveInterchangeRows (pack)
open Networks
attribute [local irreducible] ComplexRecursiveCallSchema.sites ComplexRank25.program

section Node
variable {sh : Shape} {left k : ℕ}
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (ha : sh.active≤sh.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (m ell p : ℕ) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

/-- At an arbitrary native row, the literal reversed coefficient word reads
the input at the original forward row destination. -/
theorem basisArray_reverse_entry (pc : Fin count)
    (f : CompactSpectatorVisitGeometry.Array sh m ell)
    (r : Fin (ActivePrefixStageTripleWords.count (nativeInput rho visit ha pair m ell p hG hGK hm)))
    (j : Fin (2^ell)) :
    basisArray (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (native_slots rho visit ha pair m ell p hG hGK hm) pc true f
      (coefficientIndex (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm r j)=
    f (coefficientIndex (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (ActivePrefixStageNativePairCoordinates.run (nativeInput rho visit ha pair m ell p hG hGK hm)
        (CompactNativeConjugatedPhase.ops (nativeInput rho visit ha pair m ell p hG hGK hm)
          (native_slots rho visit ha pair m ell p hG hGK hm) pc) r) j) := by
  unfold basisArray coefficientIndex
  simp only [Fin.cast_cast,Fin.cast_refl,ActivePrefixStageNativePolynomial.flattenArray,
    id_eq,Equiv.symm_apply_apply]
  change ActivePrefixStageNativePolynomialWord.word _
    (CompactNativeConjugatedPhase.ops _ (native_slots rho visit ha pair m ell p hG hGK hm) pc).reverse
    _ r j=_
  rw [ActivePrefixStageNativePolynomialWord.word_reverse_entry]
  rfl

/-- The actual inverse array at the original address reads the child result
at the forward ambient basis address, retaining every row and polynomial index. -/
theorem basisArray_at (pc : Fin count)
    (f : CompactSpectatorVisitGeometry.Array sh m ell)
    (row : Fin m) (x : BinaryWalsh.Address sh.bits) (j : Fin (2^ell)) :
    basisArray (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (native_slots rho visit ha pair m ell p hG hGK hm) pc true f
      (pack row (FlatCoordinateLayout.index x j))=
    f (pack row (FlatCoordinateLayout.index
      (insert rho visit x (fun column => CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
        (address rho visit x column))) j)) := by
  have h := basisArray_reverse_entry rho visit ha pair m ell p hG hGK hm pc f
    (nativeRow rho visit ha pair m ell p hG hGK hm row x) j
  erw [CompactComplexActualBasisPullback.run_nativeRow rho visit ha pair m ell p hG hGK hm pc row x,
    CompactComplexActualBasisPullback.coefficientIndex_nativeRow,
    CompactComplexActualBasisPullback.coefficientIndex_nativeRow] at h
  exact h

/-- Exact inverse decoded pullback at the actual completed-child denominator. -/
theorem nativeField_at (pc : Fin count) (q n : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh m ell)
    (row : Fin m) (j : Fin (2^ell)) (x : BinaryWalsh.Address sh.bits) :
    nativeField q n
      (basisArray (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
        (native_slots rho visit ha pair m ell p hG hGK hm) pc true f) row j x=
    nativeField q n f row j (insert rho visit x
      (fun column => CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
        (address rho visit x column))) := by
  unfold nativeField CompactSpectatorInheritedGrid.decoded
  erw [basisArray_at rho visit ha pair m ell p hG hGK hm pc f row x j]

end Node

section Child
variable {sh : Shape} {left k : ℕ}
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (m ell p : ℕ) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

/-- At the reverse pass's literal input address, the original forward-child
calculation gives the original factor at the unchanged parent address. -/
theorem child_factor_at_original_address (call : ComplexRecursiveCallSchema.Call) (q n : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) (row : Fin m)
    (j : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    let moved := insert rho visit anchor (fun column =>
      CompactComplexBasisTensorConjugation.coordinateMap (ComplexRecursiveCallSchema.edge call.site)
        (address rho visit anchor column))
    let native := nativeField q n
      (basisArray (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
        (native_slots rho visit ha pair m ell p hG hGK hm)
        (CompactComplexRolePhaseSite.pc call.site) false f) row j
    let original := CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor (nativeField q n f row j)
    (if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
      (CompactComplexStoppedLeafTensorSemantics.slice rho
        (CompactComplexNonleafChildAddress.childVisit visit call) moved native)
      (address rho (CompactComplexNonleafChildAddress.childVisit visit call) moved)
    else ComplexEndpoints.fullFrame (arity^k)
      (CompactComplexStoppedLeafTensorSemantics.slice rho
        (CompactComplexNonleafChildAddress.childVisit visit call) moved native)
      (address rho (CompactComplexNonleafChildAddress.childVisit visit call) moved))=
    BinaryColumns.vectorFactor (arity^(k+1)) (CompactComplexActualCallFrameEdge.kernel call)
      original (address rho visit anchor) := by
  dsimp only
  let L := CompactComplexBasisTensorConjugation.coordinateMap (ComplexRecursiveCallSchema.edge call.site)
  let moved := insert rho visit anchor (fun column => L (address rho visit anchor column))
  have h := CompactComplexActualBasisPullback.child_factor_at
    rho visit ha pair m ell p hG hGK hm call q n f row j moved
  have hs : CompactComplexStoppedLeafTensorSemantics.slice rho visit moved (nativeField q n f row j)=
      CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor (nativeField q n f row j) := by
    funext a
    unfold CompactComplexStoppedLeafTensorSemantics.slice
    dsimp only [moved]
    erw [CompactComplexActualBasisPullback.insert_insert]
  have haddr : address rho visit moved=(fun column => L (address rho visit anchor column)) :=
    CompactComplexNonleafChildAddress.address_insert rho visit anchor _
  dsimp only at h
  rw [hs,haddr] at h
  have hcancel : (fun column => L.symm (L (address rho visit anchor column)))=address rho visit anchor := by
    funext column
    exact L.symm_apply_apply _
  change _=BinaryColumns.vectorFactor (arity^(k+1)) (CompactComplexActualCallFrameEdge.kernel call)
    (CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor (nativeField q n f row j))
    (fun column => L.symm (L (address rho visit anchor column))) at h
  rw [hcancel] at h
  exact h

/-- The computed forward basis, a genuine recursive child semantic result,
and the computed inverse basis realize the original residual factor. The
only semantic premise is decoded child tensor correctness, not an execution
callback or an assumed input alignment. -/
theorem returned_factor_at (call : ComplexRecursiveCallSchema.Call) (q before after : ℕ)
    (f result : CompactSpectatorVisitGeometry.Array sh m ell) (row : Fin m)
    (j : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits)
    (hchild : ∀ x : BinaryWalsh.Address sh.bits,
      let native := nativeField q before
        (basisArray (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
          (native_slots rho visit ha pair m ell p hG hGK hm)
          (CompactComplexRolePhaseSite.pc call.site) false f) row j
      nativeField q after result row j x=
        if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
          (CompactComplexStoppedLeafTensorSemantics.slice rho
            (CompactComplexNonleafChildAddress.childVisit visit call) x native)
          (address rho (CompactComplexNonleafChildAddress.childVisit visit call) x)
        else ComplexEndpoints.fullFrame (arity^k)
          (CompactComplexStoppedLeafTensorSemantics.slice rho
            (CompactComplexNonleafChildAddress.childVisit visit call) x native)
          (address rho (CompactComplexNonleafChildAddress.childVisit visit call) x)) :
    nativeField q after
      (basisArray (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
        (native_slots rho visit ha pair m ell p hG hGK hm)
        (CompactComplexRolePhaseSite.pc call.site) true result) row j anchor=
    BinaryColumns.vectorFactor (arity^(k+1)) (CompactComplexActualCallFrameEdge.kernel call)
      (CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor (nativeField q before f row j))
      (address rho visit anchor) := by
  rw [nativeField_at rho visit ha pair m ell p hG hGK hm
    (CompactComplexRolePhaseSite.pc call.site) q after result row j anchor,
    CompactComplexRolePhaseSite.actual_edge,hchild]
  exact child_factor_at_original_address rho visit ha pair m ell p hG hGK hm call q before f row j anchor

end Child
end
end IntegerMultBounds.Machine.CompactComplexActualInverseBasisPullback
