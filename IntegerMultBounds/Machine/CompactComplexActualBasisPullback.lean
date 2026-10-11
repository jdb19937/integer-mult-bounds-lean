import IntegerMultBounds.Machine.CompactComplexActualBasisSlice
import IntegerMultBounds.Machine.CompactComplexChildTensorCoordinateFactor

/-! The literal native basis permutation gives the complete original tensor
slice pullback. The local alignment needed by child tensor conjugation is
derived from the actual row destination and its preserved spectators. -/
namespace IntegerMultBounds.Machine.CompactComplexActualBasisPullback
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactComplexNonleafChildAddress (address insert)
open CompactComplexEndpointCoordinates (rowCoordinates)
open CompactComplexActualBasisSlice (nativeInput native_slots)
open CompactAllAxisPhaseDispatch (count edge)
open RecursiveInterchangeRows (pack)
open Networks
attribute [local irreducible] Networks.ComplexRecursiveCallSchema.sites Networks.ComplexRank25.program

/-- A decoded global-address field at an actual outer row and polynomial index. -/
def nativeField {sh : Shape} {m ell : ℕ} (q n : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) (row : Fin m) (j : Fin (2^ell)) :
    BinaryWalsh.Arrays sh.bits := fun x =>
  CompactSpectatorInheritedGrid.decoded sh m ell q n f (pack row (FlatCoordinateLayout.index x j))

variable {sh : Shape} {left k : ℕ}
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (ha : sh.active≤sh.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (m ell p : ℕ) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

/-- The actual native ordinal of an original outer row and global address. -/
def nativeRow (row : Fin m) (x : BinaryWalsh.Address sh.bits) :
    Fin (ActivePrefixStageTripleWords.count (nativeInput rho visit ha pair m ell p hG hGK hm)) :=
  Fin.cast (NativePolynomialStageShape.count
    (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm).symm
    (pack row (FlatCoordinateLayout.rank x))

theorem nativeRow_val (row : Fin m) (x : BinaryWalsh.Address sh.bits) :
    (nativeRow rho visit ha pair m ell p hG hGK hm row x).val=
      row.val*2^sh.bits+(FlatCoordinateLayout.rank x).val := by
  simp only [nativeRow,Fin.val_cast,RecursiveInterchangeRows.pack_val]

theorem nativeRow_div (row : Fin m) (x : BinaryWalsh.Address sh.bits) :
    (nativeRow rho visit ha pair m ell p hG hGK hm row x).val/2^sh.bits=row.val := by
  rw [nativeRow_val,Nat.mul_comm row.val,Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (FlatCoordinateLayout.rank x).isLt]
  omega

theorem nativeRow_coordinates (row : Fin m) (x : BinaryWalsh.Address sh.bits) :
    rowCoordinates (NativePolynomialStageShape.shape sh ell p)
      (ActivePrefixStageNativePairCoordinates.start
        (nativeInput rho visit ha pair m ell p hG hGK hm)
        (nativeRow rho visit ha pair m ell p hG hGK hm row x))=x := by
  have hp : 0<(NativePolynomialStageShape.shape sh ell p).payload := by
    have h := (nativeInput rho visit ha pair m ell p hG hGK hm).hrecord
    omega
  have hmod : (nativeRow rho visit ha pair m ell p hG hGK hm row x).val%2^sh.bits=
      (FlatCoordinateLayout.rank x).val := by
    rw [nativeRow_val,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,
      Nat.mod_eq_of_lt (FlatCoordinateLayout.rank x).isLt,Nat.mod_eq_of_lt (FlatCoordinateLayout.rank x).isLt]
  unfold rowCoordinates
  simp only [ActivePrefixStageNativePairCoordinates.start,Nat.mul_div_cancel _ hp]
  have hfin : (⟨(nativeRow rho visit ha pair m ell p hG hGK hm row x).val%2^sh.bits,
      Nat.mod_lt _ (by positivity)⟩ : Fin (2^sh.bits))=FlatCoordinateLayout.rank x := Fin.ext hmod
  change FlatCoordinateLayout.coordinates _=x
  erw [hfin,FlatCoordinateLayout.coordinates_rank]

/-- Every actual basis output has exactly the original outer row and the
global address with just the selected tensor coordinates transformed. -/
theorem run_nativeRow (pc : Fin count) (row : Fin m) (x : BinaryWalsh.Address sh.bits) :
    ActivePrefixStageNativePairCoordinates.run (nativeInput rho visit ha pair m ell p hG hGK hm)
      (CompactNativeConjugatedPhase.ops (nativeInput rho visit ha pair m ell p hG hGK hm)
        (native_slots rho visit ha pair m ell p hG hGK hm) pc)
      (nativeRow rho visit ha pair m ell p hG hGK hm row x)=
    nativeRow rho visit ha pair m ell p hG hGK hm row
      (insert rho visit x (fun column => CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
        (address rho visit x column))) := by
  let d := nativeInput rho visit ha pair m ell p hG hGK hm
  let r := nativeRow rho visit ha pair m ell p hG hGK hm row x
  let ops := CompactNativeConjugatedPhase.ops d (native_slots rho visit ha pair m ell p hG hGK hm) pc
  have houter := ActivePrefixStageNativeFrameCoordinates.native_outer_row d ops r
  have hcoords := CompactComplexActualBasisSlice.node_row_destination rho visit ha pair m ell p hG hGK hm pc r
  have hin := nativeRow_coordinates rho visit ha pair m ell p hG hGK hm row x
  dsimp only [r] at hcoords
  simp only [hin] at hcoords
  have hp : 0<(NativePolynomialStageShape.shape sh ell p).payload := by have h := d.hrecord; omega
  have hmod := congrArg (fun x => (FlatCoordinateLayout.rank x).val) hcoords
  simp only [rowCoordinates,FlatCoordinateLayout.rank_coordinates,Fin.val_mk,
    ActivePrefixStageNativePairCoordinates.start,Nat.mul_div_cancel _ hp] at hmod
  change (ActivePrefixStageNativePairCoordinates.run d ops r).val/2^sh.bits=r.val/2^sh.bits at houter
  rw [nativeRow_div] at houter
  apply Fin.ext
  calc
    _ = (ActivePrefixStageNativePairCoordinates.run d ops r).val%2^sh.bits+
        2^sh.bits*((ActivePrefixStageNativePairCoordinates.run d ops r).val/2^sh.bits) :=
      (Nat.mod_add_div _ _).symm
    _ = _ := by
      erw [hmod,houter,nativeRow_val]
      simp only [Nat.mul_comm,Nat.add_comm]
      rfl

theorem coefficientIndex_nativeRow (row : Fin m) (x : BinaryWalsh.Address sh.bits)
    (j : Fin (2^ell)) :
    CompactComplexActualBasisCoordinates.coefficientIndex
      (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (nativeRow rho visit ha pair m ell p hG hGK hm row x) j=
      pack row (FlatCoordinateLayout.index x j) := by
  apply Fin.ext
  have hc : (CompactComplexActualBasisCoordinates.coefficientIndex
      (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (nativeRow rho visit ha pair m ell p hG hGK hm row x) j).val=
      j.val+2^ell*(nativeRow rho visit ha pair m ell p hG hGK hm row x).val := rfl
  rw [hc,RecursiveInterchangeRows.pack_val,FlatCoordinateLayout.index_val,nativeRow_val]
  ring

/-- Exact stored coefficients at every original row, address and polynomial
index, with no supplied reshape or local alignment equality. -/
theorem basisArray_output_layout (pc : Fin count) (f : CompactSpectatorVisitGeometry.Array sh m ell)
    (row : Fin m) (x : BinaryWalsh.Address sh.bits) (j : Fin (2^ell)) :
    CompactComplexSourceReadyReachedBasisInvariant.basisArray
      (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (native_slots rho visit ha pair m ell p hG hGK hm) pc false f
      (pack row (FlatCoordinateLayout.index
        (insert rho visit x (fun column => CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
          (address rho visit x column))) j))=
    f (pack row (FlatCoordinateLayout.index x j)) := by
  have h := CompactComplexActualBasisCoordinates.basisArray_destination
    (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
    (native_slots rho visit ha pair m ell p hG hGK hm) pc f
    (nativeRow rho visit ha pair m ell p hG hGK hm row x) j
  erw [run_nativeRow rho visit ha pair m ell p hG hGK hm pc row x,
    coefficientIndex_nativeRow,coefficientIndex_nativeRow] at h
  exact h

/-- Replacing selected coordinates twice retains the original spectators. -/
theorem insert_insert (anchor : BinaryWalsh.Address sh.bits)
    (a b : BinaryColumns.Address arity (arity^k)) :
    insert rho visit (insert rho visit anchor a) b=insert rho visit anchor b := by
  funext t
  by_cases ht : ∃ i,CompactComplexNonleafChildAddress.axis rho visit i=t
  · obtain ⟨i,rfl⟩ := ht
    obtain ⟨⟨slot,column⟩,rfl⟩ := CompactComplexStoppedLeafTensorSemantics.axisIndex_surjective (k:=k) i
    rw [CompactComplexNonleafChildAddress.insert_axis,CompactComplexNonleafChildAddress.insert_axis]
  · rw [CompactComplexNonleafChildAddress.insert_frame rho visit _ _ t ht,
      CompactComplexNonleafChildAddress.insert_frame rho visit _ _ t ht,
      CompactComplexNonleafChildAddress.insert_frame rho visit _ _ t ht]

/-- The actual basis array at an arbitrary original address is its input at
the inverse coordinate map, with both outer row and polynomial index retained. -/
theorem basisArray_at (pc : Fin count) (f : CompactSpectatorVisitGeometry.Array sh m ell)
    (row : Fin m) (x : BinaryWalsh.Address sh.bits) (j : Fin (2^ell)) :
    CompactComplexSourceReadyReachedBasisInvariant.basisArray
      (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
      (native_slots rho visit ha pair m ell p hG hGK hm) pc false f
      (pack row (FlatCoordinateLayout.index x j))=
    f (pack row (FlatCoordinateLayout.index
      (insert rho visit x (fun column => (CompactComplexBasisTensorConjugation.coordinateMap (edge pc)).symm
        (address rho visit x column))) j)) := by
  let L := CompactComplexBasisTensorConjugation.coordinateMap (edge pc)
  let pre := insert rho visit x (fun column => L.symm (address rho visit x column))
  have h := basisArray_output_layout rho visit ha pair m ell p hG hGK hm pc f row pre j
  have he : insert rho visit pre (fun column => L (address rho visit pre column))=x := by
    dsimp only [pre]
    have haddr := CompactComplexNonleafChildAddress.address_insert rho visit x
      (fun column => L.symm (address rho visit x column))
    erw [haddr]
    have hcancel : (fun column => L (L.symm (address rho visit x column)))=address rho visit x := by
      funext column
      exact L.apply_symm_apply _
    erw [hcancel,insert_insert,CompactComplexNonleafChildAddress.insert_address]
  erw [he] at h
  exact h

/-- Exact decoded pullback, at every inherited denominator. -/
theorem nativeField_at (pc : Fin count) (q n : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) (row : Fin m)
    (j : Fin (2^ell)) (x : BinaryWalsh.Address sh.bits) :
    nativeField q n
      (CompactComplexSourceReadyReachedBasisInvariant.basisArray
        (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
        (native_slots rho visit ha pair m ell p hG hGK hm) pc false f) row j x=
    nativeField q n f row j (insert rho visit x
      (fun column => (CompactComplexBasisTensorConjugation.coordinateMap (edge pc)).symm
        (address rho visit x column))) := by
  unfold nativeField CompactSpectatorInheritedGrid.decoded
  erw [basisArray_at rho visit ha pair m ell p hG hGK hm pc f row x j]

/-- The child tensor's local alignment is a theorem about the actual basis
output, rather than an assumption on a separately chosen native field. -/
theorem slice_pullback (pc : Fin count) (q n : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) (row : Fin m)
    (j : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor
      (nativeField q n
        (CompactComplexSourceReadyReachedBasisInvariant.basisArray
          (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
          (native_slots rho visit ha pair m ell p hG hGK hm) pc false f) row j)=
    CompactComplexBasisTensorConjugation.pullback
      (CompactComplexBasisTensorConjugation.coordinateMap (edge pc)).symm
      (CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor (nativeField q n f row j)) := by
  funext a
  have h := nativeField_at rho visit ha pair m ell p hG hGK hm pc q n f row j (insert rho visit anchor a)
  have haddr := CompactComplexNonleafChildAddress.address_insert rho visit anchor a
  erw [haddr,insert_insert] at h
  exact h

end

noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactComplexNonleafChildAddress (address)
open CompactComplexActualBasisSlice (native_slots)
open Networks
variable {sh : Shape} {left k : ℕ}

/-- The original residual factor follows from the actual basis array. No
local alignment callback is required; recursive child execution is separate. -/
theorem child_factor_at (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (m ell p : ℕ) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)
    (call : ComplexRecursiveCallSchema.Call) (q n : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) (row : Fin m)
    (j : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    let native := nativeField q n
      (CompactComplexSourceReadyReachedBasisInvariant.basisArray
        (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) m ell p hG hGK hm
        (native_slots rho visit ha pair m ell p hG hGK hm)
        (CompactComplexRolePhaseSite.pc call.site) false f) row j
    let original := CompactComplexStoppedLeafTensorSemantics.slice rho visit anchor (nativeField q n f row j)
    (if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
      (CompactComplexStoppedLeafTensorSemantics.slice rho
        (CompactComplexNonleafChildAddress.childVisit visit call) anchor native)
      (address rho (CompactComplexNonleafChildAddress.childVisit visit call) anchor)
    else ComplexEndpoints.fullFrame (arity^k)
      (CompactComplexStoppedLeafTensorSemantics.slice rho
        (CompactComplexNonleafChildAddress.childVisit visit call) anchor native)
      (address rho (CompactComplexNonleafChildAddress.childVisit visit call) anchor))=
    BinaryColumns.vectorFactor (arity^(k+1)) (CompactComplexActualCallFrameEdge.kernel call) original
      (fun column => (CompactComplexBasisTensorConjugation.coordinateMap
        (ComplexRecursiveCallSchema.edge call.site)).symm (address rho visit anchor column)) := by
  dsimp only
  have haligned := slice_pullback rho visit ha pair m ell p hG hGK hm
    (CompactComplexRolePhaseSite.pc call.site) q n f row j anchor
  rw [CompactComplexRolePhaseSite.actual_edge] at haligned
  exact CompactComplexChildTensorCoordinateFactor.tensor_original_factor_at rho visit call anchor _ _ haligned

end
end IntegerMultBounds.Machine.CompactComplexActualBasisPullback
