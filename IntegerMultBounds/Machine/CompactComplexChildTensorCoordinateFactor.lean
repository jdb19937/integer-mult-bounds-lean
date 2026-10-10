import IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics
import IntegerMultBounds.Machine.CompactComplexActualCallFrameEdge
import IntegerMultBounds.Machine.CompactComplexBasisTensorConjugation

/-! Child-selected native coordinates are precisely one parent slot across
all parent columns. Their genuine forward/inverse tensor is the corresponding
coordinate vector factor, retaining every surrounding native spectator. -/
namespace IntegerMultBounds.Machine.CompactComplexChildTensorCoordinateFactor
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexNonleafChildAddress (axis axisIndex address insert childVisit)
open CompactComplexStoppedLeafTensorSemantics (slice globalKernels tensorProduct)
variable {sh : Shape} {left k : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites

abbrev callSlot (call : ComplexRecursiveCallSchema.Call) : Fin arity := call.slot

/-- Actual child interval selects its call's parent slot, not a renamed
or permuted interval. The parent's remaining column coordinate is literal. -/
theorem child_axis (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (i : Fin (arity^(k+1))) :
    axis rho (childVisit visit call) i=axis rho visit (axisIndex (callSlot call) i) := by
  apply Fin.ext
  have hi : (axisIndex (callSlot call) i).val=(callSlot call).val*arity^(k+1)+i.val := by
    simp only [axisIndex,Fin.val_cast]
    exact @RecursiveInterchangeRows.pack_val arity (arity^(k+1)) (callSlot call) i
  simp only [axis,ButterflyAxisWalsh.coordinate,Fin.val_rev,CompactSpectatorVisitGeometry.selected,hi]
  simp only [Nat.add_assoc]

def slotSteps (slot : Fin arity) : List (CompactComplexStoppedLeafTensorSemantics.Step (k+1)) :=
  List.ofFn (fun column : Fin (arity^(k+1)) => ((1 : ZMod 4),(slot,column)))

theorem child_directions (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) :
    CompactSpectatorLeafSemantics.directions sh rho (childVisit visit call) (arity^(k+1)) le_rfl=
      globalKernels rho visit (slotSteps (callSlot call)) := by
  simp only [CompactSpectatorLeafSemantics.directions,globalKernels,slotSteps,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change ((1 : ZMod 4),ButterflyAxisWalsh.direction sh.bits
    (CompactSpectatorLeafSemantics.position sh rho (childVisit visit call) i) _) =
      (1,Pi.single (axis rho visit (axisIndex (callSlot call) i)) 1)
  rw [←child_axis]
  rfl

/-- The actual child leaf kernel list, viewed on the parent interval, is
one coordinate vector factor across every parent column. -/
theorem parent_slice_child_kernels (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (anchor : BinaryWalsh.Address sh.bits)
    (f : BinaryWalsh.Arrays sh.bits) :
    slice rho visit anchor (BinaryWalsh.kernelRun
      (CompactSpectatorLeafSemantics.directions sh rho (childVisit visit call) (arity^(k+1)) le_rfl) f)=
      BinaryColumns.vectorFactor (arity^(k+1)) (1,Pi.single (callSlot call) 1)
        (slice rho visit anchor f) := by
  rw [child_directions rho visit call]
  rw [CompactComplexStoppedLeafTensorSemantics.slice_kernelRun rho visit anchor (slotSteps (callSlot call)) f]
  simp only [tensorProduct,slotSteps,List.map_ofFn,Function.comp_def,BinaryColumns.vectorFactor]

/-- The recursive forward child tensor evaluated at its real native output
address is the exact parent coordinate factor at that same address. -/
theorem forward_at (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (anchor : BinaryWalsh.Address sh.bits)
    (f : BinaryWalsh.Arrays sh.bits) :
    ComplexEndpoints.fullFrame (arity^k) (slice rho (childVisit visit call) anchor f)
      (address rho (childVisit visit call) anchor)=
    BinaryColumns.vectorFactor (arity^(k+1)) (1,Pi.single (callSlot call) 1)
      (slice rho visit anchor f) (address rho visit anchor) := by
  have hc := congrFun (CompactComplexStoppedLeafTensorSemantics.forward_kernel_tensor
    rho (childVisit visit call) anchor f) (address rho (childVisit visit call) anchor)
  have hp := congrFun (parent_slice_child_kernels rho visit call anchor f) (address rho visit anchor)
  simp only [slice,CompactComplexNonleafChildAddress.insert_address] at hc hp
  exact hc.symm.trans hp

private theorem vectorFactor_conjugate {h columns : ℕ} (q : ZMod 4)
    (v : BinaryWalsh.Address h) (f : BinaryColumns.Arrays h columns) :
    BinaryColumnConjugation.conjugate (BinaryColumns.vectorFactor columns (q,v) f)=
      BinaryColumns.vectorFactor columns (-q,v) (BinaryColumnConjugation.conjugate f) := by
  have he := BinaryColumnConjugation.tensor_conjugate (BinaryWalsh.kernel q v)
    (BinaryWalsh.kernel (-q) v) (BinaryWalshComplexConjugation.kernel_conjugate q v) f
  simpa only [BinaryColumns.tensorColumns,List.map_ofFn,BinaryColumns.liftColumn_kernel,
    BinaryColumns.vectorFactor] using he

private theorem slice_conjugate (rho : Fin sh.chunk) {exponent start : ℕ}
    (visit : Visit sh.active start (exponent+1)) (anchor : BinaryWalsh.Address sh.bits)
    (f : BinaryWalsh.Arrays sh.bits) :
    slice rho visit anchor (BinaryWalshComplexConjugation.conjugate f)=
      BinaryColumnConjugation.conjugate (slice rho visit anchor f) := rfl

/-- The inverse recursive child realizes the negative coordinate factor,
using exactly the same native input/output addresses and spectators. -/
theorem inverse_at (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (anchor : BinaryWalsh.Address sh.bits)
    (f : BinaryWalsh.Arrays sh.bits) :
    (ComplexEndpoints.fullFrame (arity^k)).symm (slice rho (childVisit visit call) anchor f)
      (address rho (childVisit visit call) anchor)=
    BinaryColumns.vectorFactor (arity^(k+1)) (-1,Pi.single (callSlot call) 1)
      (slice rho visit anchor f) (address rho visit anchor) := by
  have h := forward_at rho visit call anchor (BinaryWalshComplexConjugation.conjugate f)
  rw [slice_conjugate,slice_conjugate] at h
  have hc := BinaryColumnConjugation.frame_conjugate BinaryPhase.weightPhase
    (BinaryColumnConjugation.conjugate (slice rho (childVisit visit call) anchor f))
  rw [BinaryColumnConjugation.conjugate_twice] at hc
  have hv := @vectorFactor_conjugate arity (arity^(k+1)) (1 : ZMod 4) (Pi.single (callSlot call) 1)
    (BinaryColumnConjugation.conjugate (slice rho visit anchor f))
  have hv' : BinaryColumnConjugation.conjugate
      (BinaryColumns.vectorFactor (arity^(k+1)) (1,Pi.single (callSlot call) 1)
        (BinaryColumnConjugation.conjugate (slice rho visit anchor f)))=
      BinaryColumns.vectorFactor (arity^(k+1)) (-1,Pi.single (callSlot call) 1) (slice rho visit anchor f) := by
    simpa only [BinaryColumnConjugation.conjugate_twice] using hv
  exact (congrFun hc (address rho (childVisit visit call) anchor)).symm.trans
    ((congrArg star h).trans (congrFun hv' (address rho visit anchor)))

/-- The actual saved call direction selects the correct signed parent
coordinate vector factor. This is the exact local recursive tensor IH. -/
theorem tensor_at (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (anchor : BinaryWalsh.Address sh.bits)
    (f : BinaryWalsh.Arrays sh.bits) :
    (if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
      (slice rho (childVisit visit call) anchor f) (address rho (childVisit visit call) anchor)
    else ComplexEndpoints.fullFrame (arity^k)
      (slice rho (childVisit visit call) anchor f) (address rho (childVisit visit call) anchor))=
    BinaryColumns.vectorFactor (arity^(k+1)) (if call.inverse then -1 else 1,Pi.single (callSlot call) 1)
      (slice rho visit anchor f) (address rho visit anchor) := by
  cases hi : call.inverse
  · exact forward_at rho visit call anchor f
  · exact inverse_at rho visit call anchor f

/-- With the actual basis-aligned parent input, the child's native tensor is
exactly the literal original residual factor. The input premise is a local
coordinate alignment, rather than a whole-network correctness assumption. -/
theorem tensor_original_factor_at (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (anchor : BinaryWalsh.Address sh.bits)
    (native : BinaryWalsh.Arrays sh.bits) (original : BinaryColumns.Arrays arity (arity^(k+1)))
    (haligned : slice rho visit anchor native=
      CompactComplexBasisTensorConjugation.pullback
        (CompactComplexBasisTensorConjugation.coordinateMap (ComplexRecursiveCallSchema.edge call.site)).symm
        original) :
    (if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
      (slice rho (childVisit visit call) anchor native) (address rho (childVisit visit call) anchor)
    else ComplexEndpoints.fullFrame (arity^k)
      (slice rho (childVisit visit call) anchor native) (address rho (childVisit visit call) anchor))=
    BinaryColumns.vectorFactor (arity^(k+1)) (CompactComplexActualCallFrameEdge.kernel call) original
      (fun j => (CompactComplexBasisTensorConjugation.coordinateMap
        (ComplexRecursiveCallSchema.edge call.site)).symm (address rho visit anchor j)) := by
  rw [tensor_at rho visit call anchor native,haligned]
  have h := CompactComplexBasisTensorConjugation.vectorFactor_pullback
    (CompactComplexBasisTensorConjugation.coordinateMap (ComplexRecursiveCallSchema.edge call.site)).symm
    (if call.inverse then (-1 : ZMod 4) else 1) (Pi.single call.slot 1) original
  rw [CompactComplexBasisTensorConjugation.coordinateMap_call_slot,
    ←CompactComplexActualCallFrameEdge.kernel_inverse] at h
  exact congrFun h (address rho visit anchor)

end
end IntegerMultBounds.Machine.CompactComplexChildTensorCoordinateFactor
