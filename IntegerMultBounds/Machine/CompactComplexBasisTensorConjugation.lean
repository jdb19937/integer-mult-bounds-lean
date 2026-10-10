import IntegerMultBounds.Machine.CompactComplexActualCallFrameEdge

/-! Exact coordinate changes of the column translation tensors. The inverse
coordinate map carries each canonical slot back to its literal basis vector. -/
namespace IntegerMultBounds.Machine.CompactComplexBasisTensorConjugation
noncomputable section
open Networks Module
open BinaryColumns
variable {h columns : ℕ}

/-- Relabel every parent column by the same actual binary coordinate map. -/
def pullback (L : BinaryWalsh.Address h ≃ₗ[ZMod 2] BinaryWalsh.Address h)
    (f : Arrays h columns) : Arrays h columns := fun x => f (fun j => L (x j))

theorem map_shift (L : BinaryWalsh.Address h ≃ₗ[ZMod 2] BinaryWalsh.Address h)
    (j : Fin columns) (v : BinaryWalsh.Address h) (x : Address h columns) :
    (fun i => L (shift j v x i))=shift j (L v) (fun i => L (x i)) := by
  funext i
  by_cases hi : i=j
  · subst i
    simp only [shift,Function.update_self,map_add]
  · simp only [shift,Function.update_of_ne hi]

theorem columnKernel_pullback
    (L : BinaryWalsh.Address h ≃ₗ[ZMod 2] BinaryWalsh.Address h)
    (j : Fin columns) (q : ZMod 4) (v : BinaryWalsh.Address h) (f : Arrays h columns) :
    columnKernel j q v (pullback L f)=pullback L (columnKernel j q (L v) f) := by
  funext x
  simp only [columnKernel_apply,pullback,map_shift]

theorem vectorFactor_pullback
    (L : BinaryWalsh.Address h ≃ₗ[ZMod 2] BinaryWalsh.Address h)
    (q : ZMod 4) (v : BinaryWalsh.Address h) (f : Arrays h columns) :
    vectorFactor columns (q,v) (pullback L f)=pullback L (vectorFactor columns (q,L v) f) := by
  have hp (js : List (Fin columns)) (g : Arrays h columns) :
      (js.map (fun j => columnKernel j q v)).prod (pullback L g)=
        pullback L ((js.map (fun j => columnKernel j q (L v))).prod g) := by
    induction js with
    | nil => rfl
    | cons j js ih =>
      simp only [List.map_cons,List.prod_cons]
      change columnKernel j q v ((js.map (fun j => columnKernel j q v)).prod (pullback L g)) = _
      rw [ih,columnKernel_pullback]
      rfl
  simpa only [List.map_ofFn,Function.comp_def,id_eq,vectorFactor] using hp (List.ofFn id) f

@[simp] theorem pullback_inverse
    (L : BinaryWalsh.Address h ≃ₗ[ZMod 2] BinaryWalsh.Address h) (f : Arrays h columns) :
    pullback L (pullback L.symm f)=f := by
  funext x
  simp only [pullback,LinearEquiv.symm_apply_apply]

/-- Undoing the actual basis permutation after a coordinate tensor gives
exactly the kernel in the corresponding original basis direction. -/
theorem conjugate_vectorFactor
    (L : BinaryWalsh.Address h ≃ₗ[ZMod 2] BinaryWalsh.Address h)
    (q : ZMod 4) (v : BinaryWalsh.Address h) (f : Arrays h columns) :
    pullback L (vectorFactor columns (q,v) (pullback L.symm f))=
      vectorFactor columns (q,L.symm v) f := by
  rw [vectorFactor_pullback,pullback_inverse]

/-- The inverse coordinate map of a basis sends a standard coordinate vector
to the same literal basis vector; no unspecified row alignment is assumed. -/
theorem basis_inverse_single (b : Basis (Fin h) (ZMod 2) (BinaryWalsh.Address h))
    (i : Fin h) : b.equivFun.symm (Pi.single i 1)=b i := by
  rw [Basis.equivFun_symm_apply]
  simp

open ComplexPhaseRowSchedule (Edge low high)

/-- Coordinate map realized by the literal chosen ambient row word. -/
def coordinateMap (e : Edge) : BinaryWalsh.Address (25^3) ≃ₗ[ZMod 2] BinaryWalsh.Address (25^3) :=
  (BinaryPhaseBasisExtension.ambientBasis (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
    (BinaryPhaseResidualRowProgram.W (low e) (high e))
    (ProjectionRank.residual_nondegenerate (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
      (low e) (high e) (ComplexPhaseRowSchedule.low_nondegenerate e)
      (ComplexPhaseRowSchedule.high_nondegenerate e) (ComplexPhaseRowSchedule.comparable e))
    (BinaryPhaseResidualRowProgram.basis ComplexPhaseBudget.coordinateSymm
      (low e) (high e) (ComplexPhaseRowSchedule.low_nondegenerate e)
      (ComplexPhaseRowSchedule.high_nondegenerate e) (ComplexPhaseRowSchedule.comparable e)
      (ComplexPhaseRowSchedule.residual_good e))).equivFun

theorem coordinateMap_word (e : Edge) (x : BinaryWalsh.Address (25^3)) :
    BinaryRowProgram.run (ComplexPhaseRowSchedule.word e) x=coordinateMap e x :=
  BinaryPhaseBasisExtension.word_run _ _ _ _ _ x

theorem coordinateMap_call_slot (call : ComplexRecursiveCallSchema.Call) :
    (coordinateMap (ComplexRecursiveCallSchema.edge call.site)).symm (Pi.single call.slot 1)=
      CompactComplexActualCallFrameEdge.basisVector (ComplexRecursiveCallSchema.edge call.site) call.coordinate := by
  unfold coordinateMap
  rw [basis_inverse_single]
  exact BinaryPhaseBasisExtension.retains _ _ _ _ _ call.coordinate

/-- Literal signed recursive slot factor, after undoing the literal basis
word, is the actual coordinate kernel in the original frame-edge product. -/
theorem actual_call_factor (call : ComplexRecursiveCallSchema.Call)
    (f : Arrays (25^3) columns) :
    pullback (coordinateMap (ComplexRecursiveCallSchema.edge call.site))
      (vectorFactor columns (if call.inverse then -1 else 1,Pi.single call.slot 1)
        (pullback (coordinateMap (ComplexRecursiveCallSchema.edge call.site)).symm f))=
      vectorFactor columns (CompactComplexActualCallFrameEdge.kernel call) f := by
  rw [conjugate_vectorFactor,coordinateMap_call_slot,CompactComplexActualCallFrameEdge.kernel_inverse]

end
end IntegerMultBounds.Machine.CompactComplexBasisTensorConjugation
