module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.AllCalls

/-! Programs of the non-local unit operations. A phase over a port basis is the product of the
kernels of its nonzero coefficients; a shear is one rational gate; the signed exchange is three
rational gates. Each program acts exactly as its unit operation. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Multiplicative FramedCircuit

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-! ### Phases -/

/-- The kernels of a phase over a basis, one per coordinate. -/
noncomputable def phasePrims (B : Fin 73 → Addr) (c : Fin 73 → ZMod 4) : List Prim :=
  (List.finRange 73).map fun k => .kernel (c k) (B k)

theorem wordLin_phasePrims (B : Fin 73 → Addr) (c : Fin 73 → ZMod 4) :
    wordLin (phasePrims B c) = basisOp B (ofAdd c) := by
  have key : ∀ (L : List (Fin 73)), L.Nodup →
      wordLin (L.map fun k => .kernel (c k) (B k)) =
        basisOp B (ofAdd (∑ k ∈ L.toFinset, Pi.single k (c k))) := by
    intro L hL
    induction L with
    | nil => simp [wordLin]
    | cons a L ih =>
      have hnd := List.nodup_cons.mp hL
      rw [List.map_cons, wordLin, ih hnd.2, List.toFinset_cons,
        Finset.sum_insert (by simpa using hnd.1), ofAdd_add, map_mul, basisOp_single]
      have hc : Commute (basisOp B (ofAdd (∑ k ∈ L.toFinset, Pi.single k (c k))))
          (BinaryWalsh.kernel (c a) (B a)) := by
        rw [← basisOp_single]
        exact Commute.map (Commute.all _ _) _
      exact hc.eq
  rw [phasePrims, key _ (List.nodup_finRange 73), List.toFinset_finRange, Finset.univ_sum_single]

/-! ### Unit operations -/

/-- The program of one unit operation. -/
noncomputable def unitProgram : UnitOp → List (TInstr NodeUnit)
  | .phase u a v => (phasePrims (portBasis (portData a)) v.toFun).map (TInstr.prim u)
  | .shear d s c => [.gate ⟨d, [(s, (c : ℚ))]⟩]
  | .exchange x w => [.gate ⟨x, [(w, 1)]⟩, .gate ⟨w, [(x, -1)]⟩, .gate ⟨x, [(w, 1)]⟩]

/-- An exchange of two distinct units. -/
def unitProper : UnitOp → Prop
  | .exchange x w => x ≠ w
  | _ => True

/-- **Unit operations.** -/
theorem unitProgram_run (o : UnitOp) (ho : unitProper o) (y : NodeUnit → S) :
    runT ρ (unitProgram o) y = o.run (portRep ρ) y := by
  cases o with
  | phase u a v =>
    rw [unitProgram, runT_prims, wordLin_phasePrims]
    rfl
  | shear d s c =>
    change moduleGate _ y = _
    simp only [moduleGate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      UnitOp.run]
    congr 2
    exact Int.cast_smul_eq_zsmul ℚ c (y s)
  | exchange x w =>
    have hxw : x ≠ w := ho
    funext v
    change moduleGate _ (moduleGate _ (moduleGate _ y)) v = _
    simp only [moduleGate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      one_smul, neg_one_smul, UnitOp.run]
    by_cases hv : v = w
    · subst hv
      simp [Function.update_of_ne hxw, Function.update_of_ne (Ne.symm hxw)]
    · by_cases hv' : v = x
      · subst hv'
        simp [Function.update_of_ne hxw, Function.update_of_ne (Ne.symm hxw)]
      · simp [Function.update_of_ne hv, Function.update_of_ne hv']

end IntegerMultBounds.Networks.Certificates.T16.Impl
