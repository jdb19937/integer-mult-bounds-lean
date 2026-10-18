module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Data

/-! Helper registers. A helper hosts a slice of its family: the word must apply `C` on the
slice's basis axes and leave the family otherwise unchanged. Its chart orders its port basis
with the slice axes first, so the slice becomes the C gates on the first `w` local coordinates.
The helper's own word transition lowers as `R · C_w · L` with monomial words `L` and `R`
(`Realization.lowering`); wrapping the helper by `L⁻¹` before and `R⁻¹` after leaves exactly
the C gates of the slice, whatever frame the family is in. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli Multiplicative

/-! ### The split lowering of a realization -/

theorem Realization.scalar_ne_zero_smul (K : Realization) {κ : ℂ} {g : State → State}
    (h : ∀ f, K.scalar f = κ • g f) : κ ≠ 0 := by
  intro hκ
  have hf : (Pi.single 0 1 : State) ≠ 0 := by
    intro e
    have := congrFun e 0
    simp at this
  apply hf
  have h0 : K.scalar (Pi.single 0 1) = 0 := by rw [h, hκ, zero_smul]
  rw [← K.scalar.symm_apply_apply (Pi.single 0 1), h0, map_zero]

/-- **Split lowering.** Every realization is a monomial word, the C gates on the first `r`
local coordinates and another monomial word, with `r` its X-block rank. -/
theorem Realization.exists_split (K : Realization) :
    ∃ Lw Rw : List Prim, (∀ p ∈ Lw ++ Rw, p.Invertible) ∧ childCount Lw = 0 ∧
      childCount Rw = 0 ∧
      Lowers K (Lw ++ cPrims (Module.finrank Geometry.F (Tableau.xRange K.binary)) ++ Rw) := by
  obtain ⟨A₂, G, S₂, S, hS₂, hS, c, κ, h⟩ := K.lowering
  set r := Module.finrank Geometry.F (Tableau.xRange K.binary)
  have hκ : κ ≠ 0 := Realization.scalar_ne_zero_smul K h
  have hl := lowers_smul_operator κ c h
    ((lowers_monomial A₂ S₂ hS₂).then ((lowers_hadamard r).then
      ((lowers_shear S hS).then (lowers_permutation G))))
  refine ⟨[Prim.perm (liftGL A₂), .diag (fun x => qValue (shearMatrix S₂)
      (defaultAlpha (shearMatrix S₂)) (lowPart x)),
      .diag (fun x => qValue (shearMatrix (Tableau.cut r))
        (defaultAlpha (shearMatrix (Tableau.cut r))) (lowPart x))],
    [.diag (fun x => qValue (shearMatrix (Tableau.cut r))
        (defaultAlpha (shearMatrix (Tableau.cut r))) (lowPart x)),
      .diag (fun x => qValue (shearMatrix S) (defaultAlpha (shearMatrix S)) (lowPart x)),
      .perm (liftGL G)] ++ (pauliPrims c ++ [.scale κ]), ?_, rfl, rfl, ?_⟩
  · intro p hp
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, pauliPrims] at hp
    rcases hp with ((rfl | rfl | rfl) | ((rfl | rfl | rfl) | (rfl | rfl | rfl) | rfl)) <;>
      first | trivial | exact phase_ne_zero c.phase
  · intro f
    rw [hl f]
    simp only [hadamardPrims, List.append_assoc, List.cons_append, List.nil_append]

theorem wordOp_invPrims_right (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) (f : Arrays 73) :
    wordOp ws (wordOp (invPrims ws) f) = f := by
  have hinv : invPrims (invPrims ws) = ws := by
    simp only [invPrims, List.map_reverse, List.map_map, List.reverse_reverse]
    conv_rhs => rw [← List.map_id ws]
    apply List.map_congr_left
    intro p _
    cases p <;> simp [Prim.inv]
  have hinv' : ∀ p ∈ invPrims ws, p.Invertible := by
    intro p hp
    simp only [invPrims, List.mem_reverse, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := hws q hq
    cases q <;> simp_all [Prim.inv, Prim.Invertible]
  have h := wordOp_invPrims (invPrims ws) hinv' f
  rwa [hinv] at h

theorem wordLin_invPrims_mul (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) :
    wordLin (invPrims ws) * wordLin ws = 1 :=
  LinearMap.ext fun f => by
    rw [Module.End.mul_apply, wordLin_apply, wordLin_apply, wordOp_invPrims ws hws]; rfl

theorem wordLin_mul_invPrims (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) :
    wordLin ws * wordLin (invPrims ws) = 1 :=
  LinearMap.ext fun f => by
    rw [Module.End.mul_apply, wordLin_apply, wordLin_apply, wordOp_invPrims_right ws hws]; rfl

theorem wordLin_append (ps qs : List Prim) : wordLin (ps ++ qs) = wordLin qs * wordLin ps :=
  LinearMap.ext fun f => by
    rw [Module.End.mul_apply, wordLin_apply, wordLin_apply, wordLin_apply, wordOp_append]

/-! ### The helper chart -/

/-- Basis indices in a mask, then the others. -/
def maskOrder (m : ℕ) : List (Fin 73) :=
  (List.finRange 73).filter (fun k : Fin 73 => m.testBit k.val) ++
    (List.finRange 73).filter (fun k : Fin 73 => !m.testBit k.val)

/-- The basis indices in a mask. -/
def maskIndices (m : ℕ) : List (Fin 73) := (List.finRange 73).filter fun k : Fin 73 => m.testBit k.val

theorem maskOrder_nodup (m : ℕ) : (maskOrder m).Nodup := by
  rw [maskOrder, List.nodup_append]
  refine ⟨(List.nodup_finRange 73).filter _, (List.nodup_finRange 73).filter _, ?_⟩
  intro a ha b hb e
  subst e
  simp_all

theorem mem_maskOrder (m : ℕ) (k : Fin 73) : k ∈ maskOrder m := by
  by_cases h : m.testBit k <;> simp [maskOrder, h]

theorem maskOrder_length (m : ℕ) : (maskOrder m).length = 73 := by
  have h := (maskOrder_nodup m).length_le_card
  have h' : (List.finRange 73).length ≤ (maskOrder m).length := by
    apply List.Subperm.length_le
    exact List.subperm_of_subset (List.nodup_finRange 73) (fun k _ => mem_maskOrder m k)
  simp at h h'
  omega

/-- The permutation listing a mask's indices first. -/
noncomputable def maskPerm (m : ℕ) : Equiv.Perm (Fin 73) :=
  (finCongr (maskOrder_length m).symm).trans
    ((maskOrder_nodup m).getEquivOfForallMemList _ (mem_maskOrder m))

theorem maskPerm_apply (m : ℕ) (j : Fin 73) :
    maskPerm m j = (maskOrder m)[j.val]'(by rw [maskOrder_length]; exact j.isLt) := rfl

theorem maskPerm_symm_index (m : ℕ) (i : ℕ) (hi : i < (maskIndices m).length) :
    ((maskPerm m).symm ((maskIndices m)[i])).val = i := by
  have hlen : (maskIndices m).length ≤ 73 := by
    have h1 := maskOrder_length m
    rw [maskOrder, List.length_append] at h1
    change (maskIndices m).length + _ = 73 at h1
    omega
  have h : maskPerm m ⟨i, by omega⟩ = (maskIndices m)[i] := by
    rw [maskPerm_apply]
    simp only [maskOrder]
    rw [List.getElem_append_left (by simpa [maskIndices] using hi)]
    rfl
  rw [← h, Equiv.symm_apply_apply]

/-- The chart of a helper hosting the axes of `m` in the basis of `P`. -/
noncomputable def helperChart {P : PortData} (hP : portCheck P = true) (m : ℕ) :
    Addr ≃ₗ[ZMod 2] Addr :=
  basisChart (portBasis P) (portBasis_orthonormal hP) (maskPerm m)

end IntegerMultBounds.Networks.Certificates.T16.Impl
