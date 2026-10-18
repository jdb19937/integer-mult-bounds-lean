module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Frames

/-! Orthogonal address permutations of 73-bit arrays. `permOp G` moves the value at `x` to
`G x`; for orthogonal `G` it sends the character `χ_u` to `χ_{G u}`, so conjugating a kernel
product moves its basis by `G`. The cover correction follows: for orthogonal `g`,
`P_g C_all P_g⁻¹ = C_all X_δ(g)` with `δ_i = (wt(row_i g) - 1)/2`, because weight modulo four is
additive over the orthonormal rows of `g`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open BinaryWalsh BinaryPhase Multiplicative

abbrev Addr := BinaryWalsh.Address 73

/-- Orthogonality for the binary dot product. -/
def IsOrth (G : Addr ≃ₗ[ZMod 2] Addr) : Prop := ∀ x y, Labels.binary 73 (G x) (G y) = Labels.binary 73 x y

theorem IsOrth.symm {G : Addr ≃ₗ[ZMod 2] Addr} (hG : IsOrth G) : IsOrth G.symm := fun x y => by
  rw [← hG, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The address permutation sending the value at `x` to `G x`. -/
noncomputable def permOp (G : Addr ≃ₗ[ZMod 2] Addr) : Module.End ℂ (Arrays 73) where
  toFun f x := f (G.symm x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permOp_apply (G : Addr ≃ₗ[ZMod 2] Addr) (f : Arrays 73) (x : Addr) :
    permOp G f x = f (G.symm x) := rfl

theorem permOp_char {G : Addr ≃ₗ[ZMod 2] Addr} (hG : IsOrth G) (u : Addr) :
    permOp G (charVec u) = charVec (G u) := by
  funext x
  simp only [permOp_apply, charVec, chi]
  rw [← hG u (G.symm x), LinearEquiv.apply_symm_apply]

theorem phaseExp_orth {G : Addr ≃ₗ[ZMod 2] Addr} (hG : IsOrth G) (B : Fin 73 → Addr)
    (c : Fin 73 → ZMod 4) (u : Addr) :
    phaseExp (fun k => G (B k)) c (G u) = phaseExp B c u := by
  simp only [phaseExp]
  apply Finset.sum_congr rfl
  intro k _
  rw [hG]

/-- Conjugating a kernel product by an orthogonal permutation moves its basis. -/
theorem permOp_basisOp {G : Addr ≃ₗ[ZMod 2] Addr} (hG : IsOrth G) (B : Fin 73 → Addr)
    (c : Fin 73 → ZMod 4) (f : Arrays 73) :
    permOp G (basisOp B (ofAdd c) f) = basisOp (fun k => G (B k)) (ofAdd c) (permOp G f) := by
  refine eq_of_chars_fun (A := fun f => permOp G (basisOp B (ofAdd c) f))
    (B := fun f => basisOp (fun k => G (B k)) (ofAdd c) (permOp G f))
    (by simp) (fun x y => by simp) (fun z x => by simp) (by simp) (fun x y => by simp)
    (fun z x => by simp) (fun u => ?_) f
  rw [basisOp_char, map_smul, permOp_char hG, basisOp_char, phaseExp_orth hG]

/-! ### The cover correction -/

/-- The rows of `g` are the images of the coordinate vectors under its transpose, which for
orthogonal `g` is `g⁻¹`; `δ_i = (wt(row_i) - 1)/2`. -/
noncomputable def coverDelta (g : Addr ≃ₗ[ZMod 2] Addr) (i : Fin 73) : ZMod 2 :=
  if weightPhase (g.symm (stdBasis i)) = 3 then 1 else 0

theorem stdBasis_orthonormal : Orthonormal73 stdBasis := by
  intro i j
  simp only [stdBasis, binary_single]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem orth_rows {g : Addr ≃ₗ[ZMod 2] Addr} (hg : IsOrth g) :
    Orthonormal73 fun i => g.symm (stdBasis i) := by
  intro i j
  rw [hg.symm, stdBasis_orthonormal]

/-- A norm-one vector has odd weight. -/
theorem weightPhase_odd {v : Addr} (hv : Labels.binary 73 v v = 1) :
    weightPhase v = 1 ∨ weightPhase v = 3 := by
  have hpar : ∑ i, v i = 1 := by
    have : Labels.binary 73 v v = ∑ i, v i * v i := by
      simp [Labels.binary, Labels.form_apply]
    rw [this] at hv
    have hsq : ∀ i, v i * v i = v i := fun i => by
      generalize v i = a; revert a; decide
    simpa [hsq] using hv
  -- reduce the integer weight modulo two
  have key : ∀ (s : Finset (Fin 73)),
      (∑ i ∈ s, (bitLift (v i)).val) % 2 = ((∑ i ∈ s, v i : ZMod 2)).val := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mod, ih]
      generalize v a = x
      generalize (∑ i ∈ s, v i) = y
      revert x y; decide
  have hw : weightPhase v = ((∑ i, (bitLift (v i)).val : ℕ) : ZMod 4) := by
    simp only [weightPhase]
    rw [Nat.cast_sum]
    simp
  have hm := key Finset.univ
  rw [hpar] at hm
  rw [hw]
  generalize hn : (∑ i, (bitLift (v i)).val) = n at hm
  have hn2 : n % 2 = 1 := by rw [hm]; rfl
  have : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases this with h | h
  · left; rw [← ZMod.natCast_mod n 4, h]; rfl
  · right; rw [← ZMod.natCast_mod n 4, h]; rfl

theorem phaseExp_std (x : Addr) : phaseExp stdBasis (fun _ => 1) x = weightPhase x := by
  simp [phaseExp, stdBasis, binary_single, weightPhase]

/-- `wt(u) = wt(g u) + 2 [g u · δ(g)]` modulo four, for orthogonal `g`. -/
theorem weight_cover {g : Addr ≃ₗ[ZMod 2] Addr} (hg : IsOrth g) (u : Addr) :
    weightPhase u = 2 * bitLift (Labels.binary 73 (g u) (fun i => coverDelta g i)) +
      weightPhase (g u) := by
  have hrows := (orth_rows hg).weight u
  have hrow : ∀ i, Labels.binary 73 u (g.symm (stdBasis i)) = g u i := by
    intro i
    rw [← hg u (g.symm (stdBasis i)), LinearEquiv.apply_symm_apply, stdBasis, binary_single]
  have hodd : ∀ i, weightPhase (g.symm (stdBasis i)) = 1 + doubleLift (coverDelta g i) := by
    intro i
    have hn : Labels.binary 73 (g.symm (stdBasis i)) (g.symm (stdBasis i)) = 1 := by
      rw [orth_rows hg i i]; simp
    rcases weightPhase_odd hn with h | h
    · simp only [coverDelta, h]; decide
    · simp only [coverDelta, h]; decide
  simp only [hrow, hodd] at hrows
  rw [← hrows]
  have e : ∀ i, (1 + doubleLift (coverDelta g i)) * bitLift (g u i) =
      bitLift (g u i) + doubleLift (g u i * coverDelta g i) := by
    intro i
    generalize g u i = a
    generalize coverDelta g i = b
    revert a b; decide
  simp only [e, Finset.sum_add_distrib]
  have hd : ∑ i, doubleLift (g u i * coverDelta g i) =
      2 * bitLift (Labels.binary 73 (g u) (fun i => coverDelta g i)) := by
    rw [← map_sum]
    have hs : (∑ i, g u i * coverDelta g i) = Labels.binary 73 (g u) (fun i => coverDelta g i) := by
      simp [Labels.binary, Labels.form_apply]
    rw [hs]
    rfl
  rw [hd, add_comm]
  rfl

/-- **Cover correction.** For orthogonal `g`, `P_g C_all = C_all X_δ(g) P_g`. -/
theorem cover_correction {g : Addr ≃ₗ[ZMod 2] Addr} (hg : IsOrth g) (f : Arrays 73) :
    permOp g (cAll f) = cAll (kernel 2 (fun i => coverDelta g i) (permOp g f)) := by
  refine eq_of_chars_fun (A := fun f => permOp g (cAll f))
    (B := fun f => cAll (kernel 2 (fun i => coverDelta g i) (permOp g f)))
    (by simp) (fun x y => by simp) (fun z x => by simp) (by simp) (fun x y => by simp)
    (fun z x => by simp) (fun u => ?_) f
  rw [cAll, basisOp_char, map_smul, permOp_char hg, kernel_char, map_smul, basisOp_char,
    phaseExp_std, phaseExp_std, smul_smul, ← phase_add, ← weight_cover hg]

end IntegerMultBounds.Networks.Certificates.T16.Streams
