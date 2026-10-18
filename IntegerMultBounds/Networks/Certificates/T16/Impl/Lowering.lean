module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Prim

/-! Lowering lifted nine-bit realizations to primitive words. `Lowers K ws` says that the lift
of the exact operator of `K` is the word `ws`. Permutations, diagonal gates and C gates lower to
single primitives, words compose by concatenation, and the general lowering theorem
(`Pauli.Realization.lowering`) gives, for every realization, a word whose child calls number
exactly the X-block rank of its tableau. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli

/-- The lift of the exact operator of `K` is the word `ws`. -/
def Lowers (K : Realization) (ws : List Prim) : Prop :=
  ∀ f, lift9 K.scalar.toLinearMap f = wordOp ws f

theorem Lowers.then {A B : Realization} {wa wb : List Prim} (ha : Lowers A wa) (hb : Lowers B wb) :
    Lowers (A.then B) (wa ++ wb) := by
  intro f
  rw [wordOp_append, ← ha, ← hb, lift9_comp]
  rfl

theorem lowers_identity : Lowers Realization.identity [] := fun f => lift9_id f

theorem lowers_permutation (G : Geometry.Address ≃ₗ[Geometry.F] Geometry.Address) :
    Lowers (permutationRealization G) [.perm (liftGL G)] :=
  fun f => lift9_permutation G f

theorem lowers_diagonal (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (hQ : ∀ i j, Q i j = Q j i)
    (ha : ∀ i, 2 * alpha i = doubleLift (Q i i)) :
    Lowers (diagonalRealization Q alpha hQ ha) [.diag (fun x => qValue Q alpha (lowPart x))] :=
  fun f => lift9_phaseDiagonal (qValue Q alpha) f

theorem lowers_c (q : Geometry.Address) : Lowers (cRealization q) [.kernel 1 (padLow q)] :=
  fun f => lift9_kernel 1 q f

/-- The child calls of the partial C word. -/
noncomputable def cPrims : ℕ → List Prim
  | 0 => []
  | k + 1 => cPrims k ++ if h : k < 9 then [.kernel 1 (padLow (Pi.single ⟨k, h⟩ 1))] else []

theorem realizeWord_append_scalar (gs hs : List Realization) (f : State) :
    (realizeWord (gs ++ hs)).scalar f = (realizeWord hs).scalar ((realizeWord gs).scalar f) := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih => exact ih (g.scalar f)

theorem lowers_realizeWord_append' {gs hs : List Realization} {wg wh : List Prim}
    (hg : Lowers (realizeWord gs) wg) (hh : Lowers (realizeWord hs) wh) :
    Lowers (realizeWord (gs ++ hs)) (wg ++ wh) := by
  intro f
  have e : (realizeWord (gs ++ hs)).scalar.toLinearMap =
      (realizeWord hs).scalar.toLinearMap.comp (realizeWord gs).scalar.toLinearMap :=
    LinearMap.ext fun g => realizeWord_append_scalar gs hs g
  rw [wordOp_append, ← hg, ← hh, lift9_comp, e]

theorem lowers_single (g : Realization) {w : List Prim} (hg : Lowers g w) :
    Lowers (realizeWord [g]) w := by
  intro f
  rw [← hg]
  rfl

theorem lowers_cWord (r : ℕ) : Lowers (partialCRealization r) (cPrims r) := by
  induction r with
  | zero => exact lowers_identity
  | succ k ih =>
    change Lowers (realizeWord (cWord k ++ _)) _
    apply lowers_realizeWord_append' ih
    split_ifs with h
    · exact lowers_single _ (lowers_c _)
    · exact lowers_identity

theorem childCount_cPrims (r : ℕ) : childCount (cPrims r) = min r 9 := by
  induction r with
  | zero => rfl
  | succ k ih =>
    rw [cPrims, childCount_append, ih]
    split_ifs with h
    · rw [show childCount [Prim.kernel 1 (padLow (Pi.single ⟨k, h⟩ 1))] = 1 from rfl]
      omega
    · rw [show childCount ([] : List Prim) = 0 from rfl]
      omega

theorem lowers_shear (S : Geometry.Address →ₗ[Geometry.F] Geometry.Address)
    (hS : Tableau.DotSymmetric S) :
    Lowers (shearRealization S hS)
      [.diag (fun x => qValue (shearMatrix S) (defaultAlpha (shearMatrix S)) (lowPart x))] :=
  lowers_diagonal _ _ _ _

theorem lowers_monomial (G : Geometry.Address ≃ₗ[Geometry.F] Geometry.Address)
    (S : Geometry.Address →ₗ[Geometry.F] Geometry.Address) (hS : Tableau.DotSymmetric S) :
    Lowers (monomialRealization G S hS)
      [.perm (liftGL G), .diag (fun x => qValue (shearMatrix S) (defaultAlpha (shearMatrix S))
        (lowPart x))] :=
  (lowers_permutation G).then (lowers_shear S hS)

/-- The word of the coordinate Hadamard realization `S C_r S`. -/
noncomputable def hadamardPrims (r : ℕ) : List Prim :=
  [.diag (fun x => qValue (shearMatrix (Tableau.cut r)) (defaultAlpha (shearMatrix (Tableau.cut r)))
    (lowPart x))] ++ (cPrims r ++
  [.diag (fun x => qValue (shearMatrix (Tableau.cut r)) (defaultAlpha (shearMatrix (Tableau.cut r)))
    (lowPart x))])

theorem lowers_hadamard (r : ℕ) : Lowers (hadamardRealization r) (hadamardPrims r) :=
  (lowers_shear _ _).then ((lowers_cWord r).then (lowers_shear _ _))

theorem childCount_diag (φ : Addr → ZMod 4) : childCount [Prim.diag φ] = 0 := rfl

theorem childCount_hadamardPrims (r : ℕ) : childCount (hadamardPrims r) = min r 9 := by
  rw [hadamardPrims, childCount_append, childCount_append, childCount_cPrims, childCount_diag]
  omega

/-! ### Pauli operators -/

/-- The word of a lifted Pauli operator: its character, its translation and its phase. -/
noncomputable def pauliPrims (p : Label) : List Prim :=
  [.diag (fun x => 2 * bitLift (Labels.binary 9 p.z (lowPart x))), .kernel 2 (padLow p.x),
    .scale (phase p.phase)]

theorem sign_eq_phase (b : ZMod 2) : sign b = phase (2 * bitLift b) := by
  fin_cases b
  · rfl
  · change (if (1 : ZMod 2) = 0 then (1 : ℂ) else -1) = Complex.I ^ (2 * bitLift 1 : ZMod 4).val
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide)), show (2 * bitLift 1 : ZMod 4).val = 2 from rfl, Complex.I_sq]

theorem lift9_characterMultiply (z : Address 9) (f : Arrays 73) :
    lift9 (characterMultiply z) f =
      phaseDiagonal (fun x => 2 * bitLift (Labels.binary 9 z (lowPart x))) f := by
  funext x
  change chi z (lowPart x) * f (joinAddr (lowPart x) (highPart x)) = _
  rw [join_parts, chi, sign_eq_phase]
  rfl

theorem lift9_operator (p : Label) (f : Arrays 73) :
    lift9 (operator p) f = wordOp (pauliPrims p) f := by
  change lift9 (phase p.phase • (translation p.x).comp (characterMultiply p.z)) f = _
  rw [lift9_smul, ← lift9_comp, lift9_characterMultiply, lift9_translation]
  rfl

/-! ### General lowering -/

theorem lowers_smul_operator {K W : Realization} {ws : List Prim} (κ : ℂ) (c : Label)
    (hK : ∀ f, K.scalar f = κ • operator c (W.scalar f)) (hW : Lowers W ws) :
    Lowers K (ws ++ (pauliPrims c ++ [.scale κ])) := by
  intro f
  have e : K.scalar.toLinearMap = κ • (operator c).comp W.scalar.toLinearMap :=
    LinearMap.ext hK
  rw [e, lift9_smul, ← lift9_comp, lift9_operator, hW, wordOp_append, wordOp_append]
  rfl

/-- **Lowering to primitives.** Every exact nine-bit realization lifts to a word of primitives
with exactly as many child calls as the X-block rank of its tableau. -/
theorem Realization.exists_prims (K : Realization) :
    ∃ ws : List Prim, Lowers K ws ∧
      childCount ws = Module.finrank Geometry.F (Tableau.xRange K.binary) := by
  obtain ⟨A₂, G, S₂, S, hS₂, hS, c, κ, h⟩ := K.lowering
  set r := Module.finrank Geometry.F (Tableau.xRange K.binary)
  have hr : r ≤ 9 := by
    have := Submodule.finrank_le (Tableau.xRange K.binary)
    simpa using this
  refine ⟨_, lowers_smul_operator κ c h
    ((lowers_monomial A₂ S₂ hS₂).then ((lowers_hadamard r).then
      ((lowers_shear S hS).then (lowers_permutation G)))), ?_⟩
  have hm : childCount [Prim.perm (liftGL A₂), .diag (fun x => qValue (shearMatrix S₂)
      (defaultAlpha (shearMatrix S₂)) (lowPart x))] = 0 := rfl
  have hp : childCount (pauliPrims c ++ [Prim.scale κ]) = 0 := rfl
  have hs : childCount ([Prim.diag (fun x => qValue (shearMatrix S) (defaultAlpha (shearMatrix S))
      (lowPart x))] ++ [Prim.perm (liftGL G)]) = 0 := rfl
  rw [childCount_append, childCount_append, childCount_append, childCount_hadamardPrims, hm, hp, hs]
  omega

/-! ### Inverse words -/

/-- The inverse of a primitive. -/
noncomputable def Prim.inv : Prim → Prim
  | .kernel q v => .kernel (-q) v
  | .perm G => .perm G.symm
  | .diag φ => .diag (-φ)
  | .scale c => .scale c⁻¹

/-- A primitive with a nonzero scale. -/
def Prim.Invertible : Prim → Prop
  | .scale c => c ≠ 0
  | _ => True

theorem Prim.inv_op {p : Prim} (hp : p.Invertible) (f : Arrays 73) : p.inv.op (p.op f) = f := by
  cases p with
  | kernel q v => exact kernel_inverse q v f
  | perm G =>
    funext x
    simp [Prim.inv, Prim.op, permOp_apply]
  | diag φ =>
    funext x
    change phase (-φ x) * (phase (φ x) * f x) = f x
    rw [← mul_assoc, ← phase_add, neg_add_cancel, phase_zero, one_mul]
  | scale c =>
    change c⁻¹ • c • f = f
    rw [smul_smul, inv_mul_cancel₀ (hp : c ≠ 0), one_smul]

/-- The inverse of a word: the inverses in reverse order. -/
noncomputable def invPrims (ws : List Prim) : List Prim := (ws.map Prim.inv).reverse

theorem wordOp_invPrims (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) (f : Arrays 73) :
    wordOp (invPrims ws) (wordOp ws f) = f := by
  induction ws generalizing f with
  | nil => rfl
  | cons p ps ih =>
    rw [invPrims, List.map_cons, List.reverse_cons, ← invPrims, wordOp_append]
    change wordOp [p.inv] (wordOp (invPrims ps) (wordOp ps (p.op f))) = f
    rw [ih (fun q hq => hws q (List.mem_cons_of_mem _ hq))]
    exact Prim.inv_op (hws p List.mem_cons_self) f

theorem Prim.isChild_inv (p : Prim) : p.inv.isChild = p.isChild := by
  cases p with
  | kernel q v =>
    change ((-q).val % 2 == 1) = (q.val % 2 == 1)
    generalize q = q
    revert q
    decide
  | _ => rfl

theorem childCount_invPrims (ws : List Prim) : childCount (invPrims ws) = childCount ws := by
  simp only [childCount, invPrims, ← List.countP_eq_length_filter, List.countP_reverse,
    List.countP_map]
  congr 1
  funext p
  exact Prim.isChild_inv p

end IntegerMultBounds.Networks.Certificates.T16.Impl
