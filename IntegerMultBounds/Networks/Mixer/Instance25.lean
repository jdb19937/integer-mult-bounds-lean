module

public import IntegerMultBounds.Networks.Mixer.Rectangles
public import IntegerMultBounds.Networks.Mixer.Scalar
public import IntegerMultBounds.Networks.Mixer.Enclosure
public import IntegerMultBounds.Networks.ComplexRank25
public import IntegerMultBounds.Networks.CircuitTriples

/-! The mixed complex invocation on 25 points. Its side roles are the input and
output slots of the rectangle plan of disjoint triple pairs, together with one
direct role per ordered pair of triples meeting in two points. Output slots inject
with weight `1/2` and direct roles with weight `-1/2`; with the complex central
gather and scatter, the invocation reconstructs its source bank exactly. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Instance25

open Rectangles NeighborCounts

/-! ### Rectangles and side roles -/

/-- The number of rectangles of the plan. -/
abbrev K25 : ℕ := plan25.length

/-- The `k`-th rectangle of the plan. -/
def rect (k : Fin K25) : Rect (Fin 25) := plan25.get k

theorem rect_mem (k : Fin K25) : rect k ∈ plan25 := List.get_mem _ _

/-- Input slots: one per rectangle and source of that rectangle. -/
abbrev InSlot := Σ k : Fin K25, {S : Finset (Fin 25) // S ∈ (rect k).1}

/-- Output slots: one per rectangle and target of that rectangle. -/
abbrev OutSlot := Σ k : Fin K25, {T : Finset (Fin 25) // T ∈ (rect k).2}

/-- Direct roles: ordered pairs (source, target) of triples meeting in two points. -/
abbrev Direct := {p : Triple 25 × Triple 25 // (p.1.val ∩ p.2.val).card = 2}

/-- All side roles of one invocation. -/
abbrev Side := InSlot ⊕ OutSlot ⊕ Direct

instance : DecidableEq InSlot := inferInstance
instance : DecidableEq OutSlot := inferInstance
instance : DecidableEq Direct := inferInstance
instance : DecidableEq Side := inferInstanceAs (DecidableEq (InSlot ⊕ OutSlot ⊕ Direct))

theorem in_card (σ : InSlot) : σ.2.val.card = 3 :=
  (plan25_sound (rect_mem σ.1)).1 _ σ.2.property

theorem out_card (τ : OutSlot) : τ.2.val.card = 3 :=
  (plan25_sound (rect_mem τ.1)).2 _ τ.2.property

theorem sum_rects (f : Rect (Fin 25) → ℕ) : ∑ k : Fin K25, f (rect k) = (plan25.map f).sum := by
  simp only [rect, List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem plan25 f

theorem inSlot_card : Fintype.card InSlot = 224802 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  rw [sum_rects (fun R => R.1.card)]
  exact plan25_counts.1

theorem outSlot_card : Fintype.card OutSlot = 224802 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  rw [sum_rects (fun R => R.2.card)]
  exact plan25_counts.2

theorem direct_card : Fintype.card Direct = 151800 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun S T : Triple 25 => (S.val ∩ T.val).card = 2)), Fintype.card_sigma]
  simp only [triple_intersection_card _ 2 (by omega), Finset.sum_const, Finset.card_univ,
    triple_card, smul_eq_mul]
  decide

theorem side_card : Fintype.card Side = 601404 := by
  simp only [Side, Fintype.card_sum, inSlot_card, outSlot_card, direct_card]

/-! ### Kinds and weights -/

/-- The triple of a data index. -/
noncomputable abbrev L (i : Fin 2300) : Finset (Fin 25) := (ComplexRank25.triples i).val

/-- The data index of a triple. -/
noncomputable def tri (S : Finset (Fin 25)) (h : S.card = 3) : Fin 2300 :=
  ComplexRank25.triples.symm ⟨S, h⟩

@[simp] theorem L_tri (S : Finset (Fin 25)) (h : S.card = 3) : L (tri S h) = S := by
  simp [L, tri]

theorem L_card (i : Fin 2300) : (L i).card = 3 := (ComplexRank25.triples i).property

theorem L_injective : Function.Injective L := fun _ _ h =>
  ComplexRank25.triples.injective (Subtype.ext h)

theorem tri_eq_iff {S : Finset (Fin 25)} (h : S.card = 3) (i : Fin 2300) :
    tri S h = i ↔ S = L i := by
  constructor
  · rintro rfl; simp
  · intro hS
    apply L_injective
    simp [hS]

/-- The kind of each side role. -/
noncomputable def kindOf : Side → Scalar.Kind 2300 K25
  | .inl σ => .input σ.1 (tri σ.2.val (in_card σ))
  | .inr (.inl τ) => .output τ.1 (tri τ.2.val (out_card τ))
  | .inr (.inr d) => .direct (ComplexRank25.triples.symm d.val.1)
      (ComplexRank25.triples.symm d.val.2)

/-- Injection weights: `1/2` on output slots, `-1/2` on direct roles. -/
def weightOf : Side → ℚ
  | .inl _ => 0
  | .inr (.inl _) => 1 / 2
  | .inr (.inr _) => -(1 / 2)

/-- The number of side roles of one invocation. -/
abbrev a25 : ℕ := Fintype.card Side

/-- The enumeration of side roles. -/
noncomputable def sideEquiv : Fin a25 ≃ Side := (Fintype.equivFin Side).symm

/-- The kind of each enumerated side role. -/
noncomputable def kind (p : Fin a25) : Scalar.Kind 2300 K25 := kindOf (sideEquiv p)

/-- The injection weight of each enumerated side role. -/
noncomputable def weight (p : Fin a25) : ℚ := weightOf (sideEquiv p)

theorem a25_eq : a25 = 601404 := side_card

/-! ### Facts used by the labels -/

theorem kind_input {p : Fin a25} {k : Fin K25} {i : Fin 2300} (h : kind p = .input k i) :
    L i ∈ (rect k).1 := by
  unfold kind at h
  rcases hp : sideEquiv p with σ | τ | d <;> rw [hp] at h <;> simp only [kindOf] at h
  · obtain ⟨rfl, rfl⟩ := Scalar.Kind.input.inj h
    simp [σ.2.property]
  · cases h
  · cases h

theorem kind_output {p : Fin a25} {k : Fin K25} {j : Fin 2300} (h : kind p = .output k j) :
    L j ∈ (rect k).2 := by
  unfold kind at h
  rcases hp : sideEquiv p with σ | τ | d <;> rw [hp] at h <;> simp only [kindOf] at h
  · cases h
  · obtain ⟨rfl, rfl⟩ := Scalar.Kind.output.inj h
    simp [τ.2.property]
  · cases h

theorem kind_direct {p : Fin a25} {i j : Fin 2300} (h : kind p = .direct i j) :
    (L i ∩ L j).card = 2 := by
  unfold kind at h
  rcases hp : sideEquiv p with σ | τ | d <;> rw [hp] at h <;> simp only [kindOf] at h
  · cases h
  · cases h
  · obtain ⟨rfl, rfl⟩ := Scalar.Kind.direct.inj h
    simpa [L] using d.property

/-- Joins of nonempty families are nonempty. -/
theorem join_nonempty {α : Type*} [DecidableEq α] {A B : Finset (Finset α)}
    (hA : A.Nonempty) (hB : B.Nonempty) : (join A B).Nonempty := by
  obtain ⟨X, hX⟩ := hA
  obtain ⟨Y, hY⟩ := hB
  exact ⟨X ∪ Y, mem_join.mpr ⟨X, hX, Y, hY, rfl⟩⟩

/-- Every rectangle of a plan has a source and a target. -/
theorem plan_nonempty {α : Type*} [DecidableEq α] (P : List α) (a b : ℕ) :
    P.Nodup → ∀ R ∈ plan P a b, R.1.Nonempty ∧ R.2.Nonempty := by
  induction P, a, b using plan.induct with
  | case1 P a b hab =>
    intro _ R hR
    rw [plan, dif_pos hab] at hR
    simp at hR
  | case2 P b hab =>
    intro hP R hR
    rw [plan, dif_neg hab, dif_pos rfl] at hR
    simp only [List.mem_singleton] at hR
    subst hR
    refine ⟨Finset.singleton_nonempty _, Finset.powersetCard_nonempty.mpr ?_⟩
    rw [List.toFinset_card_of_nodup hP]
    omega
  | case3 P a ha hab =>
    intro hP R hR
    rw [plan, dif_neg hab, dif_neg ha, dif_pos rfl] at hR
    simp only [List.mem_singleton] at hR
    subst hR
    refine ⟨Finset.powersetCard_nonempty.mpr ?_, Finset.singleton_nonempty _⟩
    rw [List.toFinset_card_of_nodup hP]
    omega
  | case4 P a b hab ha hb ih₁ ih₂ =>
    intro hP R hR
    rw [plan, dif_neg hab, dif_neg ha, dif_neg hb] at hR
    obtain ⟨ij, -, hR⟩ := List.mem_flatMap.mp hR
    obtain ⟨R₁, hR₁, hR⟩ := List.mem_flatMap.mp hR
    obtain ⟨R₂, hR₂, rfl⟩ := List.mem_map.mp hR
    have n₁ := ih₁ ij (hP.sublist (List.take_sublist _ _)) R₁ hR₁
    have n₂ := ih₂ ij (hP.sublist (List.drop_sublist _ _)) R₂ hR₂
    exact ⟨join_nonempty n₁.1 n₂.1, join_nonempty n₁.2 n₂.2⟩

theorem plan25_nonempty {R : Rect (Fin 25)} (hR : R ∈ plan25) : R.1.Nonempty ∧ R.2.Nonempty :=
  plan_nonempty _ _ _ (List.nodup_finRange 25) R hR

/-- Every rectangle of the plan satisfies the enclosure-label hypotheses. -/
theorem rect_valid (k : Fin K25) : Enclosure.Valid (rect k).1 (rect k).2 where
  sources_card := (plan25_sound (rect_mem k)).1
  targets_card := (plan25_sound (rect_mem k)).2
  disjoint := fun _ hS _ hT => plan25_disjoint (rect_mem k) hS hT
  sources_nonempty := (plan25_nonempty (rect_mem k)).1
  targets_nonempty := (plan25_nonempty (rect_mem k)).2

/-! ### Reconstruction -/

/-- The data value copied into a role of a given kind. -/
def ownerVal (X : Fin 2300 → ℚ) (κ : Scalar.Kind 2300 K25) : ℚ := κ.owner.elim 0 X

/-- The sum of the data values at the sources of a rectangle. -/
noncomputable def srcSum (X : Fin 2300 → ℚ) (k : Fin K25) : ℚ :=
  ∑ t, if L t ∈ (rect k).1 then X t else 0

theorem sum_side (f : Side → ℚ) : ∑ p : Fin a25, f (sideEquiv p) = ∑ σ, f σ :=
  Equiv.sum_comp sideEquiv f

theorem mv_copy (X : Fin 2300 → ℚ) (p : Fin a25) :
    Circuit.mv (Scalar.copyMatrix kind) X p = ownerVal X (kind p) := by
  simp only [Circuit.mv, Scalar.copyMatrix, ownerVal]
  cases (kind p).owner with
  | none => simp
  | some j => simp

/-- Summing over the members of a family of triples is summing over their indices. -/
theorem sum_members (F : Finset (Finset (Fin 25))) (hF : ∀ S ∈ F, S.card = 3)
    (g : Fin 2300 → ℚ) :
    ∑ S : {S // S ∈ F}, g (tri S.val (hF _ S.property)) = ∑ t, if L t ∈ F then g t else 0 := by
  rw [← Finset.sum_filter,
    Finset.sum_subtype (Finset.univ.filter fun t => L t ∈ F) (p := fun t => L t ∈ F) (by simp)]
  let e : {S // S ∈ F} ≃ {t // L t ∈ F} :=
    { toFun := fun S => ⟨tri S.val (hF _ S.property), by simp [S.property]⟩
      invFun := fun t => ⟨L t, t.property⟩
      left_inv := fun S => Subtype.ext (L_tri _ _)
      right_inv := fun t => Subtype.ext ((tri_eq_iff _ _).mpr rfl) }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem in_sum (X : Fin 2300 → ℚ) (k : Fin K25) :
    ∑ q : Fin a25, (if (kind q).inRect = some k then ownerVal X (kind q) else 0) = srcSum X k := by
  rw [Fintype.sum_equiv sideEquiv
    (fun q => if (kind q).inRect = some k then ownerVal X (kind q) else 0)
    (fun σ => if (kindOf σ).inRect = some k then ownerVal X (kindOf σ) else 0) (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, kindOf, Scalar.Kind.inRect, ownerVal, Scalar.Kind.owner,
    Option.elim, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero, Option.some.injEq]
  rw [Fintype.sum_sigma]
  have hk : ∀ k' : Fin K25, (∑ S : {S // S ∈ (rect k').1},
      if k' = k then X (tri S.val (in_card ⟨k', S⟩)) else 0) =
      if k' = k then srcSum X k' else 0 := by
    intro k'
    by_cases h : k' = k
    · simp only [h, if_true]
      subst h
      exact sum_members _ (plan25_sound (rect_mem k')).1 X
    · simp [h]
  simp only [hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mix_copy (X : Fin 2300 → ℚ) (p : Fin a25) :
    Scalar.mix kind (Circuit.mv (Scalar.copyMatrix kind) X) p =
      ((kind p).outRect).elim 0 (srcSum X) := by
  simp only [Scalar.mix]
  split
  · rename_i k hk
    simp only [mv_copy, in_sum, hk, Option.elim]
  · rename_i hk
    simp [hk]

/-- A sum over the members of a family with an indicator at one triple. -/
theorem sum_member_eq (F : Finset (Finset (Fin 25))) (A : Finset (Fin 25)) (c : ℚ) :
    ∑ T : {T // T ∈ F}, (if T.val = A then c else 0) = if A ∈ F then c else 0 := by
  rw [Finset.sum_coe_sort F (fun T => if T = A then c else 0), Finset.sum_ite_eq']

/-- The side contribution at one target. -/
theorem side_sum (X : Fin 2300 → ℚ) (s : Fin 2300) :
    Circuit.mv (Scalar.injectMatrix kind weight)
        (Circuit.mv (Scalar.copyMatrix kind) X + Scalar.mix kind (Circuit.mv (Scalar.copyMatrix kind) X)) s =
      1 / 2 * ∑ k, (if L s ∈ (rect k).2 then srcSum X k else 0) -
        1 / 2 * ∑ t, (if (L t ∩ L s).card = 2 then X t else 0) := by
  change ∑ p, Scalar.injectMatrix kind weight s p *
    (Circuit.mv (Scalar.copyMatrix kind) X + Scalar.mix kind (Circuit.mv (Scalar.copyMatrix kind) X)) p = _
  simp only [Scalar.injectMatrix, Pi.add_apply, mv_copy, mix_copy]
  rw [Fintype.sum_equiv sideEquiv
    (fun p => (if (kind p).target = some s then weight p else 0) *
      (ownerVal X (kind p) + ((kind p).outRect).elim 0 (srcSum X)))
    (fun σ => (if (kindOf σ).target = some s then weightOf σ else 0) *
      (ownerVal X (kindOf σ) + ((kindOf σ).outRect).elim 0 (srcSum X))) (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, kindOf, weightOf, Scalar.Kind.target, Scalar.Kind.outRect,
    ownerVal, Scalar.Kind.owner, Option.elim, reduceCtorEq, if_false, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, Option.some.injEq, tri_eq_iff]
  rw [Fintype.sum_sigma]
  have hout : ∀ k : Fin K25, (∑ T : {T // T ∈ (rect k).2},
      (if T.val = L s then (1 : ℚ) / 2 else 0) * srcSum X k) =
      1 / 2 * (if L s ∈ (rect k).2 then srcSum X k else 0) := by
    intro k
    simp only [← Finset.sum_mul, sum_member_eq]
    split_ifs <;> ring
  simp only [hout, ← Finset.mul_sum]
  -- direct roles
  have hdir : (∑ d : Direct, (if ComplexRank25.triples.symm d.val.2 = s then -(1 / 2 : ℚ) else 0) *
      X (ComplexRank25.triples.symm d.val.1)) =
      -(1 / 2) * ∑ t, (if (L t ∩ L s).card = 2 then X t else 0) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun p : Triple 25 × Triple 25 =>
        (p.1.val ∩ p.2.val).card = 2) (p := fun p => (p.1.val ∩ p.2.val).card = 2) (by simp)
      (fun p => (if ComplexRank25.triples.symm p.2 = s then -(1 / 2 : ℚ) else 0) *
        X (ComplexRank25.triples.symm p.1)),
      Finset.sum_filter, Fintype.sum_prod_type]
    rw [← Equiv.sum_comp ComplexRank25.triples, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Equiv.sum_comp ComplexRank25.triples]
    simp only [Equiv.symm_apply_apply]
    rw [Finset.sum_eq_single s]
    · by_cases h : (L t ∩ L s).card = 2 <;> simp [h, L]
    · intro u _ hu
      simp [hu]
    · simp
  rw [hdir]
  ring

/-- Rectangle incidences deliver exactly the disjoint sources. -/
theorem pair_sum (X : Fin 2300 → ℚ) (s : Fin 2300) :
    ∑ k, (if L s ∈ (rect k).2 then srcSum X k else 0) =
      ∑ t, (if Disjoint (L t) (L s) then X t else 0) := by
  simp only [srcSum]
  have hk : ∀ k : Fin K25, (if L s ∈ (rect k).2 then ∑ t, (if L t ∈ (rect k).1 then X t else 0)
      else 0) = ∑ t, (if L t ∈ (rect k).1 ∧ L s ∈ (rect k).2 then (1 : ℚ) else 0) * X t := by
    intro k
    by_cases h : L s ∈ (rect k).2
    · simp only [h, if_true, and_true]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp
    · simp [h]
  simp only [hk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_mul]
  have hh : (∑ k : Fin K25, (if L t ∈ (rect k).1 ∧ L s ∈ (rect k).2 then (1 : ℚ) else 0)) =
      ((hits plan25 (L t) (L s) : ℕ) : ℚ) := by
    rw [hits, ← sum_rects (fun R => if L t ∈ R.1 ∧ L s ∈ R.2 then 1 else 0)]
    push_cast
    rfl
  rw [hh, plan25_hits]
  simp only [L_card, true_and]
  split_ifs <;> simp

/-- The total coefficient from source `t` to target `s`. -/
theorem coeff_eq (s t : Fin 2300) :
    (if Disjoint (L t) (L s) then (1 : ℚ) / 2 else 0) -
        (if (L t ∩ L s).card = 2 then 1 / 2 else 0) + Circuit.centralCoeff L s t =
      if s = t then 1 else 0 := by
  have hi : L t ∩ L s = L s ∩ L t := Finset.inter_comm _ _
  obtain ⟨hle, heq⟩ := triple_inter_card (L s) (L t) (L_card s) (L_card t)
  have hd : Disjoint (L t) (L s) ↔ (L s ∩ L t).card = 0 := by
    rw [Finset.disjoint_iff_inter_eq_empty, hi, Finset.card_eq_zero]
  simp only [Circuit.centralCoeff, hi, hd]
  by_cases h : s = t
  · subst h
    simp [L_card]
    norm_num
  · have hne : (L s ∩ L t).card ≠ 3 := fun hh => h (L_injective (heq.mp hh))
    have hj : (L s ∩ L t).card = 0 ∨ (L s ∩ L t).card = 1 ∨ (L s ∩ L t).card = 2 := by omega
    rcases hj with hj | hj | hj <;> simp [hj, h] <;> norm_num

/-- The mixed complex invocation reconstructs its whole source bank. -/
theorem reconstruct (X : Fin 2300 → ℚ) :
    Circuit.mv (Scalar.injectMatrix kind weight)
        (Circuit.mv (Scalar.copyMatrix kind) X + Scalar.mix kind (Circuit.mv (Scalar.copyMatrix kind) X)) +
      Circuit.mv (Circuit.complexScatter L) (Circuit.mv (Circuit.complexGather L) X) = X := by
  funext s
  rw [Pi.add_apply, side_sum, pair_sum]
  have hc : Circuit.mv (Circuit.complexScatter L) (Circuit.mv (Circuit.complexGather L) X) s =
      ∑ t, Circuit.centralCoeff L s t * X t := by
    simp only [Circuit.mv, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Circuit.complex_central_coeff L s t, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [show X s = ∑ t, (if s = t then (1 : ℚ) else 0) * X t by simp]
  apply Finset.sum_congr rfl
  intro t _
  rw [← coeff_eq s t]
  split_ifs <;> ring

end IntegerMultBounds.Networks.Mixer.Instance25
