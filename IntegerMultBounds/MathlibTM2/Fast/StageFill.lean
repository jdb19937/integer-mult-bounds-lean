module

public import IntegerMultBounds.MathlibTM2.Fast.Runs

/-!
# Register files filled in stages

`stFill ι stage bc s R₀` is the register file `R₀` with every register `ι x` of stage
`1 ≤ stage x ≤ s` holding `bc x`; every other register is as in `R₀`. `stFill_step`: filling
the register of stage `s + 1` advances the file. `lr_chain`: a chain of programs, each taking the
file of its stage to the next, takes the first file to the last.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

section Fill

variable {T A : ℕ} {X : Type*} (ι : X → Fin T) (stage : X → ℕ)

/-- The register file after the first `s` stages, over the base file `R₀`. -/
noncomputable def stFill (bc : X → List (Fin (A + 4))) (s : ℕ) (R₀ : Fin T → List (Fin (A + 4))) :
    Fin T → List (Fin (A + 4)) :=
  Function.extend ι (fun x => if 1 ≤ stage x ∧ stage x ≤ s then bc x else R₀ (ι x)) R₀

variable {ι stage}

lemma stFill_ι (hι : Function.Injective ι) (bc : X → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) (x : X) :
    stFill ι stage bc s R₀ (ι x) = if 1 ≤ stage x ∧ stage x ≤ s then bc x else R₀ (ι x) :=
  hι.extend_apply _ _ _

lemma stFill_out (bc : X → List (Fin (A + 4))) (s : ℕ) (R₀ : Fin T → List (Fin (A + 4)))
    {t : Fin T} (ht : ∀ x, ι x ≠ t) : stFill ι stage bc s R₀ t = R₀ t :=
  Function.extend_apply' _ _ _ (by rintro ⟨x, rfl⟩; exact ht x rfl)

/-- A register filled at stage `j ≤ s`. -/
lemma stFill_of_le (hι : Function.Injective ι) (bc : X → List (Fin (A + 4))) {s : ℕ}
    (R₀ : Fin T → List (Fin (A + 4))) {x : X} (h1 : 1 ≤ stage x) (h2 : stage x ≤ s) :
    stFill ι stage bc s R₀ (ι x) = bc x := by
  rw [stFill_ι hι, ite_eq_left ⟨h1, h2⟩]

/-- A register not yet filled. -/
lemma stFill_of_gt (hι : Function.Injective ι) (bc : X → List (Fin (A + 4))) {s : ℕ}
    (R₀ : Fin T → List (Fin (A + 4))) {x : X} (h : s < stage x ∨ stage x = 0) :
    stFill ι stage bc s R₀ (ι x) = R₀ (ι x) := by
  rw [stFill_ι hι, ite_eq_right (by omega)]

lemma stFill_step (hι : Function.Injective ι)
    (hstage : ∀ x y, 1 ≤ stage x → stage x = stage y → x = y) (bc : X → List (Fin (A + 4)))
    {s : ℕ} (R₀ : Fin T → List (Fin (A + 4))) {x : X} (hx : stage x = s + 1) :
    Function.update (stFill ι stage bc s R₀) (ι x) (bc x) = stFill ι stage bc (s + 1) R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [stFill_ι hι]
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, ite_eq_left (by omega)]
    · rw [Function.update_of_ne (hι.ne hy), stFill_ι hι]
      have : stage y ≠ s + 1 := fun h => hy (hstage y x (by omega) (h.trans hx.symm))
      by_cases h1 : 1 ≤ stage y ∧ stage y ≤ s
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · simp only [not_exists] at ht
    rw [Function.update_of_ne (fun h => ht x h.symm), stFill_out _ _ _ ht, stFill_out _ _ _ ht]

lemma stFill_unstep (hι : Function.Injective ι)
    (hstage : ∀ x y, 1 ≤ stage x → stage x = stage y → x = y) (bc : X → List (Fin (A + 4)))
    {s : ℕ} (R₀ : Fin T → List (Fin (A + 4))) {x : X} (hx : stage x = s + 1) :
    Function.update (stFill ι stage bc (s + 1) R₀) (ι x) (R₀ (ι x)) = stFill ι stage bc s R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [stFill_ι hι]
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, ite_eq_right (by omega)]
    · rw [Function.update_of_ne (hι.ne hy), stFill_ι hι]
      have : stage y ≠ s + 1 := fun h => hy (hstage y x (by omega) (h.trans hx.symm))
      by_cases h1 : 1 ≤ stage y ∧ stage y ≤ s
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · simp only [not_exists] at ht
    rw [Function.update_of_ne (fun h => ht x h.symm), stFill_out _ _ _ ht, stFill_out _ _ _ ht]

lemma stFill_zero (hι : Function.Injective ι) (bc : X → List (Fin (A + 4)))
    (R₀ : Fin T → List (Fin (A + 4))) : stFill ι stage bc 0 R₀ = R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [stFill_ι hι, ite_eq_right (by omega)]
  · simp only [not_exists] at ht
    rw [stFill_out _ _ _ ht]

lemma stFill_update (hι : Function.Injective ι) (bc : X → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) {t : Fin T} (ht : ∀ x, ι x ≠ t) (l : List (Fin (A + 4))) :
    Function.update (stFill ι stage bc s R₀) t l = stFill ι stage bc s (Function.update R₀ t l) := by
  funext t'
  by_cases h : ∃ y, ι y = t'
  · obtain ⟨y, rfl⟩ := h
    rw [Function.update_of_ne (ht y), stFill_ι hι, stFill_ι hι, Function.update_of_ne (ht y)]
  · simp only [not_exists] at h
    rw [stFill_out _ _ _ h]
    by_cases htt : t' = t
    · subst htt; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne htt, Function.update_of_ne htt, stFill_out _ _ _ h]

end Fill

section Chain

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- **A chain of programs** `p (s + i)`, each taking the file `F (s + i)` to `F (s + i + 1)`. -/
theorem lr_chain (F : ℕ → Fin T → List (Fin (A + 4))) (p : ℕ → Pr P T Q A U) (c : ℕ → ℕ) :
    ∀ (N s : ℕ), (∀ i < N, LayRuns body (p (s + i)) (F (s + i)) (F (s + i + 1)) (c (s + i))) →
      LayRuns body (Prog.seqList ((List.range N).map fun i => p (s + i))) (F s) (F (s + N))
        (∑ i ∈ Finset.range N, c (s + i) + 1) := by
  intro N
  induction N with
  | zero =>
    intro s _
    simpa [Prog.seqList, synSkip] using lr_skip body (F s)
  | succ N ih =>
    intro s h
    have h₁ := h 0 (by omega)
    have h' := ih (s + 1) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show s + (i + 1) = s + 1 + i by omega] at this
    have hlist : (List.range (N + 1)).map (fun i => p (s + i)) =
        p s :: (List.range N).map (fun i => p (s + 1 + i)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]
    rw [hlist]
    simp only [Nat.add_zero] at h₁
    refine lr_weaken body (h₁.seq h') (by rw [show s + 1 + N = s + (N + 1) by omega]) ?_
    rw [Finset.sum_range_succ']
    have : ∑ i ∈ Finset.range N, c (s + (i + 1)) = ∑ i ∈ Finset.range N, c (s + 1 + i) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
    simp only [Nat.add_zero]
    omega

end Chain

end IntegerMultBounds.MathlibTM2.Fast
