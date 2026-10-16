module

public import IntegerMultBounds.MathlibTM2.Fast.CRTRot

/-!
# The CRT layout: from triangular rotations to `crtPhi`

Pure semantics of the CRT layout machines. For lengths `s : Fin d → ℕ` and offsets
`μ : Fin d → ℕ` put, for a coordinate vector `x`,

* `crtKX s x = ∑ j, x j · prefixProd s j` (the mixed-radix value),
* `crtB s μ x j = (x j + μ j · crtKI s j x) mod s j` (eq. `triangular-crt`, with the controls
  `crtKI s j x = ∑_{j' < j} x j' · prefixProd s j'`),
* `crtBeta s μ m x`: the coordinates `x j` for `j < m` and `crtB s μ x j` for `j ≥ m`.

**Forward.** `crtFwdC s μ C₀ n` is the content after the forward rotation passes for the
targets `d - 1, …, d - n` (`crtRotC … true`). `crtFwdC_beta`: from the padded content
`crtPadC s l z`, at every valid `a`, `crtFwdC … n (crtBeta s μ (d - n) a)` is `l[crtKX s a]`,
and every invalid coordinate vector holds `z` (`crtFwdC_invalid`).

**Inverse.** `crtInvC s μ X n` is the content after the inverse passes for the targets
`0, …, n - 1` (`crtRotC … false`). `crtInvC_beta`: at a valid `a`,
`crtInvC … n (crtBeta s μ n a) = X (crtBeta s μ 0 a)`.

**`crtPhi`.** With `μ j = (crtMu s hs j).val`, `crtBeta s μ 0 a` is the vector of values of
`crtPhi s hs (crtKX s a)` (`crtBeta_zero_eq_phi`), so:

* `crtFwdC_spec`: the forward content is `crtSpecC s hs l z`: at valid `x` the record
  `l[(crtPhi s hs).symm x]`, and `z` elsewhere;
* `crtInvC_spec`: at the mixed-radix digits `crtUnrank s k` of `k < ∏ s`, the inverse content is
  `X` at the values of `crtPhi s hs k`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Mult
open scoped Function

set_option linter.unusedSimpArgs false

section Spec

variable {d : ℕ} (s : Fin d → ℕ)

/-- The mixed-radix value `∑ j, x j · prefixProd s j`. -/
def crtKX (x : Fin d → ℕ) : ℕ := ∑ j, x j * prefixProd s j

/-- The target coordinate `(x j + μ j · ∑_{j' < j} x j' prefixProd s j') mod s j`. -/
def crtB (μ : Fin d → ℕ) (x : Fin d → ℕ) (j : Fin d) : ℕ := (x j + μ j * crtKI s j.val x) % s j

/-- The coordinates `x j` below `m` and `crtB s μ x j` from `m` on. -/
def crtBeta (μ : Fin d → ℕ) (m : ℕ) (x : Fin d → ℕ) : Fin d → ℕ :=
  fun j => if j.val < m then x j else crtB s μ x j

lemma crtKI_congr {i : ℕ} {x y : Fin d → ℕ} (h : ∀ j : Fin d, j.val < i → x j = y j) :
    crtKI s i x = crtKI s i y := by
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [h j hj]

/-- Adding a representative of `μ K` modulo `S`. -/
lemma crt_mod_add_lo {S x μ K lo : ℕ} (hlo : ((lo : ℕ) : ZMod S) = (μ : ZMod S) * K) :
    (x + lo) % S = (x + μ * K) % S := by
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  rw [hlo]

/-- Subtracting a representative `lo ≤ S` of `μ K` modulo `S` from `crtB`. -/
lemma crt_mod_sub_lo {S x μ K lo : ℕ} (hx : x < S) (hloS : lo ≤ S)
    (hlo : ((lo : ℕ) : ZMod S) = (μ : ZMod S) * K) :
    ((x + μ * K) % S + (S - lo)) % S = x := by
  have h : (((x + μ * K) % S + (S - lo) : ℕ) : ZMod S) = (x : ZMod S) := by
    rw [Nat.cast_add, ZMod.natCast_mod, Nat.cast_sub hloS, hlo]
    push_cast
    rw [ZMod.natCast_self]; ring
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx] at h
  exact h

/-! ### Forward -/

/-- The content after the forward rotation passes for the targets `d - 1, …, d - n`. -/
def crtFwdC {α : Type*} (μ : Fin d → ℕ) (C₀ : (Fin d → ℕ) → α) : ℕ → (Fin d → ℕ) → α
  | 0 => C₀
  | n + 1 => if h : n < d then
      crtRotC s (d - 1 - n) (by omega) (μ ⟨d - 1 - n, by omega⟩) true (crtFwdC μ C₀ n)
    else crtFwdC μ C₀ n

variable {α : Type*}

theorem crtFwdC_main (hs : ∀ j, 0 < s j) (μ : Fin d → ℕ) (hμ : ∀ j, μ j ≤ s j) (l : List α)
    (z : α) :
    ∀ n ≤ d, (∀ a : Fin d → ℕ, (∀ j, a j < s j) →
        crtFwdC s μ (crtPadC s l z) n (crtBeta s μ (d - n) a) = l.getD (crtKX s a) z) ∧
      ∀ x : Fin d → ℕ, ¬ (∀ j, x j < s j) → crtFwdC s μ (crtPadC s l z) n x = z
  | 0, _ => by
      refine ⟨fun a ha => ?_, fun x hx => ?_⟩
      · have hb : crtBeta s μ d a = a := by funext j; simp [crtBeta, j.isLt]
        simp only [crtFwdC, Nat.sub_zero, hb, crtPadC, ite_eq_left ha, crtKX]
      · simp only [crtFwdC, crtPadC, ite_eq_right hx]
  | n + 1, hn => by
      have hnd : n < d := by omega
      obtain ⟨ih₁, ih₂⟩ := crtFwdC_main hs μ hμ l z n (by omega)
      set i := d - 1 - n with hi
      have hid : i < d := by omega
      set I : Fin d := ⟨i, hid⟩ with hI
      have hrw : ∀ x, crtFwdC s μ (crtPadC s l z) (n + 1) x =
          crtRotC s i hid (μ I) true (crtFwdC s μ (crtPadC s l z) n) x := fun x => by
        rw [crtFwdC, dite_eq_left hnd]
      refine ⟨fun a ha => ?_, fun x hx => ?_⟩
      · rw [hrw, crtRotC]
        have hbI : crtBeta s μ (d - (n + 1)) a I = crtB s μ a I := by
          simp [crtBeta, hI, hi, show ¬ (d - 1 - n < d - (n + 1)) by omega]
        have hctrl : ∀ j : Fin d, j.val < i → crtBeta s μ (d - (n + 1)) a j = a j := by
          intro j hj; simp [crtBeta, show j.val < d - (n + 1) by omega]
        have hK : crtKI s i (crtBeta s μ (d - (n + 1)) a) = crtKI s i a := crtKI_congr s hctrl
        have hBlt : crtB s μ a I < s I := Nat.mod_lt _ (hs I)
        rw [ite_eq_left ⟨fun j hj => by rw [hctrl j hj]; exact ha j, by rw [hbI]; exact hBlt⟩, hbI, hK]
        have hval : (crtB s μ a I + crtShift true (s I) (μ I) (crtKI s i a)) % s I = a I := by
          simp only [crtShift, ite_true]
          exact crt_mod_sub_lo (ha I) (crtLo_le (hμ I) _) (crtLo_cast _ _ _)
        rw [hval]
        have hb' : Function.update (crtBeta s μ (d - (n + 1)) a) I (a I) =
            crtBeta s μ (d - n) a := by
          funext j
          by_cases hj : j = I
          · subst hj; simp [crtBeta, hI, hi, show d - 1 - n < d - n by omega]
          · rw [Function.update_of_ne hj]
            have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
            simp only [crtBeta]
            by_cases h1 : j.val < d - (n + 1)
            · rw [ite_eq_left h1, ite_eq_left (by omega)]
            · rw [ite_eq_right h1, ite_eq_right (by omega)]
        rw [hb']
        exact ih₁ a ha
      · rw [hrw, crtRotC]
        split_ifs with hc
        · apply ih₂
          intro hall
          apply hx
          intro j
          by_cases hj : j = I
          · subst hj; exact hc.2
          · have := hall j
            rwa [Function.update_of_ne hj] at this
        · exact ih₂ x hx

/-! ### Inverse -/

/-- The content after the inverse rotation passes for the targets `0, …, n - 1`. -/
def crtInvC (μ : Fin d → ℕ) (X : (Fin d → ℕ) → α) : ℕ → (Fin d → ℕ) → α
  | 0 => X
  | n + 1 => if h : n < d then crtRotC s n h (μ ⟨n, h⟩) false (crtInvC μ X n)
    else crtInvC μ X n

theorem crtInvC_beta (hs : ∀ j, 0 < s j) (μ : Fin d → ℕ) (X : (Fin d → ℕ) → α) :
    ∀ n ≤ d, ∀ a : Fin d → ℕ, (∀ j, a j < s j) →
      crtInvC s μ X n (crtBeta s μ n a) = X (crtBeta s μ 0 a)
  | 0, _, a, _ => rfl
  | n + 1, hn, a, ha => by
      have hnd : n < d := by omega
      set N : Fin d := ⟨n, hnd⟩ with hN
      rw [crtInvC, dite_eq_left hnd, crtRotC]
      have hctrl : ∀ j : Fin d, j.val < n → crtBeta s μ (n + 1) a j = a j := by
        intro j hj; simp [crtBeta, show j.val < n + 1 by omega]
      have hbN : crtBeta s μ (n + 1) a N = a N := by simp [crtBeta, hN]
      have hK : crtKI s n (crtBeta s μ (n + 1) a) = crtKI s n a := crtKI_congr s hctrl
      rw [ite_eq_left ⟨fun j hj => by rw [hctrl j hj]; exact ha j, by rw [hbN]; exact ha N⟩, hbN, hK]
      have hval : (a N + crtShift false (s N) (μ N) (crtKI s n a)) % s N = crtB s μ a N := by
        simp only [crtShift, Bool.false_eq_true, ite_false, crtB]
        exact crt_mod_add_lo (crtLo_cast _ _ _)
      rw [hval]
      have hb' : Function.update (crtBeta s μ (n + 1) a) N (crtB s μ a N) = crtBeta s μ n a := by
        funext j
        by_cases hj : j = N
        · subst hj; simp [crtBeta, hN]
        · rw [Function.update_of_ne hj]
          have hj' : j.val ≠ n := fun h => hj (Fin.ext h)
          simp only [crtBeta]
          by_cases h1 : j.val < n
          · rw [ite_eq_left (by omega), ite_eq_left h1]
          · rw [ite_eq_right (by omega), ite_eq_right h1]
      rw [hb']
      exact crtInvC_beta hs μ X n (by omega) a ha

/-! ### The map `crtPhi` -/

/-- The mixed-radix digits `k / prefixProd s j mod s j`. -/
lemma crtKX_unrank (k : ℕ) : ∀ m ≤ d,
    ∑ j ∈ crtLow m, crtUnrank s k j * prefixProd s j = k % crtProd s m
  | 0, _ => by simp [crtLow_zero, Nat.mod_one]
  | m + 1, hm => by
      have h : m < d := by omega
      rw [crtLow_succ h, Finset.sum_insert (crt_not_mem_low h), crtKX_unrank k m (by omega),
        crtProd_succ s h, crtUnrank, ← crtProd_eq_prefixProd s h, Nat.mod_mul]
      ring

/-- The values of `crtPhi` at the mixed-radix value of `a`. -/
theorem crtBeta_zero_eq_phi (hs : ∀ j, 0 < s j) (hcop : Pairwise (Nat.Coprime on s))
    (a : Fin d → ℕ) (j : Fin d) :
    crtBeta s (fun i => (crtMu s hcop i : ZMod (s i)).val) 0 a j =
      (crtPhi s hcop ((crtKX s a : ℕ) : ZMod (∏ i, s i)) j).val := by
  have : ∀ i, NeZero (s i) := fun i => ⟨(hs i).ne'⟩
  simp only [crtBeta, Nat.not_lt_zero, ite_false, crtB, crtKX]
  rw [crtPhi_mixedRadix, ← ZMod.val_natCast]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]
  congr 2
  simp only [crtKI]
  push_cast
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]

/-- The specified content of the box: the record of index `(crtPhi s hs).symm x` at the valid
coordinates `x`, the zero record elsewhere. -/
noncomputable def crtSpecC (hcop : Pairwise (Nat.Coprime on s)) (l : List α) (z : α)
    (x : Fin d → ℕ) : α :=
  if ∀ j, x j < s j then
    l.getD ((crtPhi s hcop).symm (fun j => (x j : ZMod (s j)))).val z
  else z

/-- The forward content after all passes is the specified content. -/
theorem crtFwdC_spec (hs : ∀ j, 0 < s j) (hcop : Pairwise (Nat.Coprime on s)) (l : List α)
    (z : α) :
    crtFwdC s (fun i => (crtMu s hcop i : ZMod (s i)).val) (crtPadC s l z) d =
      crtSpecC s hcop l z := by
  have : ∀ i, NeZero (s i) := fun i => ⟨(hs i).ne'⟩
  have hμ : ∀ j, (crtMu s hcop j : ZMod (s j)).val ≤ s j := fun j => (ZMod.val_lt _).le
  obtain ⟨h₁, h₂⟩ := crtFwdC_main s hs _ hμ l z d le_rfl
  funext x
  rw [crtSpecC]
  split_ifs with hx
  · set k := ((crtPhi s hcop).symm (fun j => (x j : ZMod (s j)))).val with hk
    have hkS : k < ∏ i, s i := ZMod.val_lt _
    set a := crtUnrank s k with ha
    have hav : ∀ j, a j < s j := fun j => Nat.mod_lt _ (hs j)
    have hKa : crtKX s a = k := by
      rw [crtKX, ← crtLow_of_le (le_refl d), crtKX_unrank s k d le_rfl, crtProd,
        crtLow_of_le le_rfl, Nat.mod_eq_of_lt hkS]
    have hbx : crtBeta s (fun i => (crtMu s hcop i : ZMod (s i)).val) 0 a = x := by
      funext j
      rw [crtBeta_zero_eq_phi s hs hcop a j, hKa, hk, ZMod.natCast_zmod_val,
        AddEquiv.apply_symm_apply, ZMod.val_cast_of_lt (hx j)]
    have := h₁ a hav
    rw [Nat.sub_self, hbx, hKa] at this
    exact this
  · exact h₂ x hx

/-- The inverse content after all passes at the mixed-radix digits of `k`: the input content at
the values of `crtPhi s hs k`. -/
theorem crtInvC_spec (hs : ∀ j, 0 < s j) (hcop : Pairwise (Nat.Coprime on s))
    (X : (Fin d → ℕ) → α) {k : ℕ} (hk : k < ∏ i, s i) :
    crtInvC s (fun i => (crtMu s hcop i : ZMod (s i)).val) X d (crtUnrank s k) =
      X fun j => (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val := by
  have : ∀ i, NeZero (s i) := fun i => ⟨(hs i).ne'⟩
  have hav : ∀ j, crtUnrank s k j < s j := fun j => Nat.mod_lt _ (hs j)
  have hKa : crtKX s (crtUnrank s k) = k := by
    rw [crtKX, ← crtLow_of_le (le_refl d), crtKX_unrank s k d le_rfl, crtProd,
      crtLow_of_le le_rfl, Nat.mod_eq_of_lt hk]
  have hb : crtBeta s (fun i => (crtMu s hcop i : ZMod (s i)).val) d (crtUnrank s k) =
      crtUnrank s k := by
    funext j; simp [crtBeta, j.isLt]
  have := crtInvC_beta s hs (fun i => (crtMu s hcop i : ZMod (s i)).val) X d le_rfl
    (crtUnrank s k) hav
  rw [hb] at this
  rw [this]
  congr 1
  funext j
  rw [crtBeta_zero_eq_phi s hs hcop _ j, hKa]

end Spec

end IntegerMultBounds.MathlibTM2.Fast
