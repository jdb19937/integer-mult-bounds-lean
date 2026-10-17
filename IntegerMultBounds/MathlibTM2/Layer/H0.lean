module

public import IntegerMultBounds.MathlibTM2.Layer.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Normalized butterflies from the C layer

`hBit i` is the normalized butterfly `H₀(u, v) = ((u + v)/2, (u - v)/2)` on active bit `i`, and
`Hfull n` applies it on every active bit. With `S` multiplying by `i ^ (number of set active
bits)` and `b = (1 - i)/2`, `Hfull n = bⁿ • S ∘ Cfull n ∘ S` (`Hfull_eq`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryPhase

variable {X : Type} {n : ℕ}

/-- The normalized butterfly on active bit `i`. -/
noncomputable def hBit (i : Fin n) : Arr X n →ₗ[ℂ] Arr X n where
  toFun f p := ((if p.2 i = 0 then 1 else -1) * f p + f (p.1, flip i p.2)) / 2
  map_add' f g := by funext p; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The normalized butterfly on every active bit. -/
noncomputable def Hfull (X : Type) (n : ℕ) : Arr X n →ₗ[ℂ] Arr X n :=
  (List.ofFn (fun i : Fin n => hBit i)).prod

/-- The phase `i ^ (active bit i)` on one bit. -/
noncomputable def sBit (i : Fin n) : Arr X n →ₗ[ℂ] Arr X n where
  toFun f p := (if p.2 i = 0 then 1 else Complex.I) * f p
  map_add' f g := by funext p; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The phase `i ^ (number of set active bits)`. -/
noncomputable def Sfull (X : Type) (n : ℕ) : Arr X n →ₗ[ℂ] Arr X n :=
  (List.ofFn (fun i : Fin n => sBit i)).prod

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma flip_self (i : Fin n) (b : Fin n → ZMod 2) : flip i b i = b i + 1 := by
  simp [flip]

lemma flip_other {i j : Fin n} (h : j ≠ i) (b : Fin n → ZMod 2) : flip i b j = b j := by
  simp [flip, h]

/-- One bit: `H₀ = b · S C S`. -/
lemma hBit_eq (i : Fin n) (f : Arr X n) :
    hBit i f = ((1 - Complex.I) / 2) • sBit i (kBit 1 i (sBit i f)) := by
  funext p
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  change ((if p.2 i = 0 then 1 else -1) * f p + f (p.1, flip i p.2)) / 2 =
    ((1 - Complex.I) / 2) * ((if p.2 i = 0 then 1 else Complex.I) *
      (((1 + phase 1) / 2) * ((if p.2 i = 0 then 1 else Complex.I) * f p) +
        ((1 - phase 1) / 2) * ((if flip i p.2 i = 0 then 1 else Complex.I) * f (p.1, flip i p.2))))
  rw [phase_one, flip_self]
  rcases zmod2_cases (p.2 i) with h | h <;> simp only [h, zero_add, h2, ite_true, one_ne_zero,
    ite_false]
  · linear_combination (f p / 4 + f (p.1, flip i p.2) * (2 - Complex.I) / 4) * Complex.I_sq
  · linear_combination (f p * (Complex.I ^ 2 - 2) / 4 + f (p.1, flip i p.2) * (2 - Complex.I) / 4) *
      Complex.I_sq

lemma sBit_kBit_commute {i j : Fin n} (h : i ≠ j) (f : Arr X n) :
    sBit i (kBit 1 j f) = kBit 1 j (sBit i f) := by
  funext p
  change (if p.2 i = 0 then 1 else Complex.I) * (((1 + phase 1) / 2) * f p +
      ((1 - phase 1) / 2) * f (p.1, flip j p.2)) =
    ((1 + phase 1) / 2) * ((if p.2 i = 0 then 1 else Complex.I) * f p) +
      ((1 - phase 1) / 2) * ((if flip j p.2 i = 0 then 1 else Complex.I) * f (p.1, flip j p.2))
  rw [flip_other h]
  ring

lemma sBit_commute (i j : Fin n) (f : Arr X n) : sBit i (sBit j f) = sBit j (sBit i f) := by
  funext p; simp only [sBit, LinearMap.coe_mk, AddHom.coe_mk]; ring

section Tensor

variable (X)

/-- Products over a list of bits. -/
noncomputable def Hl (l : List (Fin n)) : Arr X n →ₗ[ℂ] Arr X n := (l.map hBit).prod
noncomputable def Sl (l : List (Fin n)) : Arr X n →ₗ[ℂ] Arr X n := (l.map sBit).prod
noncomputable def Cl (l : List (Fin n)) : Arr X n →ₗ[ℂ] Arr X n := (l.map (kBit 1)).prod

variable {X}

lemma Sl_kBit (l : List (Fin n)) (i : Fin n) (hi : i ∉ l) (f : Arr X n) :
    Sl X l (kBit 1 i f) = kBit 1 i (Sl X l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons j l ih =>
      simp only [Sl, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      have hj : j ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
      rw [ih (fun h => hi (List.mem_cons_of_mem _ h)), sBit_kBit_commute hj]

lemma Cl_sBit (l : List (Fin n)) (i : Fin n) (hi : i ∉ l) (f : Arr X n) :
    Cl X l (sBit i f) = sBit i (Cl X l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons j l ih =>
      simp only [Cl, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      have hj : i ≠ j := fun h => hi (h ▸ List.mem_cons_self ..)
      rw [ih (fun h => hi (List.mem_cons_of_mem _ h)), sBit_kBit_commute hj]

lemma Sl_sBit (l : List (Fin n)) (i : Fin n) (f : Arr X n) :
    Sl X l (sBit i f) = sBit i (Sl X l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons j l ih =>
      simp only [Sl, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih, sBit_commute]

lemma smul_lin (T : Arr X n →ₗ[ℂ] Arr X n) (c : ℂ) (f : Arr X n) : T (c • f) = c • T f := map_smul T c f

/-- Normalized butterflies on distinct bits are `b^|l| • S C S`. -/
lemma Hl_eq (l : List (Fin n)) (hl : l.Nodup) (f : Arr X n) :
    Hl X l f = ((1 - Complex.I) / 2) ^ l.length • Sl X l (Cl X l (Sl X l f)) := by
  induction l generalizing f with
  | nil => simp [Hl, Sl, Cl]
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      change hBit i (Hl X l f) = _ • sBit i (Sl X l (kBit 1 i (Cl X l (sBit i (Sl X l f)))))
      rw [ih hl.2, hBit_eq]
      simp only [map_smul, smul_smul, List.length_cons, pow_succ]
      rw [mul_comm ((1 - Complex.I) / 2)]
      congr 2
      rw [← Sl_sBit, ← Cl_sBit _ _ hl.1, ← Sl_kBit _ _ hl.1]

lemma Sl_eq (f : Arr X n) : Sl X (List.finRange n) f = Sfull X n f := by
  rw [Sl, Sfull, List.ofFn_eq_map]
lemma Cl_eq (f : Arr X n) : Cl X (List.finRange n) f = Cfull X n f := by
  rw [Cl, Cfull, List.ofFn_eq_map]

/-- Normalized butterflies on every bit: `Hfull = bⁿ • S ∘ Cfull ∘ S`. -/
theorem Hfull_eq (f : Arr X n) :
    Hfull X n f = ((1 - Complex.I) / 2) ^ n • Sfull X n (Cfull X n (Sfull X n f)) := by
  have := Hl_eq (X := X) (List.finRange n) (List.nodup_finRange n) f
  rw [List.length_finRange, Sl_eq, Cl_eq, Sl_eq] at this
  rw [Hfull, List.ofFn_eq_map]
  exact this

end Tensor

/-! ### Explicit form -/

/-- The sign `(-1)^(Σ_{i ∈ l} a_i b_i)`. -/
noncomputable def sgn (l : List (Fin n)) (a b : Fin n → ZMod 2) : ℂ :=
  (l.map fun i => if a i = 1 ∧ b i = 1 then (-1 : ℂ) else 1).prod

/-- Bit vectors agreeing with `a` off the list `l`. -/
def agree (l : List (Fin n)) (a b : Fin n → ZMod 2) : Prop := ∀ i, i ∉ l → b i = a i

instance (l : List (Fin n)) (a : Fin n → ZMod 2) : DecidablePred (agree l a) :=
  fun b => by unfold agree; infer_instance

/-- Normalized butterflies on distinct bits `l` in explicit form. -/
lemma sgn_flip (l : List (Fin n)) (i : Fin n) (hi : i ∉ l) (a b : Fin n → ZMod 2) :
    sgn l (flip i a) b = sgn l a b := by
  unfold sgn
  congr 1
  apply List.map_congr_left
  intro j hj
  have : j ≠ i := fun h => hi (h ▸ hj)
  rw [flip_other this]

lemma agree_nil (a b : Fin n → ZMod 2) : agree [] a b ↔ b = a := by
  simp [agree, funext_iff]

lemma agree_cons (i : Fin n) (l : List (Fin n)) (a b : Fin n → ZMod 2) :
    agree (i :: l) a b ↔ agree l a b ∨ agree l (flip i a) b := by
  constructor
  · intro h
    rcases zmod2_cases (b i + a i) with hb | hb
    · left; intro j hj
      by_cases hji : j = i
      · subst hji
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        have := congrArg (· + a j) hb
        simpa [add_assoc, CharTwo.add_self_eq_zero] using this
      · exact h j (by simp [hji, hj])
    · right; intro j hj
      by_cases hji : j = i
      · subst hji
        rw [flip_self]
        have := congrArg (· + a j) hb
        simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
        rw [this]; ring
      · rw [flip_other hji]; exact h j (by simp [hji, hj])
  · rintro (h | h) j hj
    · exact h j (fun h' => hj (List.mem_cons_of_mem _ h'))
    · have hji : j ≠ i := fun h' => hj (h' ▸ List.mem_cons_self ..)
      rw [h j (fun h' => hj (List.mem_cons_of_mem _ h')), flip_other hji]

lemma agree_disjoint (i : Fin n) (l : List (Fin n)) (hi : i ∉ l) (a b : Fin n → ZMod 2)
    (h1 : agree l a b) (h2 : agree l (flip i a) b) : False := by
  have e1 := h1 i hi
  have e2 := h2 i hi
  rw [flip_self] at e2
  rw [e1] at e2
  have h2' : (1 : ZMod 2) ≠ 0 := by decide
  exact h2' (by simp at e2)

/-- Normalized butterflies on distinct bits `l` in explicit form. -/
theorem Hl_apply (l : List (Fin n)) (hl : l.Nodup) (f : Arr X n) (x : X) (a : Fin n → ZMod 2) :
    Hl X l f (x, a) = (1 / 2 ^ l.length : ℂ) *
      ∑ b ∈ Finset.univ.filter (agree l a), sgn l a b * f (x, b) := by
  induction l generalizing a with
  | nil =>
      have : Finset.univ.filter (agree [] a) = {a} := by
        ext b; simp [agree_nil]
      simp [Hl, this, sgn]
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      change hBit i (Hl X l f) (x, a) = _
      simp only [hBit, LinearMap.coe_mk, AddHom.coe_mk]
      rw [ih hl.2 a, ih hl.2 (flip i a)]
      have hsplit : Finset.univ.filter (agree (i :: l) a) =
          Finset.univ.filter (agree l a) ∪ Finset.univ.filter (agree l (flip i a)) := by
        ext b; simp [agree_cons]
      have hdisj : Disjoint (Finset.univ.filter (agree l a)) (Finset.univ.filter (agree l (flip i a))) := by
        rw [Finset.disjoint_filter]
        intro b _ h1 h2
        exact agree_disjoint i l hl.1 a b h1 h2
      rw [hsplit, Finset.sum_union hdisj]
      have hA : ∀ b ∈ Finset.univ.filter (agree l a), sgn (i :: l) a b * f (x, b) =
          (if a i = 0 then 1 else -1) * (sgn l a b * f (x, b)) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        simp only [sgn, List.map_cons, List.prod_cons]
        rw [hb i hl.1]
        rcases zmod2_cases (a i) with h | h <;> simp [h]
      have hB : ∀ b ∈ Finset.univ.filter (agree l (flip i a)), sgn (i :: l) a b * f (x, b) =
          sgn l (flip i a) b * f (x, b) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [sgn_flip l i hl.1]
        have hbi := hb i hl.1
        rw [flip_self] at hbi
        simp only [sgn, List.map_cons, List.prod_cons, hbi]
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        rcases zmod2_cases (a i) with h | h <;> simp [h, h2]
      rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, ← Finset.mul_sum]
      simp only [List.length_cons, pow_succ]
      field_simp

end IntegerMultBounds.MathlibTM2.Layer
