import IntegerMultBounds.Schoenhage.DifAxes

/-! Rounds as butterflies and twists. A round is the butterfly `H₀` on one
address bit (`bfly`) followed by a pointwise twist `y^(-f(x))` (`twist`)
(`difRoundAt_eq`). Butterflies on different bits commute, twists compose by
adding exponents, and a twist commutes with a butterfly whose bit it does not
read (`bfly_twist_comm`); hence rounds of different axes commute
(`difRoundAt_comm`). -/

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-! ### Bits -/

theorem bitAt_lt_two (x P : ℕ) : bitAt x P < 2 := Nat.mod_lt _ (by norm_num)

theorem bitAt_add_pow_self {x Q : ℕ} (h : bitAt x Q = 0) : bitAt (x + 2 ^ Q) Q = 1 := by
  unfold bitAt at *
  rw [Nat.add_div_right _ (by positivity)]
  omega

theorem bitAt_sub_pow_self {x Q : ℕ} (h : bitAt x Q ≠ 0) : bitAt (x - 2 ^ Q) Q = 0 := by
  have hle := le_of_bitAt h
  have h1 : bitAt x Q = 1 := by have := bitAt_lt_two x Q; omega
  unfold bitAt at *
  have e : x / 2 ^ Q = (x - 2 ^ Q) / 2 ^ Q + 1 := by
    rw [← Nat.add_div_right _ (by positivity), Nat.sub_add_cancel hle]
  omega

theorem div_succ_add {x Q : ℕ} (h : bitAt x Q = 0) : (x + 2 ^ Q) / 2 ^ (Q + 1) = x / 2 ^ (Q + 1) := by
  unfold bitAt at h
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ (by positivity)]
  omega

theorem div_succ_sub {x Q : ℕ} (h : bitAt x Q ≠ 0) : (x - 2 ^ Q) / 2 ^ (Q + 1) = x / 2 ^ (Q + 1) := by
  have := bitAt_sub_pow_self h
  have hle := le_of_bitAt h
  have e := div_succ_add this
  rwa [Nat.sub_add_cancel hle, eq_comm] at e

theorem bitAt_high {y P Q : ℕ} (h : Q < P) : bitAt y P = y / 2 ^ (Q + 1) / 2 ^ (P - Q - 1) % 2 := by
  unfold bitAt
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 3; omega

theorem bitAt_low_add {x P Q : ℕ} (h : P < Q) : bitAt (x + 2 ^ Q) P = bitAt x P := by
  unfold bitAt
  rw [show 2 ^ Q = 2 ^ P * (2 * 2 ^ (Q - P - 1)) by rw [← pow_succ', ← pow_add]; congr 1; omega,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem bitAt_low_sub {x P Q : ℕ} (h : P < Q) (hq : 2 ^ Q ≤ x) : bitAt (x - 2 ^ Q) P = bitAt x P := by
  conv_rhs => rw [← Nat.sub_add_cancel hq]
  exact (bitAt_low_add h).symm

/-- Flipping bit `Q` leaves the other bits. -/
theorem bitAt_add_ne {x P Q : ℕ} (hPQ : P ≠ Q) (h : bitAt x Q = 0) : bitAt (x + 2 ^ Q) P = bitAt x P := by
  rcases Nat.lt_or_gt_of_ne hPQ with hlt | hgt
  · exact bitAt_low_add hlt
  · rw [bitAt_high hgt, bitAt_high hgt, div_succ_add h]

theorem bitAt_sub_ne {x P Q : ℕ} (hPQ : P ≠ Q) (h : bitAt x Q ≠ 0) : bitAt (x - 2 ^ Q) P = bitAt x P := by
  rcases Nat.lt_or_gt_of_ne hPQ with hlt | hgt
  · exact bitAt_low_sub hlt (le_of_bitAt h)
  · rw [bitAt_high hgt, bitAt_high hgt, div_succ_sub h]

/-- The address with bit `P` flipped. -/
def flip (x P : ℕ) : ℕ := if bitAt x P = 0 then x + 2 ^ P else x - 2 ^ P

/-! ### Butterflies and twists -/

variable {r : ℕ} [NeZero r]

/-- The butterfly `H₀` on bit `P`. -/
noncomputable def bfly (P : ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ := fun x =>
  if bitAt x P = 0 then (1 / 2 : ℂ) • (z x + z (x + 2 ^ P)) else (1 / 2 : ℂ) • (z (x - 2 ^ P) - z x)

/-- The pointwise twist by `y^(-f(x))`. -/
noncomputable def twist (f : ℕ → ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ := fun x => shiftInv (f x) (z x)

/-- The exponent of a round: the axis bits below the slot, at the slot's one-side only. -/
def rexp (r o h : ℕ) (x : ℕ) : ℕ := if bitAt x (o + h) = 0 then 0 else 2 * r / 2 ^ (h + 1) * (x / 2 ^ o % 2 ^ h)

theorem difRoundAt_eq (o h : ℕ) (z : ℕ → Fin r → ℂ) :
    difRoundAt o h z = twist (rexp r o h) (bfly (o + h) z) := by
  funext x
  unfold difRoundAt twist bfly rexp
  split_ifs <;> simp [shiftInv_zero]

theorem twist_twist (f g : ℕ → ℕ) (z : ℕ → Fin r → ℂ) : twist f (twist g z) = twist (fun x => f x + g x) z := by
  funext x; simp [twist, shiftInv_add]

theorem bfly_comm {P Q : ℕ} (hPQ : P ≠ Q) (z : ℕ → Fin r → ℂ) : bfly P (bfly Q z) = bfly Q (bfly P z) := by
  funext x
  unfold bfly
  by_cases hP : bitAt x P = 0 <;> by_cases hQ : bitAt x Q = 0
  · have a1 : bitAt (x + 2 ^ P) Q = 0 := by rw [bitAt_add_ne (Ne.symm hPQ) hP]; exact hQ
    have a2 : bitAt (x + 2 ^ Q) P = 0 := by rw [bitAt_add_ne hPQ hQ]; exact hP
    simp only [hP, hQ, a1, a2, ↓reduceIte]
    rw [show x + 2 ^ P + 2 ^ Q = x + 2 ^ Q + 2 ^ P by ring]
    module
  · have a1 : bitAt (x + 2 ^ P) Q ≠ 0 := by rw [bitAt_add_ne (Ne.symm hPQ) hP]; exact hQ
    have a2 : bitAt (x - 2 ^ Q) P = 0 := by rw [bitAt_sub_ne hPQ hQ]; exact hP
    have hq := le_of_bitAt hQ
    simp only [hP, hQ, a1, a2, ↓reduceIte]
    rw [show x + 2 ^ P - 2 ^ Q = x - 2 ^ Q + 2 ^ P from Nat.sub_add_comm hq]
    module
  · have a1 : bitAt (x - 2 ^ P) Q = 0 := by rw [bitAt_sub_ne (Ne.symm hPQ) hP]; exact hQ
    have a2 : bitAt (x + 2 ^ Q) P ≠ 0 := by rw [bitAt_add_ne hPQ hQ]; exact hP
    have hp := le_of_bitAt hP
    simp only [hP, hQ, a1, a2, ↓reduceIte]
    rw [show x - 2 ^ P + 2 ^ Q = x + 2 ^ Q - 2 ^ P from (Nat.sub_add_comm hp).symm]
    module
  · have a1 : bitAt (x - 2 ^ P) Q ≠ 0 := by rw [bitAt_sub_ne (Ne.symm hPQ) hP]; exact hQ
    have a2 : bitAt (x - 2 ^ Q) P ≠ 0 := by rw [bitAt_sub_ne hPQ hQ]; exact hP
    have hp := le_of_bitAt hP
    have hq := le_of_bitAt hQ
    have a3 : 2 ^ Q ≤ x - 2 ^ P := le_of_bitAt a1
    simp only [hP, hQ, a1, a2, ↓reduceIte]
    rw [show x - 2 ^ P - 2 ^ Q = x - 2 ^ Q - 2 ^ P by omega]
    module

/-- A twist commutes with a butterfly whose bit its exponent ignores. -/
theorem bfly_twist_comm {P : ℕ} {f : ℕ → ℕ} (hf0 : ∀ x, bitAt x P = 0 → f (x + 2 ^ P) = f x)
    (z : ℕ → Fin r → ℂ) : bfly P (twist f z) = twist f (bfly P z) := by
  funext x
  simp only [bfly, twist]
  split_ifs with hP
  · rw [hf0 x hP, ← shiftInv_add_vec, ← shiftInv_smul]
  · have hp := le_of_bitAt hP
    have e : f x = f (x - 2 ^ P) := by
      rw [← hf0 (x - 2 ^ P) (bitAt_sub_pow_self hP), Nat.sub_add_cancel hp]
    rw [← e, ← shiftInv_sub_vec, ← shiftInv_smul]

/-! ### Rounds of different axes commute -/

omit [NeZero r] in
theorem div_add_pow_low {x o Q : ℕ} (hQ : Q < o) (h : bitAt x Q = 0) : (x + 2 ^ Q) / 2 ^ o = x / 2 ^ o := by
  have e : ∀ y, y / 2 ^ o = y / 2 ^ (Q + 1) / 2 ^ (o - Q - 1) := fun y => by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
  rw [e, e x, div_succ_add h]

omit [NeZero r] in
theorem mod_div_add_pow_high {x o h Q : ℕ} (hQ : o + h ≤ Q) : (x + 2 ^ Q) / 2 ^ o % 2 ^ h = x / 2 ^ o % 2 ^ h := by
  rw [show 2 ^ Q = 2 ^ o * (2 ^ h * 2 ^ (Q - o - h)) by rw [← pow_add, ← pow_add]; congr 1; omega,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

omit [NeZero r] in
/-- A round's exponent ignores bits outside its axis bits up to its slot. -/
theorem rexp_add {o h Q x : ℕ} (hQ : Q < o ∨ o + h < Q) (h0 : bitAt x Q = 0) :
    rexp r o h (x + 2 ^ Q) = rexp r o h x := by
  unfold rexp
  rw [bitAt_add_ne (by omega) h0]
  rcases hQ with hQ | hQ
  · rw [div_add_pow_low hQ h0]
  · rw [mod_div_add_pow_high (by omega)]

/-- Rounds on disjoint axis bit ranges commute. -/
theorem difRoundAt_comm {o h o' h' : ℕ} (h1 : o + h < o' ∨ o' + h' < o) (z : ℕ → Fin r → ℂ) :
    difRoundAt o h (difRoundAt o' h' z) = difRoundAt o' h' (difRoundAt o h z) := by
  simp only [difRoundAt_eq]
  rw [bfly_twist_comm (fun x hx => rexp_add (by omega) hx), bfly_twist_comm (fun x hx => rexp_add (by omega) hx),
    twist_twist, twist_twist, bfly_comm (by omega)]
  congr 1
  funext x; ring

/-! ### Interleaving commuting rounds -/

section Run

variable {α : Type*}

/-- Apply the operators of a list in order. -/
def run : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => run fs (f x)

theorem run_append (L M : List (α → α)) (x : α) : run (L ++ M) x = run M (run L x) := by
  induction L generalizing x with
  | nil => rfl
  | cons f L ih => exact ih (f x)

theorem run_comm_one {f : α → α} : ∀ (L : List (α → α)), (∀ g ∈ L, ∀ x, f (g x) = g (f x)) →
    ∀ x, run (f :: L) x = run (L ++ [f]) x
  | [], _, x => rfl
  | g :: L, h, x => by
    show run L (g (f x)) = run (L ++ [f]) (g x)
    rw [← h g (by simp) x]
    exact run_comm_one L (fun g' hg' => h g' (by simp [hg'])) (g x)

theorem run_swap : ∀ (C L : List (α → α)), (∀ f ∈ C, ∀ g ∈ L, ∀ x, f (g x) = g (f x)) →
    ∀ x, run (C ++ L) x = run (L ++ C) x
  | [], L, _, x => by simp
  | f :: C, L, h, x => by
    have ih := run_swap C L (fun f' hf' => h f' (by simp [hf'])) (f x)
    calc run (f :: C ++ L) x = run (C ++ L) (f x) := rfl
      _ = run (L ++ C) (f x) := ih
      _ = run C (run (f :: L) x) := by rw [run_append]; rfl
      _ = run C (run (L ++ [f]) x) := by rw [run_comm_one L (h f (by simp)) x]
      _ = run (L ++ f :: C) x := by rw [← run_append]; simp

/-- Interleave blocks `Rₖ`, `Cₖ` whose `C` operators commute with every `R` operator. -/
theorem run_interleave : ∀ (B : List (List (α → α) × List (α → α))),
    (∀ p ∈ B, ∀ q ∈ B, ∀ f ∈ p.2, ∀ g ∈ q.1, ∀ x, f (g x) = g (f x)) →
    ∀ x, run (B.flatMap fun p => p.1 ++ p.2) x = run ((B.flatMap Prod.fst) ++ (B.flatMap Prod.snd)) x
  | [], _, x => rfl
  | (R, C) :: B, h, x => by
    have hs := run_swap C (B.flatMap Prod.fst)
      (fun f hf g hg => by
        obtain ⟨q, hq, hg'⟩ := List.mem_flatMap.mp hg
        exact h (R, C) (by simp) q (by simp [hq]) f hf g hg') (run R x)
    simp only [run_append] at hs
    simp only [List.flatMap_cons, run_append]
    rw [run_interleave B (fun p hp q hq => h p (by simp [hp]) q (by simp [hq]))]
    simp only [run_append]
    rw [hs]

end Run

end IntegerMultBounds.Schoenhage
