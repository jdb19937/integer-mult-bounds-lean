module

public import IntegerMultBounds.Schoenhage.DifOpposite
public import IntegerMultBounds.Spec.SimultaneousLayerFacts

/-! The parallel butterfly of `prop:simultaneous-layer` as butterflies on
physical bits. With the suffix length `S = 2^s`, the layer operator
`hadamard D K ρ S` is the butterfly on the bits `s + jK + ρ`, `j < D`
(`hadamard_eq_bflys`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-! ### Bits -/

/-- Address `x` with bit `P` set to `c`. -/
def setBit (x P : ℕ) (c : Bool) : ℕ :=
  x - (if bitAt x P = 1 then 2 ^ P else 0) + (if c then 2 ^ P else 0)

theorem bitAt_eq_one_iff_ne_zero (x P : ℕ) : bitAt x P = 1 ↔ bitAt x P ≠ 0 := by
  have := bitAt_lt_two x P; omega

theorem setBit_false_of_zero {x P : ℕ} (h : bitAt x P = 0) : setBit x P false = x := by
  simp [setBit, h]

theorem setBit_true_of_zero {x P : ℕ} (h : bitAt x P = 0) : setBit x P true = x + 2 ^ P := by
  simp [setBit, h]

theorem setBit_false_of_one {x P : ℕ} (h : bitAt x P = 1) : setBit x P false = x - 2 ^ P := by
  simp [setBit, h]

theorem setBit_true_of_one {x P : ℕ} (h : bitAt x P = 1) : setBit x P true = x := by
  have := le_of_bitAt (show bitAt x P ≠ 0 by omega)
  simp [setBit, h]; omega

/-- `setBit` leaves every other bit unchanged. -/
theorem bitAt_setBit_ne {x P Q : ℕ} (hPQ : Q ≠ P) (c : Bool) : bitAt (setBit x P c) Q = bitAt x Q := by
  rcases Nat.lt_or_ge (bitAt x P) 1 with h | h
  · have h0 : bitAt x P = 0 := by omega
    cases c
    · rw [setBit_false_of_zero h0]
    · rw [setBit_true_of_zero h0]; exact bitAt_add_ne hPQ h0
  · have h1 : bitAt x P = 1 := by have := bitAt_lt_two x P; omega
    cases c
    · rw [setBit_false_of_one h1]; exact bitAt_sub_ne hPQ (by omega)
    · rw [setBit_true_of_one h1]

/-- Clearing a set bit subtracts its value. -/
theorem setBit_false_add {x P : ℕ} : setBit x P false + (if bitAt x P = 1 then 2 ^ P else 0) = x := by
  rcases Nat.lt_or_ge (bitAt x P) 1 with h | h
  · have h0 : bitAt x P = 0 := by omega
    simp [setBit, h0]
  · have h1 : bitAt x P = 1 := by have := bitAt_lt_two x P; omega
    have := le_of_bitAt (show bitAt x P ≠ 0 by omega)
    simp [setBit, h1]; omega

theorem setBit_eq_clear_add (x P : ℕ) (c : Bool) :
    setBit x P c = setBit x P false + (if c then 2 ^ P else 0) := by
  simp [setBit]

/-! ### The selected bits of a layer address -/

theorem div_two_pow_div_two_pow (x s m : ℕ) : x / 2 ^ s / 2 ^ m = x / 2 ^ (s + m) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- The selected bit of chunk `j` is the physical bit `s + jK + ρ`. -/
theorem selBit_pow {D K ρ s x : ℕ} (j : Fin D) :
    selBit K ρ (2 ^ s) x j = decide (bitAt x (s + selPos K ρ j) = 1) := by
  unfold selBit bitAt
  rw [Nat.testBit_eq_decide_div_mod_eq, div_two_pow_div_two_pow]

/-- The cleared value `Σⱼ [selected bit j set] 2^(jK+ρ)`. -/
def clearSum (K ρ : ℕ) : (D : ℕ) → (s x : ℕ) → ℕ
  | 0, _, _ => 0
  | D + 1, s, x => (if bitAt x (s + ρ) = 1 then 2 ^ ρ else 0) + 2 ^ K * clearSum K ρ D (s + K) x

/-- The written value `Σⱼ [b j] 2^(jK+ρ)`. -/
def writeSum (K ρ : ℕ) : (D : ℕ) → (Fin D → Bool) → ℕ
  | 0, _ => 0
  | D + 1, b => (if b 0 then 2 ^ ρ else 0) + 2 ^ K * writeSum K ρ D (Fin.tail b)

theorem selPos_succ (K ρ : ℕ) {D : ℕ} (j : Fin D) : selPos K ρ j.succ = K + selPos K ρ j := by
  simp [selPos, Fin.val_succ]; ring

theorem sum_sel_eq_clearSum (K ρ : ℕ) : ∀ (D s x : ℕ),
    (∑ j : Fin D, if selBit K ρ (2 ^ s) x j then 2 ^ selPos K ρ j else 0) = clearSum K ρ D s x
  | 0, _, _ => by simp [clearSum]
  | D + 1, s, x => by
    rw [Fin.sum_univ_succ, clearSum, ← sum_sel_eq_clearSum K ρ D (s + K) x, Finset.mul_sum]
    congr 1
    · simp [selBit_pow, selPos]
    · apply Finset.sum_congr rfl
      intro j _
      rw [selBit_pow, selBit_pow, selPos_succ, show s + (K + selPos K ρ j) = s + K + selPos K ρ j by ring,
        pow_add]
      split_ifs <;> simp

theorem sum_write_eq_writeSum (K ρ : ℕ) : ∀ (D : ℕ) (b : Fin D → Bool),
    (∑ j : Fin D, if b j then 2 ^ selPos K ρ j else 0) = writeSum K ρ D b
  | 0, _ => by simp [writeSum]
  | D + 1, b => by
    rw [Fin.sum_univ_succ, writeSum, ← sum_write_eq_writeSum K ρ D (Fin.tail b), Finset.mul_sum]
    congr 1
    · simp [selPos]
    · apply Finset.sum_congr rfl
      intro j _
      rw [selPos_succ, pow_add]
      simp only [Fin.tail]
      by_cases hb : b j.succ = true <;> simp [hb]

theorem setSel_pow {D K ρ s : ℕ} (x : ℕ) (b : Fin D → Bool) :
    setSel K ρ (2 ^ s) x b = x - 2 ^ s * clearSum K ρ D s x + 2 ^ s * writeSum K ρ D b := by
  unfold setSel
  rw [sum_sel_eq_clearSum, sum_write_eq_writeSum]

/-- The cleared value ignores bits below `s`. -/
theorem clearSum_congr (K ρ : ℕ) : ∀ (D s x y : ℕ), (∀ Q, s ≤ Q → bitAt x Q = bitAt y Q) →
    clearSum K ρ D s x = clearSum K ρ D s y
  | 0, _, _, _, _ => rfl
  | D + 1, s, x, y, h => by
    simp only [clearSum]
    rw [h (s + ρ) (by omega), clearSum_congr K ρ D (s + K) x y (fun Q hQ => h Q (by omega))]

/-- The selected bits sum to at most `x`. -/
theorem clearSum_le {K ρ : ℕ} (hρ : ρ < K) : ∀ (D s x : ℕ), 2 ^ s * clearSum K ρ D s x ≤ x
  | 0, _, _ => by simp [clearSum]
  | D + 1, s, x => by
    simp only [clearSum]
    have hcl := clearSum_congr K ρ D (s + K) x (setBit x (s + ρ) false)
      (fun Q hQ => (bitAt_setBit_ne (by omega) false).symm)
    have ih := clearSum_le hρ D (s + K) (setBit x (s + ρ) false)
    have hadd := setBit_false_add (x := x) (P := s + ρ)
    rw [hcl]
    have e : 2 ^ s * ((if bitAt x (s + ρ) = 1 then 2 ^ ρ else 0) + 2 ^ K * clearSum K ρ D (s + K)
        (setBit x (s + ρ) false)) = (if bitAt x (s + ρ) = 1 then 2 ^ (s + ρ) else 0) +
        2 ^ (s + K) * clearSum K ρ D (s + K) (setBit x (s + ρ) false) := by
      rw [pow_add, pow_add]; split_ifs <;> ring
    rw [e]
    omega

/-- Peeling chunk `0`: setting the selected bits of `x` to `cons c b` sets bit `s + ρ` to `c`,
then the remaining chunks at suffix `s + K`. -/
theorem setSel_cons {D K ρ s : ℕ} (hρ : ρ < K) (x : ℕ) (c : Bool) (b : Fin D → Bool) :
    setSel K ρ (2 ^ s) x (Fin.cons c b : Fin (D + 1) → Bool) =
      setSel K ρ (2 ^ (s + K)) (setBit x (s + ρ) c) b := by
  rw [setSel_pow, setSel_pow]
  simp only [clearSum, writeSum, Fin.cons_zero, Fin.tail_cons]
  set x0 := setBit x (s + ρ) false with hx0
  have hcl : clearSum K ρ D (s + K) x = clearSum K ρ D (s + K) x0 :=
    clearSum_congr K ρ D (s + K) x x0 (fun Q hQ => (bitAt_setBit_ne (by omega) false).symm)
  have hcl' : clearSum K ρ D (s + K) (setBit x (s + ρ) c) = clearSum K ρ D (s + K) x0 :=
    clearSum_congr K ρ D (s + K) _ x0 (fun Q hQ => by
      rw [bitAt_setBit_ne (by omega) c, bitAt_setBit_ne (by omega) false])
  have hadd : x0 + (if bitAt x (s + ρ) = 1 then 2 ^ (s + ρ) else 0) = x := setBit_false_add
  have hle := clearSum_le hρ D (s + K) x0
  have hc : setBit x (s + ρ) c = x0 + (if c then 2 ^ (s + ρ) else 0) := setBit_eq_clear_add _ _ _
  rw [hcl, hcl', hc]
  have e1 : 2 ^ s * ((if bitAt x (s + ρ) = 1 then 2 ^ ρ else 0) + 2 ^ K * clearSum K ρ D (s + K) x0) =
      (if bitAt x (s + ρ) = 1 then 2 ^ (s + ρ) else 0) + 2 ^ (s + K) * clearSum K ρ D (s + K) x0 := by
    rw [pow_add, pow_add]; split_ifs <;> ring
  have e2 : 2 ^ s * ((if c then 2 ^ ρ else 0) + 2 ^ K * writeSum K ρ D b) =
      (if c then 2 ^ (s + ρ) else 0) + 2 ^ (s + K) * writeSum K ρ D b := by
    rw [pow_add, pow_add]; split_ifs <;> ring
  rw [e1, e2]
  omega

/-- Peeling chunk `0` of the sign. -/
theorem card_sel_cons {D K ρ s : ℕ} (hρ : ρ < K) (x : ℕ) (c : Bool) (b : Fin D → Bool) :
    (Finset.univ.filter fun j : Fin (D + 1) => selBit K ρ (2 ^ s) x j && (Fin.cons c b : Fin (D + 1) → Bool) j).card =
      (if bitAt x (s + ρ) = 1 ∧ c = true then 1 else 0) +
        (Finset.univ.filter fun j : Fin D => selBit K ρ (2 ^ (s + K)) (setBit x (s + ρ) c) j && b j).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  congr 1
  · simp [selBit_pow, selPos]
  · apply Finset.sum_congr rfl
    intro j _
    rw [selBit_pow, selBit_pow, selPos_succ, Fin.cons_succ,
      show s + (K + selPos K ρ j) = s + K + selPos K ρ j by ring,
      bitAt_setBit_ne (by unfold selPos; omega) c]

/-! ### Butterflies -/

variable {r : ℕ}

/-- The butterfly as a two-term sum over the new value of bit `P`. -/
theorem bfly_eq_sum (P : ℕ) (w : ℕ → Fin r → ℂ) (x : ℕ) (k : Fin r) :
    bfly P w x k = (1 / 2 : ℂ) * ∑ c : Bool,
      (-1 : ℂ) ^ (if bitAt x P = 1 ∧ c = true then 1 else 0) * w (setBit x P c) k := by
  rw [Fintype.sum_bool]
  unfold bfly
  rcases Nat.lt_or_ge (bitAt x P) 1 with h | h
  · have h0 : bitAt x P = 0 := by omega
    simp only [h0, ↓reduceIte, setBit_true_of_zero h0, setBit_false_of_zero h0, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    simp; ring
  · have h1 : bitAt x P = 1 := by have := bitAt_lt_two x P; omega
    have hne : bitAt x P ≠ 0 := by omega
    simp only [hne, ↓reduceIte, h1, setBit_true_of_one h1, setBit_false_of_one h1, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    simp; ring

theorem sum_fin_succ_bool {D : ℕ} (F : (Fin (D + 1) → Bool) → ℂ) :
    ∑ b, F b = ∑ c : Bool, ∑ b : Fin D → Bool, F (Fin.cons c b) := by
  rw [← (Fin.consEquiv fun _ : Fin (D + 1) => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

/-- One more chunk: the layer on `D + 1` chunks with suffix `2^s` is the butterfly on bit `s + ρ`
after the layer on the remaining `D` chunks with suffix `2^(s + K)`. -/
theorem hadamard_succ {D K ρ s : ℕ} (hρ : ρ < K) (z : ℕ → Fin r → ℂ) :
    hadamard (D + 1) K ρ (2 ^ s) z = bfly (s + ρ) (hadamard D K ρ (2 ^ (s + K)) z) := by
  funext x k
  rw [bfly_eq_sum]
  unfold hadamard
  rw [sum_fin_succ_bool, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [card_sel_cons hρ, setSel_cons hρ, pow_add]
  push_cast
  ring

/-- The selected physical bits, top chunk first: `s + (D-1)K + ρ, …, s + ρ`. -/
def selList (s K ρ : ℕ) : ℕ → List ℕ
  | 0 => []
  | D + 1 => selList (s + K) K ρ D ++ [s + ρ]

/-- `hadamard_eq_bflys`: the parallel butterfly of `prop:simultaneous-layer` with suffix `2^s`
is the butterfly on the physical bits `s + jK + ρ`. -/
theorem hadamard_eq_bflys {K ρ : ℕ} (hρ : ρ < K) : ∀ (D s : ℕ) (z : ℕ → Fin r → ℂ),
    hadamard D K ρ (2 ^ s) z = bflys (selList s K ρ D) z
  | 0, s, z => by
    funext x k
    simp [hadamard, bflys, selList, run, setSel]
  | D + 1, s, z => by
    rw [hadamard_succ hρ, hadamard_eq_bflys hρ D (s + K) z]
    simp only [selList, bflys, List.map_append, run_append]
    rfl

/-! ### Rounding commutes with the twist -/

theorem rho0_neg (x : ℝ) : rho0 (-x) = -rho0 x := by
  unfold rho0
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos (by linarith), if_neg (by linarith), Int.floor_neg]
  · subst h; simp
  · rw [if_neg (by linarith), if_pos (by linarith), Int.ceil_neg]

theorem rhoC_neg (p : ℕ) (u : ℂ) : rhoC p (-u) = -rhoC p u := by
  apply Complex.ext <;> simp [rhoC_re, rhoC_im, rho0_neg, neg_div]

theorem rhoC_neg_one_pow (p m : ℕ) (u : ℂ) : rhoC p ((-1 : ℂ) ^ m * u) = (-1 : ℂ) ^ m * rhoC p u := by
  rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h]
  · simp
  · simp [rhoC_neg]

/-- Grid rounding of every coefficient of an array. -/
noncomputable def roundArr (p : ℕ) (w : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ := fun y k => rhoC p (w y k)

variable [NeZero r]

theorem shiftInv_apply (e : ℕ) (v : Fin r → ℂ) (k : Fin r) :
    ∃ (m : ℕ) (j : Fin r), shiftInv e v k = (-1 : ℂ) ^ m * v j := by
  unfold shiftInv
  rw [shiftNegZ_apply]
  exact ⟨_, _, rfl⟩

/-- The twist only permutes and negates coefficients, so rounding commutes with it. -/
theorem roundArr_twist (p : ℕ) (f : ℕ → ℕ) (w : ℕ → Fin r → ℂ) :
    roundArr p (twist f w) = twist f (roundArr p w) := by
  funext y k
  unfold roundArr twist shiftInv
  rw [shiftNegZ_apply, shiftNegZ_apply, rhoC_neg_one_pow]

/-! ### Contractions on the first `2^n` records -/

/-- `G` maps arrays bounded by `ε` on the first `2^n` records to such arrays. -/
def Contracts (n : ℕ) (G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) : Prop :=
  ∀ (v : ℕ → Fin r → ℂ) (ε : ℝ), (∀ y < 2 ^ n, ∀ k, ‖v y k‖ ≤ ε) → ∀ y < 2 ^ n, ∀ k, ‖G v y k‖ ≤ ε

/-- `G` commutes with differences. -/
def Additive (G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) : Prop := ∀ a b, G (a - b) = G a - G b

omit [NeZero r] in
theorem bfly_contracts {n P : ℕ} (hP : P < n) : Contracts (r := r) n (bfly P) := by
  intro v ε hv y hy k
  unfold bfly
  by_cases hb : bitAt y P = 0
  · simp only [hb, ↓reduceIte, Pi.smul_apply, Pi.add_apply, smul_eq_mul, norm_mul]
    have h1 := hv y hy k
    have h2 := hv (y + 2 ^ P) (add_pow_lt hy hP hb) k
    calc ‖(1 / 2 : ℂ)‖ * ‖v y k + v (y + 2 ^ P) k‖ ≤ 1 / 2 * (‖v y k‖ + ‖v (y + 2 ^ P) k‖) := by
          rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]; gcongr; exact norm_add_le _ _
      _ ≤ ε := by linarith
  · simp only [hb, ↓reduceIte, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul]
    have h1 := hv y hy k
    have h2 := hv (y - 2 ^ P) (lt_of_le_of_lt (Nat.sub_le _ _) hy) k
    calc ‖(1 / 2 : ℂ)‖ * ‖v (y - 2 ^ P) k - v y k‖ ≤ 1 / 2 * (‖v (y - 2 ^ P) k‖ + ‖v y k‖) := by
          rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]; gcongr; exact norm_sub_le _ _
      _ ≤ ε := by linarith

omit [NeZero r] in
theorem bfly_additive (P : ℕ) : Additive (r := r) (bfly P) := by
  intro a b
  funext y k
  by_cases hb : bitAt y P = 0
  · simp only [bfly, hb, ↓reduceIte, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
  · simp only [bfly, hb, ↓reduceIte, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem twist_contracts (n : ℕ) (f : ℕ → ℕ) : Contracts (r := r) n (twist f) := by
  intro v ε hv y hy k
  obtain ⟨m, j, h⟩ := shiftInv_apply (f y) (v y) k
  simp only [twist, h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hv y hy j

theorem twist_additive (f : ℕ → ℕ) : Additive (r := r) (twist f) := by
  intro a b
  funext y
  simp only [twist, Pi.sub_apply, shiftInv_sub_vec]

omit [NeZero r] in
theorem run_contracts {n : ℕ} : ∀ (L : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)),
    (∀ G ∈ L, Contracts n G) → Contracts n (run L)
  | [], _ => fun _ _ hv => hv
  | G :: L, h => fun v ε hv => run_contracts L (fun G' hG' => h G' (by simp [hG'])) _ ε
      (h G (by simp) v ε hv)

omit [NeZero r] in
theorem run_additive : ∀ (L : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)),
    (∀ G ∈ L, Additive G) → Additive (run L)
  | [], _ => fun _ _ => rfl
  | G :: L, h => fun a b => by
    show run L (G (a - b)) = run L (G a) - run L (G b)
    rw [h G (by simp), run_additive L (fun G' hG' => h G' (by simp [hG']))]

/-! ### The computed schedule -/

/-- The computed rounds: each round followed by grid rounding. -/
noncomputable def roundRun (p : ℕ) : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) → (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ
  | [], w => w
  | G :: L, w => roundRun p L (roundArr p (G w))

theorem roundRun_le (p n : ℕ) : ∀ (L : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)),
    (∀ G ∈ L, Contracts n G ∧ Additive G) → ∀ (w₁ w₂ : ℕ → Fin r → ℂ) (δ : ℝ),
    (∀ y < 2 ^ n, ∀ k, ‖w₁ y k - w₂ y k‖ ≤ δ) →
    ∀ y < 2 ^ n, ∀ k, ‖roundRun p L w₁ y k - run L w₂ y k‖ ≤ δ + L.length * (Real.sqrt 2 / 2 ^ p)
  | [], _, w₁, w₂, δ, h => fun y hy k => by simpa [roundRun, run] using h y hy k
  | G :: L, hL, w₁, w₂, δ, h => fun y hy k => by
    have hG := hL G (by simp)
    have step : ∀ y < 2 ^ n, ∀ k, ‖roundArr p (G w₁) y k - G w₂ y k‖ ≤ δ + Real.sqrt 2 / 2 ^ p := by
      intro y hy k
      have hd := hG.1 (w₁ - w₂) δ (fun y hy k => by simpa using h y hy k) y hy k
      rw [hG.2] at hd
      have hr := (norm_rhoC_sub_lt p (G w₁ y k)).le
      calc ‖roundArr p (G w₁) y k - G w₂ y k‖
          ≤ ‖rhoC p (G w₁ y k) - G w₁ y k‖ + ‖G w₁ y k - G w₂ y k‖ := by
            unfold roundArr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ Real.sqrt 2 / 2 ^ p + δ := by simp only [Pi.sub_apply] at hd; linarith
        _ = δ + Real.sqrt 2 / 2 ^ p := add_comm _ _
    have := roundRun_le p n L (fun G' hG' => hL G' (by simp [hG'])) _ _ _ step y hy k
    simp only [roundRun, run, List.length_cons, Nat.cast_succ] at this ⊢
    linarith

theorem roundRun_disk (p n : ℕ) : ∀ (L : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)),
    (∀ G ∈ L, Contracts n G) → ∀ (w : ℕ → Fin r → ℂ), (∀ y < 2 ^ n, ∀ k, ‖w y k‖ ≤ 1) →
    ∀ y < 2 ^ n, ∀ k, ‖roundRun p L w y k‖ ≤ 1
  | [], _, w, h => h
  | G :: L, hL, w, h => roundRun_disk p n L (fun G' hG' => hL G' (by simp [hG'])) _
      (fun y hy k => (norm_rhoC_le _ _).trans (hL G (by simp) w 1 h y hy k))

/-- A finite family of numbers each below `c` has a common bound below `c`. -/
theorem exists_uniform_lt {N : ℕ} (f : ℕ → Fin r → ℝ) {c : ℝ} (h : ∀ y < N, ∀ k, f y k < c) :
    ∃ c' < c, ∀ y < N, ∀ k, f y k ≤ c' := by
  classical
  set s := (Finset.range N) ×ˢ (Finset.univ : Finset (Fin r))
  rcases s.eq_empty_or_nonempty with hs | hs
  · refine ⟨c - 1, by linarith, fun y hy k => ?_⟩
    have : (y, k) ∈ s := Finset.mem_product.mpr ⟨Finset.mem_range.mpr hy, Finset.mem_univ _⟩
    rw [hs] at this; simp at this
  · obtain ⟨q, hq, hmax⟩ := s.exists_max_image (fun q => f q.1 q.2) hs
    have hq' := Finset.mem_product.mp hq
    refine ⟨f q.1 q.2, h _ (Finset.mem_range.mp hq'.1) _, fun y hy k => ?_⟩
    exact hmax (y, k) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hy, Finset.mem_univ _⟩)

/-- With at least one round the error is strictly below `length · √2 · 2^(-p)`. -/
theorem roundRun_lt (p n : ℕ) (L : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)) (hne : L ≠ [])
    (hL : ∀ G ∈ L, Contracts n G ∧ Additive G) (w : ℕ → Fin r → ℂ) :
    ∀ y < 2 ^ n, ∀ k, ‖roundRun p L w y k - run L w y k‖ < L.length * (Real.sqrt 2 / 2 ^ p) := by
  obtain ⟨G, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hG := hL G (by simp)
  have hstep : ∀ y < 2 ^ n, ∀ k, ‖roundArr p (G w) y k - G w y k‖ < Real.sqrt 2 / 2 ^ p :=
    fun y _ k => norm_rhoC_sub_lt p _
  obtain ⟨c', hc', hbound⟩ := exists_uniform_lt (N := 2 ^ n)
    (fun y k => ‖roundArr p (G w) y k - G w y k‖) hstep
  intro y hy k
  have := roundRun_le p n L' (fun G' hG' => hL G' (by simp [hG'])) _ _ c' hbound y hy k
  simp only [roundRun, run, List.length_cons, Nat.cast_succ] at this ⊢
  linarith

/-! ### The grouped forward schedule -/

/-- The axes taking part in the round at slot `h`. -/
def slotAxes (ts : List ℕ) (h : ℕ) : List ℕ := (List.range ts.length).filter fun i => h < axLen ts i

/-- The grouped round at slot `h`: the butterflies of every participating axis, then one twist. -/
noncomputable def slotRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (h : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  fun w => twist (slotExp π r ts (slotAxes ts h) h) (bflys (slotBits π ts (slotAxes ts h) h) w)

/-- The grouped rounds, from the top slot down. -/
noncomputable def slotRounds {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) :
    List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) :=
  (List.range H).reverse.map (slotRound π ts)

omit [NeZero r] in
theorem run_flatMap {β : Type*} (F : β → (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) (g : ℕ → List β) :
    ∀ (L : List ℕ) (w : ℕ → Fin r → ℂ),
      run ((L.flatMap g).map F) w = run (L.map fun a => run ((g a).map F)) w
  | [], _ => rfl
  | a :: L, w => by
    rw [List.flatMap_cons, List.map_append, run_append, List.map_cons]
    exact run_flatMap F g L _

/-- Grouping the paper's schedule by slot. -/
theorem fwdSchedule_slotRounds {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (H : ℕ) : fwdSchedule (r := r) π ts H = run (slotRounds (r := r) π ts H) := by
  funext w
  unfold fwdSchedule slotRounds slotPairs
  rw [run_flatMap]
  congr 1
  apply List.map_congr_left
  intro h _
  funext v
  rw [List.map_map]
  exact run_group π hts hn h (slotAxes ts h) ((List.nodup_range).filter _)
    (fun i hi => by
      simp only [slotAxes, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
      exact hi) v

theorem slotRound_contracts {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h : ℕ) : Contracts n (slotRound (r := r) π ts h) ∧ Additive (slotRound (r := r) π ts h) := by
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  have hbits : ∀ P ∈ slotBits π ts (slotAxes ts h) h, P < n := by
    intro P hP
    simp only [slotBits, slotAxes, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hP
    obtain ⟨i, ⟨hi, hih⟩, rfl⟩ := hP
    have := axOff_add_len_le hts hi
    exact π.σ_lt _ (by omega)
  constructor
  · intro v ε hv
    exact twist_contracts n _ _ ε (run_contracts _ (fun G hG => by
      simp only [List.mem_map] at hG
      obtain ⟨P, hP, rfl⟩ := hG
      exact bfly_contracts (hbits P hP)) v ε hv)
  · intro a b
    unfold slotRound
    rw [show bflys (slotBits π ts (slotAxes ts h) h) (a - b) =
        bflys (slotBits π ts (slotAxes ts h) h) a - bflys (slotBits π ts (slotAxes ts h) h) b from
      run_additive _ (fun G hG => by
        simp only [List.mem_map] at hG
        obtain ⟨P, -, rfl⟩ := hG
        exact bfly_additive P) a b, twist_additive]

/-- On tape a grouped round is computed as the rounded layer `Q_p(ℋ w)` followed by the exact
twist; this is the rounded grouped round. -/
theorem roundArr_slotRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (h p : ℕ) (w : ℕ → Fin r → ℂ) :
    roundArr p (slotRound π ts h w) =
      twist (slotExp π r ts (slotAxes ts h) h) (roundArr p (bflys (slotBits π ts (slotAxes ts h) h) w)) :=
  roundArr_twist p _ _

/-- The computed forward schedule: every grouped round rounded to the grid. -/
noncomputable def compSchedule (p : ℕ) {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  roundRun p (slotRounds π ts H)

/-- `compSchedule_close`: the computed forward schedule over `H ≥ 1` slots stays within
`√2 · H · 2^(-p)` per coefficient of `L B F⁻ z` for input stored in layout `π`, and in the
unit disk for unit-disk input. -/
theorem compSchedule_close {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (hH0 : 0 < H) (p : ℕ)
    (z w : ℕ → Fin r → ℂ) (hw : Agree n w fun y => z (π.logi y)) :
    (∀ y < 2 ^ n, ∀ k, ‖compSchedule p π ts H w y k - fwdExact ts (π.toPerm hn) z y k‖ <
      Real.sqrt 2 * H / 2 ^ p) ∧
    ((∀ y < 2 ^ n, ∀ k, ‖w y k‖ ≤ 1) → ∀ y < 2 ^ n, ∀ k, ‖compSchedule p π ts H w y k‖ ≤ 1) := by
  have hrounds : ∀ G ∈ slotRounds (r := r) π ts H, Contracts n G ∧ Additive G := by
    intro G hG
    simp only [slotRounds, List.mem_map] at hG
    obtain ⟨h, -, rfl⟩ := hG
    exact slotRound_contracts hts hn π h
  have hlen : (slotRounds (r := r) π ts H).length = H := by simp [slotRounds]
  have hne : slotRounds (r := r) π ts H ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  refine ⟨fun y hy k => ?_, fun hdisk => roundRun_disk p n _ (fun G hG => (hrounds G hG).1) w hdisk⟩
  have hlt := roundRun_lt p n _ hne hrounds w y hy k
  rw [← fwdSchedule_slotRounds hts hn π H, fwdSchedule_fwdExact hts hn π hH z w hw hy, hlen] at hlt
  unfold compSchedule
  calc _ < (H : ℝ) * (Real.sqrt 2 / 2 ^ p) := hlt
    _ = Real.sqrt 2 * H / 2 ^ p := by ring

end IntegerMultBounds.Schoenhage
