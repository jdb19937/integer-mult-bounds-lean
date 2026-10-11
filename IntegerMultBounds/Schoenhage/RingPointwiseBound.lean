module

public import IntegerMultBounds.Schoenhage.RingPointwiseProgram

/-! The pointwise-product step's time bound is `O(T p log(r p) log log(r p) + H)`
for each fixed width constant `Cw` (`pointwiseTime_le`): the four
Schönhage–Strassen products per record cost `O(r p log(r p) log log(r p))`, and
every other phase is linear in the record or the header up to one
logarithm. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Schedule

/-! ### Bit lengths -/

theorem size_le_of_lt {n m : ℕ} (h : n < 2 ^ m) : Nat.size n ≤ m := Nat.size_le.mpr h

theorem two_pow_size_le {n : ℕ} (h : 1 ≤ n) : 2 ^ Nat.size n ≤ 2 * n := by
  have hpos := Nat.size_pos.mpr h
  have hlo : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  have e : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem size_cube_le (s : ℕ) : Nat.size (s ^ 3) ≤ 3 * Nat.size s := by
  apply size_le_of_lt
  have := Nat.lt_size_self s
  calc s ^ 3 < (2 ^ Nat.size s) ^ 3 := Nat.pow_lt_pow_left this (by norm_num)
    _ = 2 ^ (3 * Nat.size s) := by rw [← pow_mul, mul_comm]

theorem lt_two_pow_log_succ (n : ℕ) : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n

theorem log_succ_le_self {n : ℕ} (h : 1 ≤ n) : Nat.log 2 n + 1 ≤ n := by
  have := Nat.log_lt_self 2 (show n ≠ 0 by omega); omega

/-! ### The width -/

theorem wOf_le {Cw p l w : ℕ} (hp : 1 ≤ p) (hl : l < p) (hw : w ≤ Cw * p) : wOf p l w ≤ (7 + 4 * Cw) * p := by
  unfold wOf
  have hm : 1 ≤ mW p l w := by unfold mW; omega
  have := two_pow_size_le hm
  have hm2 : mW p l w ≤ (3 + 2 * Cw) * p := by unfold mW; nlinarith
  nlinarith

/-! ### The multiplier's cost -/

theorem size_sum_le {a L LL : ℕ} (hL : L < 2 ^ LL) : Nat.size (a + L) ≤ a + LL + 1 := by
  apply size_le_of_lt
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have h2 : 2 ^ a ≤ 2 ^ (a + LL) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ LL ≤ 2 ^ (a + LL) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem cost_N_le {A a R p L LL N : ℕ} (hA : A < 2 ^ a) (hN : N ≤ A * (R * p)) (hRp : R * p < 2 ^ L)
    (hL : L < 2 ^ LL) (h1 : 1 ≤ L) (h2 : 1 ≤ LL) (hRp1 : 1 ≤ R * p) :
    cost cA cB cC0 N ≤ costC cA cB cC0 * (A + 1) * (a + 2) * (3 * a + 7) * (R * p * L * LL) := by
  refine (cost_le cA cB cC0 N).trans ?_
  have hNlt : N < 2 ^ (a + L) := by
    rw [pow_add]
    calc N ≤ A * (R * p) := hN
      _ < 2 ^ a * 2 ^ L := Nat.mul_lt_mul_of_lt_of_lt hA hRp
  have hs : bitlen N ≤ a + L := size_le_of_lt hNlt
  have hss : bitlen (bitlen N ^ 3) ≤ 3 * (a + LL + 1) := by
    unfold bitlen
    refine (size_cube_le _).trans (Nat.mul_le_mul_left 3 ?_)
    exact (Nat.size_le_size hs).trans (size_sum_le hL)
  have f1 : N + 1 ≤ (A + 1) * (R * p) := by nlinarith
  have f2 : bitlen N + 1 ≤ (a + 2) * L := by nlinarith
  have f3 : bitlen (bitlen N ^ 3) + 1 ≤ (3 * a + 7) * LL := by nlinarith
  calc costC cA cB cC0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1)
      ≤ costC cA cB cC0 * ((A + 1) * (R * p)) * ((a + 2) * L) * ((3 * a + 7) * LL) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ f1) f2) f3
    _ = costC cA cB cC0 * (A + 1) * (a + 2) * (3 * a + 7) * (R * p * L * LL) := by ring

/-! ### One width -/

/-- The multiplier's constant at width constant `Cw`. -/
def ptK (Cw : ℕ) : ℕ :=
  costC cA cB cC0 * (7 + 4 * Cw + 1) * (Nat.size (7 + 4 * Cw) + 2) * (3 * Nat.size (7 + 4 * Cw) + 7)

/-- The constant of the time bound at width constant `Cw`. -/
def ptC (Cw : ℕ) : ℕ :=
  4 * ptK Cw + 10000 * (7 + 4 * Cw) +
    42 * (Nat.size (7 + 4 * Cw) + 1) * (Nat.size (7 + 4 * Cw) + (7 + 4 * Cw) + 11) + 300000

set_option maxHeartbeats 4000000 in
theorem term_le {Cw p l M H w : ℕ} (hp : 2 ≤ p) (hl : 1 ≤ l) (hlp : l < p) (hM : 1 ≤ M) (hw : w ≤ Cw * p) :
    pwCost p 0 l 0 w H M (2 * (2 ^ l * M) * w) + 4 * (H + 3 * (2 * (2 ^ l * M) * w)) + 60 ≤
      ptC Cw * ((2 ^ l * M) * p * (Nat.log 2 (2 ^ l * p) + 1) *
        (Nat.log 2 (Nat.log 2 (2 ^ l * p) + 1) + 1) + H) := by
  unfold pwCost headerCost constCost ringCost
  set A := 7 + 4 * Cw with hAdef
  set a := Nat.size A
  set R := 2 ^ l with hRdef
  set L := Nat.log 2 (R * p) + 1
  set LL := Nat.log 2 L + 1
  set W := wOf p l w
  set K := ptK Cw
  have hR2 : 2 ≤ R := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ R := Nat.pow_le_pow_right (by norm_num) hl
  have hA1 : 1 ≤ A := by omega
  have hAa : A < 2 ^ a := Nat.lt_size_self A
  have hRp : R * p < 2 ^ L := lt_two_pow_log_succ _
  have hLlt : L < 2 ^ LL := lt_two_pow_log_succ _
  have hL1 : 1 ≤ L := by omega
  have hLL1 : 1 ≤ LL := by omega
  have hRp4 : 4 ≤ R * p := by nlinarith
  have hLRp : L ≤ R * p := log_succ_le_self (by omega)
  have hWA : W ≤ A * p := wOf_le (by omega) hlp hw
  have hwA : w ≤ A * p := le_trans hw (Nat.mul_le_mul_right _ (by omega))
  have hpRp : p ≤ R * p := by nlinarith
  have hlRp : l ≤ R * p := by omega
  have hRRp : R ≤ R * p := by nlinarith
  -- the multiplier
  have hN : W * R ≤ A * (R * p) := by nlinarith
  have hcost := cost_N_le (N := W * R) hAa hN hRp hLlt hL1 hLL1 (by omega)
  have hK : costC cA cB cC0 * (A + 1) * (a + 2) * (3 * a + 7) = K := rfl
  rw [hK] at hcost
  -- bit lengths
  have hsp : Nat.size p ≤ L := size_le_of_lt (lt_of_le_of_lt hpRp hRp)
  have hsR : Nat.size R ≤ L := size_le_of_lt (lt_of_le_of_lt hRRp hRp)
  have hsw : Nat.size w ≤ a + L := by
    apply size_le_of_lt
    rw [pow_add]
    calc w ≤ A * (R * p) := le_trans hwA (Nat.mul_le_mul_left _ hpRp)
      _ < 2 ^ a * 2 ^ L := Nat.mul_lt_mul_of_lt_of_lt hAa hRp
  set U := R * p * L
  set Q := R * M * p * L * LL
  have hUQ : U ≤ Q := by
    have : R * p * L * 1 ≤ R * p * L * (M * LL) := Nat.mul_le_mul_left _ (by nlinarith)
    calc U = R * p * L * 1 := by ring
      _ ≤ R * p * L * (M * LL) := this
      _ = Q := by ring
  have hRpU : R * p ≤ U := Nat.le_mul_of_pos_right _ (by omega)
  have hMRpQ : M * (R * p) ≤ Q := by
    have : M * (R * p) * 1 ≤ M * (R * p) * (L * LL) := Nat.mul_le_mul_left _ (by nlinarith)
    calc M * (R * p) = M * (R * p) * 1 := by ring
      _ ≤ M * (R * p) * (L * LL) := this
      _ = Q := by ring
  -- products
  have P1 : Nat.size p * (Nat.size p + p + 10) ≤ 12 * U := by
    calc Nat.size p * (Nat.size p + p + 10) ≤ L * (12 * (R * p)) := Nat.mul_le_mul hsp (by omega)
      _ = 12 * U := by ring
  have P2 : Nat.size R * (Nat.size R + R + 10) ≤ 12 * U := by
    calc Nat.size R * (Nat.size R + R + 10) ≤ L * (12 * (R * p)) := Nat.mul_le_mul hsR (by omega)
      _ = 12 * U := by ring
  have P3 : Nat.size w * (Nat.size w + w + 10) ≤ (a + 1) * (a + A + 11) * U := by
    have h1 : Nat.size w ≤ (a + 1) * L := by nlinarith
    have h2 : Nat.size w + w + 10 ≤ (a + A + 11) * (R * p) := by
      have : A * p ≤ A * (R * p) := Nat.mul_le_mul_left _ hpRp
      nlinarith
    calc Nat.size w * (Nat.size w + w + 10) ≤ ((a + 1) * L) * ((a + A + 11) * (R * p)) := Nat.mul_le_mul h1 h2
      _ = (a + 1) * (a + A + 11) * U := by ring
  have P4 : M * cost cA cB cC0 (W * R) ≤ K * Q := by
    calc M * cost cA cB cC0 (W * R) ≤ M * (K * (R * p * L * LL)) := Nat.mul_le_mul_left _ hcost
      _ = K * Q := by ring
  have P5 : M * (R * w) ≤ A * Q := by
    have : R * w ≤ A * (R * p) := by nlinarith
    calc M * (R * w) ≤ M * (A * (R * p)) := Nat.mul_le_mul_left _ this
      _ = A * (M * (R * p)) := by ring
      _ ≤ A * Q := Nat.mul_le_mul_left _ hMRpQ
  have P6 : M * (W * R) ≤ A * Q := by
    calc M * (W * R) ≤ M * (A * (R * p)) := Nat.mul_le_mul_left _ hN
      _ = A * (M * (R * p)) := by ring
      _ ≤ A * Q := Nat.mul_le_mul_left _ hMRpQ
  have P7 : M * (R * (p + l)) ≤ 2 * Q := by
    have : R * (p + l) ≤ 2 * (R * p) := by nlinarith
    calc M * (R * (p + l)) ≤ M * (2 * (R * p)) := Nat.mul_le_mul_left _ this
      _ = 2 * (M * (R * p)) := by ring
      _ ≤ 2 * Q := Nat.mul_le_mul_left _ hMRpQ
  have P8 : M * R ≤ Q := le_trans (by nlinarith) hMRpQ
  have P9 : W * R ≤ A * U := le_trans hN (Nat.mul_le_mul_left _ hRpU)
  have P10 : R * W ≤ A * U := by rw [mul_comm]; exact P9
  have P11 : W ≤ A * U := le_trans hWA (Nat.mul_le_mul_left _ (le_trans hpRp hRpU))
  have P12 : w ≤ A * U := le_trans hwA (Nat.mul_le_mul_left _ (le_trans hpRp hRpU))
  have P13 : R * M * w ≤ A * Q := by
    calc R * M * w = M * (R * w) := by ring
      _ ≤ A * Q := P5
  have e2 : M * (R * (56 * w + 400) + (4 * (cost cA cB cC0 (W * R) + 640 * (W * R) + 56000) + 2000 * (W * R) +
      400 * R * (W + w + (p + l) + 10) + 20000) + 204) =
      56 * (M * (R * w)) + 400 * (M * R) + 4 * (M * cost cA cB cC0 (W * R)) + 4560 * (M * (W * R)) +
      400 * (M * (W * R)) + 400 * (M * (R * w)) + 400 * (M * (R * (p + l))) + 4000 * (M * R) + 244204 * M := by ring
  rw [e2]
  have e3 : 2 * (2 ^ l * M) * w = 2 * (R * M * w) := by ring
  rw [e3]
  have hMQ : M ≤ Q := le_trans (by nlinarith) P8
  have hptC : ptC Cw = 4 * K + 10000 * A + 42 * (a + 1) * (a + A + 11) + 300000 := rfl
  rw [hptC]
  have hl' : l ≤ U := le_trans hlRp hRpU
  have hp' : p ≤ U := le_trans hpRp hRpU
  have hR' : R ≤ U := le_trans hRRp hRpU
  have h1U : 1 ≤ U := by omega
  generalize M * cost cA cB cC0 (W * R) = C1 at *
  generalize Nat.size p * (Nat.size p + p + 10) = S1 at *
  generalize Nat.size R * (Nat.size R + R + 10) = S2 at *
  generalize Nat.size w * (Nat.size w + w + 10) = S3 at *
  have X1 : A * U ≤ A * Q := Nat.mul_le_mul_left _ hUQ
  have X2 : (a + 1) * (a + A + 11) * U ≤ (a + 1) * (a + A + 11) * Q := Nat.mul_le_mul_left _ hUQ
  have X3 : 0 ≤ K * H := Nat.zero_le _
  nlinarith [X1, X2, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, hUQ, hMQ, hl', hp', hR', h1U]

/-! ### Every width -/

theorem pointwiseTime_le (Cw : ℕ) (hCw : 2 ≤ Cw) : ∃ C : ℕ, ∀ p l M H : ℕ, 1 ≤ l → 2 ≤ p → l < p → 1 ≤ M →
    pointwiseTime Cw (2 ^ l * M) p (2 ^ l) H ≤
      C * ((2 ^ l * M) * p * (Nat.log 2 (2 ^ l * p) + 1) * (Nat.log 2 (Nat.log 2 (2 ^ l * p) + 1) + 1) + H) := by
  refine ⟨ptC Cw, fun p l M H hl hp hlp hM => ?_⟩
  unfold pointwiseTime
  apply Finset.sup_le
  intro w hw
  have hw' : w ≤ Cw * p := by simp at hw; omega
  rw [Nat.log_pow (by norm_num), Nat.mul_div_cancel_left _ (by positivity)]
  exact term_le hp hl hlp hM hw'

end IntegerMultBounds.Schoenhage
