module

public import IntegerMultBounds.MathlibTM2.Layer.CompactDigits

/-!
# Segments of a slot and digits of a compact field

A slot value `Y` of `f K` bits has `n` low segments of `K` bits at `ρ + c K`, `c < n`:
`seg ρ K c Y = window (ρ + c K) K Y`. `asm ρ K n low s top` assembles a value from its low `ρ`
bits, the segments `s c` and the part `top` above bit `ρ + n K`; `eq_asm` decomposes every value
and `seg_asm`, `asm_mod`, `asm_div` read the parts back. Adding `∑ δ c 2^(ρ + c K)` adds `δ c` to
segment `c` (`asm_add`), so a rotation without carries between segments acts segmentwise.

A compact field of `n G` bits has `n` radix-`2^G` digits `cdig G c w = window (c G) G w`;
`casm G n s = ∑ s c 2^(c G)` (`cdig_casm`, `eq_casm`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactDigits

open Finset

/-! ### Segments of a slot -/

section Segments

variable (ρ K : ℕ)

/-- Segment `c` of a slot value: `K` bits at `ρ + c K`. -/
def seg (c Y : ℕ) : ℕ := window (ρ + c * K) K Y

/-- A value from its low `ρ` bits, its first `n` segments and its part above `ρ + n K`. -/
def asm (n low : ℕ) (s : ℕ → ℕ) (top : ℕ) : ℕ :=
  low + (∑ c ∈ range n, s c * 2 ^ (c * K)) * 2 ^ ρ + top * 2 ^ (ρ + n * K)

/-- The segment sum of `n` segments below `2 ^ K` fits in `n K` bits. -/
lemma segSum_lt {n : ℕ} {s : ℕ → ℕ} (hs : ∀ c < n, s c < 2 ^ K) :
    ∑ c ∈ range n, s c * 2 ^ (c * K) < 2 ^ (n * K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.succ_mul, Nat.pow_add]
    have h1 := ih (fun c hc => hs c (by omega))
    have h2 := hs n (by omega)
    have : (s n + 1) * 2 ^ (n * K) ≤ 2 ^ K * 2 ^ (n * K) := Nat.mul_le_mul_right _ h2
    nlinarith

/-- Segment `c < n` of the segment sum. -/
lemma window_segSum {n c : ℕ} {s : ℕ → ℕ} (hs : ∀ c < n, s c < 2 ^ K) (hc : c < n) :
    window (c * K) K (∑ c ∈ range n, s c * 2 ^ (c * K)) = s c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · rw [window_add_mul_low (by nlinarith)]
      exact ih (fun c h => hs c (by omega)) hc
    · rw [window_add_mul_high (segSum_lt K (fun c h => hs c (by omega))) le_rfl, Nat.sub_self]
      simp [window, Nat.mod_eq_of_lt (hs c (by omega))]

variable {ρ K}

lemma asm_mod {n low top : ℕ} {s : ℕ → ℕ} (hlow : low < 2 ^ ρ) :
    asm ρ K n low s top % 2 ^ ρ = low := by
  unfold asm
  rw [Nat.pow_add, show top * (2 ^ ρ * 2 ^ (n * K)) = top * 2 ^ (n * K) * 2 ^ ρ by ring,
    Nat.add_assoc, ← Nat.add_mul, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow]

lemma asm_lt_top {n low : ℕ} {s : ℕ → ℕ} (hlow : low < 2 ^ ρ) (hs : ∀ c < n, s c < 2 ^ K) :
    low + (∑ c ∈ range n, s c * 2 ^ (c * K)) * 2 ^ ρ < 2 ^ (ρ + n * K) := by
  have h := segSum_lt K hs
  rw [Nat.pow_add]
  have : ((∑ c ∈ range n, s c * 2 ^ (c * K)) + 1) * 2 ^ ρ ≤ 2 ^ (n * K) * 2 ^ ρ :=
    Nat.mul_le_mul_right _ h
  nlinarith

lemma asm_div {n low top : ℕ} {s : ℕ → ℕ} (hlow : low < 2 ^ ρ) (hs : ∀ c < n, s c < 2 ^ K) :
    asm ρ K n low s top / 2 ^ (ρ + n * K) = top := by
  unfold asm
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (asm_lt_top hlow hs),
    Nat.zero_add]

lemma seg_asm {n low top c : ℕ} {s : ℕ → ℕ} (hlow : low < 2 ^ ρ) (hs : ∀ c < n, s c < 2 ^ K)
    (hc : c < n) : seg ρ K c (asm ρ K n low s top) = s c := by
  unfold seg asm
  rw [window_add_mul_low (by nlinarith), window_add_mul_high hlow (by omega),
    show ρ + c * K - ρ = c * K by omega]
  exact window_segSum K hs hc

lemma asm_lt {n low top m : ℕ} {s : ℕ → ℕ} (hlow : low < 2 ^ ρ) (hs : ∀ c < n, s c < 2 ^ K)
    (htop : top < 2 ^ m) : asm ρ K n low s top < 2 ^ (ρ + n * K + m) := by
  unfold asm
  have h := asm_lt_top hlow hs
  rw [Nat.pow_add 2 (ρ + n * K) m]
  have : (top + 1) * 2 ^ (ρ + n * K) ≤ 2 ^ m * 2 ^ (ρ + n * K) := Nat.mul_le_mul_right _ htop
  nlinarith

variable (ρ K) in
/-- Every value is the assembly of its parts. -/
lemma eq_asm (n Y : ℕ) :
    Y = asm ρ K n (Y % 2 ^ ρ) (fun c => seg ρ K c Y) (Y / 2 ^ (ρ + n * K)) := by
  induction n with
  | zero =>
    simp only [asm, range_zero, sum_empty, Nat.add_zero, zero_mul]
    exact (Nat.mod_add_div' Y (2 ^ ρ)).symm
  | succ n ih =>
    have h1 : Y / 2 ^ (ρ + n * K) = seg ρ K n Y + Y / 2 ^ (ρ + (n + 1) * K) * 2 ^ K := by
      have h2 := Nat.mod_add_div (Y / 2 ^ (ρ + n * K)) (2 ^ K)
      have h3 : Y / 2 ^ (ρ + n * K) / 2 ^ K = Y / 2 ^ (ρ + (n + 1) * K) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2; ring
      rw [h3] at h2
      unfold seg window
      linarith
    have e1 : 2 ^ (ρ + (n + 1) * K) = 2 ^ (ρ + n * K) * 2 ^ K := by
      rw [← Nat.pow_add]; congr 1; ring
    have e2 : 2 ^ (ρ + n * K) = 2 ^ ρ * 2 ^ (n * K) := Nat.pow_add _ _ _
    calc Y = asm ρ K n (Y % 2 ^ ρ) (fun c => seg ρ K c Y) (Y / 2 ^ (ρ + n * K)) := ih
      _ = _ := by
        unfold asm
        rw [sum_range_succ, h1, e1, e2]
        ring

/-- Adding offsets segmentwise. -/
lemma asm_add (n low top : ℕ) (s δ : ℕ → ℕ) :
    asm ρ K n low s top + (∑ c ∈ range n, δ c * 2 ^ (ρ + c * K)) =
      asm ρ K n low (fun c => s c + δ c) top := by
  unfold asm
  rw [show (∑ c ∈ range n, δ c * 2 ^ (ρ + c * K)) =
      (∑ c ∈ range n, δ c * 2 ^ (c * K)) * 2 ^ ρ by
    rw [sum_mul]; congr 1; ext c; rw [Nat.pow_add]; ring]
  simp only [Nat.add_mul, sum_add_distrib]
  ring

lemma asm_congr {n low top : ℕ} {s s' : ℕ → ℕ} (h : ∀ c < n, s c = s' c) :
    asm ρ K n low s top = asm ρ K n low s' top := by
  unfold asm
  rw [sum_congr rfl (fun c hc => by rw [h c (mem_range.1 hc)])]

end Segments

/-! ### Digits of a compact field -/

section Compact

variable (G : ℕ)

/-- Digit `c` of a compact field: `G` bits at `c G`. -/
def cdig (c w : ℕ) : ℕ := window (c * G) G w

/-- A compact field from its `n` digits. -/
def casm (n : ℕ) (s : ℕ → ℕ) : ℕ := ∑ c ∈ range n, s c * 2 ^ (c * G)

variable {G}

lemma casm_lt {n : ℕ} {s : ℕ → ℕ} (hs : ∀ c < n, s c < 2 ^ G) : casm G n s < 2 ^ (n * G) :=
  segSum_lt G hs

lemma cdig_casm {n c : ℕ} {s : ℕ → ℕ} (hs : ∀ c < n, s c < 2 ^ G) (hc : c < n) :
    cdig G c (casm G n s) = s c :=
  window_segSum G hs hc

variable (G) in
lemma eq_casm (n w : ℕ) (hw : w < 2 ^ (n * G)) : w = casm G n (fun c => cdig G c w) := by
  have h := eq_asm 0 G n w
  simp only [asm, pow_zero, Nat.mod_one, Nat.zero_add, Nat.mul_one] at h
  rw [Nat.div_eq_of_lt hw, zero_mul, Nat.add_zero] at h
  conv_lhs => rw [h]
  simp [casm, cdig, seg]

lemma casm_add (n : ℕ) (s δ : ℕ → ℕ) :
    casm G n s + casm G n δ = casm G n (fun c => s c + δ c) := by
  unfold casm
  rw [← sum_add_distrib]
  congr 1; ext c; ring

lemma casm_congr {n : ℕ} {s s' : ℕ → ℕ} (h : ∀ c < n, s c = s' c) :
    casm G n s = casm G n s' := by
  unfold casm
  rw [sum_congr rfl (fun c hc => by rw [h c (mem_range.1 hc)])]

end Compact

end IntegerMultBounds.MathlibTM2.Layer.CompactDigits
