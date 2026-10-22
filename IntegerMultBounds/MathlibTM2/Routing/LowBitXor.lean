module

public import IntegerMultBounds.MathlibTM2.Fast.LayoutMove

/-!
# An elementary XOR at the lowest address bit

Stable routing by the new lowest bit, then merging by the ordinary lowest bit,
implements this permutation. Within either route class the remaining address
bits keep their order. This supplies the semantic contract of the existing
route-and-merge host machine without a quarter-interchange construction.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

def lowBitXor (s i : ℕ) : ℕ := if i.testBit s then i ^^^ 1 else i

theorem lowBitXor_bit (s i q : ℕ) :
    (lowBitXor s i).testBit q =
      if q = 0 then Bool.xor (i.testBit 0) (i.testBit s) else i.testBit q := by
  have hb : (1 : ℕ).testBit q = decide (q = 0) := by
    rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
    simp [eq_comm]
  cases hs : i.testBit s
  · simp only [lowBitXor, hs, Bool.false_eq_true, ite_false, Bool.xor_false]
    split_ifs with hq
    · subst q; rfl
    · rfl
  · simp only [lowBitXor, hs, ite_true]
    rw [Nat.testBit_xor, hb]
    by_cases hq : q = 0 <;> simp [hq]

theorem lowBitXor_div (s i : ℕ) : lowBitXor s i / 2 = i / 2 := by
  unfold lowBitXor
  split
  · change (i ^^^ 1) / 2 ^ 1 = i / 2
    rw [Nat.xor_div_two_pow]
    simp
  · rfl

theorem lowBitXor_source (s : ℕ) (hs : 0 < s) (i : ℕ) :
    (lowBitXor s i).testBit s = i.testBit s := by
  unfold lowBitXor
  split
  · rw [Nat.testBit_xor]
    have hz : (1 : ℕ).testBit s = false := by
      rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
      simp [show 0 ≠ s by omega]
    simp [hz]
  · rfl

theorem lowBitXor_involutive (s : ℕ) (hs : 0 < s) : Function.Involutive (lowBitXor s) := by
  intro i
  change (if (lowBitXor s i).testBit s then lowBitXor s i ^^^ 1 else lowBitXor s i) = i
  rw [lowBitXor_source s hs i]
  cases hb : i.testBit s <;> simp [lowBitXor, hb]

theorem lowBitXor_div_pow (s i n : ℕ) (hn : 0 < n) :
    lowBitXor s i / 2 ^ n = i / 2 ^ n := by
  have hp : 2 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    simpa using h
  unfold lowBitXor
  split
  · rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt (by omega : 1 < 2 ^ n)]
    simp
  · rfl

theorem lowBitXor_lt {n s R i : ℕ} (hn : 0 < n) (hi : i < R * 2 ^ n) :
    lowBitXor s i < R * 2 ^ n := by
  have hd := lowBitXor_div_pow s i n hn
  have h := (Nat.div_lt_iff_lt_mul (show 0 < 2 ^ n by positivity)).mpr hi
  rw [← hd] at h
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mp h

def lowBitXorPerm (n s R : ℕ) (hn : 0 < n) (hs : 0 < s) : Equiv.Perm (Fin (R * 2 ^ n)) where
  toFun i := ⟨lowBitXor s i.val, lowBitXor_lt hn i.isLt⟩
  invFun i := ⟨lowBitXor s i.val, lowBitXor_lt hn i.isLt⟩
  left_inv i := Fin.ext (lowBitXor_involutive s hs i.val)
  right_inv i := Fin.ext (lowBitXor_involutive s hs i.val)

def lowBitXorCode (s i : ℕ) : Fin 4 := ⟨lowBitXor s i % 2, by omega⟩

def lowBitCode (i : ℕ) : Fin 4 := ⟨i % 2, by omega⟩

/-- The route classes retain increasing order after the XOR. -/
theorem lowBitXor_monotone (s : ℕ) (hs : 0 < s) (i j : ℕ)
    (hc : lowBitXorCode s i = lowBitXorCode s j) (hi : i < j) :
    lowBitXor s i < lowBitXor s j := by
  have hr := congrArg Fin.val hc
  change lowBitXor s i % 2 = lowBitXor s j % 2 at hr
  have hd₁ := lowBitXor_div s i
  have hd₂ := lowBitXor_div s j
  have hm₁ := Nat.mod_add_div (lowBitXor s i) 2
  have hm₂ := Nat.mod_add_div (lowBitXor s j) 2
  have hinj := (lowBitXor_involutive s hs).injective
  have hne : lowBitXor s i ≠ lowBitXor s j := fun he => (Nat.ne_of_lt hi) (hinj he)
  have hdiv : i / 2 ≤ j / 2 := Nat.div_le_div_right hi.le
  omega

/-- Complete route/merge identity and class counts for the elementary host pass. -/
theorem lowBitXor_merge {α : Type} {n s R B : ℕ} (hn : 0 < n) (hs : 0 < s)
    (l : List (List α)) (hl : l.length = R * 2 ^ n) (hlB : ∀ r ∈ l, r.length = B) :
    mergeIdxList B lowBitCode (R * 2 ^ n) 0
      (fun d => blocksIdx l.flatten B (R * 2 ^ n) (lowBitXorCode s) 0 d ++ []) =
        ((moveRecs (lowBitXorPerm n s R hn hs) l).flatten, fun _ => []) ∧
    ∀ d, idxCount lowBitCode 0 (R * 2 ^ n) d = idxCount (lowBitXorCode s) 0 (R * 2 ^ n) d := by
  let π := lowBitXorPerm n s R hn hs
  have hcode : ∀ i : Fin (R * 2 ^ n), lowBitCode (π i) = lowBitXorCode s i := fun _ => rfl
  refine ⟨mergeIdxList_moveRecs π l hl hlB _ _ hcode ?_, idxCount_perm π _ _ hcode⟩
  intro i j hc hij
  exact lowBitXor_monotone s hs i.val j.val hc hij

end IntegerMultBounds.MathlibTM2.Routing
