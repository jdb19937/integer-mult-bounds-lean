module

public import IntegerMultBounds.MathlibTM2.Routing.LowBitXor

/-! # A fixed finite automaton for routing by the XOR of two masked index bits -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

def xorBitCodeAuto (A : ℕ) : CAuto A 3 4 :=
  absAuto (fun b : Bool => (⟨b.toNat, by cases b <;> simp⟩ : Fin (A + 4)))
    (fun x => decide (x.val = 1)) false
    (fun st col => Bool.xor st (Bool.xor (col 0 && col 1) (col 0 && col 2)))
    (fun b => ⟨b.toNat, by cases b <;> decide⟩)

theorem xorBitCode_fold (vals : Fin 3 → ℕ) (p q : ℕ)
    (hp : vals 1 = 2 ^ p) (hq : vals 2 = 2 ^ q) (L : ℕ) :
    (List.range L).foldl (fun st t => Bool.xor st
      (Bool.xor ((vals 0).testBit t && (vals 1).testBit t)
        ((vals 0).testBit t && (vals 2).testBit t))) false =
      Bool.xor (decide (p < L) && (vals 0).testBit p)
        (decide (q < L) && (vals 0).testBit q) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, hp, hq, Nat.testBit_two_pow]
    by_cases hpL : p = L <;> by_cases hqL : q = L
    · subst p; subst q; simp
    · subst p
      have hq' : (q ≤ L) ↔ q < L := by omega
      simp [hqL, hq', Bool.xor_comm]
    · subst q
      have hp' : (p ≤ L) ↔ p < L := by omega
      cases (vals 0).testBit L <;> cases (vals 0).testBit p <;> simp [hpL, hp']
    · have hp' : (p ≤ L) ↔ p < L := by omega
      have hq' : (q ≤ L) ↔ q < L := by omega
      simp [hpL, hqL, hp', hq']

theorem xorBitCode_eval (A L : ℕ) (vals : Fin 3 → ℕ) (p q : ℕ)
    (hp : vals 1 = 2 ^ p) (hq : vals 2 = 2 ^ q) (hpL : p < L) (hqL : q < L) :
    (xorBitCodeAuto A).eval L vals =
      ⟨(Bool.xor ((vals 0).testBit p) ((vals 0).testBit q)).toNat,
        by cases (vals 0).testBit p <;> cases (vals 0).testBit q <;> decide⟩ := by
  unfold xorBitCodeAuto
  rw [absAuto_eval _ _ (fun b => by cases b <;> simp), xorBitCode_fold vals p q hp hq L]
  simp [hpL, hqL]

theorem lowBitXor_mod (s i : ℕ) :
    lowBitXor s i % 2 = (Bool.xor (i.testBit 0) (i.testBit s)).toNat := by
  have hb := Nat.testBit_zero (lowBitXor s i)
  have hm := Nat.mod_lt (lowBitXor s i) (by decide : 0 < 2)
  unfold lowBitXor at hb ⊢
  cases hs : i.testBit s <;> cases h0 : i.testBit 0 <;>
    simp_all [Nat.testBit_zero] <;> omega

theorem xorBitIdxCode (A n s : ℕ) (hn : 0 < n) (hs : s < n) (i : ℕ) :
    idxCode (xorBitCodeAuto A) n (fun _ : Fin 1 => n) (layRsrc 0 s) i = lowBitXorCode s i := by
  rw [idxCode, lay_regVal, xorBitCode_eval A n _ 0 s rfl rfl hn hs]
  apply Fin.ext
  change (Bool.xor ((i % 2 ^ n).testBit 0) ((i % 2 ^ n).testBit s)).toNat = _
  simp only [Nat.testBit_mod_two_pow, hn, hs, decide_true, Bool.true_and]
  exact (lowBitXor_mod s i).symm

theorem lowBitIdxCode (A n s : ℕ) (hn : 0 < n) (i : ℕ) :
    idxCode (layCodeAuto A 1) n (fun _ : Fin 1 => n) (layRsrc 0 s) i = lowBitCode i := by
  rw [layIdxCode_in s hn]
  apply Fin.ext
  simp only [lowBitCode]
  have hb := Nat.testBit_zero i
  have hm := Nat.mod_lt i (by decide : 0 < 2)
  cases h0 : i.testBit 0 <;> simp_all

end IntegerMultBounds.MathlibTM2.Routing
