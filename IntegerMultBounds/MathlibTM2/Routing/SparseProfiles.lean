module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Linarith

/-!
# Residue profiles with complete segments and an explicit terminal region

An R2 digit requires the complete K-bit segment beginning at its target. For
residue r use exactly (n-r)/K segments, leaving fewer than K terminal positions.
The profile enumerates every nonterminal coordinate and never invents a segment
past the record boundary.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def sparseSlotCount (n K r : ℕ) : ℕ := (n - r) / K

theorem sparseSlot_lt (n K r c : ℕ) (hK : 0 < K) (hc : c < sparseSlotCount n K r) :
    r + c * K < n := by
  have hlt := Nat.mul_lt_mul_of_pos_right hc hK
  have hle := Nat.div_mul_le_self (n - r) K
  unfold sparseSlotCount at hlt
  omega

def sparseSlot (n K : ℕ) (hK : 0 < K) (r : Fin K)
    (c : Fin (sparseSlotCount n K r.val)) : Fin n :=
  ⟨r.val + c.val * K, sparseSlot_lt n K r.val c.val hK c.isLt⟩

theorem sparseSlot_mod (n K : ℕ) (hK : 0 < K) (r : Fin K)
    (c : Fin (sparseSlotCount n K r.val)) :
    (sparseSlot n K hK r c).val % K = r.val := by
  simp [sparseSlot, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]

theorem sparseSlot_div (n K : ℕ) (hK : 0 < K) (r : Fin K)
    (c : Fin (sparseSlotCount n K r.val)) :
    (sparseSlot n K hK r c).val / K = c.val := by
  simp [sparseSlot, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt r.isLt]

/-- Every chosen digit has its entire guard segment inside the record. -/
theorem sparseSlot_complete (n K : ℕ) (hK : 0 < K) (r : Fin K)
    (c : Fin (sparseSlotCount n K r.val)) :
    (sparseSlot n K hK r c).val + K ≤ n := by
  have hle := Nat.mul_le_mul_right K (show c.val + 1 ≤ (n - r.val) / K from c.isLt)
  have hd := Nat.div_mul_le_self (n - r.val) K
  have hr := sparseSlot_lt n K r.val c.val hK c.isLt
  have hsub : n - r.val + r.val = n := by omega
  change r.val + c.val * K + K ≤ n
  nlinarith

/-- Quotient and residue recover a digit for every complete-segment target. -/
theorem sparseSlot_covers (n K : ℕ) (hK : 0 < K) (i : Fin n)
    (hi : i.val + K ≤ n) :
    ∃ c : Fin (sparseSlotCount n K (i.val % K)),
      sparseSlot n K hK ⟨i.val % K, Nat.mod_lt _ hK⟩ c = i := by
  have he := Nat.mod_add_div i.val K
  have hm : i.val % K ≤ n := le_trans (Nat.mod_le _ _) i.isLt.le
  have hc : (i.val / K + 1) * K ≤ n - i.val % K := by
    have : i.val % K + (i.val / K + 1) * K ≤ n := by nlinarith
    omega
  have hb := (Nat.le_div_iff_mul_le hK).mpr hc
  refine ⟨⟨i.val / K, hb⟩, ?_⟩
  apply Fin.ext
  change i.val % K + i.val / K * K = i.val
  nlinarith

/-- Each residue profile covers exactly its complete-segment coordinates. -/
theorem sparseSlot_residue_iff (n K : ℕ) (hK : 0 < K) (r : Fin K) (i : Fin n) :
    (∃ c : Fin (sparseSlotCount n K r.val), sparseSlot n K hK r c = i) ↔
      i.val + K ≤ n ∧ i.val % K = r.val := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨sparseSlot_complete n K hK r c, sparseSlot_mod n K hK r c⟩
  · rintro ⟨hi, hm⟩
    obtain ⟨c, hc⟩ := sparseSlot_covers n K hK i hi
    have he : (⟨i.val % K, Nat.mod_lt _ hK⟩ : Fin K) = r := Fin.ext hm
    cases he
    exact ⟨c, hc⟩

theorem sparseSlotCount_le (n K r : ℕ) : sparseSlotCount n K r ≤ n / K :=
  Nat.div_le_div_right (Nat.sub_le n r)

/-- The coordinates needing the terminal fallback lie in a suffix of width K. -/
theorem sparseTerminal_suffix (n K : ℕ) (i : Fin n) (hi : ¬ i.val + K ≤ n) :
    n - K ≤ i.val := by omega

end IntegerMultBounds.MathlibTM2.Routing
