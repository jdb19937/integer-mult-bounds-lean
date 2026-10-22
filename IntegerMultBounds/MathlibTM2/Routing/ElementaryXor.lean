module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeChain
public import IntegerMultBounds.MathlibTM2.Routing.LowBitXor
public import IntegerMultBounds.MathlibTM2.Routing.Shear

/-!
# Arbitrary elementary coordinate XOR by two bit exchanges and one scan

Exchange the target with coordinate zero, perform the lowest-bit XOR using the
renamed source, and undo the exchange. The bit-exchange width is at most one,
so its existing host cost is linear in the stream volume. All outer rows remain
part of the complete rectangle.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {n : ℕ}

def elementarySwapSpec (t : Fin n) : BlockExchangeSpec n where
  a := 0
  b := t.val
  w := if t.val = 0 then 0 else 1
  separate := by split_ifs <;> omega
  fits := by have ht := t.isLt; split_ifs <;> omega

theorem elementarySwap_target (t : Fin n) :
    ((elementarySwapSpec t).coordinate t).val = 0 := by
  change blockExchange 0 t.val (if t.val = 0 then 0 else 1) t.val = 0
  unfold blockExchange
  split_ifs <;> omega

theorem elementarySwap_involutive (t : Fin n) :
    Function.Involutive (elementarySwapSpec t).coordinate := by
  intro i
  apply Fin.ext
  exact blockExchange_involutive _ _ _ (elementarySwapSpec t).separate i.val

theorem elementarySwap_zero_iff (t q : Fin n) :
    ((elementarySwapSpec t).coordinate q).val = 0 ↔ q = t := by
  constructor
  · intro hq
    apply (elementarySwapSpec t).coordinate.injective
    exact Fin.ext (hq.trans (elementarySwap_target t).symm)
  · intro h
    subst q
    exact elementarySwap_target t

theorem elementarySource_pos (t s : Fin n) (hne : s ≠ t) :
    0 < ((elementarySwapSpec t).coordinate s).val := by
  have h := elementarySwap_zero_iff t s
  omega

def elementaryXorRank (t s : Fin n) (hne : s ≠ t) (R : ℕ) :
    Equiv.Perm (Fin (R * 2 ^ n)) :=
  ((elementarySwapSpec t).rank R).trans
    ((lowBitXorPerm n ((elementarySwapSpec t).coordinate s).val R
      (by have := t.isLt; omega) (elementarySource_pos t s hne)).trans
        ((elementarySwapSpec t).rank R))

/-- Every bit, including all source and spectator coordinates, has its exact value. -/
theorem elementaryXorRank_bit (t s : Fin n) (hne : s ≠ t) (R : ℕ)
    (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (elementaryXorRank t s hne R i).val.testBit q.val =
      if q = t then Bool.xor (i.val.testBit t.val) (i.val.testBit s.val)
      else i.val.testBit q.val := by
  let e := (elementarySwapSpec t).coordinate
  let π := (elementarySwapSpec t).rank R
  have he (j : Fin n) : e (e j) = j := elementarySwap_involutive t j
  have hbit (j : Fin n) : (π i).val.testBit j.val = i.val.testBit (e j).val :=
    (elementarySwapSpec t).rank_bit R i j
  change (π ((lowBitXorPerm n (e s).val R _ _) (π i))).val.testBit q.val = _
  rw [BlockExchangeSpec.rank_bit]
  change (lowBitXor (e s).val (π i).val).testBit (e q).val = _
  rw [lowBitXor_bit]
  have hqs : (e q).val = 0 ↔ q = t := elementarySwap_zero_iff t q
  have hsource : (π i).val.testBit (e s).val = i.val.testBit s.val := by rw [hbit, he]
  have hq : (π i).val.testBit (e q).val = i.val.testBit q.val := by rw [hbit, he]
  by_cases ht : q = t
  · subst q
    have hz : (e t).val = 0 := elementarySwap_target t
    have htarget : (π i).val.testBit 0 = i.val.testBit t.val := by
      simpa only [hz] using hq
    simp only [hz, ite_true, htarget, hsource, ite_true]
  · rw [ite_eq_right (hqs.not.mpr ht), hq, ite_eq_right ht]

/-- The concrete rank permutation satisfies the singleton-shear contract. -/
theorem elementaryXorRank_shear (t s : Fin n) (hne : s ≠ t) (R : ℕ)
    (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (elementaryXorRank t s hne R i).val.testBit q.val) =
      shear {t} (fun _ => s) (fun q => i.val.testBit q.val) := by
  funext q
  simp only [elementaryXorRank_bit, shear, toggle, Finset.mem_singleton]
  split_ifs with h
  · subst q; rfl
  · rfl

end IntegerMultBounds.MathlibTM2.Routing
