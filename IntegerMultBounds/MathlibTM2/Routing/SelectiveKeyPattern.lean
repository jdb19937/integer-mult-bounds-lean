module

public import IntegerMultBounds.MathlibTM2.Routing.SelectivePatterns

/-!
# Executable descriptor of the selective destination word

The live header contains y, t, u and the complete spectator field. A single
optional-source descriptor places each active source at its physical target bit.
Inactive targets request zero; repeated and arbitrarily ordered sources remain
ordinary descriptor data for the existing fixed interpreter.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

private theorem patternGate_first {W L : ℕ} (s : Fin 2 → Fin L → Option (Fin W)) (x : ℕ) :
    patternGateValue (fun a _ => a) s x = patternValue (s 0) x := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [patternGateValue, gateWord_bit]
  by_cases hq : q < L
  · simp [hq]
  · have hb : (patternValue (s 0) x).testBit q = false := by
      apply Nat.testBit_eq_false_of_lt
      exact (patternValue_lt _ _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hq, hb]

variable (p : Par) (X : ℕ) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def selectiveKeySources (c : Fin p.n) : Option (Fin (p.wy + 2 * p.wc + X)) :=
  if active c then some (sourceWire p X (s c)) else none

def selectiveKeyPattern : Fin p.wy → Option (Fin (p.wy + 2 * p.wc + X)) :=
  sparsePattern (posS p) (selectiveKeySources p X active s)

/-- The single interpreted word is exactly the sparse source word used in the
all-address ideal key, evaluated on the current physical counter header. -/
theorem selectiveKeyPattern_value (hK : 0 < p.K) (i : ℕ) :
    patternValue (selectiveKeyPattern p X active s)
      ((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X)) =
      targetWord p active s (selectiveView p X i).y (selectiveView p X i).x := by
  have hp := plainPatterns_eq (m := p.n) (L := p.wy) (posS_mono hK) (fun c hc => by
    have hm := Nat.mul_lt_mul_of_pos_right hc hK
    unfold posS Par.wy
    omega)
    (selectiveKeySources p X active s) ((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X))
  rw [patternGate_first] at hp
  change patternValue (selectiveKeyPattern p X active s) _ = _ at hp
  rw [hp]
  unfold targetWord
  apply congrArg (placeVal p.n (posS p))
  funext c
  by_cases hc : c < p.n
  · simp only [dite_eq_left hc]
    have hw : (((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X))).testBit
        (sourceWire p X (s ⟨c, hc⟩)).val =
        (s ⟨c, hc⟩).physical (selectiveView p X i).y (selectiveView p X i).x := by
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      simp only [(sourceWire p X (s ⟨c, hc⟩)).isLt, decide_true, Bool.true_and]
      rw [Nat.add_comm, sourceWire_bit]
    cases ha : active ⟨c, hc⟩
    · simp [selectiveKeySources, selectorBit, ha]
    · simp only [selectiveKeySources, ha, ite_true, selectorBit, Bool.true_and]
      exact hw
  · simp [hc]

end IntegerMultBounds.MathlibTM2.Routing
