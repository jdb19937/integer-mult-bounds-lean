module

public import IntegerMultBounds.MathlibTM2.Routing.CompactPatterns

/-!
# Plain selective offsets through the same descriptor interpreter

Z spreads active dirty-control parities into the target. Y gathers current target
parities into the compact temporary. Arbitrary source descriptors use the same
plain gate for load and unload; repeated and unordered selectors are allowed.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open Finset

/-- One sparse operand, with an unused zero second operand. -/
def plainPatterns {W m L : ℕ} (pos : ℕ → ℕ) (src : Fin m → Option (Fin W)) :
    Fin 2 → Fin L → Option (Fin W) :=
  fun k => sparsePattern pos (![src, fun _ => none] k)

theorem plainPatterns_eq {W m L : ℕ} {pos : ℕ → ℕ} (hpos : StrictMono pos)
    (hbound : ∀ j < m, pos j < L) (src : Fin m → Option (Fin W)) (x : ℕ) :
    patternGateValue (fun a _ => a) (plainPatterns (L := L) pos src) x =
      placeVal m pos (fun j => if hj : j < m then selectorBit (src ⟨j, hj⟩) x else false) := by
  exact patternGate_sparse hpos hbound ![src, fun _ => none] (fun a _ => a) rfl x

variable (p : Par)

/-- Active dirty-control parities spread into selected target positions. -/
def zPatterns {W : ℕ} (hG : 0 < p.G) (active : Fin p.n → Bool)
    (uOff : ℕ) (hu : uOff + p.wc ≤ W) : Fin 2 → Fin p.wy → Option (Fin W) :=
  plainPatterns (posS p) fun c =>
    if active c then some (controlWire p hG uOff hu c) else none

/-- Current target parities gathered into compact digit starts. -/
def yPatterns {W : ℕ} (hK : 0 < p.K) (yOff : ℕ) (hy : yOff + p.wy ≤ W) :
    Fin 2 → Fin p.wc → Option (Fin W) :=
  plainPatterns (posC p) fun c => some (targetWire p hK yOff hy c)

private theorem posS_bound (hK : 0 < p.K) (c : ℕ) (hc : c < p.n) : posS p c < p.wy := by
  have := Nat.mul_lt_mul_of_pos_right hc hK
  unfold posS Par.wy
  omega

theorem zPatterns_eq {W : ℕ} (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (uOff : ℕ) (hu : uOff + p.wc ≤ W) (x : ℕ) :
    patternGateValue (fun a _ => a) (zPatterns p hG active uOff hu) x =
      Off.eval p .Z {
        b := 0
        t := 0
        u := maskedControls p active (window uOff p.wc x)
        y := 0
        x := 0 } := by
  unfold zPatterns
  rw [plainPatterns_eq (m := p.n) (L := p.wy) (posS_mono hK) (posS_bound p hK)
    (fun c => if active c then some (controlWire p hG uOff hu c) else none) x, offZ_eq hG]
  unfold placeVal
  apply sum_congr rfl
  intro c hc
  have hc' : c < p.n := mem_range.mp hc
  have hcg : posC p c < p.wc := Nat.mul_lt_mul_of_pos_right hc' hG
  simp only [dite_eq_left hc']
  rw [maskedControls_bit p hG active _ ⟨c, hc'⟩]
  simp only [window, Nat.testBit_mod_two_pow, hcg, decide_true, Bool.true_and,
    Nat.testBit_div_two_pow]
  by_cases ha : active ⟨c, hc'⟩ = true <;>
    simp [ha, selectorBit, controlWire, Nat.add_comm]

theorem yPatterns_eq {W : ℕ} (hG : 0 < p.G) (hK : 0 < p.K)
    (yOff : ℕ) (hy : yOff + p.wy ≤ W) (x : ℕ) :
    patternGateValue (fun a _ => a) (yPatterns p hK yOff hy) x =
      Off.eval p .Y { b := 0, t := 0, u := 0, y := window yOff p.wy x, x := 0 } := by
  unfold yPatterns
  rw [plainPatterns_eq (m := p.n) (L := p.wc) (posC_mono hG)
    (fun c hc => Nat.mul_lt_mul_of_pos_right hc hG)
    (fun c => some (targetWire p hK yOff hy c)) x, offY_eq hK]
  unfold placeVal
  apply sum_congr rfl
  intro c hc
  have hc' : c < p.n := mem_range.mp hc
  simp only [dite_eq_left hc']
  simp [selectorBit, targetWire, window, Nat.testBit_mod_two_pow,
    posS_bound p hK c hc', Nat.testBit_div_two_pow, Nat.add_comm]

end IntegerMultBounds.MathlibTM2.Routing
