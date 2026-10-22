module

public import IntegerMultBounds.MathlibTM2.Routing.SparsePattern
public import IntegerMultBounds.MathlibTM2.Layer.CompactOffsets

/-!
# Concrete AND/XOR descriptors for the compact gadget

The high source word contains explicit windows for control, temporary and target
fields. Optional selectors encode inactive zeros, repeated control bits and gaps.
The gate words are proved equal to the actual masked `Off.A` and `Off.YZ` formulas.
No abstract offset evaluator or host-execution hypothesis is used in this bridge.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open Finset

variable (p : Par)

/-- Only control parities affect the offsets; inactive parities are zero. -/
def maskedControls (active : Fin p.n → Bool) (u : ℕ) : ℕ :=
  placeVal p.n (posC p) fun c => if hc : c < p.n then
    active ⟨c, hc⟩ && u.testBit (posC p c) else false

theorem maskedControls_bit (hG : 0 < p.G) (active : Fin p.n → Bool) (u : ℕ) (c : Fin p.n) :
    (maskedControls p active u).testBit (posC p c.val) =
      (active c && u.testBit (posC p c.val)) := by
  simp [maskedControls, testBit_placeVal (posC_mono hG),
    (posC_mono (p := p) hG).injective.eq_iff, c.isLt]

private theorem window_bit (o w x q : ℕ) (hq : q < w) :
    (window o w x).testBit q = x.testBit (o + q) := by
  simp [window, Nat.testBit_mod_two_pow, hq, Nat.testBit_div_two_pow, Nat.add_comm]

/-- The compact digit containing a temporary bit. -/
def controlIndex (hG : 0 < p.G) (j : Fin (p.n * p.G)) : Fin p.n :=
  ⟨j.val / p.G, (Nat.div_lt_iff_lt_mul hG).2 j.isLt⟩

def controlWire {W : ℕ} (hG : 0 < p.G) (o : ℕ) (ho : o + p.wc ≤ W)
    (c : Fin p.n) : Fin W := ⟨o + posC p c.val, by
  have hc := Nat.mul_lt_mul_of_pos_right c.isLt hG
  unfold posC Par.wc at *
  omega⟩

def tempWire {W : ℕ} (o : ℕ) (ho : o + p.wc ≤ W) (j : Fin (p.n * p.G)) : Fin W :=
  ⟨o + j.val, by unfold Par.wc at ho; omega⟩

def targetWire {W : ℕ} (hK : 0 < p.K) (o : ℕ) (ho : o + p.wy ≤ W)
    (c : Fin p.n) : Fin W := ⟨o + posS p c.val, by
  have hc := Nat.mul_lt_mul_of_pos_right c.isLt hK
  unfold posS Par.wy at *
  omega⟩

/-- One repeated active control and one temporary bit for every temporary position. -/
def aSources {W : ℕ} (hG : 0 < p.G) (active : Fin p.n → Bool)
    (uOff tOff : ℕ) (hu : uOff + p.wc ≤ W) (ht : tOff + p.wc ≤ W) :
    Fin 2 → Fin (p.n * p.G) → Option (Fin W) :=
  ![fun j => if active (controlIndex p hG j) then
      some (controlWire p hG uOff hu (controlIndex p hG j)) else none,
    fun j => some (tempWire p tOff ht j)]

/-- The two actual descriptor patterns for the temporary-times-control rotation. -/
def aPatterns {W : ℕ} (hG : 0 < p.G) (active : Fin p.n → Bool)
    (uOff tOff : ℕ) (hu : uOff + p.wc ≤ W) (ht : tOff + p.wc ≤ W) :
    Fin 2 → Fin p.wy → Option (Fin W) :=
  fun k => sparsePattern (posA p) (aSources p hG active uOff tOff hu ht k)

/-- The concrete AND patterns equal the masked early-pass `2 z t` offset. -/
theorem aPatterns_eq {W : ℕ} (hG : 0 < p.G) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (uOff tOff : ℕ) (hu : uOff + p.wc ≤ W) (ht : tOff + p.wc ≤ W) (x : ℕ) :
    patternGateValue Bool.and (aPatterns p hG active uOff tOff hu ht) x =
      Off.eval p .A {
        b := 0
        t := window tOff p.wc x
        u := maskedControls p active (window uOff p.wc x)
        y := 0
        x := 0 } := by
  unfold aPatterns
  rw [patternGate_sparse (posA_mono hG hGK)
    (fun j hj => posA_lt hG hGK hj) _ Bool.and rfl x, offA_eq hG]
  unfold placeVal
  apply sum_congr rfl
  intro j hj
  have hj' : j < p.n * p.G := mem_range.mp hj
  have hc : j / p.G < p.n := (Nat.div_lt_iff_lt_mul hG).2 hj'
  have hcg : posC p (j / p.G) < p.wc := Nat.mul_lt_mul_of_pos_right hc hG
  simp only [dite_eq_left hj']
  rw [maskedControls_bit p hG active _ ⟨j / p.G, hc⟩,
    window_bit uOff p.wc x _ hcg, window_bit tOff p.wc x j hj']
  simp only [aSources, Matrix.cons_val_zero, Matrix.cons_val_one, controlIndex,
    selectorBit, controlWire, tempWire]
  by_cases ha : active ⟨j / p.G, hc⟩ = true <;> simp [ha]

/-- Current target parity and the active part of its dirty control parity. -/
def yzSources {W : ℕ} (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (uOff yOff : ℕ) (hu : uOff + p.wc ≤ W) (hy : yOff + p.wy ≤ W) :
    Fin 2 → Fin p.n → Option (Fin W) :=
  ![fun c => some (targetWire p hK yOff hy c),
    fun c => if active c then some (controlWire p hG uOff hu c) else none]

def yzPatterns {W : ℕ} (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (uOff yOff : ℕ) (hu : uOff + p.wc ≤ W) (hy : yOff + p.wy ≤ W) :
    Fin 2 → Fin p.wc → Option (Fin W) :=
  fun k => sparsePattern (posC p) (yzSources p hG hK active uOff yOff hu hy k)

/-- The concrete XOR patterns equal the masked parity offset of the early pass. -/
theorem yzPatterns_eq {W : ℕ} (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (uOff yOff : ℕ) (hu : uOff + p.wc ≤ W) (hy : yOff + p.wy ≤ W) (x : ℕ) :
    patternGateValue Bool.xor (yzPatterns p hG hK active uOff yOff hu hy) x =
      Off.eval p .YZ {
        b := 0
        t := 0
        u := maskedControls p active (window uOff p.wc x)
        y := window yOff p.wy x
        x := 0 } := by
  unfold yzPatterns
  rw [patternGate_sparse (m := p.n) (L := p.wc) (posC_mono hG)
    (fun c hc => Nat.mul_lt_mul_of_pos_right hc hG)
    (yzSources p hG hK active uOff yOff hu hy) Bool.xor rfl x, offYZ_eq hK hG]
  unfold placeVal
  apply sum_congr rfl
  intro c hc
  have hc' : c < p.n := mem_range.mp hc
  have hcg : posC p c < p.wc := Nat.mul_lt_mul_of_pos_right hc' hG
  have hcy : posS p c < p.wy := by
    have h := Nat.mul_lt_mul_of_pos_right hc' hK
    unfold posS Par.wy
    omega
  simp only [dite_eq_left hc']
  rw [maskedControls_bit p hG active _ ⟨c, hc'⟩,
    window_bit uOff p.wc x _ hcg, window_bit yOff p.wy x _ hcy]
  simp only [yzSources, Matrix.cons_val_zero, Matrix.cons_val_one, selectorBit,
    controlWire, targetWire]
  by_cases ha : active ⟨c, hc'⟩ = true <;> simp [ha]

end IntegerMultBounds.MathlibTM2.Routing
