module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIndex
public import IntegerMultBounds.MathlibTM2.Routing.HeaderFields

/-!
# Physical headers of the fixed selective layout

The two rotation targets use suffixes of the same field bank. Relative source
windows and complete header widths are computed once here; no counter-bank
redecomposition or copied physical source field is assumed.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ)

theorem selectiveFieldOff (f : Fin 5) :
    fieldOff (selectiveLen p X) f =
      ![0, p.wc, p.wc + p.wy, p.wc + p.wy + p.wc, p.wc + p.wy + 2 * p.wc] f := by
  have h0 := fieldOff_zero (selectiveLen p X) 0 rfl
  have h1 := fieldOff_succ (selectiveLen p X) 0 (by decide)
  have h2 := fieldOff_succ (selectiveLen p X) 1 (by decide)
  have h3 := fieldOff_succ (selectiveLen p X) 2 (by decide)
  have h4 := fieldOff_succ (selectiveLen p X) 3 (by decide)
  fin_cases f <;> simp_all [selectiveLen, Nat.two_mul, Nat.add_assoc]

theorem selectiveHeader_y :
    ((higherFields (1 : Fin 5)).map (selectiveLen p X)).sum = 2 * p.wc + X := by
  simp [higherFields, fieldRun, selectiveLen]
  omega

theorem selectiveHeader_b :
    ((higherFields (0 : Fin 5)).map (selectiveLen p X)).sum = p.wy + 2 * p.wc + X := by
  simp [higherFields, fieldRun, selectiveLen]
  omega

/-- Relative source position inside the header above the b field. -/
def sourceWire : SlotSource p X → Fin (p.wy + 2 * p.wc + X)
  | .low r => ⟨r.val, by have := r.isLt; unfold Par.wy; omega⟩
  | .digit c r => ⟨p.ρ + c.val * p.K + r.val, by
      have hm := Nat.mul_le_mul_right p.K (show c.val + 1 ≤ p.n by omega)
      have hr := r.isLt
      unfold Par.wy
      nlinarith⟩
  | .high r => ⟨p.ρ + p.n * p.K + r.val, by have := r.isLt; unfold Par.wy; omega⟩
  | .spectator r => ⟨p.wy + 2 * p.wc + r.val, by have := r.isLt; omega⟩

/-- Reading a wire in the actual higher header gives its physical source bit. -/
theorem sourceWire_bit (s : SlotSource p X) (i : ℕ) :
    i.testBit (p.wc + (sourceWire p X s).val) =
      s.physical (selectiveView p X i).y (selectiveView p X i).x := by
  have hy (r : ℕ) (hr : r < p.wy) :
      (digit (selectiveLen p X) 1 i).testBit r = i.testBit (p.wc + r) := by
    rw [digit, selectiveFieldOff]
    simp [selectiveLen, Nat.testBit_mod_two_pow, hr,
      Nat.testBit_div_two_pow, Nat.add_comm]
  have hx (r : ℕ) (hr : r < X) :
      (digit (selectiveLen p X) 4 i).testBit r =
        i.testBit (p.wc + (p.wy + 2 * p.wc + r)) := by
    rw [digit, selectiveFieldOff]
    simp [selectiveLen, Nat.testBit_mod_two_pow, hr,
      Nat.testBit_div_two_pow, Nat.add_comm, Nat.add_left_comm]
  cases s with
  | low r => exact (hy r.val (by have := r.isLt; unfold Par.wy; omega)).symm
  | digit c r =>
    apply Eq.symm
    apply hy
    have hm := Nat.mul_le_mul_right p.K (show c.val + 1 ≤ p.n by omega)
    have hr := r.isLt
    unfold Par.wy
    nlinarith
  | high r => exact (hy (p.ρ + p.n * p.K + r.val) (by have := r.isLt; unfold Par.wy; omega)).symm
  | spectator r => exact (hx r.val r.isLt).symm

end IntegerMultBounds.MathlibTM2.Routing
