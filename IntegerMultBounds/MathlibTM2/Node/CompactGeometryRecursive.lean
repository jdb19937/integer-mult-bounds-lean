module

public import IntegerMultBounds.MathlibTM2.Node.SlotXor
public import IntegerMultBounds.Machine.CompactGadgetReservationShape
import Mathlib.Tactic.Positivity.Finset

/-! # Recursive reserved geometry for compact slot-XOR integration

One global Shape is reused by every recursive child. Left and right active
spectators change the live selected-bit offset without allocating new reservations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationShape (Shape)

noncomputable section

/-- The whole native reservation is present in the live address, with optional unused high bits.
The low offset includes the complete dirty back reservation and the right active spectators. -/
structure CompactRecursiveLayout (s : Shape) (n a₀ k ρ left right : ℕ) : Prop where
  active : s.active = left + m * k + right
  positiveWidth : 0 < k
  widthFits : k ≤ s.axes
  selectedFits : ρ < s.chunk
  lowReserve : a₀ = s.H + s.B + right * s.chunk
  totalFits : s.bits ≤ n

/-- A child occupies one complete parent slot, retaining all other active fields as
spectators in the same global native reservation. -/
theorem CompactRecursiveLayout.child {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (p : Fin m)
    (k' : ℕ) (hk' : 0 < k') (hdivide : m*k'=k) :
    CompactRecursiveLayout s n (a₀+p.val*(s.chunk*k)) k' ρ
      (left+(m-1-p.val)*k) (right+p.val*k) where
  active := by
    have hp := p.isLt
    have he : (m-1-p.val)+1+p.val=m := by omega
    have hh := congrArg (fun z => z*k) he
    simp only [Nat.add_mul,Nat.one_mul] at hh
    have ha := layout.active
    omega
  positiveWidth := hk'
  widthFits := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le p.val) p.isLt
    have hh : k' ≤ k := by nlinarith
    exact hh.trans layout.widthFits
  selectedFits := layout.selectedFits
  lowReserve := by
    have ha := layout.lowReserve
    rw [ha]
    ring
  totalFits := layout.totalFits

/-- The strengthened reservation invariant implies the original live layout's fit premise. -/
lemma CompactRecursiveLayout.live_fit {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) : a₀ + m * (s.chunk * k) ≤ n := by
  have h := layout.totalFits
  rw [Shape.bits, layout.active] at h
  rw [layout.lowReserve]
  nlinarith

/-- All live selected bits exist inside the fully reserved address. -/
def compactRecursiveBits {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) : Fin (m * k) → Fin n := fun i =>
  ⟨a₀ + ρ + s.chunk * i.val, by
    have hi := i.isLt
    have hp := layout.selectedFits
    have hf := layout.live_fit
    have hm := Nat.mul_le_mul_left s.chunk (show i.val + 1 ≤ m * k by omega)
    nlinarith⟩

lemma compactRecursiveBits_injective {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) : Function.Injective (compactRecursiveBits layout) := by
  intro i j hij
  have hp := layout.selectedFits
  have hv := congrArg Fin.val hij
  simp only [compactRecursiveBits] at hv
  apply Fin.ext
  nlinarith

end

end IntegerMultBounds.MathlibTM2.Node
