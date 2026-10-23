module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveLayout

/-! Absolute binary coordinates of exact selective targets and source wires. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem selectiveFieldsLen (p : Par) (X : ℕ) :
    fieldsLen (selectiveLen p X) = p.wc + (p.wy + 2 * p.wc + X) := by
  simp [fieldsLen, selectiveLen, Fin.sum_univ_succ]
  omega

def selectiveSourcePosition (p : Par) (X : ℕ) (s : SlotSource p X) :
    Fin (fieldsLen (selectiveLen p X)) :=
  ⟨p.wc + (sourceWire p X s).val, by
    rw [selectiveFieldsLen]
    exact Nat.add_lt_add_left (sourceWire p X s).isLt _⟩

theorem selectiveTargetPosition_lt {p : Par} (hK : 0 < p.K) (c : Fin p.n) : posS p c.val < p.wy := by
  have hc := Nat.mul_lt_mul_of_pos_right c.isLt hK
  unfold posS Par.wy
  omega

def selectiveTargetPosition (p : Par) (X : ℕ) (hK : 0 < p.K) (c : Fin p.n) :
    Fin (fieldsLen (selectiveLen p X)) :=
  ⟨p.wc + posS p c.val, by
    rw [selectiveFieldsLen]
    have hc := selectiveTargetPosition_lt hK c
    omega⟩

theorem selectiveTargetPosition_injective (p : Par) (X : ℕ) (hK : 0 < p.K) :
    Function.Injective (selectiveTargetPosition p X hK) := by
  intro c d he
  have hv := congrArg (fun q : Fin (fieldsLen (selectiveLen p X)) => q.val) he
  change p.wc + posS p c.val = p.wc + posS p d.val at hv
  exact Fin.ext ((posS_mono hK).injective (Nat.add_left_cancel hv))

theorem selectiveSourcePosition_bit {p : Par} {X : ℕ} (s : SlotSource p X) (i : ℕ) :
    i.testBit (selectiveSourcePosition p X s).val =
      s.physical (selectiveView p X i).y (selectiveView p X i).x := sourceWire_bit p X s i

/-- The typed source restriction is exactly disjointness from active physical
target coordinates, including inactive low bits and complete spectator words. -/
theorem selectiveSourcePosition_allowed {p : Par} {X : ℕ} (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : SlotSource p X) (hs : s.Allowed active)
    (c : Fin p.n) (hc : active c = true) :
    selectiveSourcePosition p X s ≠ selectiveTargetPosition p X hK c := by
  intro he
  have hv := congrArg (fun q : Fin (fieldsLen (selectiveLen p X)) => q.val) he
  cases s with
  | low r =>
    change p.wc + r.val = p.wc + posS p c.val at hv
    unfold posS at hv
    have := r.isLt
    omega
  | digit d r =>
    change p.wc + (p.ρ + d.val * p.K + r.val) = p.wc + posS p c.val at hv
    unfold posS at hv
    have hr := r.isLt
    have hd : d = c := by
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hm := Nat.mul_le_mul_right p.K (by omega : d.val + 1 ≤ c.val)
        rw [Nat.add_mul] at hm
        omega
      · have hm := Nat.mul_le_mul_right p.K (by omega : c.val + 1 ≤ d.val)
        rw [Nat.add_mul] at hm
        omega
    subst d
    have hpos := hs hc
    omega
  | high r =>
    change p.wc + (p.ρ + p.n * p.K + r.val) = p.wc + posS p c.val at hv
    unfold posS at hv
    have hm := Nat.mul_lt_mul_of_pos_right c.isLt hK
    omega
  | spectator r =>
    change p.wc + (p.wy + 2 * p.wc + r.val) = p.wc + posS p c.val at hv
    have hpos := selectiveTargetPosition_lt hK c
    omega

end IntegerMultBounds.MathlibTM2.Routing
