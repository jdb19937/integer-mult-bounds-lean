module

public import IntegerMultBounds.Machine.Shared50NonrecursiveCoordinates
public import IntegerMultBounds.MathlibTM2.M8.ExchangeBound

/-!
# Supported nonrecursive field operations on the flat coordinate machine

The flat coordinate stages (`FlatCoordinateSchedule`) accept a scaling by `r` when `r` is a scale
that occurs (`Shared50AffineCoefficients.ScaleOccurs`), and a shift when its control precedes its
target and its coefficient occurs (`Shared50AffineCoefficients.Occurs`): a coefficient of
Shared50's schedules, or any coefficient within `Networks.coefficientBound`. An operation is
supported when its coefficients are (`CoeffSupported`); bounded coefficients are supported
(`CoeffBounded.supported`). Every legal, supported, nonrecursive field operation expands to
supported stages on the `H ++ D` vector of any width `d` (`expanded_supported`), and one fixed
physical program realizes it at every prime-power width (`realizes`), as
`Shared50NonrecursiveCoordinates.realizes` does for Shared50's operations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.Coordinates

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open AffineFieldCoordinates
open ActualAffineScaling (modulus)
open Shared50ModularControl (prime)

variable {d : ℕ}

/-- The coefficients of every operation are within the supplier bound. -/
def CoeffBounded (op : AffineFieldProgram.Op (Fin d) ℚ) : Prop :=
  ∀ r ∈ M8.Exchange.opCoeffs op, r.num.natAbs ≤ coefficientBound ∧ r.den ≤ coefficientBound

/-- The coefficients of an operation that the flat coordinate stages accept. -/
structure CoeffSupported (op : AffineFieldProgram.Op (Fin d) ℚ) : Prop where
  occurs : ∀ r ∈ M8.Exchange.opCoeffs op, Shared50AffineCoefficients.Occurs r
  scaleH : ∀ i r, op = .affineH (.scale i r) → Shared50AffineCoefficients.ScaleOccurs r
  scaleD : ∀ i r, op = .affineD (.scale i r) → Shared50AffineCoefficients.ScaleOccurs r

theorem bounded_occurs {r : ℚ} (h : r.num.natAbs ≤ coefficientBound ∧ r.den ≤ coefficientBound) :
    Shared50AffineCoefficients.Occurs r := Or.inr h

theorem bounded_scale_occurs {r : ℚ} (hr : IsUnit r)
    (h : r.num.natAbs ≤ coefficientBound ∧ r.den ≤ coefficientBound) :
    Shared50AffineCoefficients.ScaleOccurs r := Or.inr ⟨hr.ne_zero, h⟩

private theorem unit_bounded {r : ℚ} (hr : r = 1 ∨ r = -1) :
    r.num.natAbs ≤ coefficientBound ∧ r.den ≤ coefficientBound := by
  have h1 : 1 ≤ coefficientBound := Nat.one_le_two_pow
  rcases hr with rfl | rfl <;> exact ⟨by simpa using h1, by simpa using h1⟩

/-- A legal operation with bounded coefficients is supported. -/
theorem CoeffBounded.supported {op : AffineFieldProgram.Op (Fin d) ℚ} (hb : CoeffBounded op)
    (hl : AffineFieldProgram.Legal op) : CoeffSupported op where
  occurs r hr := bounded_occurs (hb r hr)
  scaleH i r he := by
    subst he
    exact bounded_scale_occurs hl (hb r (by simp [M8.Exchange.opCoeffs]))
  scaleD i r he := by
    subst he
    exact bounded_scale_occurs hl (hb r (by simp [M8.Exchange.opCoeffs]))

/-- A legal nonrecursive operation with supported coefficients expands to supported stages. -/
theorem expanded_supported (op : AffineFieldProgram.Op (Fin d) ℚ)
    (hl : AffineFieldProgram.Legal op) (hb : CoeffSupported op) (hn : Nonrecursive op) :
    ∀ out ∈ expand op, FlatCoordinateSchedule.Supported out := by
  cases op with
  | affineH op =>
    intro out hout
    have he : out = liftH op := by simpa only [expand, List.mem_singleton] using hout
    subst out
    cases op with
    | scale i r => exact hb.scaleH i r rfl
    | shift i j r =>
      exact ⟨(hl : j.val < i.val), hb.occurs r (by simp [M8.Exchange.opCoeffs])⟩
  | affineD op =>
    intro out hout
    have he : out = liftD op := by simpa only [expand, List.mem_singleton] using hout
    subst out
    cases op with
    | scale i r => exact hb.scaleD i r rfl
    | shift i j r =>
      refine ⟨?_, hb.occurs r (by simp [M8.Exchange.opCoeffs])⟩
      exact Nat.add_lt_add_left (hl : j.val < i.val) d
  | addToD i j =>
    intro out hout
    simp only [expand, List.mem_singleton] at hout
    subst out
    exact ⟨h_before_d i j, bounded_occurs (unit_bounded (Or.inl rfl))⟩
  | subFromD i j =>
    intro out hout
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hout with rfl | rfl
    · exact bounded_scale_occurs isUnit_one.neg (unit_bounded (Or.inr rfl))
    · exact ⟨h_before_d i j, bounded_occurs (unit_bounded (Or.inl rfl))⟩
  | interchange i j => exact hn.elim

/-- The fixed stage description of one bounded nonrecursive operation. -/
def description (op : AffineFieldProgram.Op (Fin d) ℚ) (hl : AffineFieldProgram.Legal op)
    (hb : CoeffSupported op) (hn : Nonrecursive op) : List (FlatCoordinateSchedule.Op (d + d)) :=
  FlatCoordinateSchedule.ofList (expand op) (expanded_supported op hl hb hn)

theorem description_rational (op : AffineFieldProgram.Op (Fin d) ℚ)
    (hl : AffineFieldProgram.Legal op) (hb : CoeffSupported op) (hn : Nonrecursive op) :
    (description op hl hb hn).map FlatCoordinateSchedule.Op.rational = expand op :=
  FlatCoordinateSchedule.rational_ofList _ _

private theorem ratMod_neg_one (m : ℕ) : Swap.Modular.ratMod m (-1) = -1 := by
  simp [Swap.Modular.ratMod]

theorem description_actions (op : AffineFieldProgram.Op (Fin d) ℚ)
    (hl : AffineFieldProgram.Legal op) (hb : CoeffSupported op) (hn : Nonrecursive op) (b : ℕ) :
    (description op hl hb hn).map (fun op => op.action b) =
      expand (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) := by
  change (description op hl hb hn).map
    ((OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b))) ∘ FlatCoordinateSchedule.Op.rational) = _
  rw [← List.map_map, description_rational]
  exact expand_map _ (Swap.Modular.ratMod_one _) (ratMod_neg_one _) _

/-- The output array has the exact `H`/`D` field semantics of the reduced operation. -/
theorem array_entry (op : AffineFieldProgram.Op (Fin d) ℚ) (hl : AffineFieldProgram.Legal op)
    (hb : CoeffSupported op) (hn : Nonrecursive op)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array (d + d) b W)
    (s : Swap.Shear.State (Fin d) (ZMod (modulus b))) (j : Fin W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    FlatCoordinateScheduleCompile.array (description op hl hb hn) b W hW a
      (FlatCoordinateLayout.index
        (embed (AffineFieldProgram.execute (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) s)) j) =
      a (FlatCoordinateLayout.index (embed s) j) := by
  dsimp only
  have hm : Nonrecursive (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) := by
    cases op <;> exact hn
  have hh := FlatCoordinateScheduleCompile.array_entry (description op hl hb hn) b W hW a (embed s) j
  rw [description_actions, expand_run _ hm] at hh
  exact hh

end
end IntegerMultBounds.MathlibTM2.M8.Machine.Coordinates
