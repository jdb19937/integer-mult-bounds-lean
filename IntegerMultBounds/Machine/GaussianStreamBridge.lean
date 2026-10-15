module

public import IntegerMultBounds.Machine.ButterflyStreamSemantics
public import IntegerMultBounds.MathlibTM2.Layer.GaussLin

/-! The native signed radix words and the new Gaussian carry automata represent
the same butterfly numerators. The comparison is between actual output words,
not an assumed codec specification. Signed interpretation and the inherited
grid bounds are supplied by `ButterflyPhaseRecordSemantics`. -/

@[expose] public section

namespace IntegerMultBounds.Machine.GaussianStreamBridge

open ButterflyStreamData
open IntegerMultBounds.MathlibTM2.Layer

/-- The Gaussian integer stored in a native complex coefficient. -/
def numerator (b : ℕ) (x : Coefficient) : GaussianInt :=
  ⟨ButterflySigned.signedValue b x.1, ButterflySigned.signedValue b x.2⟩

/-- The two native word residues, at their common physical width. -/
def residue (w : ℕ) (x : Coefficient) : GR w :=
  ((RadixDigits.value x.1 : ZMod (2 ^ w)), (RadixDigits.value x.2 : ZMod (2 ^ w)))

/-- Centered signed decoding retains the residue, including the signed minimum. -/
theorem red_numerator (b : ℕ) (x : Coefficient) :
    red (b + 1) (numerator b x) = residue (b + 1) x := by
  exact Prod.ext (ButterflySigned.signed_cast b x.1) (ButterflySigned.signed_cast b x.2)

/-- The old four physical numerator words are precisely the new doubled kernel
in the residue ring. This requires only their actual input widths. -/
theorem butterfly_residue (a b : Coefficient) (w : ℕ)
    (ha : a.1.length = w ∧ a.2.length = w)
    (hb : b.1.length = w ∧ b.2.length = w) :
    (residue w (result a b 0), residue w (result a b 1)) =
      GR.kernel2 (residue w a) (residue w b) := by
  have hw : ∀ i, (componentWords a b i).length = w := by
    intro i
    cases i with
    | zero => exact ha.1
    | succ i =>
      cases i with
      | zero => exact ha.2
      | succ i =>
        cases i with
        | zero => exact hb.1
        | succ i => exact hb.2
  have h := fun i => ButterflyNumerator.words_value i (componentWords a b) w hw
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [residue, result, Matrix.cons_val_zero, Matrix.cons_val_one, GR.kernel2, GR.mulG]
  · rw [h 0]; simp [ButterflyNumerator.numerator, componentWords]; ring
  · rw [h 1]; simp [ButterflyNumerator.numerator, componentWords]; ring
  · rw [h 2]; simp [ButterflyNumerator.numerator, componentWords]; ring
  · rw [h 3]; simp [ButterflyNumerator.numerator, componentWords]; ring

/-- The new carry automaton emits exactly the columns of the old physical
butterfly output, at every bit position of both complex words. -/
theorem butterfly_columns (a b : Coefficient) (w : ℕ)
    (ha : a.1.length = w ∧ a.2.length = w)
    (hb : b.1.length = w ∧ b.2.length = w) :
    grun gKernel2 (fun _ => (0, 0)) (gcols ![residue w a, residue w b]) =
      gcols ![residue w (result a b 0), residue w (result a b 1)] := by
  rw [grun_kernel2]
  have h := butterfly_residue a b w ha hb
  rw [← h]

end IntegerMultBounds.Machine.GaussianStreamBridge
