module

public import IntegerMultBounds.MathlibTM2.Mult.Pipeline
public import IntegerMultBounds.ExactRecoveryOutput
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The concrete numerical pipeline supplies the existing exact-width output
contract. This uses the pipeline's own size parameters; no compatibility with
the compact-control parameters or execution of the pipeline is assumed proved. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PipelineOutput

open Filter Machine

/-- The concrete recovered coefficients for original MSB operand words. -/
noncomputable def coefficients (n : ℕ) (x y : List Bool) : List ℕ :=
  Pipeline.pipelineCoeffs n (binaryValue x) (binaryValue y)

/-- Carry normalization and exact-width serialization of the concrete pipeline. -/
noncomputable def output (n : ℕ) (x y : List Bool) : List Bool :=
  ExactRecoveryOutput.output (Sizes.b n) (ExactRecoveryOutput.chunkCount (Sizes.b n) n) n
    (coefficients n x y)

/-- All numerical stages are instantiated: no supplied transform-error or
coefficient-correctness hypothesis remains in the exact-width output theorem. -/
theorem eventually_output_spec : ∀ᶠ n : ℕ in atTop,
    ∀ x y : List Bool, x.length = n → y.length = n →
      (output n x y).length = 2*n ∧ binaryValue (output n x y) = binaryValue x*binaryValue y := by
  filter_upwards [Pipeline.pipeline_correct, Sizes.eventually_big] with n hcorrect hbig
  intro x y hx hy
  apply ExactRecoveryOutput.output_spec_chunks (Sizes.one_le_b hbig.1) hx hy
  apply hcorrect
  · exact Nat.size_le.mpr (hx ▸ binaryValue_lt x)
  · exact Nat.size_le.mpr (hy ▸ binaryValue_lt y)

/-- Installing that concrete word discharges the literal machine output
contract. Physical installation and the fast-program runtime remain separate. -/
theorem eventually_outputCorrect : ∀ᶠ n : ℕ in atTop,
    ∀ {t q a : ℕ} (M : Program t q a) (c : Config t q a) (x y : List Bool),
      x.length = n → y.length = n →
      c.tape ⟨0,M.tapes_pos⟩ = wordTape ((output n x y).map bitSymbol) →
      outputCorrect M n x y c := by
  filter_upwards [eventually_output_spec] with n houtput
  intro t q a M c x y hx hy htape
  obtain ⟨hlen,hvalue⟩ := houtput x y hx hy
  exact ⟨output n x y,hlen,hvalue,htape⟩

end IntegerMultBounds.MathlibTM2.Mult.PipelineOutput
