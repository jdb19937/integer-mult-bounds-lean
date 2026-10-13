module

public import IntegerMultBounds.Schoenhage.LayoutPlacementGenerated
public import IntegerMultBounds.Schoenhage.TwistCleanupGenerated
public import IntegerMultBounds.Schoenhage.LayoutGenRun
import Lean.Util.CollectAxioms

/-! Validate generated adapters against the actual existing layout placements
and twist cleanup. Input readiness remains an explicit mathematical obligation. -/
@[expose] public section
namespace IntegerMultBounds.Schoenhage.LayoutAdapterPilot
open Machine LayoutGenSetup LayoutGenRun LayoutPlacementGenerated TwistCleanupGenerated
open Resampling.Script

theorem width_program : widthConverterProgram = binOf.map fb1 fb1_injective := by
  have sameSlots : widthConverterSlots = fb1 := by funext tape; fin_cases tape <;> rfl
  unfold widthConverterProgram
  simp only [sameSlots]
theorem chunk_program : chunkConverterProgram = binOf.map fb2 fb2_injective := by
  have sameSlots : chunkConverterSlots = fb2 := by funext tape; fin_cases tape <;> rfl
  unfold chunkConverterProgram
  simp only [sameSlots]
theorem cleanup_program : twistCleanupProgram = TwistDescriptors.cleanup := rfl

/-- The same width-converter adapter used in `runs_binPhase`. -/
theorem width_at_layout (ell chunk width axes : ℕ) (flags : List Bool) :
    Runs (binOf.map fb1 fb1_injective) (stD ell chunk width axes flags)
      (· = Function.update (stD ell chunk width axes flags) 44 (reg (bin width)))
      (8 * width * width + 70 * width + 40) := by
  rw [← width_program]
  apply widthConverter_runs width (stD ell chunk width axes flags)
  funext tape
  fin_cases tape <;> tsimp [widthConverterSlots, bbank, stD, stC, stB, stA, lstart, emp]

/-- The second placement preserves the already installed record-width word. -/
theorem chunk_at_layout (ell chunk width axes : ℕ) (flags : List Bool) (recordWord : WTape) :
    Runs (binOf.map fb2 fb2_injective) (Function.update (stD ell chunk width axes flags) 6 recordWord)
      (· = Function.update (Function.update (stD ell chunk width axes flags) 6 recordWord) 24 (reg (bin chunk)))
      (8 * chunk * chunk + 70 * chunk + 40) := by
  rw [← chunk_program]
  apply chunkConverter_runs chunk (Function.update (stD ell chunk width axes flags) 6 recordWord)
  funext tape
  fin_cases tape <;> tsimp [chunkConverterSlots, bbank, stD, stC, stB, stA, lstart, emp]

end IntegerMultBounds.Schoenhage.LayoutAdapterPilot

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if [`IntegerMultBounds.Schoenhage.CertifiedSequence,
        `IntegerMultBounds.Schoenhage.LayoutPlacementGenerated,
        `IntegerMultBounds.Schoenhage.TwistCleanupGenerated,
        `IntegerMultBounds.Schoenhage.LayoutAdapterPilot].any (·.isPrefixOf name) then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Adapter pilot axiom audit passed for {count} declarations."
