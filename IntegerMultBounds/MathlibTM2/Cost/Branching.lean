module

public import IntegerMultBounds.MathlibTM2.Node.Body
public import IntegerMultBounds.Machine.CompactComplexActualCallLoweredNetwork
import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import IntegerMultBounds.Networks.NetworkBudget

/-!
# The branching ratio of the layer recursion

A node of level `j + 1` of the layer machine runs `F = factorCount (program ds)` child calls on
`NW` data roles. For the T16 node `F = 1,041,408` (`Impl.layerProgram_children`) and
`NW = 14,336`, so `F / NW < m ^ (999/1000)` with `m = 73` (`br_branching_999`).

The direction lists `brDirs` of the earlier network remain a parameter of `program` and of the
statements below; the program does not read them.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks
  IntegerMultBounds.Machine ComplexFramedExecution

/-! ### Factor count of the node program -/

lemma br_factorCount_ofK (l : List (Networks.Certificates.T16.Impl.KInstr NWire)) :
    factorCount (l.map ofK) = Networks.Certificates.T16.Impl.kChildren l := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    rw [List.map_cons, show Networks.Certificates.T16.Impl.kChildren (i :: rest) =
      Networks.Certificates.T16.Impl.kChildren [i] + Networks.Certificates.T16.Impl.kChildren rest from
        Networks.Certificates.T16.Impl.kChildren_append [i] rest]
    cases i with
    | factor w g =>
      simp only [ofK, factorCount, ih]
      rw [show Networks.Certificates.T16.Impl.kChildren
        [Networks.Certificates.T16.Impl.KInstr.factor w g] = 1 from rfl]; omega
    | gate g =>
      simp only [ofK, factorCount, ih]
      rw [show Networks.Certificates.T16.Impl.kChildren
        [Networks.Certificates.T16.Impl.KInstr.gate g] = 0 from rfl]; omega
    | trans w v =>
      simp only [ofK, factorCount, ih]
      rw [show Networks.Certificates.T16.Impl.kChildren
        [Networks.Certificates.T16.Impl.KInstr.trans w v] = 0 from rfl]; omega
    | xor w i j =>
      simp only [ofK, factorCount, ih]
      rw [show Networks.Certificates.T16.Impl.kChildren
        [Networks.Certificates.T16.Impl.KInstr.xor w i j] = 0 from rfl]; omega
    | phase w i c =>
      simp only [ofK, factorCount, ih]
      rw [show Networks.Certificates.T16.Impl.kChildren
        [Networks.Certificates.T16.Impl.KInstr.phase w i c] = 0 from rfl]; omega

/-- **The factor count of the node program.** -/
theorem br_factorCount_program (ds : Directions) : factorCount (program ds) = 1041408 := by
  rw [program_eq, br_factorCount_ofK, Networks.Certificates.T16.Impl.layerProgram_children]

/-! ### The directions of the earlier call schema -/

/-- The directions of the original recursive call schema (not read by the program). -/
noncomputable abbrev brDirs : Directions := CompactComplexActualCallLoweredNetwork.directions

theorem br_directions_realizes : ComplexPhaseBudget.Realizes brDirs :=
  CompactComplexActualCallLoweredNetwork.realizes

theorem br_factorCount_directions : factorCount (program brDirs) = 1041408 :=
  br_factorCount_program brDirs

theorem br_factorCount_le : factorCount (program brDirs) ≤ 1041408 :=
  (br_factorCount_directions).le

/-! ### The branching ratio -/

/-- The number of data roles. -/
theorem br_NW_eq : NW = 14336 := NW_eq

/-- The branching ratio of the T16 node: `F / NW < m ^ (999/1000)`. -/
theorem br_branching_999 :
    (factorCount (program brDirs) : ℝ) / NW < (m : ℝ) ^ (999 / 1000 : ℝ) := by
  rw [br_factorCount_directions, br_NW_eq, show ((m : ℕ) : ℝ) = 73 by norm_num [m]]
  simp only [Nat.cast_ofNat]
  have hpos : (0 : ℝ) < (1041408 : ℝ) / 14336 := by norm_num
  rw [← Real.rpow_lt_rpow_iff hpos.le (by positivity) (by norm_num : (0 : ℝ) < 1000),
    ← Real.rpow_mul (by norm_num), show (999 / 1000 : ℝ) * 1000 = (999 : ℕ) by norm_num,
    Real.rpow_natCast, show (1000 : ℝ) = (1000 : ℕ) by norm_num, Real.rpow_natCast]
  rw [div_pow, div_lt_iff₀ (by positivity)]
  exact_mod_cast (show (1041408 : ℕ) ^ 1000 < 73 ^ 999 * 14336 ^ 1000 by decide +kernel)

/-- The branching ratio: `F / NW < m ^ σ` with `σ < 1`. -/
theorem br_branching :
    (factorCount (program brDirs) : ℝ) / NW < (m : ℝ) ^ Parameters.sigma :=
  br_branching_999.trans_le (Real.rpow_le_rpow_of_exponent_le (by norm_num [m])
    (by norm_num [Parameters.sigma]))

/-- `log_m (F / NW) < 999/1000`. -/
theorem br_logb_lt_999 :
    Real.logb (m : ℝ) ((factorCount (program brDirs) : ℝ) / NW) < 999 / 1000 := by
  have hpos : (0 : ℝ) < (factorCount (program brDirs) : ℝ) / NW := by
    rw [br_factorCount_directions, br_NW_eq]; norm_num
  exact (Real.logb_lt_iff_lt_rpow (by norm_num [m]) hpos).2 br_branching_999

end IntegerMultBounds.MathlibTM2.Cost
