module

public import IntegerMultBounds.Machine.FlatPaddedScaleFromCounters
public import IntegerMultBounds.Machine.LevelLoop
public import IntegerMultBounds.Machine.CounterBank
public import IntegerMultBounds.MathlibTM2.M8.AtomShiftLoop

/-!
# Atom scalings as level loops

An atom scaling `x_t ← c x_t` on `n` coordinates of `f` atoms is `f` ordinary scalings of the
refined coordinates `t f + l`. The level loop runs `FlatPaddedScaleFromCounters` at each level
and steps the counters `T` up and `R` down between levels (`scale_realizes`); its array realizes
the refined atom scaling (`scale_transport`). The cost is `C f V`, with `C` depending only on the
coefficient.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.AtomScaleLoop
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateSchedule (bits)
open SharedPlacementAlphabet (setTape)
open FlatPaddedScaleFromCounters (TapeCount Local)
open AtomTransport (Transports)
open AtomShiftLoop (lv lv_val shiftT at_val count_le count_le_volume levels_eq)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance {b : ℕ} : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

variable {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)

variable (r) in
abbrev Tape2 := TapeCount r + TapeCount r

variable {D b W : ℕ}

variable (r) in
/-- The loop body bank with counters `w`. -/
def scaleBank (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) : Tapes (Tape2 r) prime :=
  ((CounterBank.counters w).append ((SharedBank.empty 9 prime).append (FlatPaddedScaleFromCounters.work r a))).append
    (SharedBank.empty (TapeCount r) prime)

/-- The counters of a scaling at target `T`. -/
def counters (b W : ℕ) (T : Fin D) : Fin 6 → ℕ := ![b, W, T.val, D-1-T.val, 0, 0]

theorem bank_eq (T : Fin D) (a : FlatCoordinateStages.Array D b W) :
    (FlatPaddedScaleFromCounters.bank r b W T a).append (SharedBank.empty (TapeCount r) prime) =
      scaleBank r (counters b W T) a := by
  rw [FlatPaddedScaleFromCounters.bank, FlatPaddedScaleFromCounters.dimsInput, CounterBank.counters_eq]
  rfl

variable (r) in
def cslot (j : Fin 6) : Fin (Tape2 r) :=
  Fin.castAdd (TapeCount r) (Fin.castAdd (9 + Local r) (CounterBank.slot j))
variable (r) in
def oslot : Fin (Tape2 r) := Fin.natAdd (TapeCount r) ⟨0, by simp [TapeCount]⟩
variable (r) in
def zslot : Fin (Tape2 r) := Fin.natAdd (TapeCount r) ⟨1, by simp only [TapeCount]; omega⟩

theorem cslot_ne_o (j : Fin 6) : cslot r j ≠ oslot r := by
  intro e; have := congrArg Fin.val e; simp [cslot, oslot, CounterBank.slot, TapeCount] at this; omega
theorem cslot_ne_z (j : Fin 6) : cslot r j ≠ zslot r := by
  intro e; have := congrArg Fin.val e; simp [cslot, zslot, CounterBank.slot, TapeCount] at this; omega
theorem o_ne_z : oslot r ≠ zslot r := by
  intro e; have := congrArg Fin.val e; simp only [oslot, zslot, Fin.val_natAdd] at this; omega

theorem cslot_set (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) (x : ℕ) :
    setTape (scaleBank r w a) (cslot r j) (RadixZeroFill.encodedBinary (bits x)) 1 =
      scaleBank r (Function.update w j x) a := by
  rw [scaleBank, cslot, SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left, CounterBank.counters_set]
  rfl

theorem inc_hoare (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) :
    HoareTime (CounterSteps.incProgram (a := prime) (cslot r j)) (fun v => v = scaleBank r w a)
      (fun v => v = scaleBank r (Function.update w j (w j + 1)) a) (2*w j+4) := by
  have h := CounterSteps.inc_hoare (cslot r j) (scaleBank r w a) (w j)
    (by simp only [scaleBank, cslot, Tapes.append, Fin.addCases_left]; exact CounterBank.counters_tape w j)
    (by simp only [scaleBank, cslot, Tapes.append, Fin.addCases_left]; exact CounterBank.counters_head w j)
  rwa [cslot_set] at h

theorem dec_hoare (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) (hj : 1 ≤ w j) :
    HoareTime (CounterSteps.decProgram (a := prime) (cslot r j) (oslot r) (zslot r) (cslot_ne_o j)
        (cslot_ne_z j) o_ne_z)
      (fun v => v = scaleBank r w a) (fun v => v = scaleBank r (Function.update w j (w j - 1)) a)
      (20*w j+80) := by
  have h := CounterSteps.dec_hoare (cslot_ne_o j) (cslot_ne_z j) o_ne_z (scaleBank r w a) (w j) hj
    (by simp only [scaleBank, cslot, Tapes.append, Fin.addCases_left]; exact CounterBank.counters_tape w j)
    (by simp only [scaleBank, cslot, Tapes.append, Fin.addCases_left]; exact CounterBank.counters_head w j)
    (by simp only [scaleBank, oslot, Tapes.append, Fin.addCases_right]; rfl)
    (by simp only [scaleBank, oslot, Tapes.append, Fin.addCases_right]; rfl)
    (by simp only [scaleBank, zslot, Tapes.append, Fin.addCases_right]; rfl)
    (by simp only [scaleBank, zslot, Tapes.append, Fin.addCases_right]; rfl)
  rwa [cslot_set] at h

variable {f : ℕ} (T : ℕ → Fin D)

/-- The arrays after each level. -/
def arrays (a : FlatCoordinateStages.Array D b W) : ℕ → FlatCoordinateStages.Array D b W
  | 0 => a
  | l + 1 => FlatCoordinateScaling.array hr (arrays a l) (T l)

/-- The bank at level `l`. -/
def levelBank (a : FlatCoordinateStages.Array D b W) (l : ℕ) : Tapes (Tape2 r) prime :=
  scaleBank r (counters b W (T l)) (arrays hr T a l)

variable (r) in
/-- The counter steps of the atom scaling: `T + 1`, `R - 1`. -/
def steps :=
  seq (CounterSteps.incProgram (a := prime) (cslot r 2))
    (CounterSteps.decProgram (a := prime) (cslot r 3) (oslot r) (zslot r) (cslot_ne_o 3) (cslot_ne_z 3)
      o_ne_z)

def program := LevelLoop.program (seq (FlatPaddedScaleFromCounters.program hr) (steps r))
  (FlatPaddedScaleFromCounters.program hr)

theorem stage_hoare (hb0 : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array D b W) (l : ℕ) :
    HoareTime (FlatPaddedScaleFromCounters.program hr) (fun v => v = levelBank hr T a l)
      (fun v => v = scaleBank r (counters b W (T l)) (arrays hr T a (l+1)))
      (FlatPaddedScaleFromCounters.constant r*((modulus b)^D*W)) := by
  have h := FlatPaddedScaleFromCounters.realizes hr (T l) hb0 hW (arrays hr T a l)
  refine h.consequence (fun v hv => by rw [hv, levelBank, bank_eq]) (fun v hv => by
    rw [hv]; exact bank_eq _ _) le_rfl

/-- The arrays realize the run of the per-level scalings. -/
theorem levels_transport (a : FlatCoordinateStages.Array D b W) (f : ℕ) :
    Transports a (arrays hr T a f)
      (OrderedAffine.run ((List.range f).map fun l =>
        .scale (T l) (Swap.Modular.ratMod (modulus b) r))) := by
  have h := AtomTransport.transports_run ((List.range f).map fun l =>
      OrderedAffine.Op.scale (T l) (Swap.Modular.ratMod (modulus b) r))
    (arrays hr T a) (fun i hi => by
      simp only [List.getElem_map, List.getElem_range]
      exact FlatCoordinateScaling.array_entry hr (arrays hr T a i) (T i))
  simp only [List.length_map, List.length_range] at h
  exact h

section Atoms

variable {n : ℕ} (t : Fin n)

theorem steps_hoare (hf : 0 < f) (l : ℕ) (a : FlatCoordinateStages.Array (n * f) b W) (hl : l + 1 < f) :
    HoareTime (steps r)
      (fun v => v = scaleBank r (counters b W (shiftT t hf l)) a)
      (fun v => v = scaleBank r (counters b W (shiftT t hf (l+1))) a)
      (22 * (n * f) + 100) := by
  have e0 := lv_val hf (show l < f by omega)
  have e1 := lv_val hf hl
  have hT : (shiftT t hf l).val = l + f * t.val := by rw [shiftT, at_val, e0]
  have hT' : (shiftT t hf (l+1)).val = l + 1 + f * t.val := by rw [shiftT, at_val, e1]
  have hTD := (shiftT t hf l).isLt
  have hR := count_le t l hl
  set w := counters b W (shiftT t hf l)
  have h1 := inc_hoare (r := r) w a 2
  set w1 := Function.update w 2 (w 2 + 1)
  have h2 := dec_hoare (r := r) w1 a 3 (by simp [w1, w, counters, hT]; omega)
  have he : Function.update w1 3 (w1 3 - 1) = counters b W (shiftT t hf (l+1)) := by
    funext j
    fin_cases j <;> simp [w1, w, counters, Function.update, hT, hT'] <;> omega
  rw [he] at h2
  apply (h1.seq h2).consequence (fun _ h => h) (fun _ h => h)
  simp only [w1, w, counters, Function.update, hT]
  simp
  omega

variable (r) in
/-- The constant of the atom scaling loop. -/
def constant : ℕ := FlatPaddedScaleFromCounters.constant r + 300

theorem cost_le (hb0 : 0 < b) (hW : 0 < W) (hf : 0 < f) :
    (f-1)*(FlatPaddedScaleFromCounters.constant r*((modulus b)^(n*f)*W)+1+(22 * (n * f) + 100)) +
      6*(f-1) + 7*(bits (f-1)).length + 16 + 1 + FlatPaddedScaleFromCounters.constant r*((modulus b)^(n*f)*W)
      ≤ constant r * f * ((modulus b)^(n*f)*W) := by
  have hD := count_le_volume hb0 hW (n * f)
  have hl := CounterSteps.bits_length (f-1)
  set V := (modulus b)^(n*f)*W
  set C := FlatPaddedScaleFromCounters.constant r
  have hV : 1 ≤ V := by omega
  have hb : (f-1)*(C*V+1+(22 * (n * f) + 100)) ≤ (f-1)*((C+123)*V) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hb hl ⊢
  unfold constant
  nlinarith

/-- The array after the atom scaling. -/
def scaleArray (hf : 0 < f) (a : FlatCoordinateStages.Array (n * f) b W) := arrays hr (shiftT t hf) a f

/-- **The atom scaling on the machine.** One fixed program for each coefficient, for every `n`,
`f` and `t`. -/
theorem scale_realizes (hf : 0 < f) (hb0 : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array (n * f) b W) :
    HoareTime (program hr)
      (fun v => v = LevelLoop.bank (scaleBank r (counters b W (shiftT t hf 0)) a) f)
      (fun v => v = LevelLoop.bank (scaleBank r (counters b W (shiftT t hf (f-1))) (scaleArray hr t hf a)) f)
      (constant r * f * ((modulus b)^(n*f)*W)) := by
  have hlast := stage_hoare hr (shiftT t hf) hb0 hW a (f-1)
  rw [show f - 1 + 1 = f by omega] at hlast
  have h := LevelLoop.level_hoare (seq (FlatPaddedScaleFromCounters.program hr) (steps r)) _ f
    (levelBank hr (shiftT t hf) a) _ _ _ (fun l hl =>
      (stage_hoare hr (shiftT t hf) hb0 hW a l).seq (steps_hoare t hf l _ hl)) hlast
  exact h.consequence (fun _ h => h) (fun _ h => h) (cost_le hb0 hW hf)

/-- The atom scaling's array realizes the refined atom scaling. -/
theorem scale_transport (hf : 0 < f) (a : FlatCoordinateStages.Array (n * f) b W) :
    Transports a (scaleArray hr t hf a)
      (OrderedAffine.run (AtomOps.refined (f := f)
        (AtomOps.AtomOp.scale t (Swap.Modular.ratMod (modulus b) r)))) := by
  have h := levels_transport hr (shiftT t hf) a f
  rw [AtomOps.refined, levels_eq _ (fun l => .scale (shiftT t hf l)
    (Swap.Modular.ratMod (modulus b) r)) (fun l => by
      have e := lv_val hf l.isLt
      simp only [shiftT]
      congr 2; ext; simp [e])]
  exact h

end Atoms

end
end IntegerMultBounds.MathlibTM2.M8.AtomScaleLoop
