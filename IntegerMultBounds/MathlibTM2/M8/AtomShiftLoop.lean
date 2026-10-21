module

public import IntegerMultBounds.Machine.FlatPaddedShiftFromCounters
public import IntegerMultBounds.Machine.LevelLoop
public import IntegerMultBounds.Machine.CounterBank
public import IntegerMultBounds.MathlibTM2.M8.AtomTransport

/-!
# Atom shifts as level loops

An atom shift `x_t ← x_t + c x_k` on `n` coordinates of `f` atoms is `f` ordinary shifts on the
`n f` refined coordinates, one per level (`AtomOps.refined`). The level loop runs them with one
fixed program: at level `l` the bank holds the counters of target `T l` and control `K l`, the
body runs `FlatPaddedShiftFromCounters` and steps the counters to level `l + 1`, and the last
level runs the stage alone.

`shift_levels` is the loop for any targets and controls with a counter-step program between
levels; it moves the records along the run of the per-level shifts (`levels_transport`). The
atom shift (`shift_realizes`, control `K l = k f + l`: `T`, `K` up, `R` down) and the reversed
atom shift (`revShift_realizes`, control `K l = k f + f - 1 - l`: `T`, `M` up by one and two,
`R`, `K` down) instantiate it, and their arrays realize the refined atom operations
(`shift_transport`, `revShift_transport`). Each costs `C f V` with `C` independent of `n`, `f`, `t`
and `k`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.AtomShiftLoop
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateSchedule (bits)
open SharedPlacementAlphabet (setTape)
open FlatPaddedShiftFromCounters (TapeCount prefixTapes)
open AtomTransport (Transports)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance {b : ℕ} : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

abbrev Tape2 := TapeCount + TapeCount

variable {D b W : ℕ}

/-! ### The bank with counters -/

/-- The loop body bank with counters `w`. -/
def shiftBank (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) : Tapes Tape2 prime :=
  (((CounterBank.counters w).append (PrefixWidthCopies.blankBank prime prefixTapes)).append
    (FlatPaddedShiftFromCounters.payload a)).append (SharedBank.empty TapeCount prime)

/-- The counters of a shift with target `T` and control `K`. -/
def counters (b W : ℕ) (T K : Fin D) : Fin 6 → ℕ := ![b, W, T.val, D-1-T.val, K.val, T.val-1-K.val]

theorem bank_eq (T K : Fin D) (a : FlatCoordinateStages.Array D b W) :
    (FlatPaddedShiftFromCounters.bank b W T K a).append (SharedBank.empty TapeCount prime) =
      shiftBank (counters b W T K) a := by
  rw [FlatPaddedShiftFromCounters.bank, FlatPaddedShiftFromCounters.dimsInput, CounterBank.counters_eq]
  rfl

def cslot (j : Fin 6) : Fin Tape2 :=
  Fin.castAdd TapeCount (Fin.castAdd 17 (Fin.castAdd prefixTapes (CounterBank.slot j)))
def oslot : Fin Tape2 := Fin.natAdd TapeCount 0
def zslot : Fin Tape2 := Fin.natAdd TapeCount 1

theorem cslot_ne_o (j : Fin 6) : cslot j ≠ oslot := by
  intro e; have := congrArg Fin.val e
  simp [cslot, oslot, CounterBank.slot, TapeCount, FlatPaddedShiftFromCounters.prefixTapes_eq] at this
  omega
theorem cslot_ne_z (j : Fin 6) : cslot j ≠ zslot := by
  intro e; have := congrArg Fin.val e
  simp [cslot, zslot, CounterBank.slot, TapeCount, FlatPaddedShiftFromCounters.prefixTapes_eq] at this
  omega
theorem o_ne_z : oslot ≠ zslot := by
  intro e; have := congrArg Fin.val e; simp [oslot, zslot] at this

theorem cslot_tape (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) :
    (shiftBank w a).tape (cslot j) = RadixZeroFill.encodedBinary (bits (w j)) := by
  simp only [shiftBank, cslot, Tapes.append, Fin.addCases_left]
  exact CounterBank.counters_tape w j

theorem cslot_head (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) :
    (shiftBank w a).head (cslot j) = 1 := by
  simp only [shiftBank, cslot, Tapes.append, Fin.addCases_left]
  exact CounterBank.counters_head w j

theorem cslot_set (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) (x : ℕ) :
    setTape (shiftBank w a) (cslot j) (RadixZeroFill.encodedBinary (bits x)) 1 =
      shiftBank (Function.update w j x) a := by
  rw [shiftBank, cslot, SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_append_left,
    CounterBank.counters_set]
  rfl

theorem scratch_blank (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) :
    (shiftBank w a).tape oslot = (fun _ => blank) ∧ (shiftBank w a).head oslot = 0 ∧
    (shiftBank w a).tape zslot = (fun _ => blank) ∧ (shiftBank w a).head zslot = 0 := by
  simp only [shiftBank, oslot, zslot, Tapes.append, Fin.addCases_right, SharedBank.empty]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- Counter steps on the shift bank. -/
theorem inc_hoare (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) :
    HoareTime (CounterSteps.incProgram (a := prime) (cslot j)) (fun v => v = shiftBank w a)
      (fun v => v = shiftBank (Function.update w j (w j + 1)) a) (2*w j+4) := by
  have h := CounterSteps.inc_hoare (cslot j) (shiftBank w a) (w j) (cslot_tape w a j) (cslot_head w a j)
  rwa [cslot_set] at h

theorem dec_hoare (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (j : Fin 6) (hj : 1 ≤ w j) :
    HoareTime (CounterSteps.decProgram (a := prime) (cslot j) oslot zslot (cslot_ne_o j) (cslot_ne_z j) o_ne_z)
      (fun v => v = shiftBank w a) (fun v => v = shiftBank (Function.update w j (w j - 1)) a)
      (20*w j+80) := by
  obtain ⟨h1, h2, h3, h4⟩ := scratch_blank w a
  have h := CounterSteps.dec_hoare (cslot_ne_o j) (cslot_ne_z j) o_ne_z (shiftBank w a) (w j) hj
    (cslot_tape w a j) (cslot_head w a j) h1 h2 h3 h4
  rwa [cslot_set] at h

/-! ### Level loops over any targets and controls -/

variable (r : ℚ) {f : ℕ} (T K : ℕ → Fin D) (hKT : ∀ l, K l < T l)

/-- The arrays after each level. -/
def arrays (a : FlatCoordinateStages.Array D b W) : ℕ → FlatCoordinateStages.Array D b W
  | 0 => a
  | l + 1 => FlatPaddedShift.array r (arrays a l) (T l) (K l) (hKT l)

/-- The bank at level `l`. -/
def levelBank (a : FlatCoordinateStages.Array D b W) (l : ℕ) : Tapes Tape2 prime :=
  shiftBank (counters b W (T l) (K l)) (arrays r T K hKT a l)

/-- The body: the stage at the current level and the counter steps to the next. -/
def body {s : ℕ} (U : Program Tape2 s prime) := seq (FlatPaddedShiftFromCounters.program r) U

def program {s : ℕ} (U : Program Tape2 s prime) :=
  LevelLoop.program (body r U) (FlatPaddedShiftFromCounters.program r)

theorem stage_hoare (hden : r.den < prime) (hb0 : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array D b W)
    (l : ℕ) :
    HoareTime (FlatPaddedShiftFromCounters.program r)
      (fun v => v = levelBank r T K hKT a l)
      (fun v => v = shiftBank (counters b W (T l) (K l)) (arrays r T K hKT a (l+1)))
      (401000*((modulus b)^D*W)) := by
  have h := FlatPaddedShiftFromCounters.realizes r hden (T l) (K l) (hKT l) hb0 hW
    (arrays r T K hKT a l)
  refine h.consequence (fun v hv => by rw [hv, levelBank, bank_eq]) (fun v hv => by
    rw [hv]; exact bank_eq _ _ _) le_rfl

/-- **The level loop of shifts.** With counter steps `U` from each level to the next, the loop
runs the shift at every level. -/
theorem shift_levels (hden : r.den < prime) (hb0 : 0 < b) (hW : 0 < W) (hf : 0 < f)
    {s : ℕ} (U : Program Tape2 s prime) (cu : ℕ)
    (hU : ∀ l (a : FlatCoordinateStages.Array D b W), l + 1 < f →
      HoareTime U (fun v => v = shiftBank (counters b W (T l) (K l)) a)
        (fun v => v = shiftBank (counters b W (T (l+1)) (K (l+1))) a) cu)
    (a : FlatCoordinateStages.Array D b W) :
    HoareTime (program r U) (fun v => v = LevelLoop.bank (levelBank r T K hKT a 0) f)
      (fun v => v = LevelLoop.bank
        (shiftBank (counters b W (T (f-1)) (K (f-1))) (arrays r T K hKT a f)) f)
      ((f-1)*(401000*((modulus b)^D*W)+1+cu) + 6*(f-1) + 7*(bits (f-1)).length + 16 + 1 +
        401000*((modulus b)^D*W)) := by
  have hlast := stage_hoare r T K hKT hden hb0 hW a (f-1)
  rw [show f - 1 + 1 = f by omega] at hlast
  refine LevelLoop.level_hoare (body r U) _ f (levelBank r T K hKT a) _ _ _ (fun l hl => ?_) hlast
  exact (stage_hoare r T K hKT hden hb0 hW a l).seq (hU l _ hl)

/-- The arrays realize the run of the per-level shifts. -/
theorem levels_transport (a : FlatCoordinateStages.Array D b W) (f : ℕ) :
    Transports a (arrays r T K hKT a f)
      (OrderedAffine.run ((List.range f).map fun l =>
        .shift (T l) (K l) (Swap.Modular.ratMod (modulus b) r))) := by
  have h := AtomTransport.transports_run ((List.range f).map fun l =>
      OrderedAffine.Op.shift (T l) (K l) (Swap.Modular.ratMod (modulus b) r))
    (arrays r T K hKT a) (fun i hi => by
      simp only [List.getElem_map, List.getElem_range]
      exact FlatPaddedShift.array_entry r (arrays r T K hKT a i) (T i) (K i) (hKT i))
  simp only [List.length_map, List.length_range] at h
  exact h

/-! ### The atom shift and the reversed atom shift -/

section Atoms

variable {n : ℕ} (t k : Fin n)

/-- The level, clamped to the last. -/
def lv (hf : 0 < f) (l : ℕ) : Fin f :=
  ⟨min l (f-1), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hf Nat.one_pos)⟩

theorem lv_val (hf : 0 < f) {l : ℕ} (hl : l < f) : (lv hf l).val = l := by simp [lv]; omega

/-- The atom shift: target `t f + l`, control `k f + l`. -/
def shiftT (hf : 0 < f) (l : ℕ) : Fin (n * f) := AtomOps.«at» t (lv hf l)
def shiftK (hf : 0 < f) (l : ℕ) : Fin (n * f) := AtomOps.«at» k (lv hf l)
/-- The reversed atom shift: control `k f + f - 1 - l`. -/
def revK (hf : 0 < f) (l : ℕ) : Fin (n * f) := AtomOps.«at» k (lv hf l).rev

theorem shift_lt (hk : k < t) (hf : 0 < f) (l : ℕ) : shiftK k hf l < shiftT t hf l :=
  AtomOps.at_lt hk _ _
theorem rev_lt (hk : k < t) (hf : 0 < f) (l : ℕ) : revK k hf l < shiftT t hf l := AtomOps.at_lt hk _ _

theorem at_val (x : Fin n) (l : Fin f) : (AtomOps.«at» x l).val = l.val + f * x.val := by
  simp [AtomOps.«at», finProdFinEquiv_apply_val]

/-- The counter steps of the atom shift: `T + 1`, `R - 1`, `K + 1`. -/
def shiftSteps :=
  seq (seq (CounterSteps.incProgram (a := prime) (cslot 2))
    (CounterSteps.decProgram (a := prime) (cslot 3) oslot zslot (cslot_ne_o 3) (cslot_ne_z 3) o_ne_z))
    (CounterSteps.incProgram (a := prime) (cslot 4))

/-- The counter steps of the reversed atom shift: `T + 1`, `R - 1`, `K - 1`, `M + 2`. -/
def revSteps :=
  seq (seq (seq (seq (CounterSteps.incProgram (a := prime) (cslot 2))
    (CounterSteps.decProgram (a := prime) (cslot 3) oslot zslot (cslot_ne_o 3) (cslot_ne_z 3) o_ne_z))
    (CounterSteps.decProgram (a := prime) (cslot 4) oslot zslot (cslot_ne_o 4) (cslot_ne_z 4) o_ne_z))
    (CounterSteps.incProgram (a := prime) (cslot 5)))
    (CounterSteps.incProgram (a := prime) (cslot 5))

theorem count_le (l : ℕ) (hl : l + 1 < f) : 1 ≤ n * f - 1 - (l + f * t.val) := by
  have ht := t.isLt
  have : f * (t.val + 1) ≤ f * n := Nat.mul_le_mul_left f ht
  have : f * (t.val + 1) = f * t.val + f := by ring
  have : n * f = f * n := Nat.mul_comm _ _
  omega

theorem shiftSteps_hoare (hk : k < t) (hf : 0 < f) (l : ℕ) (a : FlatCoordinateStages.Array (n * f) b W) (hl : l + 1 < f) :
    HoareTime (shiftSteps)
      (fun v => v = shiftBank (counters b W (shiftT t hf l) (shiftK k hf l)) a)
      (fun v => v = shiftBank (counters b W (shiftT t hf (l+1)) (shiftK k hf (l+1))) a)
      (24 * (n * f) + 100) := by
  have e0 := lv_val hf (show l < f by omega)
  have e1 := lv_val hf hl
  have hT : (shiftT t hf l).val = l + f * t.val := by rw [shiftT, at_val, e0]
  have hT' : (shiftT t hf (l+1)).val = l + 1 + f * t.val := by rw [shiftT, at_val, e1]
  have hK : (shiftK k hf l).val = l + f * k.val := by rw [shiftK, at_val, e0]
  have hK' : (shiftK k hf (l+1)).val = l + 1 + f * k.val := by rw [shiftK, at_val, e1]
  have hkt : f * k.val + f ≤ f * t.val := by
    have : f * (k.val + 1) ≤ f * t.val := Nat.mul_le_mul_left f hk
    rw [Nat.mul_succ] at this; exact this
  have hTD := (shiftT t hf l).isLt
  have hKD := (shiftK k hf l).isLt
  have hR := count_le t l hl
  set w := counters b W (shiftT t hf l) (shiftK k hf l)
  have h1 := inc_hoare w a 2
  set w1 := Function.update w 2 (w 2 + 1)
  have h2 := dec_hoare w1 a 3 (by simp [w1, w, counters, hT]; omega)
  set w2 := Function.update w1 3 (w1 3 - 1)
  have h3 := inc_hoare w2 a 4
  have he : Function.update w2 4 (w2 4 + 1) = counters b W (shiftT t hf (l+1)) (shiftK k hf (l+1)) := by
    funext j
    fin_cases j <;> simp [w2, w1, w, counters, Function.update, hT, hT', hK, hK'] <;> omega
  rw [he] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  simp only [w2, w1, w, counters, Function.update, hT, hK]
  simp
  omega

theorem revSteps_hoare (hk : k < t) (hf : 0 < f) (l : ℕ) (a : FlatCoordinateStages.Array (n * f) b W) (hl : l + 1 < f) :
    HoareTime (revSteps)
      (fun v => v = shiftBank (counters b W (shiftT t hf l) (revK k hf l)) a)
      (fun v => v = shiftBank (counters b W (shiftT t hf (l+1)) (revK k hf (l+1))) a)
      (30 * (n * f) + 200) := by
  have e0 := lv_val hf (show l < f by omega)
  have e1 := lv_val hf hl
  have hT : (shiftT t hf l).val = l + f * t.val := by rw [shiftT, at_val, e0]
  have hT' : (shiftT t hf (l+1)).val = l + 1 + f * t.val := by rw [shiftT, at_val, e1]
  have hK : (revK k hf l).val = f - 1 - l + f * k.val := by rw [revK, at_val, Fin.val_rev, e0]; omega
  have hK' : (revK k hf (l+1)).val = f - 1 - (l + 1) + f * k.val := by
    rw [revK, at_val, Fin.val_rev, e1]; omega
  have hkt : f * k.val + f ≤ f * t.val := by
    have : f * (k.val + 1) ≤ f * t.val := Nat.mul_le_mul_left f hk
    rw [Nat.mul_succ] at this; exact this
  have hTD := (shiftT t hf l).isLt
  have hR := count_le t l hl
  set w := counters b W (shiftT t hf l) (revK k hf l)
  have h1 := inc_hoare w a 2
  set w1 := Function.update w 2 (w 2 + 1)
  have h2 := dec_hoare w1 a 3 (by simp [w1, w, counters, hT]; omega)
  set w2 := Function.update w1 3 (w1 3 - 1)
  have h3 := dec_hoare w2 a 4 (by simp [w2, w1, w, counters, hK]; omega)
  set w3 := Function.update w2 4 (w2 4 - 1)
  have h4 := inc_hoare w3 a 5
  set w4 := Function.update w3 5 (w3 5 + 1)
  have h5 := inc_hoare w4 a 5
  have he : Function.update w4 5 (w4 5 + 1) = counters b W (shiftT t hf (l+1)) (revK k hf (l+1)) := by
    funext j
    fin_cases j <;> simp [w4, w3, w2, w1, w, counters, Function.update, hT, hT', hK, hK'] <;> omega
  rw [he] at h5
  apply ((((h1.seq h2).seq h3).seq h4).seq h5).consequence (fun _ h => h) (fun _ h => h)
  simp only [w4, w3, w2, w1, w, counters, Function.update, hT, hK]
  simp
  omega

/-- The volume bounds the coordinate count. -/
theorem count_le_volume (hb0 : 0 < b) (hW : 0 < W) (D : ℕ) : D + 1 ≤ (modulus b)^D * W := by
  have hq : 2 ≤ modulus b := by
    have := Shared50ModularControl.prime_prime.two_le
    exact this.trans (Nat.le_self_pow (by omega) _)
  have h1 : D + 1 ≤ 2^D := Nat.lt_two_pow_self
  have h2 : 2^D ≤ (modulus b)^D := Nat.pow_le_pow_left hq D
  have h3 : (modulus b)^D ≤ (modulus b)^D * W := Nat.le_mul_of_pos_right _ hW
  omega

/-- The constant of the atom shift loops. -/
def constant : ℕ := 402000

theorem cost_le (hb0 : 0 < b) (hW : 0 < W) (hf : 0 < f) (cu : ℕ) (hcu : cu ≤ 30 * (n * f) + 200) :
    (f-1)*(401000*((modulus b)^(n*f)*W)+1+cu) + 6*(f-1) + 7*(bits (f-1)).length + 16 + 1 +
      401000*((modulus b)^(n*f)*W) ≤ constant * f * ((modulus b)^(n*f)*W) := by
  set V := (modulus b)^(n*f)*W
  have hD := count_le_volume hb0 hW (n * f)
  have hl := CounterSteps.bits_length (f-1)
  have hcu' : cu ≤ 230 * V := by omega
  have hV : 1 ≤ V := by omega
  have hb : (f-1)*(401000*V+1+cu) ≤ (f-1)*(401231*V) := Nat.mul_le_mul_left _ (by omega)
  have hf1 : (f-1) + 1 = f := by omega
  unfold constant
  nlinarith

/-- The array after the atom shift. -/
def shiftArray (hk : k < t) (hf : 0 < f) (r : ℚ) (a : FlatCoordinateStages.Array (n * f) b W) :=
  arrays r (shiftT t hf) (shiftK k hf) (shift_lt t k hk hf) a f

/-- The array after the reversed atom shift. -/
def revArray (hk : k < t) (hf : 0 < f) (r : ℚ) (a : FlatCoordinateStages.Array (n * f) b W) :=
  arrays r (shiftT t hf) (revK k hf) (rev_lt t k hk hf) a f

/-- **The atom shift on the machine.** One fixed program for every `n`, `f`, `t` and `k`. -/
theorem shift_realizes (hk : k < t) (hf : 0 < f) (hden : r.den < prime) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (n * f) b W) :
    HoareTime (program r shiftSteps)
      (fun v => v = LevelLoop.bank
        (shiftBank (counters b W (shiftT t hf 0) (shiftK k hf 0)) a) f)
      (fun v => v = LevelLoop.bank
        (shiftBank (counters b W (shiftT t hf (f-1)) (shiftK k hf (f-1))) (shiftArray t k hk hf r a)) f)
      (constant * f * ((modulus b)^(n*f)*W)) :=
  (shift_levels r (shiftT t hf) (shiftK k hf) (shift_lt t k hk hf) hden hb0 hW hf shiftSteps
    (24 * (n * f) + 100) (fun l a hl => shiftSteps_hoare t k hk hf l a hl) a).consequence
    (fun _ h => h) (fun _ h => h) (cost_le hb0 hW hf _ (by omega))

/-- **The reversed atom shift on the machine.** -/
theorem revShift_realizes (hk : k < t) (hf : 0 < f) (hden : r.den < prime) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (n * f) b W) :
    HoareTime (program r revSteps)
      (fun v => v = LevelLoop.bank
        (shiftBank (counters b W (shiftT t hf 0) (revK k hf 0)) a) f)
      (fun v => v = LevelLoop.bank
        (shiftBank (counters b W (shiftT t hf (f-1)) (revK k hf (f-1))) (revArray t k hk hf r a)) f)
      (constant * f * ((modulus b)^(n*f)*W)) :=
  (shift_levels r (shiftT t hf) (revK k hf) (rev_lt t k hk hf) hden hb0 hW hf revSteps
    (30 * (n * f) + 200) (fun l a hl => revSteps_hoare t k hk hf l a hl) a).consequence
    (fun _ h => h) (fun _ h => h) (cost_le hb0 hW hf _ le_rfl)

theorem levels_eq (g : Fin f → OrderedAffine.Op (Fin (n * f)) (ZMod (modulus b)))
    (g' : ℕ → OrderedAffine.Op (Fin (n * f)) (ZMod (modulus b))) (h : ∀ l : Fin f, g l = g' l) :
    AtomOps.levels g = (List.range f).map g' := by
  apply List.ext_getElem (by simp [AtomOps.levels])
  intro i h1 h2
  simp only [AtomOps.levels, List.getElem_map, List.getElem_finRange, List.getElem_range]
  exact h _

/-- The atom shift's array realizes the refined atom shift. -/
theorem shift_transport (hk : k < t) (hf : 0 < f) (a : FlatCoordinateStages.Array (n * f) b W) :
    Transports a (shiftArray t k hk hf r a)
      (OrderedAffine.run (AtomOps.refined (f := f)
        (AtomOps.AtomOp.shift t k (Swap.Modular.ratMod (modulus b) r)))) := by
  have h := levels_transport r (shiftT t hf) (shiftK k hf) (shift_lt t k hk hf) a f
  rw [AtomOps.refined, levels_eq _ (fun l => .shift (shiftT t hf l) (shiftK k hf l)
    (Swap.Modular.ratMod (modulus b) r)) (fun l => by
      have e := lv_val hf l.isLt
      simp only [shiftT, shiftK]
      congr 2 <;> ext <;> simp [e])]
  exact h

/-- The reversed atom shift's array realizes the refined reversed atom shift. -/
theorem revShift_transport (hk : k < t) (hf : 0 < f) (a : FlatCoordinateStages.Array (n * f) b W) :
    Transports a (revArray t k hk hf r a)
      (OrderedAffine.run (AtomOps.refined (f := f)
        (AtomOps.AtomOp.revShift t k (Swap.Modular.ratMod (modulus b) r)))) := by
  have h := levels_transport r (shiftT t hf) (revK k hf) (rev_lt t k hk hf) a f
  rw [AtomOps.refined, levels_eq _ (fun l => .shift (shiftT t hf l) (revK k hf l)
    (Swap.Modular.ratMod (modulus b) r)) (fun l => by
      have e := lv_val hf l.isLt
      simp only [shiftT, revK]
      congr 2 <;> ext <;> simp [e])]
  exact h

end Atoms

end
end IntegerMultBounds.MathlibTM2.M8.AtomShiftLoop
