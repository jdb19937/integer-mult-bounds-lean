module

public import IntegerMultBounds.Machine.FlatPaddedShiftFromCounters
public import IntegerMultBounds.Machine.FlatCoordinateScalingConstruct
public import IntegerMultBounds.Machine.FlatCoordinateScalingSharedBank

/-!
# The coordinate scaling from runtime counters

One fixed program, for each coefficient `r`, scales the target coordinate `x_t ← r x_t` of an
array of `d` coordinates of width `b`, whatever `d` and `t`: the bank carries `b`, the record
width `W` and the counters `t` and `d - 1 - t` (the control counters of `CounterDimensions` are
zero). `CounterDimensions` computes `Q`, `P` and `B`, three copies put them on a nine-tape
dimension bank, `FlatAffineScalingInstall` installs them on the scaler's workspace,
`FlatAffineScalingPayload` scales, and `CleanExecution` erases everything generated. The final
bank is the input bank with the scaled array (`realizes`), so the program can be the body of a
counted loop.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.FlatPaddedScaleFromCounters
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateSchedule (bits)
open SharedPlacementAlphabet (setTape)
open FlatPaddedShiftFromCounters (hprime setTape_left setTape_right)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance {b : ℕ} : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- A program on the right part of an appended bank, the left part framed. -/
theorem left_frame {n s q k : ℕ} {M : Program n s prime} {x y : Tapes n prime}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes q prime) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n prime) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append, finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z, hz, rfl⟩
  subst z
  simpa only [Placement.replace, Placement.extra_combine] using he y

variable (r : ℚ)

/-- The scaler's workspace. -/
abbrev Local := FlatAffineScalingInstall.LocalTapes r.num.natAbs r.den

abbrev TapeCount := 17 + (9 + Local r)

variable {d b W : ℕ}

/-- The counters of a scaling at target `t`: `b, W, t, d - 1 - t` and two zero controls. -/
def dimsInput (b W : ℕ) (t : Fin d) : Tapes 17 prime :=
  CounterDimensions.input (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits 0) (bits 0)

def dimsOutput (b W : ℕ) (t : Fin d) : Tapes 17 prime :=
  CounterDimensions.output hprime (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits 0) (bits 0)
    b W t.val (d-1-t.val) 0 0

/-- The array on its source tape. -/
def source (a : FlatCoordinateStages.Array d b W) : ℤ → Fin 4 := putWord (fun _ => blank) 0 (List.ofFn a)

/-- The scaler's workspace with the array and no descriptors. -/
def work (a : FlatCoordinateStages.Array d b W) : Tapes (Local r) prime :=
  FlatAffineScalingInstall.liftedBank prime r.num.natAbs r.den (source a) [] [] []

/-- The loop bank: the counters and the array, everything else blank. -/
def bank (b W : ℕ) (t : Fin d) (a : FlatCoordinateStages.Array d b W) : Tapes (TapeCount r) prime :=
  (dimsInput b W t).append ((SharedBank.empty 9 prime).append (work r a))

def qWord (b : ℕ) : List Bool := CounterDimensions.qBits hprime b
def pWord (b : ℕ) (t : Fin d) : List Bool := CounterDimensions.pBits hprime t.val b
def bWord (b W : ℕ) (t : Fin d) : List Bool := CounterDimensions.bBits (q := prime) (d-1-t.val) b W

/-- The nine-tape dimension bank of `FlatAffineScalingInstall`: `Q`, `P`, `B` at `4`, `5`, `7`. -/
def mid (b W : ℕ) (t : Fin d) : Tapes 9 prime :=
  setTape (setTape (setTape (SharedBank.empty 9 prime) 4 (RadixZeroFill.encodedBinary (qWord b)) 1)
    5 (RadixZeroFill.encodedBinary (pWord b t)) 1) 7 (RadixZeroFill.encodedBinary (bWord b W t)) 1

def midSlot (j : Fin 9) : Fin (TapeCount r) := Fin.natAdd 17 (Fin.castAdd (Local r) j)
def dimSlot (j : Fin 17) : Fin (TapeCount r) := Fin.castAdd (9 + Local r) j

theorem dim_ne_mid (i : Fin 17) (j : Fin 9) : dimSlot r i ≠ midSlot r j := by
  intro e; have := congrArg Fin.val e; simp [dimSlot, midSlot] at this; omega

def setup :=
  seq (seq (seq (seq
    (extend (CounterDimensions.program hprime) (9 + Local r))
    (BinaryDescriptorInstall.program prime (dimSlot r 9) (midSlot r 4) (dim_ne_mid r _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot r 10) (midSlot r 5) (dim_ne_mid r _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot r 12) (midSlot r 7) (dim_ne_mid r _ _)))
    (Placement.placed (FlatAffineScalingInstall.program prime r.num.natAbs r.den)
      (finAddFlip : Fin ((9 + Local r) + 17) ≃ Fin (17 + (9 + Local r))))

theorem install_mid (D : Tapes 17 prime) (M : Tapes 9 prime) (S : Tapes (Local r) prime)
    (src : Fin 17) (j : Fin 9) (xs : List Bool)
    (hs : D.tape src = RadixZeroFill.encodedBinary xs) (hsh : D.head src = 1)
    (hd : M.tape j = fun _ => blank) (hdh : M.head j = 0) :
    HoareTime (BinaryDescriptorInstall.program prime (dimSlot r src) (midSlot r j) (dim_ne_mid r src j))
      (fun v => v = D.append (M.append S))
      (fun v => v = D.append ((setTape M j (RadixZeroFill.encodedBinary xs) 1).append S))
      (2*xs.length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (dimSlot r src) (midSlot r j) (dim_ne_mid r src j)
    (D.append (M.append S)) xs
    (by simp [dimSlot, Tapes.append, hs]) (by simp [dimSlot, Tapes.append, hsh])
    (by simp [midSlot, Tapes.append, hd]) (by simp [midSlot, Tapes.append, hdh])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  rw [midSlot, setTape_right, setTape_left]

variable (b W) in
theorem dims_slot (t : Fin d) (j : Fin 17) :
    (dimsOutput b W t).head j = CounterDimensions.descriptorHead
      (CounterDimensions.outputs hprime (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits 0)
        (bits 0) b W t.val (d-1-t.val) 0 0 j) ∧
    (dimsOutput b W t).tape j = CounterDimensions.descriptorTape prime
      (CounterDimensions.outputs hprime (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits 0)
        (bits 0) b W t.val (d-1-t.val) 0 0 j) := ⟨rfl, rfl⟩

/-- The workspace with the array and the three descriptors installed. -/
def ready (b W : ℕ) (t : Fin d) (a : FlatCoordinateStages.Array d b W) : Tapes (Local r) prime :=
  FlatAffineScalingInstall.liftedBank prime r.num.natAbs r.den (source a) (bWord b W t) (qWord b)
    (pWord b t)

def prepared (b W : ℕ) (t : Fin d) (a : FlatCoordinateStages.Array d b W) : Tapes (TapeCount r) prime :=
  (dimsOutput b W t).append ((mid b W t).append (ready r b W t a))

def setupCost (b W : ℕ) (t : Fin d) : ℕ :=
  720*(prime^(t.val*b)*prime^b*(prime^((d-1-t.val)*b)*W)) +
    (2*(qWord b).length+5) + (2*(pWord b t).length+5) + (2*(bWord b W t).length+5) +
    BinaryDescriptorInstallList.cost (FlatAffineScalingInstall.instructions r.num.natAbs r.den)
      (FlatAffineScalingInstall.allWords r.num.natAbs r.den (bWord b W t) (qWord b) (pWord b t)) + 4

theorem mid_ready (t : Fin d) (k : FlatAffineScalingInputLayout.Kind) :
    (mid b W t).head (FlatAffineScalingInstall.sourceSlot k) = 1 ∧
    (mid b W t).tape (FlatAffineScalingInstall.sourceSlot k) =
      RadixZeroFill.encodedBinary (FlatAffineScalingInstall.sourceWords (bWord b W t) (qWord b) (pWord b t)
        (FlatAffineScalingInstall.sourceSlot k)) := by
  cases k <;> simp [mid, setTape, FlatAffineScalingInstall.sourceSlot,
    FlatAffineScalingInstall.sourceWords]

theorem setup_hoare (t : Fin d) (hb0 : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (setup r) (fun v => v = bank r b W t a) (fun v => v = prepared r b W t a)
      (setupCost r b W t) := by
  unfold setupCost
  have h1 := FamilyPlacementAlphabet.extend_hoare
    (CounterDimensions.construct_hoare_volume hprime (FlatCoordinateSchedule.bits_value b)
      (FlatCoordinateSchedule.bits_value W) (FlatCoordinateSchedule.bits_value t.val)
      (FlatCoordinateSchedule.bits_value (d-1-t.val)) (FlatCoordinateSchedule.bits_value 0)
      (FlatCoordinateSchedule.bits_value 0) (FlatCoordinateSchedule.bits_canonical _)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
      (FlatCoordinateSchedule.bits_canonical _) hb0 hW (Nat.zero_le _) (Nat.zero_le _))
    ((SharedBank.empty 9 prime).append (work r a))
  set D := dimsOutput b W t
  have hD (j : Fin 17) := dims_slot b W t j
  set M0 := SharedBank.empty 9 prime
  set M1 := setTape M0 4 (RadixZeroFill.encodedBinary (qWord b)) 1
  set M2 := setTape M1 5 (RadixZeroFill.encodedBinary (pWord b t)) 1
  have i1 := install_mid r D M0 (work r a) 9 4 (qWord b) (hD 9).2 (hD 9).1 rfl rfl
  have i2 := install_mid r D M1 (work r a) 10 5 (pWord b t) (hD 10).2 (hD 10).1
    (by simp only [M1, setTape]; rw [Function.update_of_ne (by decide)]; rfl)
    (by simp only [M1, setTape]; rw [Function.update_of_ne (by decide)]; rfl)
  have i3 := install_mid r D M2 (work r a) 12 7 (bWord b W t) (hD 12).2 (hD 12).1
    (by simp only [M2, M1, setTape]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; rfl)
    (by simp only [M2, M1, setTape]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; rfl)
  have i4 := left_frame (FlatAffineScalingInstall.installs_hoare prime r.num.natAbs r.den
    (mid b W t) (source a) (bWord b W t) (qWord b) (pWord b t) (mid_ready t)) D
  have h := (((h1.seq i1).seq i2).seq i3).seq i4
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-! ### The stage -/

variable {r} (hr : Shared50AffineCoefficients.ScaleOccurs r)

theorem ready_eq (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    ready r b W t a = FlatAffineScalingPayload.input (radix := prime) hr (fiberView a t)
      (bWord b W t) (qWord b) (pWord b t) := by
  rw [FlatAffineScalingInputLayout.payload_input, ready, FlatAffineScalingInstall.liftedBank, source,
    fiberView_word]

/-- The bank after the stage. -/
def final (t : Fin d) (a : FlatCoordinateStages.Array d b W) : Tapes (TapeCount r) prime :=
  (dimsOutput b W t).append ((mid b W t).append
    (FlatAffineScalingPayload.output (radix := prime) hr (fiberView a t) (bWord b W t) (qWord b) (pWord b t)))

def stage := Placement.placed
  (Placement.placed (FlatAffineScalingPayload.program (radix := prime) hr)
    (finAddFlip : Fin (Local r + 9) ≃ Fin (9 + Local r)))
  (finAddFlip : Fin ((9 + Local r) + 17) ≃ Fin (17 + (9 + Local r)))

def stageCost (b W : ℕ) : ℕ :=
  (2064+120*(r.num.natAbs+r.den))*((modulus b)^d*W)+254

theorem stage_hoare (t : Fin d) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (stage hr) (fun v => v = prepared r b W t a) (fun v => v = final hr t a)
      (stageCost (r := r) (d := d) b W) := by
  have hs := FlatAffineScalingPayload.realizes_hoare (radix := prime) hr (fiberView a t)
    (Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW)
    (pow_pos (ActualAffineScaling.modulus_pos b) _) (bWord b W t) (qWord b) (pWord b t)
    (by
      simp only [bWord, CounterDimensions.bBits, DimensionProductDescriptor.bits_value, suffixSize,
        suffixFields, ActualAffineScaling.modulus]
      rw [← pow_mul, Nat.mul_comm b])
    (RadixPowerDescriptor.bits_value hprime b)
    (by
      simp only [pWord, CounterDimensions.pBits, RadixPowerDescriptor.bits_value, prefixSize,
        ActualAffineScaling.modulus]
      rw [← pow_mul, Nat.mul_comm b])
    (DimensionProductDescriptor.bits_canonical _ _) (RadixPowerDescriptor.bits_canonical hprime b)
    (RadixPowerDescriptor.bits_canonical hprime _)
  rw [← split_volume t] at hs
  have h := left_frame (left_frame hs (mid b W t)) (dimsOutput b W t)
  rw [prepared, ready_eq hr]
  exact h

/-! ### The clean loop body -/

variable (r) in
/-- The six counters start with their heads on the first cell. -/
def right (i : Fin (TapeCount r)) : Bool := decide (3 ≤ i.val ∧ i.val ≤ 8)

variable (r) in
/-- The six counters and the payload pair survive. -/
def keep (i : Fin (TapeCount r)) : Bool :=
  decide ((3 ≤ i.val ∧ i.val ≤ 8) ∨ i.val = 26 + (FlatAffineScaling.sourceSlot r).val ∨
    i.val = 26 + (ActualAffineScalingStream.destinationSlot r).val)

def inner := seq (setup r) (stage hr)

def program := CleanExecution.program (inner hr) (right r) (keep r)

theorem work_head (a : FlatCoordinateStages.Array d b W) (i : Fin (Local r)) : (work r a).head i = 0 := rfl

/-- Off the source tape the workspace is blank. -/
theorem work_blank (a : FlatCoordinateStages.Array d b W) (i : Fin (Local r))
    (hi : i ≠ FlatAffineScaling.sourceSlot r) : (work r a).tape i = fun _ => blank := by
  have hk : FlatAffineScalingInputLayout.kinds r.num.natAbs r.den i ≠ .payload :=
    fun h => hi ((FlatCoordinateScalingSharedBank.kinds_payload r i).mp h)
  unfold work FlatAffineScalingInstall.liftedBank Alphabet.mapTapes FlatAffineScalingInputLayout.bank
  dsimp only
  funext z
  cases hk' : FlatAffineScalingInputLayout.kinds r.num.natAbs r.den i
  all_goals first
    | exact (hk hk').elim
    | (by_cases hz : z = 0 <;>
        simp [FlatAffineScalingInputLayout.word, BinaryDescriptorInstallRaw.rawWord,
          RadixZeroFill.encodedBinary, RadixToBinary.binaryEncoding, CountedCopyReuse.binary,
          CountedCopyReuse.empty, putBits, hz, blank])

include hr in
/-- The payload pair of the workspace. -/
theorem work_payload (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedPayload.payload (work r a) (FlatAffineScaling.sourceSlot r)
      (ActualAffineScalingStream.destinationSlot r) = FlatAffineScalingPayload.pair a := by
  have hw : work r a = FlatAffineScalingPayload.input (radix := prime) hr (fiberView a t) [] [] [] := by
    rw [FlatAffineScalingInputLayout.payload_input, work, FlatAffineScalingInstall.liftedBank, source,
      fiberView_word]
  rw [hw, FlatAffineScalingPayload.input_payload]
  unfold FlatAffineScalingPayload.pair
  rw [fiberView_word]

theorem final_payload (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedPayload.payload
      (FlatAffineScalingPayload.output (radix := prime) hr (fiberView a t) (bWord b W t) (qWord b) (pWord b t))
      (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) =
      FlatAffineScalingPayload.pair (FlatCoordinateScaling.array hr a t) := by
  rw [FlatAffineScalingPayload.output_payload]
  unfold FlatAffineScalingPayload.pair
  rw [FlatCoordinateScaling.array_word]

theorem bank_head (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    (bank r b W t a).head = TrackedInit.position (right r) := by
  funext i
  refine Fin.addCases (fun x => ?_) (fun y => ?_) i
  · simp only [bank, Tapes.append, Fin.addCases_left, TrackedInit.position, right, Fin.val_castAdd]
    fin_cases x <;> rfl
  · have hr : right r (Fin.natAdd 17 y) = false := by simp [right]; omega
    simp only [TrackedInit.position, hr]
    simp only [bank, Tapes.append, Fin.addCases_right]
    refine Fin.addCases (fun z => ?_) (fun w => ?_) y
    · simp [SharedBank.empty]
    · simp [work_head]

theorem source_val : (FlatAffineScaling.sourceSlot r).val < Local r := (FlatAffineScaling.sourceSlot r).isLt

theorem bank_blank (t : Fin d) (a : FlatCoordinateStages.Array d b W) (i : Fin (TapeCount r))
    (hi : keep r i = false) : (bank r b W t a).tape i = fun _ => blank := by
  revert hi
  refine Fin.addCases (fun x => ?_) (fun y => ?_) i
  · simp only [bank, Tapes.append, Fin.addCases_left, keep, Fin.val_castAdd]
    fin_cases x <;> simp [dimsInput, CounterDimensions.input, CounterDimensions.bank,
      CounterDimensions.inputs, CounterDimensions.descriptorTape]
  · intro hk
    simp only [bank, Tapes.append, Fin.addCases_right]
    revert hk
    refine Fin.addCases (fun z => ?_) (fun w => ?_) y
    · intro _; simp [SharedBank.empty]
    · intro hk
      simp only [Fin.addCases_right]
      apply work_blank
      intro he
      subst he
      simp [keep] at hk
      omega

theorem final_retained (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    TrackedCleanupList.retained (keep r) (final hr t a) =
      bank r b W t (FlatCoordinateScaling.array hr a t) := by
  have hp := final_payload hr t a
  have hq := work_payload hr t (FlatCoordinateScaling.array hr a t)
  have hps : (FlatAffineScalingPayload.output (radix := prime) hr (fiberView a t) (bWord b W t) (qWord b)
      (pWord b t)).head (FlatAffineScaling.sourceSlot r) =
      (work r (FlatCoordinateScaling.array hr a t)).head (FlatAffineScaling.sourceSlot r) ∧
    (FlatAffineScalingPayload.output (radix := prime) hr (fiberView a t) (bWord b W t) (qWord b)
      (pWord b t)).tape (FlatAffineScaling.sourceSlot r) =
      (work r (FlatCoordinateScaling.array hr a t)).tape (FlatAffineScaling.sourceSlot r) ∧
    (FlatAffineScalingPayload.output (radix := prime) hr (fiberView a t) (bWord b W t) (qWord b)
      (pWord b t)).head (ActualAffineScalingStream.destinationSlot r) =
      (work r (FlatCoordinateScaling.array hr a t)).head (ActualAffineScalingStream.destinationSlot r) ∧
    (FlatAffineScalingPayload.output (radix := prime) hr (fiberView a t) (bWord b W t) (qWord b)
      (pWord b t)).tape (ActualAffineScalingStream.destinationSlot r) =
      (work r (FlatCoordinateScaling.array hr a t)).tape (ActualAffineScalingStream.destinationSlot r) := by
    rw [← hq] at hp
    have h0 := congrArg (fun v : Tapes 2 prime => v.head 0) hp
    have h1 := congrArg (fun v : Tapes 2 prime => v.tape 0) hp
    have h2 := congrArg (fun v : Tapes 2 prime => v.head 1) hp
    have h3 := congrArg (fun v : Tapes 2 prime => v.tape 1) hp
    simp only [SharedPayload.payload] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  have hsd := FlatAffineScalingPayload.slots_distinct r
  apply congrArg₂ Tapes.mk <;> funext i <;> refine Fin.addCases (fun x => ?_) (fun y => ?_) i
  · simp only [final, Tapes.append, Fin.addCases_left, keep, Fin.val_castAdd]
    fin_cases x <;> simp [dimsOutput, dimsInput, CounterDimensions.output, CounterDimensions.input,
      CounterDimensions.bank, CounterDimensions.outputs, CounterDimensions.inputs,
      CounterDimensions.descriptorHead] <;> omega
  · simp only [final, Tapes.append, Fin.addCases_right]
    refine Fin.addCases (fun z => ?_) (fun w => ?_) y
    · have hk : keep r (Fin.natAdd 17 (Fin.castAdd (Local r) z)) = false := by
        simp [keep]; omega
      simp [hk, SharedBank.empty]
    · simp only [Fin.addCases_right]
      by_cases hs : w = FlatAffineScaling.sourceSlot r
      · subst hs
        have hk : keep r (Fin.natAdd 17 (Fin.natAdd 9 (FlatAffineScaling.sourceSlot r))) = true := by
          simp [keep]; omega
        simp only [hk, ↓reduceIte]; exact hps.1
      by_cases hd : w = ActualAffineScalingStream.destinationSlot r
      · subst hd
        have hk : keep r (Fin.natAdd 17 (Fin.natAdd 9 (ActualAffineScalingStream.destinationSlot r))) = true := by
          simp [keep]; omega
        simp only [hk, ↓reduceIte]; exact hps.2.2.1
      have hk : keep r (Fin.natAdd 17 (Fin.natAdd 9 w)) = false := by
        simp only [keep, Fin.val_natAdd, decide_eq_false_iff_not]
        intro h
        rcases h with h | h | h
        · omega
        · exact hs (Fin.ext (by omega))
        · exact hd (Fin.ext (by omega))
      simp only [hk, Bool.false_eq_true, ↓reduceIte]
      rfl
  · simp only [final, Tapes.append, Fin.addCases_left, keep, Fin.val_castAdd]
    fin_cases x <;> simp [dimsOutput, dimsInput, CounterDimensions.output, CounterDimensions.input,
      CounterDimensions.bank, CounterDimensions.outputs, CounterDimensions.inputs,
      CounterDimensions.descriptorTape] <;> omega
  · simp only [final, Tapes.append, Fin.addCases_right]
    refine Fin.addCases (fun z => ?_) (fun w => ?_) y
    · have hk : keep r (Fin.natAdd 17 (Fin.castAdd (Local r) z)) = false := by
        simp [keep]; omega
      simp [hk, SharedBank.empty]
    · simp only [Fin.addCases_right]
      by_cases hs : w = FlatAffineScaling.sourceSlot r
      · subst hs
        have hk : keep r (Fin.natAdd 17 (Fin.natAdd 9 (FlatAffineScaling.sourceSlot r))) = true := by
          simp [keep]; omega
        simp only [hk, ↓reduceIte]; exact hps.2.1
      by_cases hd : w = ActualAffineScalingStream.destinationSlot r
      · subst hd
        have hk : keep r (Fin.natAdd 17 (Fin.natAdd 9 (ActualAffineScalingStream.destinationSlot r))) = true := by
          simp [keep]; omega
        simp only [hk, ↓reduceIte]; exact hps.2.2.2
      have hk : keep r (Fin.natAdd 17 (Fin.natAdd 9 w)) = false := by
        simp only [keep, Fin.val_natAdd, decide_eq_false_iff_not]
        intro h
        rcases h with h | h | h
        · omega
        · exact hs (Fin.ext (by omega))
        · exact hd (Fin.ext (by omega))
      simp only [hk, Bool.false_eq_true, ↓reduceIte]
      exact (work_blank (FlatCoordinateScaling.array hr a t) w hs).symm

/-- The exact cost of the loop body. -/
def cost (b W : ℕ) (t : Fin d) : ℕ :=
  (2+5*TapeCount r)*(setupCost r b W t + 1 + stageCost (r := r) (d := d) b W) + 11*TapeCount r + 4

theorem realizes_exact (t : Fin d) (hb0 : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program hr)
      (fun v => v = (bank r b W t a).append (SharedBank.empty (TapeCount r) prime))
      (fun v => v = (bank r b W t (FlatCoordinateScaling.array hr a t)).append
        (SharedBank.empty (TapeCount r) prime))
      (cost (r := r) b W t) := by
  have h : HoareTime (inner hr) (fun v => v = bank r b W t a) (fun v => v = final hr t a)
      (setupCost r b W t + 1 + stageCost (r := r) (d := d) b W) :=
    (setup_hoare r t hb0 hW a).seq (stage_hoare hr t hW a)
  have hc := CleanExecution.realizes (inner hr) (right r) (keep r) (bank r b W t a) (final hr t a)
    (setupCost r b W t + 1 + stageCost (r := r) (d := d) b W) (bank_head t a) (bank_blank t a) h
  rw [final_retained] at hc
  exact hc

private theorem length_le (xs : List Bool) (h : GrowingCounterData.Canonical xs) :
    xs.length ≤ Counter.value xs + 1 := by
  have hw := GrowingCounterData.canonical_width xs h
  have hl := Nat.log2_le_self (Counter.value xs)
  omega

variable (r) in
/-- The constant of the loop body; it depends only on the coefficient. -/
def constant : ℕ :=
  (2+5*TapeCount r)*(800 + 22*Local r + (2064+120*(r.num.natAbs+r.den)) + 300) + 11*TapeCount r + 4

theorem cost_le (t : Fin d) (hW : 0 < W) : cost (r := r) b W t ≤ constant r*((modulus b)^d*W) := by
  have ht : t.val < d := t.isLt
  set V := (modulus b)^d*W with hV
  have hD : prime^(d*b) ≤ V := by
    rw [hV, ActualAffineScaling.modulus, ← pow_mul, Nat.mul_comm b]
    exact Nat.le_mul_of_pos_right _ hW
  have hp : 1 ≤ prime := by have := hprime; omega
  have hpow {x : ℕ} (hx : x ≤ d) : prime^(x*b) ≤ V :=
    (Nat.pow_le_pow_right hp (Nat.mul_le_mul_right b hx)).trans hD
  have hV1 : 1 ≤ V := (Nat.one_le_pow _ _ (by omega)).trans hD
  have hvol : prime^(t.val*b)*prime^b*(prime^((d-1-t.val)*b)*W) = V := by
    rw [hV, ActualAffineScaling.modulus, ← pow_mul, ← Nat.mul_assoc, ← pow_add, ← pow_add]
    congr 2
    have e : t.val + 1 + (d-1-t.val) = d := by omega
    calc t.val*b + b + (d-1-t.val)*b = (t.val + 1 + (d-1-t.val))*b := by ring
      _ = b*d := by rw [e, Nat.mul_comm]
  have l3 : (bWord b W t).length ≤ V + 1 := by
    have h := length_le _ (DimensionProductDescriptor.bits_canonical (prime^((d-1-t.val)*b)) W)
    rw [DimensionProductDescriptor.bits_value] at h
    have : prime^((d-1-t.val)*b)*W ≤ V := by
      rw [← hvol]
      exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by positivity) (by positivity))
    exact h.trans (by omega)
  have l4 : (qWord b).length ≤ V + 1 := by
    have h := length_le _ (RadixPowerDescriptor.bits_canonical hprime b)
    rw [RadixPowerDescriptor.bits_value] at h
    have := hpow (x := 1) (by omega); rw [Nat.one_mul] at this
    exact h.trans (by omega)
  have l5 : (pWord b t).length ≤ V + 1 := by
    have h := length_le _ (RadixPowerDescriptor.bits_canonical hprime (t.val*b))
    rw [RadixPowerDescriptor.bits_value] at h
    have := hpow (x := t.val) (by omega)
    exact h.trans (by omega)
  have hc := FlatAffineScalingInstall.cost_volume r.num.natAbs r.den (2*V) (bWord b W t) (qWord b)
    (pWord b t) (by omega) (by omega) (by omega) (by omega)
  unfold cost setupCost stageCost constant
  rw [hvol]
  rw [← hV]
  nlinarith

/-- **The scaling from counters.** One fixed program for each coefficient, for every coordinate
count and target: the loop bank with the array `a` goes to the loop bank with the scaled array
in time linear in the array volume. -/
theorem realizes (t : Fin d) (hb0 : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program hr)
      (fun v => v = (bank r b W t a).append (SharedBank.empty (TapeCount r) prime))
      (fun v => v = (bank r b W t (FlatCoordinateScaling.array hr a t)).append
        (SharedBank.empty (TapeCount r) prime))
      (constant r*((modulus b)^d*W)) :=
  (realizes_exact hr t hb0 hW a).consequence (fun _ h => h) (fun _ h => h) (cost_le t hW)

/-- The scaled array has the ordered-affine scaling semantics. -/
theorem array_entry (t : Fin d) (a : FlatCoordinateStages.Array d b W)
    (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    FlatCoordinateScaling.array hr a t
      (index (OrderedAffine.execute (.scale t (Swap.Modular.ratMod (modulus b) r)) x) j) =
      a (index x j) :=
  FlatCoordinateScaling.array_entry hr a t x j

end
end IntegerMultBounds.Machine.FlatPaddedScaleFromCounters
