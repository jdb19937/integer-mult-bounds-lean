module

public import IntegerMultBounds.MathlibTM2.M8.AtomShiftLoop
public import IntegerMultBounds.MathlibTM2.M8.AtomScaleLoop
public import IntegerMultBounds.Machine.CounterAdvance

/-!
# The common bank of atom operations

The level loops of the atom shifts and the atom scalings run on banks of different sizes: a
counter region of `17` tapes, one array tape, the two control tapes of the loop, and blank
workspace (`opBank`). A segment runs them all on one bank of `22 + P` tapes (`outer`): the counter
region at `0..16`, the array at `17`, the loop controls at `18, 19`, the atom count `f` at `20`,
a blank advance clock at `21`, and blank workspace from `22`. Each loop is placed by an
injection (`slot`) that fixes the counter region and sends the array and the controls to their
common tapes and the workspace to distinct blank tapes. Its active bank is then the loop's bank
(`active_outer`), and its result is put back as the common bank with the new counters and array
(`replace_outer`). The loop banks of the atom shift (`shift_opBank`) and the atom scaling
(`scale_opBank`) have this form.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.AtomBank
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open CounterDimensions (descriptorHead descriptorTape)
noncomputable section

/-- The array on its tape. -/
def arrTape {K : ℕ} (a : Fin K → Fin 4) : ℤ → Fin (prime + 4) :=
  fun z => RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn a) z)

/-- The common bank: counters `d`, array tape `A`, the loop controls for `f - 1`, the count
`f`, and blank tapes. -/
def outer (P : ℕ) (d : Fin 17 → Option (List Bool)) (A : ℤ → Fin (prime + 4)) (f : ℕ) :
    Tapes (22 + P) prime :=
  ⟨fun j => if h : j.val < 17 then descriptorHead (d ⟨j.val, h⟩) else
      if j.val = 17 then 0 else if 18 ≤ j.val ∧ j.val ≤ 20 then 1 else 0,
    fun j => if h : j.val < 17 then descriptorTape prime (d ⟨j.val, h⟩) else
      if j.val = 17 then A else if j.val = 18 then CountedLoopReuseAlphabet.empty else
      if j.val = 19 then CountedLoopReuseAlphabet.binary (bits (f - 1)) else
      if j.val = 20 then CountedLoopReuseAlphabet.binary (bits f) else fun _ => blank⟩

/-- A loop bank: counters `d`, the array tape at `ai`, the controls as the last two tapes, and
blank tapes. -/
def opBank (L ai : ℕ) (d : Fin 17 → Option (List Bool)) (A : ℤ → Fin (prime + 4)) (f : ℕ) :
    Tapes L prime :=
  ⟨fun i => if h : i.val < 17 then descriptorHead (d ⟨i.val, h⟩) else
      if i.val = ai then 0 else if i.val + 2 = L ∨ i.val + 1 = L then 1 else 0,
    fun i => if h : i.val < 17 then descriptorTape prime (d ⟨i.val, h⟩) else
      if i.val = ai then A else if i.val + 2 = L then CountedLoopReuseAlphabet.empty else
      if i.val + 1 = L then CountedLoopReuseAlphabet.binary (bits (f - 1)) else fun _ => blank⟩

/-- The tape of the common bank that holds tape `i` of a loop bank. -/
def slotVal (L ai i : ℕ) : ℕ :=
  if i < 17 then i else if i = ai then 17 else if i + 2 = L then 18 else if i + 1 = L then 19 else 22 + i

theorem slotVal_lt {L ai P i : ℕ} (hL : L ≤ P) (hi : i < L) : slotVal L ai i < 22 + P := by
  unfold slotVal; split_ifs <;> omega

def slot (L ai P : ℕ) (hL : L ≤ P) : Fin L → Fin (22 + P) :=
  fun i => ⟨slotVal L ai i.val, slotVal_lt hL i.isLt⟩

theorem slot_injective {L ai P : ℕ} (hL : L ≤ P) (_ha : 17 ≤ ai) (_ha' : ai + 2 < L) :
    Function.Injective (slot L ai P hL) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [slot, slotVal] at h'
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  split_ifs at h' <;> omega

theorem size {L P : ℕ} (hL : L ≤ P) : L + (22 + P - L) = 22 + P := by omega

/-- The placement of a loop bank into the common bank. -/
def place (L ai P : ℕ) (hL : L ≤ P) (ha : 17 ≤ ai) (ha' : ai + 2 < L) :
    Fin (L + (22 + P - L)) ≃ Fin (22 + P) :=
  InjectivePlacement.placement (slot L ai P hL) (slot_injective hL ha ha') (size hL)

theorem outer_slot {L ai P : ℕ} (hL : L ≤ P) (_ha : 17 ≤ ai) (_ha' : ai + 2 < L)
    (d : Fin 17 → Option (List Bool)) (A : ℤ → Fin (prime + 4)) (f : ℕ) (i : Fin L) :
    (outer P d A f).head (slot L ai P hL i) = (opBank L ai d A f).head i ∧
    (outer P d A f).tape (slot L ai P hL i) = (opBank L ai d A f).tape i := by
  have hi := i.isLt
  by_cases h1 : i.val < 17
  · have hs : (slot L ai P hL i).val = i.val := by simp [slot, slotVal, h1]
    have hs' : (slot L ai P hL i).val < 17 := hs ▸ h1
    simp only [outer, opBank, dite_eq_left hs', dite_eq_left h1]
    have he : (⟨(slot L ai P hL i).val, hs'⟩ : Fin 17) = ⟨i.val, h1⟩ := Fin.ext hs
    rw [he]
    exact ⟨rfl, rfl⟩
  · by_cases h2 : i.val = ai
    · have ha17 : ¬ ai < 17 := by omega
      have hs : (slot L ai P hL i).val = 17 := by simp [slot, slotVal, h2, ha17]
      simp [outer, opBank, hs, h2, ha17]
    · by_cases h3 : i.val + 2 = L
      · have hs : (slot L ai P hL i).val = 18 := by simp [slot, slotVal, h1, h2, h3]
        simp [outer, opBank, hs, h1, h2, h3]
      · by_cases h4 : i.val + 1 = L
        · have hs : (slot L ai P hL i).val = 19 := by simp [slot, slotVal, h1, h2, h3, h4]
          simp [outer, opBank, hs, h1, h2, h3, h4]
        · have hs : (slot L ai P hL i).val = 22 + i.val := by simp [slot, slotVal, h1, h2, h3, h4]
          have h5 : ¬ (22 + i.val < 17) := by omega
          have h6 : ¬ (22 + i.val = 17) := by omega
          have h7 : ¬ (18 ≤ 22 + i.val ∧ 22 + i.val ≤ 20) := by omega
          have h8 : ¬ (22 + i.val = 18) := by omega
          have h9 : ¬ (22 + i.val = 19) := by omega
          have h10 : ¬ (22 + i.val = 20) := by omega
          simp [outer, opBank, hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- **The active bank** of a placed loop is the loop's bank. -/
theorem active_outer {L ai P : ℕ} (hL : L ≤ P) (ha : 17 ≤ ai) (ha' : ai + 2 < L)
    (d : Fin 17 → Option (List Bool)) (A : ℤ → Fin (prime + 4)) (f : ℕ) :
    Placement.active (place L ai P hL ha ha') (outer P d A f) = opBank L ai d A f := by
  rw [place, InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (outer_slot hL ha ha' d A f i).1
  · exact (outer_slot hL ha ha' d A f i).2

/-- **The result of a placed loop** is the common bank with its counters and array. -/
theorem replace_outer {L ai P : ℕ} (hL : L ≤ P) (ha : 17 ≤ ai) (ha' : ai + 2 < L)
    (d d' : Fin 17 → Option (List Bool)) (A A' : ℤ → Fin (prime + 4)) (f : ℕ) :
    Placement.replace (place L ai P hL ha ha') (outer P d A f) (opBank L ai d' A' f) =
      outer P d' A' f := by
  apply CounterAdvance.replace_eq _ _ _ _ _ _ (fun i => outer_slot hL ha ha' d' A' f i)
  intro j hj
  have hj20 : 20 ≤ j.val := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    by_cases h1 : j.val < 17
    · exact hj ⟨j.val, by omega⟩ (Fin.ext (by simp [slot, slotVal, h1]))
    · by_cases h2 : j.val = 17
      · exact hj ⟨ai, by omega⟩ (Fin.ext (by simp [slot, slotVal, h2]; omega))
      · by_cases h3 : j.val = 18
        · exact hj ⟨L - 2, by omega⟩ (Fin.ext (by
            simp only [slot, slotVal]; split_ifs <;> omega))
        · exact hj ⟨L - 1, by omega⟩ (Fin.ext (by
            simp only [slot, slotVal]; split_ifs <;> omega))
  have h1 : ¬ j.val < 17 := by omega
  have h2 : ¬ j.val = 17 := by omega
  have h3 : ¬ j.val = 18 := by omega
  have h4 : ¬ j.val = 19 := by omega
  simp [outer, h1, h2, h3, h4]

/-! ### The loop banks -/

theorem append_head {s u a : ℕ} (x : Tapes s a) (y : Tapes u a) (i : Fin (s + u)) :
    (x.append y).head i = if h : i.val < s then x.head ⟨i.val, h⟩ else y.head ⟨i.val - s, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [Tapes.append, j.isLt]
  · simp [Tapes.append]

theorem append_tape {s u a : ℕ} (x : Tapes s a) (y : Tapes u a) (i : Fin (s + u)) :
    (x.append y).tape i = if h : i.val < s then x.tape ⟨i.val, h⟩ else y.tape ⟨i.val - s, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [Tapes.append, j.isLt]
  · simp [Tapes.append]

theorem payload_head {D b W : ℕ} (a : FlatCoordinateStages.Array D b W) (k : Fin 17) :
    (FlatPaddedShiftFromCounters.payload a).head k = 0 := by
  fin_cases k <;> rfl

theorem payload_tape {D b W : ℕ} (a : FlatCoordinateStages.Array D b W) (k : Fin 17) :
    (FlatPaddedShiftFromCounters.payload a).tape k = if k.val = 10 then arrTape a else fun _ => blank := by
  fin_cases k <;> rfl

theorem tape2_eq : AtomShiftLoop.Tape2 = 88 := rfl

/-- The loop bank of an atom shift. -/
theorem shift_opBank {D b W : ℕ} (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (f : ℕ) :
    LevelLoop.bank (AtomShiftLoop.shiftBank w a) f =
      opBank (AtomShiftLoop.Tape2 + 2) 37 (CounterBank.entries w) (arrTape a) f := by
  have h88 : AtomShiftLoop.Tape2 = 88 := rfl
  have h44 : FlatPaddedShiftFromCounters.TapeCount = 44 := rfl
  have h10 : FlatPaddedShiftFromCounters.prefixTapes = 10 := rfl
  unfold LevelLoop.bank CountedLoopReuseAlphabet.bank
  apply congrArg₂ Tapes.mk <;> funext i
  · simp only [AtomShiftLoop.shiftBank, CounterBank.counters, Tapes.append, CounterAdvance.addCases_val, payload_head,
      CounterDimensions.bank, PrefixWidthCopies.blankBank, SharedBank.empty,
      CountedLoopReuseAlphabet.controls]
    have hi := i.isLt
    split_ifs <;> first | rfl | omega
  · simp only [AtomShiftLoop.shiftBank, CounterBank.counters, Tapes.append, CounterAdvance.addCases_val, payload_tape,
      CounterDimensions.bank, PrefixWidthCopies.blankBank, SharedBank.empty,
      CountedLoopReuseAlphabet.controls, Fin.ext_iff, Fin.val_zero]
    have hi := i.isLt
    split_ifs <;> first | rfl | omega

theorem work_tape (r : ℚ) {D b W : ℕ} (a : FlatCoordinateStages.Array D b W)
    (k : Fin (FlatPaddedScaleFromCounters.Local r)) :
    (FlatPaddedScaleFromCounters.work r a).tape k =
      if k.val = (FlatAffineScaling.sourceSlot r).val then arrTape a else fun _ => blank := by
  split_ifs with hk
  · rw [show k = FlatAffineScaling.sourceSlot r from Fin.ext hk]
    have hp := (FlatCoordinateScalingSharedBank.kinds_payload r (FlatAffineScaling.sourceSlot r)).mpr rfl
    unfold FlatPaddedScaleFromCounters.work FlatAffineScalingInstall.liftedBank Alphabet.mapTapes
      FlatAffineScalingInputLayout.bank
    dsimp only
    rw [hp]
    rfl
  · exact FlatPaddedScaleFromCounters.work_blank (r := r) a k (fun h => hk (congrArg Fin.val h))

/-- The array tape of the scaling bank. -/
def scaleIndex (r : ℚ) : ℕ := 26 + (FlatAffineScaling.sourceSlot r).val

theorem scaleIndex_ge (r : ℚ) : 17 ≤ scaleIndex r := by unfold scaleIndex; omega

theorem scaleIndex_lt (r : ℚ) : scaleIndex r + 2 < AtomScaleLoop.Tape2 r + 2 := by
  have := (FlatAffineScaling.sourceSlot r).isLt
  change _ < FlatAffineScalingInstall.LocalTapes r.num.natAbs r.den at this
  simp only [scaleIndex, AtomScaleLoop.Tape2, FlatPaddedScaleFromCounters.TapeCount,
    FlatPaddedScaleFromCounters.Local]
  omega

/-- The loop bank of an atom scaling. -/
theorem scale_opBank (r : ℚ) {D b W : ℕ} (w : Fin 6 → ℕ) (a : FlatCoordinateStages.Array D b W) (f : ℕ) :
    LevelLoop.bank (AtomScaleLoop.scaleBank r w a) f =
      opBank (AtomScaleLoop.Tape2 r + 2) (scaleIndex r) (CounterBank.entries w) (arrTape a) f := by
  have hs := (FlatAffineScaling.sourceSlot r).isLt
  change _ < FlatAffineScalingInstall.LocalTapes r.num.natAbs r.den at hs
  have hT : AtomScaleLoop.Tape2 r = 2 * (26 + FlatPaddedScaleFromCounters.Local r) := by
    simp only [AtomScaleLoop.Tape2, FlatPaddedScaleFromCounters.TapeCount]; ring
  have hL : FlatPaddedScaleFromCounters.Local r = FlatAffineScalingInstall.LocalTapes r.num.natAbs r.den := rfl
  have hL2 : ActualAffineScalingStream.TapeCount r = FlatPaddedScaleFromCounters.Local r := rfl
  have hTC : FlatPaddedScaleFromCounters.TapeCount r = 17 + (9 + FlatPaddedScaleFromCounters.Local r) := rfl
  unfold LevelLoop.bank CountedLoopReuseAlphabet.bank
  apply congrArg₂ Tapes.mk <;> funext i <;> refine Fin.addCases (fun x => ?_) (fun c => ?_) i
  · refine Fin.addCases (fun y => ?_) (fun e => ?_) x
    · refine Fin.addCases (fun u => ?_) (fun z => ?_) y
      · simp only [AtomScaleLoop.scaleBank, CounterBank.counters, CounterDimensions.bank,
          Tapes.append, Fin.addCases_left, Fin.val_castAdd, u.isLt, dite_true]
      · refine Fin.addCases (fun p => ?_) (fun k => ?_) z
        · have hp := p.isLt
          simp only [AtomScaleLoop.scaleBank, Tapes.append, Fin.addCases_left,
            Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, SharedBank.empty, scaleIndex]
          split_ifs <;> first | rfl | omega
        · have hk := k.isLt
          simp only [AtomScaleLoop.scaleBank, Tapes.append, Fin.addCases_left,
            Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
            FlatPaddedScaleFromCounters.work_head, scaleIndex]
          split_ifs <;> first | rfl | omega
    · have he := e.isLt
      simp only [AtomScaleLoop.scaleBank, Tapes.append, Fin.addCases_left,
        Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, SharedBank.empty, scaleIndex]
      split_ifs <;> first | rfl | omega
  · fin_cases c <;>
      simp only [CountedLoopReuseAlphabet.controls, scaleIndex, Fin.addCases_right,
        Fin.val_natAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> split_ifs <;> first | rfl | omega
  · refine Fin.addCases (fun y => ?_) (fun e => ?_) x
    · refine Fin.addCases (fun u => ?_) (fun z => ?_) y
      · simp only [AtomScaleLoop.scaleBank, CounterBank.counters, CounterDimensions.bank,
          Tapes.append, Fin.addCases_left, Fin.val_castAdd, u.isLt, dite_true]
      · refine Fin.addCases (fun p => ?_) (fun k => ?_) z
        · have hp := p.isLt
          simp only [AtomScaleLoop.scaleBank, Tapes.append, Fin.addCases_left,
            Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, SharedBank.empty, scaleIndex]
          split_ifs <;> first | rfl | omega
        · have hk := k.isLt
          simp only [AtomScaleLoop.scaleBank, Tapes.append, Fin.addCases_left,
            Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, work_tape,
            scaleIndex]
          split_ifs <;> first | rfl | omega
    · have he := e.isLt
      simp only [AtomScaleLoop.scaleBank, Tapes.append, Fin.addCases_left,
        Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, SharedBank.empty, scaleIndex]
      split_ifs <;> first | rfl | omega
  · fin_cases c <;>
      simp only [CountedLoopReuseAlphabet.controls, scaleIndex, Fin.addCases_right,
        Fin.val_natAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> split_ifs <;> first | rfl | omega

end
end IntegerMultBounds.MathlibTM2.M8.AtomBank
