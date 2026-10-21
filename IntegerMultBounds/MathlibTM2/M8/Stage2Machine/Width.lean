module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Straight
public import IntegerMultBounds.MathlibTM2.M8.Stage2Width
public import IntegerMultBounds.Machine.FixedBasePowerUntilRange
public import IntegerMultBounds.Machine.FixedBasePowerDescriptor
public import IntegerMultBounds.Machine.BinaryDescriptorIncrement

/-!
# The atom width at runtime

On `22` optional descriptors (`Headers.bank`) holding a width `e` at slot `3`, a fixed program
(`program`) builds the core's atom width `atomWidth K e = 2^⌈size e / K⌉` at slot `12` and the
constant `529` at slot `4` (`runs`): `size e = clog 2 (e + 1)` by a copy, an increment and a
power search, then `(size e - 1) / K + 1` by a difference, a division and an increment, then the
power of two; the scratch is erased. Besides the straight-line steps (`Straight`) it uses an
increment, a power search, a fixed-base power and a constant writer on the bank (`inc_step`,
`until_step`, `pow2_step`, `const_step`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width

noncomputable section
set_option linter.unusedSimpArgs false
open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.CounterDimensions (descriptorHead descriptorTape)
open FlatCoordinateSchedule (bits)
open RevMachine
open Headers (bank placed_bank)
open Straight (State words val)

variable {q : ℕ}

theorem encoded_descriptor (bs : List Bool) : RadixZeroFill.encodedBinary (q := q) bs =
    BinaryDescriptorStack.descriptor bs := (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := q) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun z => (RadixToBinary.binaryEncoding (q := q)).encode (CountedCopyReuse.binary bs z)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

/-! ### The steps -/

/-- Increment slot `j`. -/
def incAt (j : Fin 22) := Placement.placed (BinaryDescriptorIncrement.program (q := q))
  (InjectivePlacement.placement (u := 21) ![j] (by intro a b _; exact Subsingleton.elim a b) (by norm_num))

theorem inc_step {s : State} {j : Fin 22} {v : ℕ} (hs : s j = some v) :
    HoareTime (incAt (q := q) j) (fun w => w = bank (words s))
      (fun w => w = bank (words (Function.update s j (some (v + 1))))) (2 * ((bits v).length + 1)) := by
  have h := BinaryDescriptorIncrement.increment_linear (q := q) (bits v)
  have hv : GrowingCounterData.increment (bits v) = bits (v + 1) := by
    rw [Routines.canon (BinaryDescriptorIncrement.canonical _ (FlatCoordinateSchedule.bits_canonical v)),
      BinaryDescriptorIncrement.value, FlatCoordinateSchedule.bits_value]
  rw [hv] at h
  refine placed_bank _ _ _ ?_ ?_ ?_ h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [words, hs, descriptorHead, descriptorTape, BinaryDescriptorIncrement.bank, encoded_descriptor]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [words, descriptorHead, descriptorTape, BinaryDescriptorIncrement.bank, encoded_descriptor]
  · intro k hk
    have : k ≠ j := fun h => hk 0 (by simp [h])
    simp [words, Function.update_of_ne this]

/-- Write the constant `n` into a blank slot `j`. -/
def constAt (n : ℕ) (j : Fin 22) := Placement.placed (RecursiveChildQuotientsConstant.program (a := q) n)
  (InjectivePlacement.placement (u := 21) ![j] (by intro a b _; exact Subsingleton.elim a b) (by norm_num))

theorem const_step {s : State} {j : Fin 22} (n : ℕ) (hs : s j = none) :
    HoareTime (constAt (q := q) n j) (fun w => w = bank (words s))
      (fun w => w = bank (words (Function.update s j (some n)))) (RecursiveChildQuotientsConstant.cost n) := by
  have h := RecursiveChildQuotientsConstant.initialize_hoare (a := q) n
  have hv : RecursiveChildQuotientsConstant.bits n = bits n :=
    Routines.canon (RecursiveChildQuotientsConstant.bits_canonical n) |>.trans
      (by rw [RecursiveChildQuotientsConstant.bits_value])
  refine placed_bank _ _ _ ?_ ?_ ?_ h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [words, hs, descriptorHead, descriptorTape, FiniteReturnStack.bank]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [words, descriptorHead, descriptorTape, FiniteReturnStack.bank, encoded_descriptor, hv]
  · intro k hk
    have : k ≠ j := fun h => hk 0 (by simp [h])
    simp [words, Function.update_of_ne this]

/-- The power search's slots: scratch `13..17`, power `5`, threshold `4`, exponent `6`, scratch `18`. -/
def untilSlots : Fin 9 → Fin 22 := ![13, 14, 15, 16, 17, 5, 4, 6, 18]

theorem untilSlots_inj : Function.Injective untilSlots := by decide

/-- The least power of `B` at least slot `4`: the power at slot `5`, its exponent at slot `6`. -/
def untilAt (B : ℕ) := Placement.placed (FixedBasePowerUntil.program (q := q) B)
  (InjectivePlacement.placement (u := 13) untilSlots untilSlots_inj (by norm_num))

theorem until_step {s : State} (B : ℕ) (hB : 2 ≤ B) {D : ℕ} (hD : s 4 = some D)
    (h5 : s 5 = none) (h6 : s 6 = none) (h13 : s 13 = none) (h14 : s 14 = none) (h15 : s 15 = none)
    (h16 : s 16 = none) (h17 : s 17 = none) (h18 : s 18 = none) :
    HoareTime (untilAt (q := q) B) (fun w => w = bank (words s))
      (fun w => w = bank (words (Function.update (Function.update s 5 (some (B ^ Nat.clog B D)))
        6 (some (Nat.clog B D)))))
      (FixedBasePowerUntil.constant B * B ^ Nat.clog B D) := by
  have h := FixedBasePowerUntil.constructs_linear (q := q) B D hB (bits D) (FlatCoordinateSchedule.bits_value D)
    (FlatCoordinateSchedule.bits_canonical D)
  have hp : FixedBasePowerStep.bits B (FixedBasePowerUntilBound.rho B D) = bits (B ^ Nat.clog B D) :=
    Routines.canon (FixedBasePowerStep.bits_canonical _ _) |>.trans (by rw [FixedBasePowerStep.bits_value]; rfl)
  have hk : FixedBasePowerUntil.counter (FixedBasePowerUntilBound.rho B D) = bits (Nat.clog B D) :=
    Routines.canon (FixedBasePowerUntil.counter_canonical _) |>.trans (by rw [FixedBasePowerUntil.counter_value]; rfl)
  refine placed_bank _ _ _ ?_ ?_ ?_ h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [untilSlots, words, hD, h5, h6, h13, h14, h15, h16, h17, h18, descriptorHead, descriptorTape,
        FixedBasePowerUntil.input, SharedPlacementAlphabet.setTape, SharedBank.empty, encoded_descriptor]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [untilSlots, words, hD, h5, h6, h13, h14, h15, h16, h17, h18, descriptorHead, descriptorTape,
        FixedBasePowerUntil.output, FixedBasePowerUntil.input, SharedPlacementAlphabet.setTape, SharedBank.empty,
        encoded_descriptor, hp, hk, Function.update_apply]
  · intro k hk'
    have h5' : k ≠ 5 := fun h => hk' 5 (by simp [untilSlots, h])
    have h6' : k ≠ 6 := fun h => hk' 7 (by simp [untilSlots, h])
    simp [words, Function.update_of_ne h5', Function.update_of_ne h6']

/-- The fixed-base power's slots: scratch `13..17`, output `12`, clock `18`, exponent `10`. -/
def powSlots : Fin 8 → Fin 22 := ![13, 14, 15, 16, 17, 12, 18, 10]

theorem powSlots_inj : Function.Injective powSlots := by decide

theorem pow_input (ks : List Bool) : (FixedBasePowerDescriptor.input ks : Tapes 8 q) =
    ⟨![0, 0, 0, 0, 0, 0, 0, 1], ![fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank,
      fun _ => blank, fun _ => blank, fun _ => blank, CountedLoopReuseAlphabet.binary ks]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- `B^(slot 10)` at slot `12`. -/
def powAt (B : ℕ) := Placement.placed (FixedBasePowerDescriptor.program (q := q) B)
  (InjectivePlacement.placement (u := 14) powSlots powSlots_inj (by norm_num))

theorem pow_step {s : State} (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : s 10 = some k) (h12 : s 12 = none)
    (h13 : s 13 = none) (h14 : s 14 = none) (h15 : s 15 = none) (h16 : s 16 = none) (h17 : s 17 = none)
    (h18 : s 18 = none) :
    HoareTime (powAt (q := q) B) (fun w => w = bank (words s))
      (fun w => w = bank (words (Function.update s 12 (some (B ^ k)))))
      (FixedBasePowerDescriptor.constant B * B ^ k) := by
  have h := FixedBasePowerDescriptor.constructs_linear (q := q) B k hB (bits k) (FlatCoordinateSchedule.bits_value k)
    (FlatCoordinateSchedule.bits_canonical k)
  have hp : FixedBasePowerStep.bits B k = bits (B ^ k) :=
    Routines.canon (FixedBasePowerStep.bits_canonical _ _) |>.trans (by rw [FixedBasePowerStep.bits_value])
  refine placed_bank _ _ _ ?_ ?_ ?_ h
  · rw [pow_input]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powSlots, words, hk, h12, h13, h14, h15, h16, h17, h18, descriptorHead, descriptorTape, encoded_binary]
  · rw [FixedBasePowerDescriptor.output, pow_input]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powSlots, words, hk, h12, h13, h14, h15, h16, h17, h18, descriptorHead, descriptorTape,
        SharedPlacementAlphabet.setTape, encoded_binary, hp, Function.update_apply]
  · intro j hj
    have : j ≠ 12 := fun h => hj 5 (by simp [powSlots, h])
    simp [words, Function.update_of_ne this]

/-! ### The atom width -/

/-- The atom width exponent's divisor `K`. -/
abbrev K : ℕ := 1000

theorem size_eq_clog (n : ℕ) : Nat.size n = Nat.clog 2 (n + 1) := by
  apply le_antisymm
  · exact Nat.size_le.mpr (by have := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 1); omega)
  · exact Nat.clog_le_of_le_pow (Nat.lt_size_self n)

theorem atomExp_eq {e : ℕ} (he : 1 ≤ e) :
    Stage2Width.atomExp K e = (Nat.clog 2 (e + 1) - 1) / K + 1 := by
  unfold Stage2Width.atomExp
  rw [size_eq_clog]
  have : 1 ≤ Nat.clog 2 (e + 1) := by
    rw [← size_eq_clog]; exact Nat.lt_size.mpr (by simpa using he)
  simp only [K]
  omega

/-- The width at slot `3`. -/
def init (e : ℕ) : State := Function.update (fun _ => none) 3 (some e)

/-- The width at slot `3`, the constant `529` at slot `4` and the atom width at slot `12`. -/
def final (e : ℕ) : State :=
  Function.update (Function.update (init e) 4 (some 529)) 12 (some (Stage2Width.atomWidth K e))

variable (hq : 2 ≤ q)

theorem copy_ne : (3 : Fin 22) ≠ 4 := by decide
theorem diff_inj : Function.Injective (Arith.diffSlots 6 7 9) := by decide
theorem div_inj : Function.Injective (Arith.divSlots 9 8 10 11) := by decide

/-- **The atom width program.** -/
def program :=
  seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq
    (Straight.prog1 hq (.copy 3 4 copy_ne)).2 (incAt (q := q) 4)) (untilAt (q := q) 2))
    (Straight.prog1 hq (.erase 4)).2) (Straight.prog1 hq (.erase 5)).2) (constAt (q := q) 1 7))
    (constAt (q := q) K 8)) (Straight.prog1 hq (.diff 6 7 9 diff_inj)).2)
    (Straight.prog1 hq (.div 9 8 10 11 div_inj)).2) (incAt (q := q) 10)) (powAt (q := q) 2))
    (Straight.prog1 hq (.erase 6)).2) (Straight.prog1 hq (.erase 7)).2) (Straight.prog1 hq (.erase 8)).2)
    (Straight.prog1 hq (.erase 9)).2) (Straight.prog1 hq (.erase 10)).2) (Straight.prog1 hq (.erase 11)).2)
    (constAt (q := q) 529 4)

/-- The constant of the atom width program. -/
def constant : ℕ := FixedBasePowerUntil.constant 2 + FixedBasePowerDescriptor.constant 2 +
  RecursiveChildQuotientsConstant.cost 1 + RecursiveChildQuotientsConstant.cost K +
  RecursiveChildQuotientsConstant.cost 529 + 10000 * 2000

/-- **The atom width at runtime.** -/
theorem runs {e : ℕ} (he : 2 ≤ e) :
    HoareTime (program hq) (fun w => w = bank (words (init e))) (fun w => w = bank (words (final e)))
      (100 * constant * (e + 1)) := by
  set sz := Nat.clog 2 (e + 1)
  have hsz : 1 ≤ sz := by
    have h' : 1 ≤ Nat.size e := Nat.lt_size.mpr (by simpa using (by omega : 1 ≤ e))
    rw [size_eq_clog] at h'; exact h'
  have hpow : 2 ^ sz < 2 * (e + 1) := FixedBasePowerUntilRange.final_power_lt 2 (e + 1) le_rfl (by omega)
  have hszle : sz < 2 * (e + 1) := (Nat.lt_two_pow_self).trans hpow
  set a := (sz - 1) / K + 1
  have ha : a = Stage2Width.atomExp K e := (atomExp_eq (by omega)).symm
  have hw : 2 ^ a ≤ e := by rw [ha]; exact Stage2Width.atomWidth_le_self (by norm_num) he
  -- the states
  let s0 := init e
  let s1 := Straight.exec1 q (.copy 3 4 copy_ne) s0
  let s2 := Function.update s1 4 (some (e + 1))
  let s3 := Function.update (Function.update s2 5 (some (2 ^ sz))) 6 (some sz)
  let s4 := Straight.exec1 q (.erase 4) s3
  let s5 := Straight.exec1 q (.erase 5) s4
  let s6 := Function.update s5 7 (some 1)
  let s7 := Function.update s6 8 (some K)
  let s8 := Straight.exec1 q (.diff 6 7 9 diff_inj) s7
  let s9 := Straight.exec1 q (.div 9 8 10 11 div_inj) s8
  let s10 := Function.update s9 10 (some a)
  let s11 := Function.update s10 12 (some (2 ^ a))
  let s12 := Straight.exec1 q (.erase 6) s11
  let s13 := Straight.exec1 q (.erase 7) s12
  let s14 := Straight.exec1 q (.erase 8) s13
  let s15 := Straight.exec1 q (.erase 9) s14
  let s16 := Straight.exec1 q (.erase 10) s15
  let s17 := Straight.exec1 q (.erase 11) s16
  let s18 := Function.update s17 4 (some 529)
  have e1 : s1 = Function.update s0 4 (some e) := by
    simp [s1, s0, Straight.exec1, init, Function.update_apply]
  have h1 := Straight.run1 hq (.copy 3 4 copy_ne) s0 (by simp [Straight.Pre, s0, init, Function.update_apply])
  have h2 := inc_step (q := q) (s := s1) (j := 4) (v := e) (by rw [e1]; simp)
  have h3 := until_step (q := q) (s := s2) 2 le_rfl (D := e + 1) (by simp [s2])
    (by simp [s2, e1, s0, init, Function.update_apply]) (by simp [s2, e1, s0, init, Function.update_apply])
    (by simp [s2, e1, s0, init, Function.update_apply]) (by simp [s2, e1, s0, init, Function.update_apply])
    (by simp [s2, e1, s0, init, Function.update_apply]) (by simp [s2, e1, s0, init, Function.update_apply])
    (by simp [s2, e1, s0, init, Function.update_apply]) (by simp [s2, e1, s0, init, Function.update_apply])
  have h4 := Straight.run1 hq (.erase 4) s3 (by simp [Straight.Pre, s3, s2, Function.update_apply])
  have h5 := Straight.run1 hq (.erase 5) s4 (by simp [Straight.Pre, s4, s3, Straight.exec1, Function.update_apply])
  have h6 := const_step (q := q) (s := s5) (j := 7) 1
    (by simp [s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
  have h7 := const_step (q := q) (s := s6) (j := 8) K
    (by simp [s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
  have h8 := Straight.run1 hq (.diff 6 7 9 diff_inj) s7
    (by simp [Straight.Pre, Straight.val, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1,
      Function.update_apply]; omega)
  have h9 := Straight.run1 hq (.div 9 8 10 11 div_inj) s8
    (by simp [Straight.Pre, Straight.val, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1,
      Function.update_apply])
  have e9 : s9 10 = some ((sz - 1) / K) := by
    simp [s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Straight.val, Function.update_apply]
  have h10 := inc_step (q := q) (s := s9) (j := 10) e9
  have h11 := pow_step (q := q) (s := s10) 2 le_rfl (k := a) (by simp [s10])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply])
  have h12 := Straight.run1 hq (.erase 6) s11 (by simp [Straight.Pre, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2,
    Straight.exec1, Function.update_apply])
  have h13 := Straight.run1 hq (.erase 7) s12 (by simp [Straight.Pre, s12, s11, s10, s9, s8, s7, s6,
    Straight.exec1, Function.update_apply])
  have h14 := Straight.run1 hq (.erase 8) s13 (by simp [Straight.Pre, s13, s12, s11, s10, s9, s8, s7,
    Straight.exec1, Function.update_apply])
  have h15 := Straight.run1 hq (.erase 9) s14 (by simp [Straight.Pre, s14, s13, s12, s11, s10, s9, s8,
    Straight.exec1, Function.update_apply])
  have h16 := Straight.run1 hq (.erase 10) s15 (by simp [Straight.Pre, s15, s14, s13, s12, s11, s10,
    Straight.exec1, Function.update_apply])
  have h17 := Straight.run1 hq (.erase 11) s16 (by simp [Straight.Pre, s16, s15, s14, s13, s12, s11, s10, s9,
    Straight.exec1, Function.update_apply])
  have h18 := const_step (q := q) (s := s17) (j := 4) 529
    (by simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, Straight.exec1, Function.update_apply])
  have hfin : s18 = final e := by
    funext i
    simp only [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, final, init,
      Straight.exec1, Function.update_apply, ha, Stage2Width.atomWidth]
    fin_cases i <;> simp
  have h := ((((((((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq
    h12).seq h13).seq h14).seq h15).seq h16).seq h17).seq h18
  refine h.consequence (fun _ h => h) (fun w hw => hw.trans (congrArg (fun s => bank (q := q) (words s)) hfin)) ?_
  -- the costs
  have hdiv' : (sz - 1) / K ≤ sz := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hmod : (sz - 1) % K < K := Nat.mod_lt _ (by norm_num)
  have hK : K = 1000 := rfl
  have c1 : Straight.cost1 q (.copy 3 4 copy_ne) s0 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c4 : Straight.cost1 q (.erase 4) s3 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c5 : Straight.cost1 q (.erase 5) s4 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c8 : Straight.cost1 q (.diff 6 7 9 diff_inj) s7 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c9 : Straight.cost1 q (.div 9 8 10 11 div_inj) s8 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c12 : Straight.cost1 q (.erase 6) s11 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c13 : Straight.cost1 q (.erase 7) s12 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c14 : Straight.cost1 q (.erase 8) s13 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c15 : Straight.cost1 q (.erase 9) s14 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c16 : Straight.cost1 q (.erase 10) s15 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have c17 : Straight.cost1 q (.erase 11) s16 ≤ 10000 * (3 * (e + 1) + K + 1) :=
    (Straight.cost1_le _ _).trans (by
      simp [Straight.weight, Straight.val, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, e1, s0, init, Straight.exec1, Function.update_apply] <;> omega)
  have l2 := Straight.length_le e
  have l10 := Straight.length_le ((sz - 1) / K)
  have hdiv : (sz - 1) / K ≤ sz := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hu : FixedBasePowerUntil.constant 2 * 2 ^ sz ≤ FixedBasePowerUntil.constant 2 * (2 * (e + 1)) :=
    Nat.mul_le_mul_left _ hpow.le
  have hp : FixedBasePowerDescriptor.constant 2 * 2 ^ a ≤ FixedBasePowerDescriptor.constant 2 * e :=
    Nat.mul_le_mul_left _ hw
  unfold constant
  nlinarith

/-! ### On a caller's width tape -/

/-- Erase the atom width and the constant. -/
def cleanup := seq (Straight.prog1 hq (.erase 12)).2 (Straight.prog1 hq (.erase 4)).2

theorem cleans (e : ℕ) :
    HoareTime (cleanup hq) (fun w => w = bank (words (final e))) (fun w => w = bank (words (init e)))
      (20000 * (e + 2) + 20000 * 530 + 1) := by
  have h1 := Straight.run1 hq (.erase 12) (final e) (by simp [Straight.Pre, final])
  have h2 := Straight.run1 hq (.erase 4) (Straight.exec1 q (.erase 12) (final e))
    (by simp [Straight.Pre, final, Straight.exec1, Function.update_apply])
  have hi : Straight.exec1 q (.erase 4) (Straight.exec1 q (.erase 12) (final e)) = init e := by
    funext i; simp only [Straight.exec1, final, init, Function.update_apply]; fin_cases i <;> simp
  have c1 : Straight.cost1 q (.erase 12) (final e) ≤ 10000 * (Stage2Width.atomWidth K e + 1) :=
    (Straight.cost1_le _ _).trans (by simp [Straight.weight, Straight.val, final])
  have c2 : Straight.cost1 q (.erase 4) (Straight.exec1 q (.erase 12) (final e)) ≤ 10000 * (529 + 1) :=
    (Straight.cost1_le _ _).trans (by simp [Straight.weight, Straight.val, final, Straight.exec1, Function.update_apply])
  have hw : Stage2Width.atomWidth K e ≤ e + 2 := by
    have := Stage2Width.atomWidth_pos K e
    rcases Nat.lt_or_ge e 2 with h | h
    · have hs : Nat.size e ≤ 1 := Nat.size_le.mpr (by omega)
      have : Stage2Width.atomExp K e ≤ 1 := by unfold Stage2Width.atomExp; simp only [K]; omega
      have : Stage2Width.atomWidth K e ≤ 2 := by
        unfold Stage2Width.atomWidth; exact (Nat.pow_le_pow_right (by norm_num) this).trans (by norm_num)
      omega
    · exact (Stage2Width.atomWidth_le_self (by norm_num) h).trans (by omega)
  refine (h1.seq h2).consequence (fun _ h => h) (fun w hw' => hw'.trans (by rw [hi])) ?_
  omega

/-- The atom width program's own bank: blank, the width shared. -/
def privateIn : Tapes 22 q := bank (words (fun _ => none))

/-- With the atom width and the constant. -/
def privateOut (e : ℕ) : Tapes 22 q :=
  bank (words (Function.update (Function.update (fun _ => none) 4 (some 529)) 12 (some (Stage2Width.atomWidth K e))))

/-- The atom width program on the caller's width tape. -/
def shared {l : ℕ} (focus : Fin l) := Placement.placed (program hq) (SharedPlacementAlphabet.sharedPlacement focus 3)

/-- Its cleanup on the caller's width tape. -/
def sharedCleanup {l : ℕ} (focus : Fin l) :=
  Placement.placed (cleanup hq) (SharedPlacementAlphabet.sharedPlacement focus 3)

theorem strip (s : State) :
    SharedPlacementAlphabet.setTape (bank (q := q) (words s)) 3 (fun _ => blank) 0 =
      bank (words (Function.update s 3 none)) := by
  rw [Straight.words_update, Option.map_none, Headers.bank_update]; rfl

theorem init_strip (e : ℕ) : SharedPlacementAlphabet.setTape (bank (q := q) (words (init e))) 3 (fun _ => blank) 0 =
    privateIn := by
  rw [strip (init e)]; unfold privateIn init; simp

theorem final_strip (e : ℕ) : SharedPlacementAlphabet.setTape (bank (q := q) (words (final e))) 3 (fun _ => blank) 0 =
    privateOut e := by
  rw [strip (final e)]
  unfold privateOut final init
  congr 2
  funext i; simp only [Function.update_apply]; fin_cases i <;> simp

theorem bank_three (e : ℕ) (s : State) (hs : s 3 = some e) :
    (bank (q := q) (words s)).tape 3 = RadixZeroFill.encodedBinary (bits e) ∧ (bank (q := q) (words s)).head 3 = 1 := by
  simp [bank, words, hs, descriptorHead, descriptorTape]

/-- **The atom width on the caller's width tape.** -/
theorem shared_runs {l : ℕ} (caller : Tapes l q) (focus : Fin l) {e : ℕ} (he : 2 ≤ e)
    (ht : caller.tape focus = RadixZeroFill.encodedBinary (bits e)) (hh : caller.head focus = 1) :
    HoareTime (shared hq focus) (fun w => w = caller.append privateIn)
      (fun w => w = caller.append (privateOut e)) (100 * constant * (e + 1)) := by
  have h3 := bank_three (q := q) e (init e) (by simp [init])
  have h3' := bank_three (q := q) e (final e) (by simp [final, init])
  have h := SharedPlacementAlphabet.shared_hoare (runs hq he) caller focus 3 (fun _ => blank) 0
    (ht.trans h3.1.symm) (hh.trans h3.2.symm)
  rw [init_strip, final_strip, h3'.1, h3'.2, ← ht, ← hh, SharedPlacementAlphabet.setTape_self] at h
  exact h

theorem shared_cleans {l : ℕ} (caller : Tapes l q) (focus : Fin l) {e : ℕ}
    (ht : caller.tape focus = RadixZeroFill.encodedBinary (bits e)) (hh : caller.head focus = 1) :
    HoareTime (sharedCleanup hq focus) (fun w => w = caller.append (privateOut e))
      (fun w => w = caller.append privateIn) (20000 * (e + 2) + 20000 * 530 + 1) := by
  have h3 := bank_three (q := q) e (init e) (by simp [init])
  have h3' := bank_three (q := q) e (final e) (by simp [final, init])
  have h := SharedPlacementAlphabet.shared_hoare (cleans hq e) caller focus 3 (fun _ => blank) 0
    (ht.trans h3'.1.symm) (hh.trans h3'.2.symm)
  rw [init_strip, final_strip, h3.1, h3.2, ← ht, ← hh, SharedPlacementAlphabet.setTape_self] at h
  exact h

/-- The atom width and the constant on the program's own bank. -/
theorem out_cells (e : ℕ) :
    (privateOut (q := q) e).head 12 = 1 ∧
      (privateOut (q := q) e).tape 12 = RadixZeroFill.encodedBinary (bits (Stage2Width.atomWidth K e)) ∧
    (privateOut (q := q) e).head 4 = 1 ∧ (privateOut (q := q) e).tape 4 = RadixZeroFill.encodedBinary (bits 529) := by
  simp [privateOut, bank, words, descriptorHead, descriptorTape, Function.update_apply]

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width
