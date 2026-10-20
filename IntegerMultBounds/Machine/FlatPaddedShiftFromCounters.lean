module

public import IntegerMultBounds.Machine.CounterDimensions
public import IntegerMultBounds.Machine.FlatPaddedShift
public import IntegerMultBounds.Machine.FlatCoordinateShiftFromDimensions
public import IntegerMultBounds.Machine.CleanExecution

/-!
# The padded shift from runtime counters

One fixed program runs the shift `x_t ← x_t + r x_k` on an array of `d` coordinates of width `b`,
whatever `d`, `t` and `k`: the bank carries the width `b`, the record width `W` and four counters
`t`, `d - 1 - t`, `k` and `t - 1 - k` as canonical descriptors. `CounterDimensions` computes the
stage dimensions from them, six descriptor copies install the padded prefix widths and the
`B`, `Q`, `P` words, `FlatPaddedShift` runs the shift, and `CleanExecution` erases everything
generated. The final bank is the input bank with the shifted array (`realizes`), so the program
can be the body of a counted loop.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.FlatPaddedShiftFromCounters
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateSchedule (bits)
open SharedPlacementAlphabet (setTape)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance {b : ℕ} : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

theorem hprime : 2 ≤ prime := Shared50ModularControl.prime_prime.two_le

/-! ### Updates of appended banks -/

theorem addCases_update_left {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) (j : Fin m)
    (v : α) : Fin.addCases (motive := fun _ => α) (Function.update f j v) g =
      Function.update (Fin.addCases (motive := fun _ => α) f g) (Fin.castAdd n j) v := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · by_cases h : i = j
    · subst h; simp
    · rw [Fin.addCases_left, Function.update_of_ne h,
        Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.addCases_left]
  · have hne : Fin.natAdd m i ≠ Fin.castAdd n j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    rw [Fin.addCases_right, Function.update_of_ne hne, Fin.addCases_right]

theorem addCases_update_right {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) (j : Fin n)
    (v : α) : Fin.addCases (motive := fun _ => α) f (Function.update g j v) =
      Function.update (Fin.addCases (motive := fun _ => α) f g) (Fin.natAdd m j) v := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have hne : Fin.castAdd n i ≠ Fin.natAdd m j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    rw [Fin.addCases_left, Function.update_of_ne hne, Fin.addCases_left]
  · by_cases h : i = j
    · subst h; simp
    · rw [Fin.addCases_right, Function.update_of_ne h,
        Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.addCases_right]

variable {s u : ℕ}

theorem setTape_left (x : Tapes s prime) (y : Tapes u prime) (j : Fin s) (f : ℤ → Fin (prime+4))
    (p : ℤ) : setTape (x.append y) (Fin.castAdd u j) f p = (setTape x j f p).append y := by
  simp only [setTape, Tapes.append, addCases_update_left]

theorem setTape_right (x : Tapes s prime) (y : Tapes u prime) (j : Fin u) (f : ℤ → Fin (prime+4))
    (p : ℤ) : setTape (x.append y) (Fin.natAdd s j) f p = x.append (setTape y j f p) := by
  simp only [setTape, Tapes.append, addCases_update_right]

/-! ### The banks -/

/-- The prefix initializer of the three padded fields. -/
abbrev prefixTapes := PrefixCounterInit.tapeCount (2+1)

abbrev TapeCount := (17+prefixTapes)+17

theorem prefixTapes_eq : prefixTapes = 10 := rfl

variable {d b W : ℕ}

/-- The six counter descriptors of a shift at target `t` and control `k`. -/
def dimsInput (b W : ℕ) (t k : Fin d) : Tapes 17 prime :=
  CounterDimensions.input (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits k.val)
    (bits (t.val-1-k.val))

def dimsOutput (b W : ℕ) (t k : Fin d) : Tapes 17 prime :=
  CounterDimensions.output hprime (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits k.val)
    (bits (t.val-1-k.val)) b W t.val (d-1-t.val) k.val (t.val-1-k.val)

/-- The payload suffix with the array and no dimension words. -/
def payload (a : FlatCoordinateStages.Array d b W) : Tapes 17 prime :=
  FlatControlledShiftLayout.suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0 none none none

/-- The loop bank: the six counters and the array, everything else blank. -/
def bank (b W : ℕ) (t k : Fin d) (a : FlatCoordinateStages.Array d b W) : Tapes TapeCount prime :=
  ((dimsInput b W t k).append (PrefixWidthCopies.blankBank prime prefixTapes)).append (payload a)

/-- The three padded widths. -/
def widths (b : ℕ) (t k : Fin d) : Fin (2+1) → List Bool :=
  ![bits b, CounterDimensions.mbBits (t.val-1-k.val) b, CounterDimensions.kbBits k.val b]

def qWord (b : ℕ) : List Bool := CounterDimensions.qBits hprime b
def pWord (b : ℕ) (t : Fin d) : List Bool := CounterDimensions.pBits hprime t.val b
def bWord (b W : ℕ) (t : Fin d) : List Bool := CounterDimensions.bBits (q := prime) (d-1-t.val) b W

/-- The bank ready for the stage. -/
def prepared (b W : ℕ) (t k : Fin d) (a : FlatCoordinateStages.Array d b W) : Tapes TapeCount prime :=
  ((dimsOutput b W t k).append (PrefixCounterInit.input (q := prime) (2+1) (widths b t k))).append
    (FlatControlledShiftLayout.suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0
      (some (bWord b W t)) (some (qWord b)) (some (pWord b t)))

/-! ### Setup -/

def dimSlot (j : Fin 17) : Fin TapeCount := Fin.castAdd 17 (Fin.castAdd prefixTapes j)
def preSlot (j : Fin prefixTapes) : Fin TapeCount := Fin.castAdd 17 (Fin.natAdd 17 j)
def sufSlot (j : Fin 17) : Fin TapeCount := Fin.natAdd (17+prefixTapes) j

theorem dim_ne_pre (i : Fin 17) (j : Fin prefixTapes) : dimSlot i ≠ preSlot j := by
  intro e; have := congrArg Fin.val e; simp [dimSlot, preSlot] at this; omega

theorem dim_ne_suf (i j : Fin 17) : dimSlot i ≠ sufSlot j := by
  intro e; have := congrArg Fin.val e; simp [dimSlot, sufSlot] at this; omega

theorem install_pre (D : Tapes 17 prime) (P : Tapes prefixTapes prime) (S : Tapes 17 prime)
    (src : Fin 17) (j : Fin prefixTapes) (xs : List Bool)
    (hs : D.tape src = RadixZeroFill.encodedBinary xs) (hsh : D.head src = 1)
    (hd : P.tape j = fun _ => blank) (hdh : P.head j = 0) :
    HoareTime (BinaryDescriptorInstall.program prime (dimSlot src) (preSlot j) (dim_ne_pre src j))
      (fun v => v = (D.append P).append S)
      (fun v => v = (D.append (setTape P j (RadixZeroFill.encodedBinary xs) 1)).append S)
      (2*xs.length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (dimSlot src) (preSlot j) (dim_ne_pre src j)
    ((D.append P).append S) xs
    (by simp [dimSlot, Tapes.append, hs]) (by simp [dimSlot, Tapes.append, hsh])
    (by simp [preSlot, Tapes.append, hd]) (by simp [preSlot, Tapes.append, hdh])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  rw [preSlot, setTape_left, setTape_right]

theorem install_suf (D : Tapes 17 prime) (P : Tapes prefixTapes prime) (S : Tapes 17 prime)
    (src j : Fin 17) (xs : List Bool)
    (hs : D.tape src = RadixZeroFill.encodedBinary xs) (hsh : D.head src = 1)
    (hd : S.tape j = fun _ => blank) (hdh : S.head j = 0) :
    HoareTime (BinaryDescriptorInstall.program prime (dimSlot src) (sufSlot j) (dim_ne_suf src j))
      (fun v => v = (D.append P).append S)
      (fun v => v = (D.append P).append (setTape S j (RadixZeroFill.encodedBinary xs) 1))
      (2*xs.length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (dimSlot src) (sufSlot j) (dim_ne_suf src j)
    ((D.append P).append S) xs
    (by simp [dimSlot, Tapes.append, hs]) (by simp [dimSlot, Tapes.append, hsh])
    (by simp [sufSlot, Tapes.append, hd]) (by simp [sufSlot, Tapes.append, hdh])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  rw [sufSlot, setTape_right]

/-- The field width slots of the prefix initializer. -/
abbrev fieldSlot (j : Fin (2+1)) : Fin prefixTapes := PrefixWidthCopies.descriptorSlot (2+1) j

def setup :=
  seq (seq (seq (seq (seq (seq
    (extend (extend (CounterDimensions.program hprime) prefixTapes) 17)
    (BinaryDescriptorInstall.program prime (dimSlot 3) (preSlot (fieldSlot 0)) (dim_ne_pre _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot 13) (preSlot (fieldSlot 1)) (dim_ne_pre _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot 14) (preSlot (fieldSlot 2)) (dim_ne_pre _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot 12) (sufSlot 5) (dim_ne_suf _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot 9) (sufSlot 7) (dim_ne_suf _ _)))
    (BinaryDescriptorInstall.program prime (dimSlot 10) (sufSlot 16) (dim_ne_suf _ _))

theorem prefix_eq (w : Fin (2+1) → List Bool) :
    setTape (setTape (setTape (PrefixWidthCopies.blankBank prime prefixTapes)
      (fieldSlot 0) (RadixZeroFill.encodedBinary (w 0)) 1)
      (fieldSlot 1) (RadixZeroFill.encodedBinary (w 1)) 1)
      (fieldSlot 2) (RadixZeroFill.encodedBinary (w 2)) 1 =
    PrefixCounterInit.input (q := prime) (2+1) w := by
  have hd := PrefixWidthCopies.input_descriptor (q := prime) (2+1) w
  have hf := PrefixWidthCopies.input_frame (q := prime) (2+1) w
  have hinj : ∀ a c : Fin (2+1), fieldSlot a = fieldSlot c ↔ a = c :=
    fun a c => (PrefixWidthCopies.descriptorSlot_injective (2+1)).eq_iff
  have s01 : fieldSlot 0 ≠ fieldSlot 1 := by rw [Ne, hinj]; decide
  have s02 : fieldSlot 0 ≠ fieldSlot 2 := by rw [Ne, hinj]; decide
  have s12 : fieldSlot 1 ≠ fieldSlot 2 := by rw [Ne, hinj]; decide
  generalize PrefixCounterInit.input (q := prime) (2+1) w = R at hd hf ⊢
  obtain ⟨Rh, Rt⟩ := R
  simp only at hd hf
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [setTape]
  all_goals
    by_cases h0 : i = fieldSlot 0
    · subst h0
      rw [Function.update_of_ne s02, Function.update_of_ne s01, Function.update_self]
      first | exact (hd 0).1.symm | exact (hd 0).2.symm
    by_cases h1 : i = fieldSlot 1
    · subst h1
      rw [Function.update_of_ne s12, Function.update_self]
      first | exact (hd 1).1.symm | exact (hd 1).2.symm
    by_cases h2 : i = fieldSlot 2
    · subst h2
      rw [Function.update_self]
      first | exact (hd 2).1.symm | exact (hd 2).2.symm
    have h : ∀ j, i ≠ PrefixWidthCopies.descriptorSlot (2+1) j := fun j =>
      match j with
      | 0 => h0
      | 1 => h1
      | 2 => h2
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]
    first | exact (hf i h).1.symm | exact (hf i h).2.symm

theorem suffix_eq (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    setTape (setTape (setTape (FlatControlledShiftLayout.suffix prime source (fun _ => blank) 0 0 none none none)
      5 (RadixZeroFill.encodedBinary bs) 1) 7 (RadixZeroFill.encodedBinary qs) 1)
      16 (RadixZeroFill.encodedBinary ns) 1 =
    FlatControlledShiftLayout.suffix prime source (fun _ => blank) 0 0 (some bs) (some qs) (some ns) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [setTape, FlatControlledShiftLayout.suffix, FlatControlledShiftLayout.descriptorHead,
      FlatControlledShiftLayout.descriptorTape]

variable (b W) in
theorem dims_slot (t k : Fin d) (j : Fin 17) :
    (dimsOutput b W t k).head j = CounterDimensions.descriptorHead
      (CounterDimensions.outputs hprime (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits k.val)
        (bits (t.val-1-k.val)) b W t.val (d-1-t.val) k.val (t.val-1-k.val) j) ∧
    (dimsOutput b W t k).tape j = CounterDimensions.descriptorTape prime
      (CounterDimensions.outputs hprime (bits b) (bits W) (bits t.val) (bits (d-1-t.val)) (bits k.val)
        (bits (t.val-1-k.val)) b W t.val (d-1-t.val) k.val (t.val-1-k.val) j) := ⟨rfl, rfl⟩

/-- The setup cost: the dimensions and six descriptor copies. -/
def setupCost (b W : ℕ) (t k : Fin d) : ℕ :=
  720*(prime^(t.val*b)*prime^b*(prime^((d-1-t.val)*b)*W)) +
    (2*(widths b t k 0).length+5) + (2*(widths b t k 1).length+5) + (2*(widths b t k 2).length+5) +
    (2*(bWord b W t).length+5) + (2*(qWord b).length+5) + (2*(pWord b t).length+5) + 6

theorem setup_hoare (t k : Fin d) (hk : k < t) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) :
    HoareTime setup (fun v => v = bank b W t k a) (fun v => v = prepared b W t k a)
      (setupCost b W t k) := by
  unfold setupCost
  have hkt : k.val ≤ t.val := hk.le
  have h1 := FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.extend_hoare
    (CounterDimensions.construct_hoare_volume hprime (FlatCoordinateSchedule.bits_value b)
      (FlatCoordinateSchedule.bits_value W) (FlatCoordinateSchedule.bits_value t.val)
      (FlatCoordinateSchedule.bits_value (d-1-t.val)) (FlatCoordinateSchedule.bits_value k.val)
      (FlatCoordinateSchedule.bits_value (t.val-1-k.val)) (FlatCoordinateSchedule.bits_canonical _)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
      (FlatCoordinateSchedule.bits_canonical _) hb0 hW hkt (by omega))
    (PrefixWidthCopies.blankBank prime prefixTapes)) (payload a)
  set D := dimsOutput b W t k
  have hD (j : Fin 17) := dims_slot b W t k j
  set w := widths b t k
  set P0 := PrefixWidthCopies.blankBank prime prefixTapes
  set P1 := setTape P0 (fieldSlot 0) (RadixZeroFill.encodedBinary (w 0)) 1
  set P2 := setTape P1 (fieldSlot 1) (RadixZeroFill.encodedBinary (w 1)) 1
  set P3 := setTape P2 (fieldSlot 2) (RadixZeroFill.encodedBinary (w 2)) 1
  have hinj : ∀ a c : Fin (2+1), fieldSlot a = fieldSlot c ↔ a = c :=
    fun a c => (PrefixWidthCopies.descriptorSlot_injective (2+1)).eq_iff
  have s01 : fieldSlot 1 ≠ fieldSlot 0 := by rw [Ne, hinj]; decide
  have s02 : fieldSlot 2 ≠ fieldSlot 0 := by rw [Ne, hinj]; decide
  have s12 : fieldSlot 2 ≠ fieldSlot 1 := by rw [Ne, hinj]; decide
  have i1 := install_pre D P0 (payload a) 3 (fieldSlot 0) (w 0) (hD 3).2 (hD 3).1 rfl rfl
  have i2 := install_pre D P1 (payload a) 13 (fieldSlot 1) (w 1) (hD 13).2 (hD 13).1
    (by simp only [P1, setTape]; rw [Function.update_of_ne s01]; rfl)
    (by simp only [P1, setTape]; rw [Function.update_of_ne s01]; rfl)
  have i3 := install_pre D P2 (payload a) 14 (fieldSlot 2) (w 2) (hD 14).2 (hD 14).1
    (by simp only [P2, P1, setTape]; rw [Function.update_of_ne s12, Function.update_of_ne s02]; rfl)
    (by simp only [P2, P1, setTape]; rw [Function.update_of_ne s12, Function.update_of_ne s02]; rfl)
  set S0 := payload a
  set S1 := setTape S0 5 (RadixZeroFill.encodedBinary (bWord b W t)) 1
  set S2 := setTape S1 7 (RadixZeroFill.encodedBinary (qWord b)) 1
  have i4 := install_suf D P3 S0 12 5 (bWord b W t) (hD 12).2 (hD 12).1 rfl rfl
  have i5 := install_suf D P3 S1 9 7 (qWord b) (hD 9).2 (hD 9).1
    (by simp only [S1, setTape]; rw [Function.update_of_ne (by decide)]; rfl)
    (by simp only [S1, setTape]; rw [Function.update_of_ne (by decide)]; rfl)
  have i6 := install_suf D P3 S2 10 16 (pWord b t) (hD 10).2 (hD 10).1
    (by simp only [S2, S1, setTape]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; rfl)
    (by simp only [S2, S1, setTape]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; rfl)
  have h := ((((((h1.seq i1).seq i2).seq i3).seq i4).seq i5).seq i6)
  have hP : P3 = PrefixCounterInit.input (q := prime) (2+1) w := prefix_eq w
  have hS : setTape S2 16 (RadixZeroFill.encodedBinary (pWord b t)) 1 =
      FlatControlledShiftLayout.suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0
        (some (bWord b W t)) (some (qWord b)) (some (pWord b t)) := suffix_eq _ _ _ _
  rw [hP, hS] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-! ### The stage -/

/-- The stage runs on the prefix initializer and the payload suffix; the dimension bank is its
frame. -/
def stagePlacement (n : ℕ) : Fin ((n+17)+17) ≃ Fin ((17+n)+17) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd 17 (Fin.natAdd 17 i)) (Fin.natAdd (17+n)))
    (fun i => Fin.castAdd 17 (Fin.castAdd n i))
  invFun := Fin.addCases
    (Fin.addCases (Fin.natAdd (n+17)) (fun i => Fin.castAdd 17 (Fin.castAdd 17 i)))
    (fun i => Fin.castAdd 17 (Fin.natAdd n i))
  left_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp

theorem stage_active {n : ℕ} (dim : Tapes 17 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.active (stagePlacement n) ((dim.append pre).append suf) = pre.append suf := by
  unfold Placement.active stagePlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem stage_extra {n : ℕ} (dim : Tapes 17 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.extra (stagePlacement n) ((dim.append pre).append suf) = dim := by
  unfold Placement.extra stagePlacement Tapes.append
  congr 1 <;> funext i <;> simp

theorem stage_dim {n : ℕ} (j : Fin 17) :
    stagePlacement n (Fin.natAdd (n+17) j) = Fin.castAdd 17 (Fin.castAdd n j) := by
  simp [stagePlacement]

theorem stage_pre {n : ℕ} (j : Fin n) :
    stagePlacement n (Fin.castAdd 17 (Fin.castAdd 17 j)) = Fin.castAdd 17 (Fin.natAdd 17 j) := by
  simp [stagePlacement]

theorem stage_suf {n : ℕ} (j : Fin 17) :
    stagePlacement n (Fin.castAdd 17 (Fin.natAdd n j)) = Fin.natAdd (17+n) j := by
  simp [stagePlacement]

variable (r : ℚ)

def stageOutput (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W) :
    Tapes (prefixTapes+17) prime :=
  FlatControlledShiftReady.output r FlatPaddedShift.low FlatPaddedShift.high (FlatPaddedShift.width b t k)
    (widths b t k) (FlatPaddedShift.view a t k hk) (fun _ => blank) (fun _ => blank) 0 0
    (bWord b W t) (qWord b) (pWord b t)

/-- The bank after the stage. -/
def final (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W) : Tapes TapeCount prime :=
  Placement.combine (stagePlacement prefixTapes) (stageOutput r t k hk a) (dimsOutput b W t k)

theorem widths_value (t k : Fin d) (i : Fin (2+1)) :
    Counter.value (widths b t k i) = FlatPaddedShift.width b t k i := by
  fin_cases i
  · exact FlatCoordinateSchedule.bits_value b
  · simp [widths, FlatPaddedShift.width, CounterDimensions.mbBits,
      DimensionProductDescriptor.bits_value, Nat.mul_comm]
  · simp [widths, FlatPaddedShift.width, CounterDimensions.kbBits,
      DimensionProductDescriptor.bits_value, Nat.mul_comm]

theorem widths_canonical (t k : Fin d) (i : Fin (2+1)) :
    GrowingCounterData.Canonical (widths b t k i) := by
  fin_cases i
  · exact FlatCoordinateSchedule.bits_canonical b
  · exact DimensionProductDescriptor.bits_canonical _ _
  · exact DimensionProductDescriptor.bits_canonical _ _

theorem stage_hoare (hden : r.den < prime) (t k : Fin d) (hk : k < t) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) :
    HoareTime (Placement.placed
        (FlatControlledShiftReady.program (radix := prime) r (FlatPaddedShift.low ++ 0 :: FlatPaddedShift.high)
          (by simp)) (stagePlacement prefixTapes))
      (fun v => v = prepared b W t k a) (fun v => v = final r t k hk a)
      ((878+4*2)*((modulus b)^d*W)+29*(2+1)+29) := by
  have hs := FlatPaddedShift.realizes_hoare (radix := prime) (b := b) (W := W) r hden a t k hk hW
    (widths b t k) (widths_value t k) (widths_canonical t k) (fun _ => blank) (fun _ => blank) 0 0
    (bWord b W t) (qWord b) (pWord b t)
    (by
      simp only [bWord, CounterDimensions.bBits, DimensionProductDescriptor.bits_value, suffixSize,
        suffixFields]
      rw [← pow_mul, Nat.mul_comm b])
    (RadixPowerDescriptor.bits_value hprime b)
    (by
      simp only [pWord, CounterDimensions.pBits, RadixPowerDescriptor.bits_value]
      rw [← pow_mul, Nat.mul_comm b])
    (DimensionProductDescriptor.bits_canonical _ _) (RadixPowerDescriptor.bits_canonical hprime b)
    (RadixPowerDescriptor.bits_canonical hprime _) (fun _ _ _ => rfl)
  have ha : Placement.active (stagePlacement prefixTapes) (prepared b W t k a) =
      RationalPrefixTranslationBootstrap.input r (FlatPaddedShift.low ++ 0 :: FlatPaddedShift.high)
        (FlatPaddedShift.width b t k) (widths b t k) (FlatPaddedShift.view a t k hk)
        (fun _ => blank) (fun _ => blank) 0 0 (bWord b W t) (qWord b) (pWord b t) := by
    have hv := FlatPaddedShift.view_word (radix := prime) (b := b) (W := W) a t k hk
    rw [prepared, stage_active, FlatControlledShiftLayout.input_layout, hv]
    rfl
  apply (Placement.hoare_at hs (stagePlacement prefixTapes) (prepared b W t k a) ha).consequence
    (fun _ h => h) ?_ le_rfl
  rintro v ⟨w, hw, rfl⟩
  rw [hw.1, Placement.replace, prepared, stage_extra]
  rfl

/-! ### The clean loop body -/

/-- The six counters start with their heads on the first cell. -/
def right (i : Fin TapeCount) : Bool := decide (3 ≤ i.val ∧ i.val ≤ 8)

/-- The six counters and the payload pair survive. -/
def keep (i : Fin TapeCount) : Bool := decide ((3 ≤ i.val ∧ i.val ≤ 8) ∨ i.val = 37 ∨ i.val = 38)

def inner :=
  seq setup (Placement.placed
    (FlatControlledShiftReady.program (radix := prime) r (FlatPaddedShift.low ++ 0 :: FlatPaddedShift.high)
      (by simp)) (stagePlacement prefixTapes))

def program := CleanExecution.program (inner r) right keep

omit r in
theorem bank_head (t k : Fin d) (a : FlatCoordinateStages.Array d b W) :
    (bank b W t k a).head = TrackedInit.position right := by
  funext i
  refine Fin.addCases (fun x => ?_) (fun y => ?_) i
  · refine Fin.addCases (fun z => ?_) (fun w => ?_) x
    · simp only [bank, Tapes.append, Fin.addCases_left, TrackedInit.position, right, Fin.val_castAdd]
      fin_cases z <;> rfl
    · have hr : right (Fin.castAdd 17 (Fin.natAdd 17 w)) = false := by
        simp [right]; omega
      simp only [TrackedInit.position, hr]
      simp [bank, Tapes.append, PrefixWidthCopies.blankBank]
  · have hr : right (Fin.natAdd (17+prefixTapes) y) = false := by
      simp [right]; omega
    simp only [TrackedInit.position, hr]
    simp only [bank, Tapes.append, Fin.addCases_right]
    fin_cases y <;> rfl

omit r in
theorem bank_blank (t k : Fin d) (a : FlatCoordinateStages.Array d b W) (i : Fin TapeCount)
    (hi : keep i = false) : (bank b W t k a).tape i = fun _ => blank := by
  revert hi
  refine Fin.addCases (fun x => ?_) (fun y => ?_) i
  · refine Fin.addCases (fun z => ?_) (fun w => ?_) x
    · simp only [bank, Tapes.append, Fin.addCases_left, keep, Fin.val_castAdd]
      fin_cases z <;> simp [dimsInput, CounterDimensions.input, CounterDimensions.bank,
        CounterDimensions.inputs, CounterDimensions.descriptorTape]
    · intro _
      simp [bank, Tapes.append, PrefixWidthCopies.blankBank]
  · simp only [bank, Tapes.append, Fin.addCases_right, keep, Fin.val_natAdd, prefixTapes_eq]
    fin_cases y <;> simp [payload, FlatControlledShiftLayout.suffix,
      FlatControlledShiftLayout.descriptorTape]

theorem final_payload (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W) :
    (stageOutput r t k hk a).head (Fin.natAdd prefixTapes 10) = 0 ∧
    (stageOutput r t k hk a).tape (Fin.natAdd prefixTapes 10) =
      (fun z => (RadixToBinary.binaryEncoding (q := prime)).encode
        (putWord (fun _ => blank) 0 (List.ofFn (FlatPaddedShift.array r a t k hk)) z)) ∧
    (stageOutput r t k hk a).head (Fin.natAdd prefixTapes 11) = 0 ∧
    (stageOutput r t k hk a).tape (Fin.natAdd prefixTapes 11) =
      (fun z => (RadixToBinary.binaryEncoding (q := prime)).encode ((fun _ => blank) z)) := by
  have hp := FlatControlledShiftPayload.output_payload (c := 2) (radix := prime) r FlatPaddedShift.low
    FlatPaddedShift.high (FlatPaddedShift.width b t k) (widths b t k) (FlatPaddedShift.view a t k hk)
    (fun _ => blank) (fun _ => blank) 0 0 (bWord b W t) (qWord b) (pWord b t)
  have h0 := congrArg (fun v : Tapes 2 prime => v.head 0) hp
  have h1 := congrArg (fun v : Tapes 2 prime => v.tape 0) hp
  have h2 := congrArg (fun v : Tapes 2 prime => v.head 1) hp
  have h3 := congrArg (fun v : Tapes 2 prime => v.tape 1) hp
  simp only [SharedPayload.payload, FlatArrayNormalize.pair] at h0 h1 h2 h3
  refine ⟨h0, ?_, h2, h3⟩
  have hw := FlatPaddedShift.array_word (radix := prime) (b := b) (W := W) r a t k hk
  rw [hw]
  exact h1

theorem final_dim (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W) (z : Fin 17) :
    (final r t k hk a).head (Fin.castAdd 17 (Fin.castAdd prefixTapes z)) = (dimsOutput b W t k).head z ∧
    (final r t k hk a).tape (Fin.castAdd 17 (Fin.castAdd prefixTapes z)) = (dimsOutput b W t k).tape z := by
  rw [← stage_dim z, final, Placement.combine_head_extra, Placement.combine_tape_extra]
  exact ⟨rfl, rfl⟩

theorem final_suf (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W) (y : Fin 17) :
    (final r t k hk a).head (Fin.natAdd (17+prefixTapes) y) =
      (stageOutput r t k hk a).head (Fin.natAdd prefixTapes y) ∧
    (final r t k hk a).tape (Fin.natAdd (17+prefixTapes) y) =
      (stageOutput r t k hk a).tape (Fin.natAdd prefixTapes y) := by
  rw [← stage_suf y, final, Placement.combine_head_active, Placement.combine_tape_active]
  exact ⟨rfl, rfl⟩

theorem final_retained (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W) :
    TrackedCleanupList.retained keep (final r t k hk a) =
      bank b W t k (FlatPaddedShift.array r a t k hk) := by
  obtain ⟨p0, p1, p2, p3⟩ := final_payload r t k hk a
  have q0 : (stageOutput r t k hk a).head 20 = 0 := p0
  have q1 : (stageOutput r t k hk a).tape 20 = _ := p1
  have q2 : (stageOutput r t k hk a).head 21 = 0 := p2
  have q3 : (stageOutput r t k hk a).tape 21 = _ := p3
  apply congrArg₂ Tapes.mk
  · funext i
    refine Fin.addCases (fun x => ?_) (fun y => ?_) i
    · refine Fin.addCases (fun z => ?_) (fun w => ?_) x
      · simp only [(final_dim r t k hk a z).1, Tapes.append, Fin.addCases_left]
        fin_cases z <;> simp [keep, dimsOutput, dimsInput, CounterDimensions.output,
          CounterDimensions.input, CounterDimensions.bank, CounterDimensions.outputs,
          CounterDimensions.inputs, CounterDimensions.descriptorHead, CounterDimensions.descriptorTape]
      · have hkp : keep (Fin.castAdd 17 (Fin.natAdd 17 w)) = false := by
          have h1 : (Fin.castAdd 17 (Fin.natAdd 17 w) : Fin TapeCount).val = 17 + w.val := by simp
          have h2 : w.val < 10 := w.isLt
          simp only [keep, h1, decide_eq_false_iff_not]
          omega
        simp only [hkp]
        simp [Tapes.append, PrefixWidthCopies.blankBank]
    · simp only [(final_suf r t k hk a y).1, Tapes.append, Fin.addCases_right]
      fin_cases y
      all_goals
        simp only [keep, prefixTapes_eq]
        simp [payload, FlatControlledShiftLayout.suffix,
          FlatControlledShiftLayout.descriptorHead]
        try first | exact q0 | exact q2
  · funext i
    refine Fin.addCases (fun x => ?_) (fun y => ?_) i
    · refine Fin.addCases (fun z => ?_) (fun w => ?_) x
      · simp only [(final_dim r t k hk a z).2, Tapes.append, Fin.addCases_left]
        fin_cases z <;> simp [keep, dimsOutput, dimsInput, CounterDimensions.output,
          CounterDimensions.input, CounterDimensions.bank, CounterDimensions.outputs,
          CounterDimensions.inputs, CounterDimensions.descriptorHead, CounterDimensions.descriptorTape]
      · have hkp : keep (Fin.castAdd 17 (Fin.natAdd 17 w)) = false := by
          have h1 : (Fin.castAdd 17 (Fin.natAdd 17 w) : Fin TapeCount).val = 17 + w.val := by simp
          have h2 : w.val < 10 := w.isLt
          simp only [keep, h1, decide_eq_false_iff_not]
          omega
        simp only [hkp]
        simp [Tapes.append, PrefixWidthCopies.blankBank]
    · simp only [(final_suf r t k hk a y).2, Tapes.append, Fin.addCases_right]
      fin_cases y
      all_goals
        simp only [keep, prefixTapes_eq]
        simp [payload, FlatControlledShiftLayout.suffix,
          FlatControlledShiftLayout.descriptorTape]
        try first | exact q1 | exact q3

/-- The exact cost of the loop body. -/
def cost (b W : ℕ) (t k : Fin d) : ℕ :=
  (2+5*TapeCount)*(setupCost b W t k + 1 + ((878+4*2)*((modulus b)^d*W)+29*(2+1)+29)) + 11*TapeCount + 4

/-- **The padded shift from counters**, exactly: from the loop bank with the array `a` to the loop
bank with the shifted array, every generated tape erased. -/
theorem realizes_exact (hden : r.den < prime) (t k : Fin d) (hk : k < t) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program r)
      (fun v => v = (bank b W t k a).append (SharedBank.empty TapeCount prime))
      (fun v => v = (bank b W t k (FlatPaddedShift.array r a t k hk)).append
        (SharedBank.empty TapeCount prime))
      (cost b W t k) := by
  have h : HoareTime (inner r) (fun v => v = bank b W t k a) (fun v => v = final r t k hk a)
      (setupCost b W t k + 1 + ((878+4*2)*((modulus b)^d*W)+29*(2+1)+29)) :=
    (setup_hoare t k hk hb0 hW a).seq (stage_hoare r hden t k hk hW a)
  have hc := CleanExecution.realizes (inner r) right keep (bank b W t k a) (final r t k hk a)
    (setupCost b W t k + 1 + ((878+4*2)*((modulus b)^d*W)+29*(2+1)+29))
    (bank_head t k a) (bank_blank t k a) h
  rw [final_retained] at hc
  exact hc

omit r in
private theorem length_le (xs : List Bool) (h : GrowingCounterData.Canonical xs) :
    xs.length ≤ Counter.value xs + 1 := by
  have hw := GrowingCounterData.canonical_width xs h
  have hl := Nat.log2_le_self (Counter.value xs)
  omega

omit r in
/-- The body is linear in the array volume, with a constant independent of `d`, `t` and `k`. -/
theorem cost_le (t k : Fin d) (hk : k < t) (hW : 0 < W) :
    cost b W t k ≤ 401000*((modulus b)^d*W) := by
  have ht : t.val < d := t.isLt
  have hkt : k.val < t.val := hk
  set V := (modulus b)^d*W with hV
  have hp : 1 ≤ prime := by have := hprime; omega
  have hD : prime^(d*b) ≤ V := by
    rw [hV, ActualAffineScaling.modulus, ← pow_mul, Nat.mul_comm b]
    exact Nat.le_mul_of_pos_right _ hW
  have hpow {x : ℕ} (hx : x ≤ d) : prime^(x*b) ≤ V :=
    (Nat.pow_le_pow_right hp (Nat.mul_le_mul_right b hx)).trans hD
  have hlin {x : ℕ} (hx : x ≤ d) : x*b ≤ V :=
    ((Nat.lt_pow_self (n := x*b) (by have := hprime; omega : 1 < prime)).le).trans (hpow hx)
  have hV1 : 1 ≤ V := (Nat.one_le_pow _ _ (by omega)).trans hD
  have hvol : prime^(t.val*b)*prime^b*(prime^((d-1-t.val)*b)*W) = V := by
    rw [hV, ActualAffineScaling.modulus, ← pow_mul, ← Nat.mul_assoc, ← pow_add, ← pow_add]
    congr 2
    have e : t.val + 1 + (d-1-t.val) = d := by omega
    calc t.val*b + b + (d-1-t.val)*b = (t.val + 1 + (d-1-t.val))*b := by ring
      _ = b*d := by rw [e, Nat.mul_comm]
  have e0 : FlatPaddedShift.width b t k 0 = b := rfl
  have e1 : FlatPaddedShift.width b t k 1 = b*(t.val-1-k.val) := rfl
  have e2 : FlatPaddedShift.width b t k 2 = b*k.val := rfl
  have l0 : (widths b t k 0).length ≤ V + 1 := by
    have h := length_le _ (widths_canonical (b := b) t k 0)
    rw [widths_value, e0] at h
    have : 1*b ≤ V := hlin (by omega)
    omega
  have l1 : (widths b t k 1).length ≤ V + 1 := by
    have h := length_le _ (widths_canonical (b := b) t k 1)
    rw [widths_value, e1, Nat.mul_comm] at h
    have := hlin (x := t.val-1-k.val) (by omega)
    omega
  have l2 : (widths b t k 2).length ≤ V + 1 := by
    have h := length_le _ (widths_canonical (b := b) t k 2)
    rw [widths_value, e2, Nat.mul_comm] at h
    have := hlin (x := k.val) (by omega)
    omega
  have l3 : (bWord b W t).length ≤ V + 1 := by
    have h := length_le _ (DimensionProductDescriptor.bits_canonical (prime^((d-1-t.val)*b)) W)
    rw [DimensionProductDescriptor.bits_value] at h
    have : prime^((d-1-t.val)*b)*W ≤ V := by
      rw [← hvol]
      calc prime^((d-1-t.val)*b)*W ≤ prime^(t.val*b)*prime^b*(prime^((d-1-t.val)*b)*W) :=
            Nat.le_mul_of_pos_left _ (Nat.mul_pos (by positivity) (by positivity))
        _ = _ := rfl
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
  unfold cost setupCost
  rw [hvol]
  simp only [TapeCount, prefixTapes_eq]
  nlinarith

/-- **The padded shift from counters.** One fixed program, for every coordinate count, target and
control: the loop bank with the array `a` goes to the loop bank with the shifted array in time
linear in the array volume. -/
theorem realizes (hden : r.den < prime) (t k : Fin d) (hk : k < t) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program r)
      (fun v => v = (bank b W t k a).append (SharedBank.empty TapeCount prime))
      (fun v => v = (bank b W t k (FlatPaddedShift.array r a t k hk)).append
        (SharedBank.empty TapeCount prime))
      (401000*((modulus b)^d*W)) :=
  (realizes_exact r hden t k hk hb0 hW a).consequence (fun _ h => h) (fun _ h => h)
    (cost_le t k hk hW)

/-- The shifted array has the ordered-affine shift semantics. -/
theorem array_entry (t k : Fin d) (hk : k < t) (a : FlatCoordinateStages.Array d b W)
    (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    FlatPaddedShift.array r a t k hk
      (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (modulus b) r)) x) j) =
      a (index x j) :=
  FlatPaddedShift.array_entry r a t k hk x j

end
end IntegerMultBounds.Machine.FlatPaddedShiftFromCounters
