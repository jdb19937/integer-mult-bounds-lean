module

public import IntegerMultBounds.MathlibTM2.M8.AtomBank

/-!
# Nonrecursive segments on atom fields

A segment of a field program on fields of `f` atoms is a list of atom operations (`AtomOps`), and
each atom operation is a level loop (`AtomShiftLoop`, `AtomScaleLoop`). One fixed program runs
them in order on the common bank `AtomBank.outer`, for every atom count `f`, width `b` and record
width `W`. Between the loops the bank holds `b`, `W`, the array, the count `f` and the loop count
`f - 1`, and no other counter (`neutral`). Each operation writes the four counters of its first
level from `f` (`setCounter`: a multiple of `f`, less one or not), runs its loop placed in the common
bank, and erases the counters (`step_hoare`). The segment moves the records along the run of the
refined atom operations (`segment_realizes`) at cost `C f V`, with `C` depending only on the
operations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.AtomSegment
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateSchedule (bits)
open SharedPlacementAlphabet (setTape)
open CounterDimensions (descriptorHead descriptorTape)
open AtomBank (outer arrTape)
open AtomTransport (Transports)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance {b : ℕ} : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

variable {P : ℕ}

/-! ### Slots of the common bank -/

/-- Counter `j` (`b, W, T, R, K, M`). -/
def cs (P : ℕ) (j : Fin 6) : Fin (22 + P) := ⟨3 + j.val, by omega⟩
def fslot (P : ℕ) : Fin (22 + P) := ⟨20, by omega⟩
def clk (P : ℕ) : Fin (22 + P) := ⟨21, by omega⟩
def oslot (P : ℕ) (hP : 2 ≤ P) : Fin (22 + P) := ⟨22, by omega⟩
def zslot (P : ℕ) (hP : 2 ≤ P) : Fin (22 + P) := ⟨23, by omega⟩

theorem cs_ne_clk (j : Fin 6) : cs P j ≠ clk P := by
  intro h; have := congrArg Fin.val h; simp [cs, clk] at this; omega
theorem cs_ne_f (j : Fin 6) : cs P j ≠ fslot P := by
  intro h; have := congrArg Fin.val h; simp [cs, fslot] at this; omega
theorem clk_ne_f : clk P ≠ fslot P := by
  intro h; have := congrArg Fin.val h; simp [clk, fslot] at this
theorem cs_ne_o (hP : 2 ≤ P) (j : Fin 6) : cs P j ≠ oslot P hP := by
  intro h; have := congrArg Fin.val h; simp [cs, oslot] at this; omega
theorem cs_ne_z (hP : 2 ≤ P) (j : Fin 6) : cs P j ≠ zslot P hP := by
  intro h; have := congrArg Fin.val h; simp [cs, zslot] at this; omega
theorem o_ne_z (hP : 2 ≤ P) : oslot P hP ≠ zslot P hP := by
  intro h; have := congrArg Fin.val h; simp [oslot, zslot] at this

variable (d : Fin 17 → Option (List Bool)) (A : ℤ → Fin (prime + 4)) (f : ℕ)

theorem outer_cs (j : Fin 6) :
    (outer P d A f).head (cs P j) = descriptorHead (d (CounterBank.slot j)) ∧
    (outer P d A f).tape (cs P j) = descriptorTape prime (d (CounterBank.slot j)) := by
  have h : (cs P j).val < 17 := by simp [cs]; omega
  simp only [outer, dite_eq_left h]
  exact ⟨rfl, rfl⟩

theorem outer_f : (outer P d A f).head (fslot P) = 1 ∧
    (outer P d A f).tape (fslot P) = RadixZeroFill.encodedBinary (bits f) := by
  simp [outer, fslot, CounterAdvance.binary_encoded]

theorem outer_clk : (outer P d A f).head (clk P) = 0 ∧ (outer P d A f).tape (clk P) = fun _ => blank := by
  simp [outer, clk]

theorem outer_o (hP : 2 ≤ P) : (outer P d A f).head (oslot P hP) = 0 ∧
    (outer P d A f).tape (oslot P hP) = fun _ => blank := by
  simp [outer, oslot]

theorem outer_z (hP : 2 ≤ P) : (outer P d A f).head (zslot P hP) = 0 ∧
    (outer P d A f).tape (zslot P hP) = fun _ => blank := by
  simp [outer, zslot]

theorem outer_set (j : Fin 6) (o : Option (List Bool)) :
    setTape (outer P d A f) (cs P j) (descriptorTape prime o) (descriptorHead o) =
      outer P (Function.update d (CounterBank.slot j) o) A f := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [setTape, outer] <;>
    by_cases hi : i = cs P j
  · subst hi
    have h : (cs P j).val < 17 := by simp [cs]; omega
    rw [Function.update_self, dite_eq_left h]
    have he : (⟨(cs P j).val, h⟩ : Fin 17) = CounterBank.slot j := Fin.ext (by simp [cs, CounterBank.slot])
    rw [he, Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · have hne : (⟨i.val, h⟩ : Fin 17) ≠ CounterBank.slot j := by
        intro e; apply hi; apply Fin.ext; have := congrArg Fin.val e
        simp [cs, CounterBank.slot] at this ⊢; omega
      rw [Function.update_of_ne hne]
    all_goals rfl
  · subst hi
    have h : (cs P j).val < 17 := by simp [cs]; omega
    rw [Function.update_self, dite_eq_left h]
    have he : (⟨(cs P j).val, h⟩ : Fin 17) = CounterBank.slot j := Fin.ext (by simp [cs, CounterBank.slot])
    rw [he, Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · have hne : (⟨i.val, h⟩ : Fin 17) ≠ CounterBank.slot j := by
        intro e; apply hi; apply Fin.ext; have := congrArg Fin.val e
        simp [cs, CounterBank.slot] at this ⊢; omega
      rw [Function.update_of_ne hne]
    all_goals rfl

/-! ### Writing and erasing counters -/

/-- `c f` on counter `j`: zero, then `c` advances by `f`. -/
def advs (P : ℕ) (j : Fin 6) : ℕ → (q : ℕ) × Program (22 + P) q prime
  | 0 => ⟨_, CounterAdvance.zeroProgram (cs P j)⟩
  | c + 1 => ⟨_, seq (advs P j c).2
      (CounterAdvance.advProgram (cs P j) (clk P) (fslot P) (cs_ne_clk j) (cs_ne_f j) clk_ne_f)⟩

def advCost (f : ℕ) : ℕ → ℕ
  | 0 => 6
  | c + 1 => advCost f c + 1 + (10*f+2*(bits (c*f)).length+7*(bits f).length+28)

theorem advs_hoare (j : Fin 6) (hd : d (CounterBank.slot j) = none) :
    ∀ c, HoareTime (advs P j c).2 (fun v => v = outer P d A f)
      (fun v => v = outer P (Function.update d (CounterBank.slot j) (some (bits (c*f)))) A f)
      (advCost f c)
  | 0 => by
    have h := CounterAdvance.zero_hoare (a := prime) (cs P j) (outer P d A f)
      (by rw [(outer_cs d A f j).2, hd]; rfl) (by rw [(outer_cs d A f j).1, hd]; rfl)
    have he := outer_set (P := P) d A f j (some (bits 0))
    simp only [CounterDimensions.descriptorTape, CounterDimensions.descriptorHead] at he
    rw [he] at h
    simpa [advs, advCost] using h
  | c + 1 => by
    have ih := advs_hoare j hd c
    set d' := Function.update d (CounterBank.slot j) (some (bits (c*f)))
    have h := CounterAdvance.adv_hoare (a := prime) (cs_ne_clk (P := P) j) (cs_ne_f j) clk_ne_f
      (outer P d' A f) (c*f) f
      (by rw [(outer_cs d' A f j).2]; simp [d', CounterDimensions.descriptorTape])
      (by rw [(outer_cs d' A f j).1]; simp [d', CounterDimensions.descriptorHead])
      (outer_clk d' A f).2 (outer_clk d' A f).1 (outer_f d' A f).2 (outer_f d' A f).1
    have he := outer_set (P := P) d' A f j (some (bits (c*f+f)))
    simp only [CounterDimensions.descriptorTape, CounterDimensions.descriptorHead] at he
    rw [he, Function.update_idem, show c*f+f = (c+1)*f by ring] at h
    exact ih.seq h

/-- `c f - e` on counter `j`, for `e` zero or one. -/
def setCounter (P : ℕ) (hP : 2 ≤ P) (j : Fin 6) (c : ℕ) : Bool → (q : ℕ) × Program (22 + P) q prime
  | false => advs P j c
  | true => ⟨_, seq (advs P j c).2
      (CounterSteps.decProgram (cs P j) (oslot P hP) (zslot P hP) (cs_ne_o hP j) (cs_ne_z hP j) (o_ne_z hP))⟩

def setCost (f c : ℕ) : Bool → ℕ
  | false => advCost f c
  | true => advCost f c + 1 + (20*(c*f)+80)

theorem setCounter_hoare (hP : 2 ≤ P) (j : Fin 6) (hd : d (CounterBank.slot j) = none) (c : ℕ) (e : Bool)
    (he : (if e then 1 else 0) ≤ c*f) :
    HoareTime (setCounter P hP j c e).2 (fun v => v = outer P d A f)
      (fun v => v = outer P (Function.update d (CounterBank.slot j)
        (some (bits (c*f - if e then 1 else 0)))) A f) (setCost f c e) := by
  cases e
  · simpa [setCounter, setCost] using advs_hoare d A f j hd c
  · set d' := Function.update d (CounterBank.slot j) (some (bits (c*f)))
    have hdec := CounterSteps.dec_hoare (cs_ne_o hP j) (cs_ne_z hP j) (o_ne_z hP) (outer P d' A f) (c*f)
      (by simpa using he)
      (by rw [(outer_cs d' A f j).2]; simp [d', CounterDimensions.descriptorTape])
      (by rw [(outer_cs d' A f j).1]; simp [d', CounterDimensions.descriptorHead])
      (outer_o d' A f hP).2 (outer_o d' A f hP).1 (outer_z d' A f hP).2 (outer_z d' A f hP).1
    have hs := outer_set (P := P) d' A f j (some (bits (c*f-1)))
    simp only [CounterDimensions.descriptorTape, CounterDimensions.descriptorHead] at hs
    rw [hs, Function.update_idem] at hdec
    simpa [setCounter, setCost] using (advs_hoare d A f j hd c).seq hdec

/-- Erase counter `j`. -/
def eraseCounter (P : ℕ) (j : Fin 6) := BinaryDescriptorCleanupList.oneProgram (a := prime) (cs P j)

theorem eraseCounter_hoare (j : Fin 6) (xs : List Bool) (hd : d (CounterBank.slot j) = some xs) :
    HoareTime (eraseCounter P j) (fun v => v = outer P d A f)
      (fun v => v = outer P (Function.update d (CounterBank.slot j) none) A f) (2*xs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (cs P j) (outer P d A f) xs
    (by rw [(outer_cs d A f j).2, hd, BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl)
    (by rw [(outer_cs d A f j).1, hd]; rfl)
  have he := outer_set (P := P) d A f j none
  simp only [CounterDimensions.descriptorTape, CounterDimensions.descriptorHead] at he
  rwa [he] at h


/-! ### Neutral counters, setup and erasure -/

/-- The counters between operations: `b` and `W` only. -/
def neutral (b W : ℕ) : Fin 17 → Option (List Bool) :=
  fun i => if i.val = 3 then some (bits b) else if i.val = 4 then some (bits W) else none

/-- The value `c f - e` of a counter plan entry. -/
def planValue (f : ℕ) (x : ℕ × Bool) : ℕ := x.1 * f - if x.2 then 1 else 0

theorem neutral_set (b W : ℕ) (x : Fin 4 → ℕ) :
    Function.update (Function.update (Function.update (Function.update (neutral b W)
      (CounterBank.slot 2) (some (bits (x 0)))) (CounterBank.slot 3) (some (bits (x 1))))
      (CounterBank.slot 4) (some (bits (x 2)))) (CounterBank.slot 5) (some (bits (x 3))) =
    CounterBank.entries ![b, W, x 0, x 1, x 2, x 3] := by
  funext i
  fin_cases i <;> simp [neutral, CounterBank.entries, CounterBank.slot, Function.update] <;> rfl

theorem entries_erase (w : Fin 6 → ℕ) :
    Function.update (Function.update (Function.update (Function.update (CounterBank.entries w)
      (CounterBank.slot 2) none) (CounterBank.slot 3) none) (CounterBank.slot 4) none)
      (CounterBank.slot 5) none = neutral (w 0) (w 1) := by
  funext i
  fin_cases i <;> simp [neutral, CounterBank.entries, CounterBank.slot, Function.update] <;> rfl

/-- Write the counters `T, R, K, M` of a plan. -/
def setup (P : ℕ) (hP : 2 ≤ P) (pl : Fin 4 → ℕ × Bool) :=
  seq (seq (seq (setCounter P hP 2 (pl 0).1 (pl 0).2).2 (setCounter P hP 3 (pl 1).1 (pl 1).2).2)
    (setCounter P hP 4 (pl 2).1 (pl 2).2).2) (setCounter P hP 5 (pl 3).1 (pl 3).2).2

def setupCost (f : ℕ) (pl : Fin 4 → ℕ × Bool) : ℕ :=
  setCost f (pl 0).1 (pl 0).2 + 1 + setCost f (pl 1).1 (pl 1).2 + 1 + setCost f (pl 2).1 (pl 2).2 + 1 +
    setCost f (pl 3).1 (pl 3).2

theorem setup_hoare (hP : 2 ≤ P) (b W : ℕ) (pl : Fin 4 → ℕ × Bool)
    (hpl : ∀ j, (if (pl j).2 then 1 else 0) ≤ (pl j).1 * f) :
    HoareTime (setup P hP pl) (fun v => v = outer P (neutral b W) A f)
      (fun v => v = outer P (CounterBank.entries ![b, W, planValue f (pl 0), planValue f (pl 1),
        planValue f (pl 2), planValue f (pl 3)]) A f) (setupCost f pl) := by
  have h0 := setCounter_hoare (neutral b W) A f hP 2 (by simp [neutral, CounterBank.slot]) _ _ (hpl 0)
  have h1 := setCounter_hoare (Function.update (neutral b W) (CounterBank.slot 2)
    (some (bits (planValue f (pl 0))))) A f hP 3
    (by simp [neutral, CounterBank.slot, Function.update]) _ _ (hpl 1)
  have h2 := setCounter_hoare (Function.update (Function.update (neutral b W) (CounterBank.slot 2)
    (some (bits (planValue f (pl 0))))) (CounterBank.slot 3) (some (bits (planValue f (pl 1))))) A f hP 4
    (by simp [neutral, CounterBank.slot, Function.update]) _ _ (hpl 2)
  have h3 := setCounter_hoare (Function.update (Function.update (Function.update (neutral b W)
    (CounterBank.slot 2) (some (bits (planValue f (pl 0))))) (CounterBank.slot 3)
    (some (bits (planValue f (pl 1))))) (CounterBank.slot 4) (some (bits (planValue f (pl 2))))) A f hP 5
    (by simp [neutral, CounterBank.slot, Function.update]) _ _ (hpl 3)
  have he := neutral_set b W (fun j => planValue f (pl j))
  simp only [planValue] at he h0 h1 h2 h3 ⊢
  rw [he] at h3
  exact ((h0.seq h1).seq h2).seq h3

/-- Erase the counters `T, R, K, M`. -/
def erase (P : ℕ) :=
  seq (seq (seq (eraseCounter P 2) (eraseCounter P 3)) (eraseCounter P 4)) (eraseCounter P 5)

def eraseCost (w : Fin 6 → ℕ) : ℕ :=
  (2*(bits (w 2)).length+4) + 1 + (2*(bits (w 3)).length+4) + 1 + (2*(bits (w 4)).length+4) + 1 +
    (2*(bits (w 5)).length+4)

theorem erase_hoare (w : Fin 6 → ℕ) :
    HoareTime (erase P) (fun v => v = outer P (CounterBank.entries w) A f)
      (fun v => v = outer P (neutral (w 0) (w 1)) A f) (eraseCost w) := by
  have hs (d : Fin 17 → Option (List Bool)) (j : Fin 6) (hj : d (CounterBank.slot j) = some (bits (w j))) :=
    eraseCounter_hoare (P := P) d A f j (bits (w j)) hj
  have hent (j : Fin 6) : CounterBank.entries w (CounterBank.slot j) = some (bits (w j)) := by
    have h : 3 ≤ (CounterBank.slot j).val ∧ (CounterBank.slot j).val < 9 := by simp [CounterBank.slot]; omega
    simp only [CounterBank.entries, dite_eq_left h]
    congr 3
    ext; simp [CounterBank.slot]
  have h2 := hs _ 2 (hent 2)
  have h3 := hs (Function.update (CounterBank.entries w) (CounterBank.slot 2) none) 3
    (by rw [Function.update_of_ne (by simp [CounterBank.slot])]; exact hent 3)
  have h4 := hs (Function.update (Function.update (CounterBank.entries w) (CounterBank.slot 2) none)
    (CounterBank.slot 3) none) 4 (by
    rw [Function.update_of_ne (by simp [CounterBank.slot]), Function.update_of_ne (by simp [CounterBank.slot])]
    exact hent 4)
  have h5 := hs (Function.update (Function.update (Function.update (CounterBank.entries w)
    (CounterBank.slot 2) none) (CounterBank.slot 3) none) (CounterBank.slot 4) none) 5 (by
    rw [Function.update_of_ne (by simp [CounterBank.slot]), Function.update_of_ne (by simp [CounterBank.slot]),
      Function.update_of_ne (by simp [CounterBank.slot])]
    exact hent 5)
  rw [entries_erase] at h5
  exact ((h2.seq h3).seq h4).seq h5

/-! ### Placed loops -/

theorem placed_hoare {L ai q c : ℕ} (hL : L ≤ P) (ha : 17 ≤ ai) (ha' : ai + 2 < L) (M : Program L q prime)
    (d d' : Fin 17 → Option (List Bool)) (A' : ℤ → Fin (prime + 4))
    (hM : HoareTime M (fun v => v = AtomBank.opBank L ai d A f) (fun v => v = AtomBank.opBank L ai d' A' f) c) :
    HoareTime (Placement.placed M (AtomBank.place L ai P hL ha ha')) (fun v => v = outer P d A f)
      (fun v => v = outer P d' A' f) c := by
  have h := Placement.hoare_at hM (AtomBank.place L ai P hL ha ha') (outer P d A f)
    (AtomBank.active_outer hL ha ha' d A f)
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨w, rfl, rfl⟩
  exact AtomBank.replace_outer hL ha ha' d d' A A' f


/-! ### Atom operations -/

section Ops

variable {n : ℕ} {f : ℕ}

/-- The coefficients the stages accept, and controls before targets. -/
def Supported : AtomOps.AtomOp n ℚ → Prop
  | .scale _ c => Shared50AffineCoefficients.ScaleOccurs c
  | .shift t k c => k < t ∧ c.den < prime
  | .revShift t k c => k < t ∧ c.den < prime

/-- The loop bank size of an operation. -/
def len : AtomOps.AtomOp n ℚ → ℕ
  | .scale _ c => AtomScaleLoop.Tape2 c + 2
  | _ => AtomShiftLoop.Tape2 + 2

/-- The first-level counters `T, R, K, M` as multiples of `f`, less one or not. -/
def plan : AtomOps.AtomOp n ℚ → Fin 4 → ℕ × Bool
  | .scale t _ => ![(t.val, false), (n - t.val, true), (0, false), (0, false)]
  | .shift t k _ => ![(t.val, false), (n - t.val, true), (k.val, false), (t.val - k.val, true)]
  | .revShift t k _ => ![(t.val, false), (n - t.val, true), (k.val + 1, true), (t.val - k.val - 1, false)]

theorem tape2_ai : 37 + 2 < AtomShiftLoop.Tape2 + 2 := by rw [AtomBank.tape2_eq]; norm_num

/-- One atom operation on the common bank: its counters, its loop, and the erasure. -/
def step (P : ℕ) (hP : 2 ≤ P) : (op : AtomOps.AtomOp n ℚ) → Supported op → len op ≤ P →
    (q : ℕ) × Program (22 + P) q prime
  | .shift t k c, _, hL => ⟨_, seq (seq (setup P hP (plan (.shift t k c)))
      (Placement.placed (AtomShiftLoop.program c AtomShiftLoop.shiftSteps)
        (AtomBank.place (AtomShiftLoop.Tape2 + 2) 37 P hL (by norm_num) tape2_ai))) (erase P)⟩
  | .revShift t k c, _, hL => ⟨_, seq (seq (setup P hP (plan (.revShift t k c)))
      (Placement.placed (AtomShiftLoop.program c AtomShiftLoop.revSteps)
        (AtomBank.place (AtomShiftLoop.Tape2 + 2) 37 P hL (by norm_num) tape2_ai))) (erase P)⟩
  | .scale t c, hr, hL => ⟨_, seq (seq (setup P hP (plan (.scale t c)))
      (Placement.placed (AtomScaleLoop.program hr)
        (AtomBank.place (AtomScaleLoop.Tape2 c + 2) (AtomBank.scaleIndex c) P hL
          (AtomBank.scaleIndex_ge c) (AtomBank.scaleIndex_lt c)))) (erase P)⟩

theorem first_level (t : Fin n) (hf : 0 < f) :
    (AtomShiftLoop.shiftT t hf 0).val = t.val * f := by
  rw [AtomShiftLoop.shiftT, AtomShiftLoop.at_val, AtomShiftLoop.lv_val hf hf, Nat.mul_comm, Nat.zero_add]

theorem shift_plan (b W : ℕ) (t k : Fin n) (c : ℚ) (hk : k < t) (hf : 0 < f) :
    ![b, W, planValue f (plan (.shift t k c) 0), planValue f (plan (.shift t k c) 1),
      planValue f (plan (.shift t k c) 2), planValue f (plan (.shift t k c) 3)] =
    AtomShiftLoop.counters b W (AtomShiftLoop.shiftT t hf 0) (AtomShiftLoop.shiftK k hf 0) := by
  have hT := first_level t hf
  have hK : (AtomShiftLoop.shiftK k hf 0).val = k.val * f := first_level k hf
  have hkt : k.val * f + f ≤ t.val * f := by
    have := Nat.mul_le_mul_right f (show k.val + 1 ≤ t.val from hk); rwa [Nat.succ_mul] at this
  have htn : t.val * f + f ≤ n * f := by
    have := Nat.mul_le_mul_right f (show t.val + 1 ≤ n from t.isLt); rwa [Nat.succ_mul] at this
  funext j
  fin_cases j <;> simp [plan, planValue, AtomShiftLoop.counters, hT, hK, Nat.sub_mul] <;> omega

theorem shift_step_exact (hP : 2 ≤ P) (b W : ℕ) (t k : Fin n) (c : ℚ) (hk : k < t) (hden : c.den < prime)
    (hL : AtomShiftLoop.Tape2 + 2 ≤ P) (hf : 0 < f) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (n * f) b W) :
    HoareTime (step P hP (.shift t k c) ⟨hk, hden⟩ hL).2 (fun v => v = outer P (neutral b W) (arrTape a) f)
      (fun v => v = outer P (neutral b W) (arrTape (AtomShiftLoop.shiftArray t k hk hf c a)) f)
      (setupCost f (plan (.shift t k c)) + 1 + AtomShiftLoop.constant * f * ((modulus b)^(n*f)*W) + 1 +
        eraseCost (AtomShiftLoop.counters b W (AtomShiftLoop.shiftT t hf (f-1))
          (AtomShiftLoop.shiftK k hf (f-1)))) := by
  have hpl : ∀ j, (if (plan (.shift t k c) j).2 then 1 else 0) ≤ (plan (.shift t k c) j).1 * f := by
    intro j
    have h1 : 1 ≤ (n - t.val) * f := Nat.mul_pos (by have := t.isLt; omega) hf
    have h2 : 1 ≤ (t.val - k.val) * f := Nat.mul_pos (by have : k.val < t.val := hk; omega) hf
    fin_cases j <;> simp [plan] <;> omega
  have hs := setup_hoare (arrTape a) f hP b W _ hpl
  rw [shift_plan b W t k c hk hf] at hs
  have hl := AtomShiftLoop.shift_realizes c t k hk hf hden hb0 hW a
  rw [AtomBank.shift_opBank, AtomBank.shift_opBank] at hl
  have hp := placed_hoare (arrTape a) f hL (by norm_num) tape2_ai _ _ _ _ hl
  have he := erase_hoare (P := P) (arrTape (AtomShiftLoop.shiftArray t k hk hf c a)) f
    (AtomShiftLoop.counters b W (AtomShiftLoop.shiftT t hf (f-1)) (AtomShiftLoop.shiftK k hf (f-1)))
  simp only [AtomShiftLoop.counters, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at he
  exact (hs.seq hp).seq he

theorem rev_first (k : Fin n) (hf : 0 < f) :
    (AtomShiftLoop.revK k hf 0).val = (k.val + 1) * f - 1 := by
  rw [AtomShiftLoop.revK, AtomShiftLoop.at_val, Fin.val_rev, AtomShiftLoop.lv_val hf hf, Nat.succ_mul,
    Nat.mul_comm]
  omega

theorem rev_plan (b W : ℕ) (t k : Fin n) (c : ℚ) (hk : k < t) (hf : 0 < f) :
    ![b, W, planValue f (plan (.revShift t k c) 0), planValue f (plan (.revShift t k c) 1),
      planValue f (plan (.revShift t k c) 2), planValue f (plan (.revShift t k c) 3)] =
    AtomShiftLoop.counters b W (AtomShiftLoop.shiftT t hf 0) (AtomShiftLoop.revK k hf 0) := by
  have hT := first_level t hf
  have hK := rev_first k hf
  have hkt : k.val * f + f ≤ t.val * f := by
    have := Nat.mul_le_mul_right f (show k.val + 1 ≤ t.val from hk); rwa [Nat.succ_mul] at this
  have htn : t.val * f + f ≤ n * f := by
    have := Nat.mul_le_mul_right f (show t.val + 1 ≤ n from t.isLt); rwa [Nat.succ_mul] at this
  have h1 : (t.val - k.val - 1) * f = t.val * f - k.val * f - f := by
    rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul]
  funext j
  fin_cases j <;> simp [plan, planValue, AtomShiftLoop.counters, hT, hK, Nat.sub_mul, Nat.succ_mul, h1] <;>
    omega

theorem rev_step_exact (hP : 2 ≤ P) (b W : ℕ) (t k : Fin n) (c : ℚ) (hk : k < t) (hden : c.den < prime)
    (hL : AtomShiftLoop.Tape2 + 2 ≤ P) (hf : 0 < f) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (n * f) b W) :
    HoareTime (step P hP (.revShift t k c) ⟨hk, hden⟩ hL).2 (fun v => v = outer P (neutral b W) (arrTape a) f)
      (fun v => v = outer P (neutral b W) (arrTape (AtomShiftLoop.revArray t k hk hf c a)) f)
      (setupCost f (plan (.revShift t k c)) + 1 + AtomShiftLoop.constant * f * ((modulus b)^(n*f)*W) + 1 +
        eraseCost (AtomShiftLoop.counters b W (AtomShiftLoop.shiftT t hf (f-1))
          (AtomShiftLoop.revK k hf (f-1)))) := by
  have hpl : ∀ j, (if (plan (.revShift t k c) j).2 then 1 else 0) ≤ (plan (.revShift t k c) j).1 * f := by
    intro j
    have h1 : 1 ≤ (n - t.val) * f := Nat.mul_pos (by have := t.isLt; omega) hf
    have h2 : 1 ≤ (k.val + 1) * f := Nat.mul_pos (by omega) hf
    fin_cases j <;> simp [plan] <;> omega
  have hs := setup_hoare (arrTape a) f hP b W _ hpl
  rw [rev_plan b W t k c hk hf] at hs
  have hl := AtomShiftLoop.revShift_realizes c t k hk hf hden hb0 hW a
  rw [AtomBank.shift_opBank, AtomBank.shift_opBank] at hl
  have hp := placed_hoare (arrTape a) f hL (by norm_num) tape2_ai _ _ _ _ hl
  have he := erase_hoare (P := P) (arrTape (AtomShiftLoop.revArray t k hk hf c a)) f
    (AtomShiftLoop.counters b W (AtomShiftLoop.shiftT t hf (f-1)) (AtomShiftLoop.revK k hf (f-1)))
  simp only [AtomShiftLoop.counters, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  exact (hs.seq hp).seq he

theorem scale_plan (b W : ℕ) (t : Fin n) (c : ℚ) (hf : 0 < f) :
    ![b, W, planValue f (plan (.scale t c) 0), planValue f (plan (.scale t c) 1),
      planValue f (plan (.scale t c) 2), planValue f (plan (.scale t c) 3)] =
    AtomScaleLoop.counters b W (AtomShiftLoop.shiftT t hf 0) := by
  have hT := first_level t hf
  have htn : t.val * f + f ≤ n * f := by
    have := Nat.mul_le_mul_right f (show t.val + 1 ≤ n from t.isLt); rwa [Nat.succ_mul] at this
  funext j
  fin_cases j <;> simp [plan, planValue, AtomScaleLoop.counters, hT, Nat.sub_mul] <;> omega

theorem scale_step_exact (hP : 2 ≤ P) (b W : ℕ) (t : Fin n) (c : ℚ)
    (hr : Shared50AffineCoefficients.ScaleOccurs c)
    (hL : AtomScaleLoop.Tape2 c + 2 ≤ P) (hf : 0 < f) (hb0 : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (n * f) b W) :
    HoareTime (step P hP (.scale t c) hr hL).2 (fun v => v = outer P (neutral b W) (arrTape a) f)
      (fun v => v = outer P (neutral b W) (arrTape (AtomScaleLoop.scaleArray hr t hf a)) f)
      (setupCost f (plan (.scale t c)) + 1 + AtomScaleLoop.constant c * f * ((modulus b)^(n*f)*W) + 1 +
        eraseCost (AtomScaleLoop.counters b W (AtomShiftLoop.shiftT t hf (f-1)))) := by
  have hpl : ∀ j, (if (plan (.scale t c) j).2 then 1 else 0) ≤ (plan (.scale t c) j).1 * f := by
    intro j
    have h1 : 1 ≤ (n - t.val) * f := Nat.mul_pos (by have := t.isLt; omega) hf
    fin_cases j <;> simp [plan] <;> omega
  have hs := setup_hoare (arrTape a) f hP b W _ hpl
  rw [scale_plan b W t c hf] at hs
  have hl := AtomScaleLoop.scale_realizes hr t hf hb0 hW a
  rw [AtomBank.scale_opBank, AtomBank.scale_opBank] at hl
  have hp := placed_hoare (arrTape a) f hL (AtomBank.scaleIndex_ge c) (AtomBank.scaleIndex_lt c) _ _ _ _ hl
  have he := erase_hoare (P := P) (arrTape (AtomScaleLoop.scaleArray hr t hf a)) f
    (AtomScaleLoop.counters b W (AtomShiftLoop.shiftT t hf (f-1)))
  simp only [AtomScaleLoop.counters, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  exact (hs.seq hp).seq he

end Ops

end
end IntegerMultBounds.MathlibTM2.M8.AtomSegment
