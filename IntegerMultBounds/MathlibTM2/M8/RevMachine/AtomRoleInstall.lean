module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePlan
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePad
public import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-!
# Installing the position counters of an atom operation

Between atom operations the four position counters of the role bank hold zero. The auxiliary
tapes hold the atom count `f` and a blank clock. An atom operation's first-level counters are
multiples `c f` of the atom count, less one or not (`AtomSegment.planValue`): `setup_hoare`
installs them by `c` advances by `f` and an optional decrement, and `erase_hoare` resets them to
zero.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleInstall

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
open AtomRoleLoop (levelBank)
open AtomRoleSteps (cslot oslot zslot bank_port bank_set)
open AtomSegment (planValue)
variable {t : ℕ}
noncomputable section

/-- The auxiliary tapes: the atom count and a blank clock. -/
def fAux (f : ℕ) : Tapes 2 prime :=
  ⟨fun z => if z = 0 then 1 else 0, fun z => if z = 0 then RadixZeroFill.encodedBinary (bits f) else fun _ => blank⟩

/-- The counters between atom operations: the width, and four zeros. -/
def rest (b : ℕ) : Fin 5 → List Bool := ![bits b, bits 0, bits 0, bits 0, bits 0]

/-- The counters of an atom operation's first level. -/
def target (b : ℕ) (x : Fin 4 → ℕ) : Fin 5 → List Bool := ![bits b, bits (x 0), bits (x 1), bits (x 2), bits (x 3)]

section Slots

variable (T : ℕ) (hT : count t (5+2) + 2 ≤ T)
include hT

/-- The atom count and the clock on the machine's tapes. -/
def fslot : Fin T := ⟨t+13, by unfold count at hT; omega⟩
def kslot : Fin T := ⟨t+14, by unfold count at hT; omega⟩

theorem bank_f (hs : Fin 6 → List Bool) (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool)
    (f : ℕ) : (levelBank T hs (fAux f) data ws).head (fslot T hT) = 1 ∧
      (levelBank T hs (fAux f) data ws).tape (fslot T hT) = RadixZeroFill.encodedBinary (bits f) := by
  have hk : t+13 < count t (5+2) := by unfold count; omega
  have he : (⟨t+13, hk⟩ : Fin (count t (5+2))) =
      Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 1 (Fin.natAdd 5 (0 : Fin 2)))) := Fin.ext (by simp)
  simp only [levelBank, raw, fslot, hk, dite_true]
  rw [he]
  simp only [bank, RecursiveShiftRoleBank.common, Tapes.append, Fin.addCases_right]
  simp [fAux]

theorem bank_k (hs : Fin 6 → List Bool) (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool)
    (f : ℕ) : (levelBank T hs (fAux f) data ws).head (kslot T hT) = 0 ∧
      (levelBank T hs (fAux f) data ws).tape (kslot T hT) = fun _ => blank := by
  have hk : t+14 < count t (5+2) := by unfold count; omega
  have he : (⟨t+14, hk⟩ : Fin (count t (5+2))) =
      Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 1 (Fin.natAdd 5 (1 : Fin 2)))) := Fin.ext (by simp)
  simp only [levelBank, raw, kslot, hk, dite_true]
  rw [he]
  simp only [bank, RecursiveShiftRoleBank.common, Tapes.append, Fin.addCases_right]
  simp [fAux]

theorem cslot_ne_k (z : Fin 5) : cslot T hT z ≠ kslot T hT := by
  intro h; have := congrArg Fin.val h; simp [cslot, kslot] at this; omega
theorem cslot_ne_f (z : Fin 5) : cslot T hT z ≠ fslot T hT := by
  intro h; have := congrArg Fin.val h; simp [cslot, fslot] at this; omega
theorem k_ne_f : kslot T hT ≠ fslot T hT := by
  intro h; have := congrArg Fin.val h; simp [kslot, fslot] at this

/-! ### One counter -/

/-- Add the atom count to counter `z`. -/
def adv (z : Fin 5) :=
  CounterAdvance.advProgram (a := prime) (cslot T hT z) (kslot T hT) (fslot T hT)
    (cslot_ne_k T hT z) (cslot_ne_f T hT z) (k_ne_f T hT)

variable (hs : Fin 6 → List Bool) (data : RecursiveViewedAction.Data t v) (f : ℕ)

theorem adv_hoare (ws : Fin 5 → List Bool) (z : Fin 5) (x : ℕ) (hz : ws z = bits x) :
    HoareTime (adv T hT z) (fun y => y = levelBank T hs (fAux f) data ws)
      (fun y => y = levelBank T hs (fAux f) data (Function.update ws z (bits (x+f))))
      (10*f+2*(bits x).length+7*(bits f).length+28) := by
  have hp := bank_port T hT hs (fAux f) data ws z
  rw [hz] at hp
  have hf := bank_f T hT hs data ws f
  have hk := bank_k T hT hs data ws f
  rw [← bank_set T hT]
  exact CounterAdvance.adv_hoare _ _ _ _ x f hp.2 hp.1 hk.2 hk.1 hf.2 hf.1

/-- `c` advances of counter `z`. -/
def advs (z : Fin 5) : ℕ → (q : ℕ) × Program T q prime
  | 0 => ⟨1, skip T prime (by omega)⟩
  | c+1 => ⟨_, seq (advs z c).2 (adv T hT z)⟩

omit hT in
/-- The cost of `c` advances. -/
def advCost (f : ℕ) : ℕ → ℕ
  | 0 => 0
  | c+1 => advCost f c + 1 + (10*f+2*(bits (c*f)).length+7*(bits f).length+28)

theorem advs_hoare (ws : Fin 5 → List Bool) (z : Fin 5) (hz : ws z = bits 0) :
    ∀ c, HoareTime (advs T hT z c).2 (fun y => y = levelBank T hs (fAux f) data ws)
      (fun y => y = levelBank T hs (fAux f) data (Function.update ws z (bits (c*f)))) (advCost f c)
  | 0 => by
    rw [Nat.zero_mul, ← hz, Function.update_eq_self]
    exact skip_hoare _ _
  | c+1 => by
    have h := adv_hoare T hT hs data f (Function.update ws z (bits (c*f))) z (c*f) (by simp)
    rw [Function.update_idem, ← Nat.succ_mul] at h
    exact (advs_hoare ws z hz c).seq h

/-- Decrement counter `z`. -/
def dec (z : Fin 5) :=
  CounterSteps.decProgram (a := prime) (cslot T hT z) (oslot T hT) (zslot T hT)
    (AtomRoleSteps.cslot_ne_o T hT z) (AtomRoleSteps.cslot_ne_z T hT z) (AtomRoleSteps.o_ne_z T hT)

/-- Set counter `z` from zero to `c f`, less one or not. -/
def set (z : Fin 5) (c : ℕ) : Bool → (q : ℕ) × Program T q prime
  | false => advs T hT z c
  | true => ⟨_, seq (advs T hT z c).2 (dec T hT z)⟩

omit hT in
def setCost (f c : ℕ) : Bool → ℕ
  | false => advCost f c
  | true => advCost f c + 1 + (20*(c*f)+80)

theorem set_hoare (ws : Fin 5 → List Bool) (z : Fin 5) (hz : ws z = bits 0) (x : ℕ × Bool)
    (he : (if x.2 then 1 else 0) ≤ x.1*f) :
    HoareTime (set T hT z x.1 x.2).2 (fun y => y = levelBank T hs (fAux f) data ws)
      (fun y => y = levelBank T hs (fAux f) data (Function.update ws z (bits (planValue f x))))
      (setCost f x.1 x.2) := by
  obtain ⟨c, e⟩ := x
  cases e
  · simpa [set, setCost, planValue] using advs_hoare T hT hs data f ws z hz c
  · have h := AtomRoleSteps.dec_level T hT hs (fAux f) data (Function.update ws z (bits (c*f))) z (c*f)
      (by simpa using he) (by simp)
    rw [Function.update_idem] at h
    exact (advs_hoare T hT hs data f ws z hz c).seq h

/-- Reset counter `z` to zero. -/
def erase (z : Fin 5) :=
  seq (BinaryDescriptorCleanupList.oneProgram (a := prime) (cslot T hT z))
    (CounterAdvance.zeroProgram (a := prime) (cslot T hT z))

theorem erase_hoare (ws : Fin 5 → List Bool) (z : Fin 5) (n : ℕ) (hz : ws z = bits n) :
    HoareTime (erase T hT z) (fun y => y = levelBank T hs (fAux f) data ws)
      (fun y => y = levelBank T hs (fAux f) data (Function.update ws z (bits 0)))
      (2*(bits n).length+4+1+6) := by
  have hp := bank_port T hT hs (fAux f) data ws z
  rw [hz] at hp
  have h1 := BinaryDescriptorCleanupList.one_hoare (cslot T hT z) (levelBank T hs (fAux f) data ws) (bits n)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; exact hp.2) hp.1
  have h2 := CounterAdvance.zero_hoare (a := prime) (cslot T hT z)
    (setTape (levelBank T hs (fAux f) data ws) (cslot T hT z) (fun _ => blank) 0) (by simp [setTape])
    (by simp [setTape])
  rw [SharedPlacementAlphabet.setTape_setTape, bank_set T hT] at h2
  exact h1.seq h2

/-! ### The four position counters -/

/-- Install the first-level counters of a plan. -/
def setup (pl : Fin 4 → ℕ × Bool) :=
  seq (seq (seq (set T hT 1 (pl 0).1 (pl 0).2).2 (set T hT 2 (pl 1).1 (pl 1).2).2)
    (set T hT 3 (pl 2).1 (pl 2).2).2) (set T hT 4 (pl 3).1 (pl 3).2).2

omit hT in
def setupCost (f : ℕ) (pl : Fin 4 → ℕ × Bool) : ℕ :=
  setCost f (pl 0).1 (pl 0).2 + 1 + setCost f (pl 1).1 (pl 1).2 + 1 + setCost f (pl 2).1 (pl 2).2 + 1 +
    setCost f (pl 3).1 (pl 3).2

theorem setup_hoare (b : ℕ) (pl : Fin 4 → ℕ × Bool) (hpl : ∀ j, (if (pl j).2 then 1 else 0) ≤ (pl j).1 * f) :
    HoareTime (setup T hT pl) (fun y => y = levelBank T hs (fAux f) data (rest b))
      (fun y => y = levelBank T hs (fAux f) data (target b (fun j => planValue f (pl j))))
      (setupCost f pl) := by
  have h1 := set_hoare T hT hs data f (rest b) 1 rfl (pl 0) (hpl 0)
  set w1 := Function.update (rest b) 1 (bits (planValue f (pl 0)))
  have h2 := set_hoare T hT hs data f w1 2 (by simp [w1, rest]) (pl 1) (hpl 1)
  set w2 := Function.update w1 2 (bits (planValue f (pl 1)))
  have h3 := set_hoare T hT hs data f w2 3 (by simp [w2, w1, rest, Function.update]) (pl 2) (hpl 2)
  set w3 := Function.update w2 3 (bits (planValue f (pl 2)))
  have h4 := set_hoare T hT hs data f w3 4 (by simp [w3, w2, w1, rest, Function.update]) (pl 3) (hpl 3)
  have he : Function.update w3 4 (bits (planValue f (pl 3))) = target b (fun j => planValue f (pl j)) := by
    funext z; fin_cases z <;> rfl
  rw [he] at h4
  exact ((h1.seq h2).seq h3).seq h4

/-- Reset the four position counters. -/
def eraseAll := seq (seq (seq (erase T hT 1) (erase T hT 2)) (erase T hT 3)) (erase T hT 4)

omit hT in
def eraseCost (x : Fin 4 → ℕ) : ℕ :=
  (2*(bits (x 0)).length+4+1+6) + 1 + (2*(bits (x 1)).length+4+1+6) + 1 +
    (2*(bits (x 2)).length+4+1+6) + 1 + (2*(bits (x 3)).length+4+1+6)

theorem eraseAll_hoare (b : ℕ) (x : Fin 4 → ℕ) :
    HoareTime (eraseAll T hT) (fun y => y = levelBank T hs (fAux f) data (target b x))
      (fun y => y = levelBank T hs (fAux f) data (rest b)) (eraseCost x) := by
  have h1 := erase_hoare T hT hs data f (target b x) 1 (x 0) rfl
  set w1 := Function.update (target b x) 1 (bits 0)
  have h2 := erase_hoare T hT hs data f w1 2 (x 1) (by simp [w1, target])
  set w2 := Function.update w1 2 (bits 0)
  have h3 := erase_hoare T hT hs data f w2 3 (x 2) (by simp [w2, w1, target, Function.update])
  set w3 := Function.update w2 3 (bits 0)
  have h4 := erase_hoare T hT hs data f w3 4 (x 3) (by simp [w3, w2, w1, target, Function.update])
  have he : Function.update w3 4 (bits 0) = rest b := by
    funext z; fin_cases z <;> rfl
  rw [he] at h4
  exact ((h1.seq h2).seq h3).seq h4

end Slots

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleInstall
