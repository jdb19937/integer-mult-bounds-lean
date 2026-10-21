module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Headers
public import IntegerMultBounds.Machine.Shared50RecursiveBank

/-!
# The common bank of the reversed family

The reversed family runs on the permanent recursive bank of stage 1
(`Shared50RecursiveBank.bank`: the role streams, the six headers, the payload work tapes, the
node and scalar view stacks and the descriptor and PC stacks) with `K` counter tapes as its
auxiliary tapes (`bank`). A counter is absent (blank, head zero) or holds the canonical binary
word of a value at head one (`counters`), the format of the headers and of `Headers.bank`.

A routine on `22` optional descriptors (`Headers.bank`) is placed on the common bank by sending
each of its slots to a header, a counter or a private tape (`Target`). `counter_runs`: the
routine's exact contract becomes a block run that updates the headers and counters it writes and
keeps everything else.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open CounterDimensions (descriptorHead descriptorTape)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)

/-- The number of counter tapes. -/
abbrev K : ℕ := 24

abbrev count (t : ℕ) : ℕ := Shared50RecursiveBank.Count t K

/-- An optional counter value as an optional descriptor word. -/
def word (x : Option ℕ) : Option (List Bool) := x.map bits

/-- The counter tapes. -/
def counters (c : Fin K → Option ℕ) : Tapes K prime :=
  ⟨fun i => descriptorHead (word (c i)), fun i => descriptorTape prime (word (c i))⟩

variable {t : ℕ}

/-- **The common bank.** -/
def bank (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (c : Fin K → Option ℕ) (st : Tapes 2 prime) : Tapes (count t) prime :=
  Shared50RecursiveBank.bank roles hs f p node scalar (counters c) st

/-! ### Slots -/

def headerSlot (j : Fin 6) : Fin (count t) :=
  Fin.natAdd t (Fin.castAdd ((3+(1+(1+K)))+2) (Fin.natAdd 1 j))

def auxSlot (j : Fin K) : Fin (count t) :=
  Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd 2 (Fin.natAdd 3 (Fin.natAdd 1 (Fin.natAdd 1 j)))))

theorem headerSlot_val (j : Fin 6) : (headerSlot (t := t) j).val = t + 1 + j.val := by
  simp [headerSlot]; omega

theorem auxSlot_val (j : Fin K) : (auxSlot (t := t) j).val = t + 12 + j.val := by
  simp [auxSlot]; omega

variable (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
  (node scalar : Tapes 1 prime) (c : Fin K → Option ℕ) (st : Tapes 2 prime)

@[simp] theorem bank_header (j : Fin 6) :
    (bank roles hs f p node scalar c st).head (headerSlot j) = descriptorHead (some (hs j)) ∧
      (bank roles hs f p node scalar c st).tape (headerSlot j) = descriptorTape prime (some (hs j)) := by
  simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    RecursiveShiftRoleBank.headers, headerSlot, Tapes.append, descriptorHead, descriptorTape]

@[simp] theorem bank_aux (j : Fin K) :
    (bank roles hs f p node scalar c st).head (auxSlot j) = descriptorHead (word (c j)) ∧
      (bank roles hs f p node scalar c st).tape (auxSlot j) = descriptorTape prime (word (c j)) := by
  simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    auxSlot, Tapes.append, counters]

/-- Two banks that differ only in headers and counters agree at every other tape. -/
theorem bank_other (hs' : Fin 6 → List Bool) (c' : Fin K → Option ℕ) (z : Fin (count t))
    (hh : ∀ j, headerSlot j ≠ z) (ha : ∀ j, auxSlot j ≠ z) :
    (bank roles hs' f p node scalar c' st).head z = (bank roles hs f p node scalar c st).head z ∧
      (bank roles hs' f p node scalar c' st).tape z = (bank roles hs f p node scalar c st).tape z := by
  revert hh ha
  simp only [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common]
  induction z using Fin.addCases with
  | left z => intro _ _; simp [Tapes.append]
  | right z =>
    induction z using Fin.addCases with
    | left z =>
      change Fin (1+6) at z
      induction z using Fin.addCases with
      | left z => intro _ _; simp [Tapes.append]
      | right z => intro hh _; exact absurd rfl (hh z)
    | right z =>
      induction z using Fin.addCases with
      | left z =>
        induction z using Fin.addCases with
        | left z => intro _ _; simp [Tapes.append]
        | right z =>
          induction z using Fin.addCases with
          | left z => intro _ _; simp [Tapes.append]
          | right z =>
            induction z using Fin.addCases with
            | left z => intro _ _; simp [Tapes.append]
            | right z => intro _ ha; exact absurd rfl (ha z)
      | right z => intro _ _; simp [Tapes.append]

/-- Two banks agree at a tape where their headers and counters agree. -/
theorem bank_agree (hs' : Fin 6 → List Bool) (c' : Fin K → Option ℕ) (z : Fin (count t))
    (hh : ∀ j, headerSlot j = z → hs' j = hs j) (ha : ∀ j, auxSlot j = z → c' j = c j) :
    (bank roles hs' f p node scalar c' st).head z = (bank roles hs f p node scalar c st).head z ∧
      (bank roles hs' f p node scalar c' st).tape z = (bank roles hs f p node scalar c st).tape z := by
  by_cases hz : ∃ j, headerSlot j = z
  · obtain ⟨j, rfl⟩ := hz
    rw [(bank_header ..).1, (bank_header ..).2, (bank_header ..).1, (bank_header ..).2, hh j rfl]
    exact ⟨rfl, rfl⟩
  by_cases hz' : ∃ j, auxSlot j = z
  · obtain ⟨j, rfl⟩ := hz'
    rw [(bank_aux ..).1, (bank_aux ..).2, (bank_aux ..).1, (bank_aux ..).2, ha j rfl]
    exact ⟨rfl, rfl⟩
  push Not at hz hz'
  exact bank_other roles hs f p node scalar c st hs' c' z hz hz'

/-! ### Routines on optional descriptors -/

/-- Where a slot of a `22`-descriptor routine lives: a header, a counter or a private tape. -/
inductive Target (pp : ℕ) where
  | header (j : Fin 6)
  | aux (j : Fin K)
  | priv (j : Fin pp)

def Target.slot {pp : ℕ} : Target pp → Fin (count t + pp)
  | .header j => Fin.castAdd pp (headerSlot j)
  | .aux j => Fin.castAdd pp (auxSlot j)
  | .priv j => Fin.natAdd (count t) j

/-- The descriptor a target holds on the bank with headers `hs` and counters `c`. -/
def Target.value {pp : ℕ} (hs : Fin 6 → List Bool) (c : Fin K → Option ℕ) : Target pp → Option (List Bool)
  | .header j => some (hs j)
  | .aux j => word (c j)
  | .priv _ => none

theorem Target.read {pp : ℕ} (x : Target pp) :
    (raw (bank roles hs f p node scalar c st) (count t + pp)).head (x.slot (t := t)) =
        descriptorHead (x.value hs c) ∧
      (raw (bank roles hs f p node scalar c st) (count t + pp)).tape (x.slot (t := t)) =
        descriptorTape prime (x.value hs c) := by
  cases x with
  | header j => rw [Target.slot, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]; exact bank_header ..
  | aux j => rw [Target.slot, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]; exact bank_aux ..
  | priv j =>
    rw [Target.slot, (Embed.raw_right _ _).1, (Embed.raw_right _ _).2]
    exact ⟨rfl, rfl⟩

variable {roles hs f p node scalar c st}

/-- **A placed descriptor routine.** The routine runs from the descriptors the targets hold
before to those they hold after; headers and counters outside its image are kept. -/
theorem counter_runs {pp q B : ℕ} {M : Program 22 q prime} {d d' : Fin 22 → Option (List Bool)}
    (hM : HoareTime M (fun w => w = Headers.bank d) (fun w => w = Headers.bank d') B)
    (σ : Fin 22 → Target pp) (hinj : Function.Injective fun i => (σ i).slot (t := t))
    (hsize : 22 + (count t + pp - 22) = count t + pp)
    (hs' : Fin 6 → List Bool) (c' : Fin K → Option ℕ)
    (hin : ∀ i, d i = (σ i).value hs c) (hout : ∀ i, d' i = (σ i).value hs' c')
    (hh : ∀ j, (∀ i, σ i ≠ .header j) → hs' j = hs j)
    (ha : ∀ j, (∀ i, σ i ≠ .aux j) → c' j = c j) :
    HoareTime (Embed.place M (fun i => (σ i).slot (t := t)) hinj hsize).program
      (fun w => w = raw (bank roles hs f p node scalar c st)
        (Embed.place M (fun i => (σ i).slot (t := t)) hinj hsize).tapes)
      (fun w => w = raw (bank roles hs' f p node scalar c' st)
        (Embed.place M (fun i => (σ i).slot (t := t)) hinj hsize).tapes) B := by
  refine Embed.place_runs hM _ hinj hsize _ _ (fun i => ?_) (fun i => ?_) (fun z hz => ?_)
  · rw [(Target.read roles hs f p node scalar c st (σ i)).1,
      (Target.read roles hs f p node scalar c st (σ i)).2, ← hin i]
    exact ⟨rfl, rfl⟩
  · rw [(Target.read roles hs' f p node scalar c' st (σ i)).1,
      (Target.read roles hs' f p node scalar c' st (σ i)).2, ← hout i]
    exact ⟨rfl, rfl⟩
  · refine bank_agree roles hs f p node scalar c st hs' c' z (fun j hj => hh j fun i he => ?_)
      (fun j hj => ha j fun i he => ?_)
    · exact hz i (by rw [he, ← hj]; rfl)
    · exact hz i (by rw [he, ← hj]; rfl)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank
