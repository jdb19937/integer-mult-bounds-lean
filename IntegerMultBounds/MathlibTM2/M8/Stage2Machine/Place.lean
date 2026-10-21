module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank

/-!
# Routines reading the memo on the common bank

The core keeps the field width `e` of its view on the scalar tape (`memo e`), which the family and
the leaf keep. A routine on `22` optional descriptors is placed on the common bank by sending each
slot to a header, a counter, the memo (read only) or a private tape (`Slot`). `memo_runs`: the
routine's exact contract becomes a run of the common bank that updates the headers and counters it
writes and keeps everything else.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Place

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open CounterDimensions (descriptorHead descriptorTape)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open RevMachine
open CommonBank (bank K headerSlot auxSlot word count)

variable {t : ℕ}

/-- The memo tape: the canonical word of `e` at head one. -/
def memo (e : ℕ) : Tapes 1 prime :=
  ⟨fun _ => descriptorHead (some (bits e)), fun _ => descriptorTape prime (some (bits e))⟩

/-- The scalar tape of the common bank. -/
def scalarSlot : Fin (count t) :=
  Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd 2 (Fin.natAdd 3 (Fin.natAdd 1 (Fin.castAdd K 0)))))

theorem scalarSlot_val : (scalarSlot (t := t)).val = t + 11 := by simp [scalarSlot]

variable (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
  (node : Tapes 1 prime) (e : ℕ) (c : Fin K → Option ℕ) (st : Tapes 2 prime)

@[simp] theorem bank_memo :
    (bank roles hs f p node (memo e) c st).head scalarSlot = descriptorHead (some (bits e)) ∧
      (bank roles hs f p node (memo e) c st).tape scalarSlot = descriptorTape prime (some (bits e)) := by
  simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    scalarSlot, Tapes.append, memo]

/-- Where a slot of a `22`-descriptor routine lives. -/
inductive Slot where
  | header (j : Fin 6)
  | aux (j : Fin K)
  | scalar
  | priv (j : Fin 22)
  deriving DecidableEq

def Slot.pos : Slot → Fin (count t + 22)
  | .header j => Fin.castAdd 22 (headerSlot j)
  | .aux j => Fin.castAdd 22 (auxSlot j)
  | .scalar => Fin.castAdd 22 scalarSlot
  | .priv j => Fin.natAdd (count t) j

/-- The descriptor a slot holds on the bank with headers `hs`, counters `c` and memo `e`. -/
def Slot.value (hs : Fin 6 → List Bool) (c : Fin K → Option ℕ) (e : ℕ) : Slot → Option (List Bool)
  | .header j => some (hs j)
  | .aux j => word (c j)
  | .scalar => some (bits e)
  | .priv _ => none

theorem pos_val (x : Slot) : (x.pos (t := t)).val =
    match x with
    | .header j => t + 1 + j.val
    | .aux j => t + 12 + j.val
    | .scalar => t + 11
    | .priv j => t + 38 + j.val := by
  cases x <;> simp [Slot.pos, CommonBank.headerSlot_val, CommonBank.auxSlot_val, scalarSlot_val]; rfl

theorem pos_injective : Function.Injective (Slot.pos (t := t)) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [pos_val, pos_val] at hv
  have hK : K = 24 := rfl
  rcases x with j | j | _ | j <;> rcases y with k | k | _ | k <;> simp only at hv <;>
    first | rfl | (congr 1; apply Fin.ext; omega) | (have := j.isLt; have := k.isLt; omega) |
      (have := j.isLt; omega) | (have := k.isLt; omega)

theorem Slot.read (x : Slot) :
    (raw (bank roles hs f p node (memo e) c st) (count t + 22)).head (x.pos (t := t)) =
        descriptorHead (x.value hs c e) ∧
      (raw (bank roles hs f p node (memo e) c st) (count t + 22)).tape (x.pos (t := t)) =
        descriptorTape prime (x.value hs c e) := by
  cases x with
  | header j => rw [Slot.pos, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]; exact CommonBank.bank_header ..
  | aux j => rw [Slot.pos, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]; exact CommonBank.bank_aux ..
  | scalar => rw [Slot.pos, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]; exact bank_memo ..
  | priv j =>
    rw [Slot.pos, (Embed.raw_right _ _).1, (Embed.raw_right _ _).2]
    exact ⟨rfl, rfl⟩

/-- A routing of the `22` slots: unrouted slots are private. -/
def sel (a : Fin 22 → Option Slot) (i : Fin 22) : Slot := (a i).getD (.priv i)

variable {roles hs f p node e c st}

/-- **A placed routine reading the memo.** -/
theorem memo_runs {qq B : ℕ} {M : Program 22 qq prime} (a : Fin 22 → Option Slot)
    (ha : Function.Injective (sel a)) {d d' : Fin 22 → Option (List Bool)}
    (hM : HoareTime M (fun w => w = Headers.bank d) (fun w => w = Headers.bank d') B)
    (hs' : Fin 6 → List Bool) (c' : Fin K → Option ℕ)
    (hin : ∀ i, d i = (sel a i).value hs c e) (hout : ∀ i, d' i = (sel a i).value hs' c' e)
    (hh : ∀ j, (∀ i, sel a i ≠ .header j) → hs' j = hs j)
    (hc : ∀ j, (∀ i, sel a i ≠ .aux j) → c' j = c j) :
    HoareTime (Embed.place M (fun i => (sel a i).pos (t := t)) (pos_injective.comp ha)
        (Nat.add_comm _ _)).program
      (fun w => w = raw (bank roles hs f p node (memo e) c st) (count t + 22))
      (fun w => w = raw (bank roles hs' f p node (memo e) c' st) (count t + 22)) B := by
  refine Embed.place_runs hM (fun i => (sel a i).pos (t := t)) (pos_injective.comp ha) (Nat.add_comm _ _) _ _
    (fun i => ?_) (fun i => ?_)
    (fun z hz => ?_)
  · rw [(Slot.read roles hs f p node e c st (sel a i)).1, (Slot.read roles hs f p node e c st (sel a i)).2,
      ← hin i]
    exact ⟨rfl, rfl⟩
  · rw [(Slot.read roles hs' f p node e c' st (sel a i)).1, (Slot.read roles hs' f p node e c' st (sel a i)).2,
      ← hout i]
    exact ⟨rfl, rfl⟩
  · refine CommonBank.bank_agree roles hs f p node (memo e) c st hs' c' z (fun j hj => hh j fun i he => ?_)
      (fun j hj => hc j fun i he => ?_)
    · exact hz i (by rw [he, ← hj]; rfl)
    · exact hz i (by rw [he, ← hj]; rfl)

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Place
