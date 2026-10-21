module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Arith
public import IntegerMultBounds.Machine.BinaryCanonicalData

/-!
# Counter routines on the common bank

A routine on `22` optional descriptors is placed by a routing `a`: a slot routed to `some x` lives
at the header or counter `x`, every other slot on its own private tape (`sel`). `routine_runs` is
`CommonBank.counter_runs` for such routings.

The canonical word of a value is unique (`canon`), so the headers of a positive descriptor are
determined by it (`hdr`), and every routine's canonical outputs are counter values.

The first routine of the family's preparation divides the width header by the atom width
(`atoms_runs`): the atom count `n` of a view of `n` atoms of `b` digits.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Routines

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open CounterDimensions (descriptorHead descriptorTape)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank Target word K)
open RecursiveInterchangeLayout (Descriptor volume)

deriving instance DecidableEq for Target

variable {t : ℕ}

theorem slot_injective (pp : ℕ) : Function.Injective (Target.slot (t := t) (pp := pp)) := by
  have hc : CommonBank.count t = t + (7 + ((3 + (1 + (1 + K))) + 2)) := rfl
  intro x y h
  have hv := congrArg Fin.val h
  cases x with
  | header i =>
    cases y with
    | header j => simp [Target.slot, CommonBank.headerSlot_val] at hv; rw [Fin.ext hv]
    | aux j => simp [Target.slot, CommonBank.headerSlot_val, CommonBank.auxSlot_val] at hv; omega
    | priv j => simp [Target.slot, CommonBank.headerSlot_val] at hv; omega
  | aux i =>
    cases y with
    | header j => simp [Target.slot, CommonBank.headerSlot_val, CommonBank.auxSlot_val] at hv; omega
    | aux j => simp [Target.slot, CommonBank.auxSlot_val] at hv; rw [Fin.ext hv]
    | priv j => simp [Target.slot, CommonBank.auxSlot_val] at hv; omega
  | priv i =>
    cases y with
    | header j => simp [Target.slot, CommonBank.headerSlot_val] at hv; omega
    | aux j => simp [Target.slot, CommonBank.auxSlot_val] at hv; omega
    | priv j => simp [Target.slot] at hv; rw [Fin.ext hv]

/-- A routing of the `22` slots. -/
def sel (a : Fin 22 → Option (Target 22)) (i : Fin 22) : Target 22 := (a i).getD (.priv i)

/-- The canonical word of a value is unique. -/
theorem canon {xs : List Bool} (hx : GrowingCounterData.Canonical xs) : xs = bits (Counter.value xs) :=
  BinaryCanonicalData.value_injective _ _ hx (FlatCoordinateSchedule.bits_canonical _)
    (FlatCoordinateSchedule.bits_value _).symm

/-- The headers of a descriptor. -/
def hdr (v : Descriptor) : Fin 6 → List Bool := fun i => bits (RecursiveDimensionBank.values v i)

theorem hdr_headers (v : Descriptor) : RecursiveDimensionBank.Headers v (hdr v) :=
  ⟨fun _ => FlatCoordinateSchedule.bits_value _, fun _ => FlatCoordinateSchedule.bits_canonical _⟩

theorem hdr_eq {v : Descriptor} {hs : Fin 6 → List Bool} (h : RecursiveDimensionBank.Headers v hs) :
    hs = hdr v := by
  funext i; rw [canon (h.2 i), h.1 i]; rfl

variable {roles : Tapes t prime} {hs : Fin 6 → List Bool} {f : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {c : Fin K → Option ℕ} {st : Tapes 2 prime}

/-- **A routed routine.** -/
theorem routine_runs {q B : ℕ} {M : Program 22 q prime} (a : Fin 22 → Option (Target 22))
    (ha : Function.Injective (sel a)) {d' : Fin 22 → Option (List Bool)}
    (hM : HoareTime M (fun w => w = Headers.bank fun i => (sel a i).value hs c)
      (fun w => w = Headers.bank d') B)
    (hs' : Fin 6 → List Bool) (c' : Fin K → Option ℕ)
    (hout : ∀ i, d' i = (sel a i).value hs' c')
    (hh : ∀ j, (∀ i, sel a i ≠ .header j) → hs' j = hs j)
    (hc : ∀ j, (∀ i, sel a i ≠ .aux j) → c' j = c j) :
    Runs (Embed.place (u := CommonBank.count t) M (fun i => (sel a i).slot (t := t))
        ((slot_injective 22).comp ha) (Nat.add_comm _ _))
      (bank roles hs f p node scalar c st) (bank roles hs' f p node scalar c' st) B :=
  CommonBank.counter_runs hM (sel a) _ _ hs' c' (fun _ => rfl) hout hh hc

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Routines
