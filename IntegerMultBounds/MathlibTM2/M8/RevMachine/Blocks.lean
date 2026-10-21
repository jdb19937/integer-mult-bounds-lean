module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphContract
public import IntegerMultBounds.Machine.SharedBankRawCompose
public import IntegerMultBounds.Machine.RecursiveViewFrameRoleBank

/-!
# Blocks on the common bank

Blocks run one after the other (`seq_runs`). The node view stack saves the six headers and
restores them (`push_runs`, `restore_runs`), as the stage-1 node frame does. A counter at head
one is zero exactly when its first cell is blank (`counter_blank`), which the leaf test reads.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open CounterDimensions (descriptorHead descriptorTape)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank)
open Shared50RecursiveBank (adapt commonRename nodeSlot)

variable {t a : ℕ}

/-- Two blocks in sequence. -/
def seqB (s r : Graph.Block t a) : Graph.Block t a := SharedBankSkeleton.compose s r

theorem seq_slots (s r : Graph.Block t a) (i : Fin t) : ((seqB s r).slots i).val = i.val := rfl

/-- Blocks whose common slots are the leading tapes. -/
def Leading (s : Graph.Block t a) : Prop := ∀ i, (s.slots i).val = i.val

theorem seq_leading (s r : Graph.Block t a) : Leading (seqB s r) := fun _ => rfl

theorem place_leading {s q p u : ℕ} (M : Program s q a) (slot : Fin s → Fin (t+p)) (hinj)
    (hsize : s + u = t + p) : Leading (Embed.place M slot hinj hsize) := fun _ => rfl

theorem adapt_leading {k : ℕ} (s : Graph.Block k a) (e : Fin k ≃ Fin t) : Leading (adapt s e) :=
  fun _ => rfl

theorem seq_runs {s r : Graph.Block t a} (hs : Leading s) (hr : Leading r) {x y z : Tapes t a} {B C : ℕ}
    (h₁ : Runs s x y B) (h₂ : Runs r y z C) : Runs (seqB s r) x z (B + C + 1) :=
  SharedBankRawCompose.realizes s r hs hr x y z B C h₁ h₂

theorem runs_mono {s : Graph.Block t a} {x y : Tapes t a} {B C : ℕ} (h : Runs s x y B) (hBC : B ≤ C) :
    Runs s x y C :=
  h.consequence (fun _ h => h) (fun _ h => h) hBC

/-! ### The node view stack -/

abbrev K := CommonBank.K

/-- Save the six headers on the node view stack. -/
def push : Graph.Block (CommonBank.count t) prime :=
  adapt (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := Shared50RecursiveBank.AuxCount K - 1))
    (commonRename nodeSlot)

/-- Restore the six headers from the node view stack. -/
def restore : Graph.Block (CommonBank.count t) prime :=
  adapt (RecursiveViewFrameRoleBank.restoreSkeleton (t := t) (u := Shared50RecursiveBank.AuxCount K - 1))
    (commonRename nodeSlot)

variable (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
  (node scalar : Tapes 1 prime) (c : Fin K → Option ℕ) (st : Tapes 2 prime)

theorem push_runs :
    Runs push (bank roles hs f p node scalar c st)
      (bank roles hs f p (RecursiveViewFrame.savedStack hs node) scalar c st) (RecursiveViewFrame.pushCost hs) := by
  have h := RecursiveViewFrameRoleBank.push_hoare roles hs node
    (Shared50RecursiveBank.rest nodeSlot (Shared50RecursiveBank.auxiliary f p node scalar (CommonBank.counters c) st))
  simp only [SharedBankRawCompose.bank_eq_raw] at h
  have h' := Shared50RecursiveBank.adapt_realizes
    (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := Shared50RecursiveBank.AuxCount K - 1))
    (commonRename nodeSlot) _ _ _ h
  rw [Shared50RecursiveBank.node_endpoint, Shared50RecursiveBank.rest_node f p node
    (RecursiveViewFrame.savedStack hs node), Shared50RecursiveBank.node_endpoint] at h'
  exact h'

theorem restore_runs (old : Fin 6 → List Bool) (hf : RecursiveViewFrame.Free old node) :
    Runs restore (bank roles hs f p (RecursiveViewFrame.savedStack old node) scalar c st)
      (bank roles old f p node scalar c st) (RecursiveViewFrame.restoreCost old hs) := by
  have h := RecursiveViewFrameRoleBank.restore_hoare roles old hs node
    (Shared50RecursiveBank.rest nodeSlot (Shared50RecursiveBank.auxiliary f p node scalar (CommonBank.counters c) st)) hf
  simp only [SharedBankRawCompose.bank_eq_raw] at h
  have h' := Shared50RecursiveBank.adapt_realizes
    (RecursiveViewFrameRoleBank.restoreSkeleton (t := t) (u := Shared50RecursiveBank.AuxCount K - 1))
    (commonRename nodeSlot) _ _ _ h
  have e₁ := Shared50RecursiveBank.node_endpoint roles hs f p (RecursiveViewFrame.savedStack old node) scalar
    (CommonBank.counters c) st
  rw [← Shared50RecursiveBank.rest_node f p node (RecursiveViewFrame.savedStack old node)] at e₁
  rw [Shared50RecursiveBank.node_endpoint, e₁] at h'
  exact h'

/-! ### Counters -/

theorem encode_ne_blank {y : Fin 4} (hy : y ≠ blank) :
    (RadixToBinary.binaryEncoding (q := prime)).encode y ≠ blank := by
  intro h
  apply hy
  have := congrArg Fin.val h
  exact Fin.ext this

theorem counter_blank (x : ℕ) :
    descriptorTape prime (some (bits x)) (descriptorHead (some (bits x))) ≠ blank ↔ x ≠ 0 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [ne_eq, not_true_eq_false, iff_false, not_not]
    rfl
  · have hne : bits x ≠ [] := fun h => by
      have := FlatCoordinateSchedule.bits_value x
      rw [h] at this
      simp [Counter.value] at this
      omega
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
    simp only [ne_eq, hx.ne', not_false_eq_true, iff_true]
    rw [hb]
    change (RadixToBinary.binaryEncoding (q := prime)).encode (CountedCopyReuse.binary (b :: bs) 1) ≠ blank
    apply encode_ne_blank
    simp only [CountedCopyReuse.binary, putBits, Function.update_self]
    cases b <;> decide

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
