module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
public import IntegerMultBounds.MathlibTM2.M8.RevNetwork
public import IntegerMultBounds.Machine.RecursiveRowsNode
public import IntegerMultBounds.MathlibTM2.M8.Machine.RoleOpsBank

/-!
# The role tapes of a reversed network on the common bank

The role tapes of a reversed network `N` are its wires, contract roles then temporaries, and one
input/output tape `io` (`tapes`). A frame's data sits on `io`, every other role tape blank
(`Good`): the input of the row split over the contract roles (`wires`).

Every role-bank block of stage 1 (the row split and merge, XOR gates and fills) runs on the role
bank with the node view stack as its one stack tape. One theorem places any such block on the
common bank (`role_runs`): its run on the role bank becomes a run on the common bank that keeps
the payload stack, the scalar stack, the counters and the call stacks.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeBank

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open GraphContract (Runs)
open CommonBank (bank K)
open Shared50RecursiveBank (adapt commonRename nodeSlot)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRoleSerialization (roles)
open RecursiveRowsSerialization (sourceData roleData)

/-! ### Role tapes -/

section Wires

variable (N : RevNetwork)

/-- The number of wires. -/
abbrev wireCount : ℕ := N.roleCount + N.tempCount

/-- The role tapes: the wires and the input/output tape. -/
abbrev tapes : ℕ := wireCount N + 1

/-- The wires in order: contract roles, then temporaries. -/
def wireEquiv : Fin (wireCount N) ≃ N.World ⊕ N.Temp :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr N.roleEquiv N.tempEquiv)

/-- The input/output tape. -/
def io : Fin (tapes N) := Fin.last _

/-- The tape of a wire. -/
def wireSlot (w : N.World ⊕ N.Temp) : Fin (tapes N) := Fin.castAdd 1 ((wireEquiv N).symm w)

theorem wireSlot_injective : Function.Injective (wireSlot N) := by
  intro w w' h
  exact (wireEquiv N).symm.injective (Fin.castAdd_injective _ _ h)

theorem wireSlot_ne_io (w : N.World ⊕ N.Temp) : wireSlot N w ≠ io N := by
  intro h
  have := congrArg Fin.val h
  simp [wireSlot, io] at this
  omega

/-- Every role tape other than `io` is a wire's. -/
theorem eq_wireSlot (i : Fin (tapes N)) (hi : i ≠ io N) : ∃ w, wireSlot N w = i := by
  refine ⟨wireEquiv N ⟨i.val, ?_⟩, ?_⟩
  · have h₁ : i.val < wireCount N + 1 := i.isLt
    have h₂ : i.val ≠ wireCount N := fun h => hi (Fin.ext (by simp [io, h]))
    omega
  · apply Fin.ext; simp [wireSlot]

/-- The tape of a temporary. -/
def tempSlot (k : Fin N.tempCount) : Fin (tapes N) := wireSlot N (.inr (N.tempEquiv k))

/-- The split and merge tapes: `io`, then the contract roles in their enumeration. -/
def wires : Fin (1 + N.roleCount) → Fin (tapes N) :=
  Fin.addCases (fun _ => io N) (fun j => wireSlot N (.inl (N.roleEquiv j)))

theorem wires_injective : Function.Injective (wires N) := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => congr 1; exact Subsingleton.elim _ _
    | right j =>
      simp only [wires, Fin.addCases_left, Fin.addCases_right] at he
      exact absurd he.symm (wireSlot_ne_io N _)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [wires, Fin.addCases_left, Fin.addCases_right] at he
      exact absurd he (wireSlot_ne_io N _)
    | right j =>
      simp only [wires, Fin.addCases_right] at he
      have h := wireSlot_injective N he
      simp only [Sum.inl.injEq] at h
      exact congrArg (Fin.natAdd 1) (N.roleEquiv.injective h)

@[simp] theorem wires_zero : wires N (Fin.castAdd N.roleCount (0 : Fin 1)) = io N := by
  simp only [wires, Fin.addCases_left]

/-- The merge route as a permutation of the role enumeration. -/
def mergeRoute : Equiv.Perm (Fin N.roleCount) :=
  N.roleEquiv.trans ((⟨N.route, N.route, N.route_involutive, N.route_involutive⟩ : Equiv.Perm N.World).trans
    N.roleEquiv.symm)

/-- **A frame's role streams**: its data on `io`, every other role tape blank. -/
def Good (v : Descriptor) (x : Tapes (tapes N) prime) : Prop :=
  ∃ a : Fin (volume prime v) → Fin 4, x = roles (sourceData (wires N) a)

end Wires

/-! ### Role-bank blocks on the common bank -/

section Place

variable {t : ℕ}

/-- A role-bank block, placed with the node view stack as its stack tape. -/
def roleBlock (s : SharedBankSkeleton.Skeleton (RecursiveViewFrameRoleBank.count t
    (Shared50RecursiveBank.AuxCount K - 1)) prime) : Graph.Block (CommonBank.count t) prime :=
  adapt s (commonRename nodeSlot)

theorem roleBlock_leading (s : SharedBankSkeleton.Skeleton (RecursiveViewFrameRoleBank.count t
    (Shared50RecursiveBank.AuxCount K - 1)) prime) : Blocks.Leading (roleBlock s) :=
  Blocks.adapt_leading _ _

/-- **A placed role-bank block**: a run of the role bank, for every rest of the bank, is a run
of the common bank that keeps everything outside the roles, the headers and the node stack. -/
theorem role_runs {s : SharedBankSkeleton.Skeleton (RecursiveViewFrameRoleBank.count t
    (Shared50RecursiveBank.AuxCount K - 1)) prime}
    {x x' : Tapes t prime} {hs hs' : Fin 6 → List Bool} {node node' : Tapes 1 prime} {B : ℕ}
    (h : ∀ R : Tapes (Shared50RecursiveBank.AuxCount K - 1) prime, HoareTime s.program
      (fun w => w = raw (RecursiveViewFrameRoleBank.bank x hs node R) s.tapes)
      (fun w => w = raw (RecursiveViewFrameRoleBank.bank x' hs' node' R) s.tapes) B)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (scalar : Tapes 1 prime) (c : Fin K → Option ℕ) (st : Tapes 2 prime) :
    Runs (roleBlock s) (bank x hs f p node scalar c st) (bank x' hs' f p node' scalar c st) B := by
  have h' := Shared50RecursiveBank.adapt_realizes s (commonRename nodeSlot) _ _ _
    (h (Shared50RecursiveBank.rest nodeSlot
      (Shared50RecursiveBank.auxiliary f p node scalar (CommonBank.counters c) st)))
  rw [Shared50RecursiveBank.node_endpoint, Shared50RecursiveBank.rest_node f p node node',
    Shared50RecursiveBank.node_endpoint] at h'
  exact h'

/-- A list of role operations. -/
def ops (l : List (Machine.RoleOps.Op t)) : Graph.Block (CommonBank.count t) prime :=
  roleBlock (Machine.RoleOpsBank.machine (u := Shared50RecursiveBank.AuxCount K - 1) l)

theorem ops_runs {v : Descriptor} (l : List (Machine.RoleOps.Op t)) {hs : Fin 6 → List Bool}
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (data : RecursiveMixedSchedule.Data t v) (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (c : Fin K → Option ℕ) (st : Tapes 2 prime) :
    Runs (ops l) (bank (roles data) hs f p node scalar c st)
      (bank (roles (Machine.RoleOps.run l data)) hs f p node scalar c st)
      (Machine.RoleOpsClean.coefficient l * volume prime v) :=
  role_runs (fun R => Machine.RoleOpsBank.realizes l hs node R hv hp data) f p scalar c st

end Place

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeBank
