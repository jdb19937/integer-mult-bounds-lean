module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomStepCost
public import IntegerMultBounds.Machine.LevelLoop

/-!
# Level loops of refined atom operations on the role bank

An atom operation on fields of `f` atoms per coordinate is `f` refined operations, one per atom
level, whose selections differ only in their positions. The machine of a refined operation depends
on the kind of its selection only (`AtomStep.machine`), so one fixed body serves every level: the
refined operation, then a fixed counter-step program that moves the five position counters to the
next level. `loop_hoare`: the level loop runs the refined operations of all `f` levels in order, at
`f` times the per-level cost.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoop

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection layout)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open AtomStep (words machine)
variable {t u : ℕ}
noncomputable section

/-- The role bank at one level: the role data, the parent headers and the level's counters. -/
def levelBank (T : ℕ) {v : Descriptor} (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool) : Tapes T prime :=
  raw (bank (roles data) hs (SharedBank.empty 1 prime) ((AtomView.counters ws).append aux)) T

/-- The role data after the refined operations of the first `l` levels. -/
def datas {N b : ℕ} (s : ℕ → Selection N) (act : RecursiveViewedAction.Action t) (v : Descriptor)
    (hw : v.width = N*b) (data : RecursiveViewedAction.Data t v) : ℕ → RecursiveViewedAction.Data t v
  | 0 => data
  | l+1 => RecursiveViewedAction.array (s l) act b v hw (datas s act v hw data l)

/-- **The level loop of an atom operation.** -/
theorem loop_hoare {N b : ℕ} (hb0 : 0 < b) (K : Selection N) (s : ℕ → Selection N)
    (act : RecursiveViewedAction.Action t)
    (hk : ∀ l, machine (u := u) (s l) act = machine (u := u) K act)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime) (f : ℕ) (hf : 0 < f)
    {sU : ℕ} (U : Program (machine (u := u) K act).tapes sU prime) (cu : ℕ)
    (hU : ∀ l, l + 1 < f → ∀ data : RecursiveViewedAction.Data t v,
      HoareTime U (fun x => x = levelBank _ hs aux data (words b (s l)))
        (fun x => x = levelBank _ hs aux data (words b (s (l+1)))) cu)
    (data : RecursiveViewedAction.Data t v) :
    HoareTime (LevelLoop.program (seq (machine (u := u) K act).program U) (machine (u := u) K act).program)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux data (words b (s 0))) f)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux (datas s act v hw data f) (words b (s (f-1)))) f)
      ((f-1)*(AtomStepCost.constant act * volume prime v + 1 + cu) + 6*(f-1) + 7*(bits (f-1)).length +
        16 + 1 + AtomStepCost.constant act * volume prime v) := by
  have step (l : ℕ) : HoareTime (machine (u := u) K act).program
      (fun x => x = levelBank _ hs aux (datas s act v hw data l) (words b (s l)))
      (fun x => x = levelBank _ hs aux (datas s act v hw data (l+1)) (words b (s l)))
      (AtomStepCost.constant act * volume prime v) := by
    have h := AtomStepCost.realizes_le (u := u) hb0 (s l) act v hw hp hs hv aux (datas s act v hw data l)
    rw [hk l] at h
    exact h
  have hlast := step (f-1)
  rw [show f-1+1 = f by omega] at hlast
  exact LevelLoop.level_hoare _ _ f (fun l => levelBank _ hs aux (datas s act v hw data l) (words b (s l)))
    _ _ _ (fun l hl => (step l).seq (hU l hl _)) hlast

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoop
