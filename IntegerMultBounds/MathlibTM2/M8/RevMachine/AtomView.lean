module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimeWithin
public import IntegerMultBounds.Machine.RecursiveViewedAction

/-!
# Runtime atom views on the role bank

Stage 1's viewed actions (`RecursiveViewedAction`) save the six parent headers, prepare the
headers of a coordinate view, run one scalar shift or scaling on the view and restore the parent
headers. The stage-2 adapters do the same with views of single atoms at runtime positions: the
preparation is `RuntimeCross.program` or `RuntimeWithin.program`, which reads the atom width and
four position counters. Here the counters live in the first five auxiliary tapes of the role bank
(`aux = counters ws ++ rest`), and the 47-tape preparation runs as a clean sub-bank whose ports are
the six headers and the five counters (`view_hoare`): the parent headers become the view's, the
counters, rows, stack and every other auxiliary tape are kept.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomView

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveViewFrameRoleBank (count bank)
variable {t u : ℕ}
noncomputable section

/-- The five counters on the first auxiliary tapes. -/
def counters (ws : Fin 5 → List Bool) : Tapes 5 prime :=
  ⟨fun _ => 1, fun z => RadixZeroFill.encodedBinary (ws z)⟩

/-- The local ports: the six parent headers and the five counters of the 47-tape preparation. -/
def ports : Fin (6+5) → Fin 47 := ![3,4,5,6,7,8,38,39,40,41,42]

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

/-- The matching role-bank tapes: the headers, then the first five auxiliary tapes. -/
def commonPorts : Fin (6+5) → Fin (count t (5+u)) :=
  Fin.addCases (motive := fun _ => Fin (count t (5+u)))
    (fun j : Fin 6 => Fin.natAdd t (Fin.castAdd (1+(5+u)) (Fin.natAdd 1 j)))
    (fun z : Fin 5 => Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 1 (Fin.castAdd u z))))

theorem commonPorts_injective : Function.Injective (commonPorts (t := t) (u := u)) := by
  intro i j h
  have hv : ∀ x : Fin (6+5), (commonPorts (t := t) (u := u) x).val =
      if x.val < 6 then t+1+x.val else t+8+(x.val-6) := by
    intro x
    induction x using Fin.addCases with
    | left x => simp [commonPorts, Fin.addCases_left]; omega
    | right x => simp [commonPorts, Fin.addCases_right]; omega
  have := congrArg Fin.val h
  rw [hv, hv] at this
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at this <;> omega

/-- The local bank of a preparation. -/
def localBank (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) : Tapes 47 prime :=
  (RecursiveChildHeaderHandoff.canonical hs).append (RuntimeCross.extras ws)

/-- The common payload: six headers and five counters. -/
def payload (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) : Tapes (6+5) prime :=
  ⟨fun _ => 1, Fin.addCases (fun j => RadixZeroFill.encodedBinary (hs j))
    (fun z => RadixZeroFill.encodedBinary (ws z))⟩

theorem local_payload (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) :
    SharedBank.payload (localBank hs ws) ports = payload hs ws := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem common_payload (roles : Tapes t prime) (hs : Fin 6 → List Bool) (st : Tapes 1 prime)
    (ws : Fin 5 → List Bool) (aux : Tapes u prime) :
    SharedBank.payload (bank roles hs st ((counters ws).append aux)) commonPorts = payload hs ws := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i => simp only [bank, commonPorts, RecursiveShiftRoleBank.common,
        RecursiveShiftRoleBank.headers, Tapes.append, Fin.addCases_left, Fin.addCases_right]
    | right i => simp only [bank, commonPorts, RecursiveShiftRoleBank.common,
        Tapes.append, Fin.addCases_left, Fin.addCases_right, counters]

theorem local_clean (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) :
    SharedBank.strip (localBank hs ws) ports = SharedBank.empty 47 prime := by
  have hblank (i : Fin 47) (hi : ¬∃ j, ports j = i) :
      (localBank hs ws).head i = 0 ∧ (localBank hs ws).tape i = fun _ => blank := by
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ |
      exact (hi ⟨0,rfl⟩).elim | exact (hi ⟨1,rfl⟩).elim | exact (hi ⟨2,rfl⟩).elim |
      exact (hi ⟨3,rfl⟩).elim | exact (hi ⟨4,rfl⟩).elim | exact (hi ⟨5,rfl⟩).elim |
      exact (hi ⟨6,rfl⟩).elim | exact (hi ⟨7,rfl⟩).elim | exact (hi ⟨8,rfl⟩).elim |
      exact (hi ⟨9,rfl⟩).elim | exact (hi ⟨10,rfl⟩).elim
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi, ↓reduceIte]
    · simpa only [SharedBank.strip, hi, ↓reduceIte, SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi, ↓reduceIte]
    · simpa only [SharedBank.strip, hi, ↓reduceIte, SharedBank.empty] using (hblank i hi).2

theorem common_frame (roles : Tapes t prime) (hs ch : Fin 6 → List Bool) (st : Tapes 1 prime)
    (ws : Fin 5 → List Bool) (aux : Tapes u prime) :
    SharedBank.strip (bank roles hs st ((counters ws).append aux)) commonPorts =
      SharedBank.strip (bank roles ch st ((counters ws).append aux)) commonPorts := by
  have selected (i : Fin 6) : ∃ j, commonPorts (t := t) (u := u) j =
      Fin.natAdd t (Fin.castAdd (1+(5+u)) (Fin.natAdd 1 i)) :=
    ⟨Fin.castAdd 5 i, by simp [commonPorts, Fin.addCases_left]⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i => simp only [bank, RecursiveShiftRoleBank.common, Tapes.append, Fin.addCases_left]
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        change Fin (1+6) at i
        induction i using Fin.addCases with
        | left i => simp only [bank, RecursiveShiftRoleBank.common, Tapes.append,
            Fin.addCases_left, Fin.addCases_right]
        | right i => simp only [selected i, ↓reduceIte]
      | right i => simp only [bank, RecursiveShiftRoleBank.common, Tapes.append, Fin.addCases_right]

/-- **A preparation on the role bank.** Any 47-tape preparation from the local bank of `hs` to the
local bank of `ch` runs on the role bank, changing the parent headers to `ch` only. -/
theorem view_hoare {s : ℕ} (M : Program 47 s prime) (roles : Tapes t prime)
    (hs ch : Fin 6 → List Bool) (st : Tapes 1 prime) (ws : Fin 5 → List Bool) (aux : Tapes u prime)
    (c : ℕ) (h : HoareTime M (fun x => x = localBank hs ws) (fun x => x = localBank ch ws) c) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports (commonPorts (t := t) (u := u))
        commonPorts_injective))
      (fun x => x = CleanSubbank.bank (bank roles hs st ((counters ws).append aux)))
      (fun x => x = CleanSubbank.bank (bank roles ch st ((counters ws).append aux))) c :=
  CleanSubbank.realizes M ports commonPorts ports_injective commonPorts_injective _ _ _ _ c
    ((local_payload hs ws).trans (common_payload roles hs st ws aux).symm)
    ((local_payload ch ws).trans (common_payload roles ch st ws aux).symm)
    (local_clean hs ws) (local_clean ch ws) (common_frame roles hs ch st ws aux) h

/-! ### The viewed atom action -/

open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Action Data transform actionSkeleton)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)

/-- The preparation as a skeleton on the role bank. -/
def viewSkeleton {s : ℕ} (M : Program 47 s prime) :
    SharedBankSkeleton.Skeleton (count t (5+u)) prime where
  tapes := count t (5+u)+47
  states := s
  program := Placement.placed M (CleanSubbank.placement ports (commonPorts (t := t) (u := u))
    commonPorts_injective)
  slots := Fin.castAdd 47
  slots_injective := Fin.castAdd_injective _ _

/-- Save the parent headers, prepare the view, act, restore. -/
def machine {s : ℕ} (M : Program 47 s prime) (act : Action t) :
    SharedBankSkeleton.Skeleton (count t (5+u)) prime :=
  SharedBankSkeleton.compose
    (SharedBankSkeleton.compose
      (SharedBankSkeleton.compose RecursiveViewFrameRoleBank.pushSkeleton (viewSkeleton M))
      (actionSkeleton act)) RecursiveViewFrameRoleBank.restoreSkeleton

private theorem action_slots (act : Action t) (i : Fin (count t (5+u))) :
    ((actionSkeleton (u := 5+u) act).slots i).val = i.val := by cases act <;> rfl

theorem action_hoare {v : Descriptor} (act : Action t) (hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes (5+u) prime) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (data : Data t v) :
    HoareTime (actionSkeleton (u := 5+u) act).program
      (fun w => w = raw (bank (roles data) hs st aux) (actionSkeleton (u := 5+u) act).tapes)
      (fun w => w = raw (bank (roles (transform act data)) hs st aux) (actionSkeleton (u := 5+u) act).tapes)
      (RecursiveViewedAction.cost v act) := by
  cases act with
  | shift wire r hd =>
    simpa only [actionSkeleton, RecursiveViewedAction.cost, bank, transform,
      SharedBankRawCompose.bank_eq_raw, RecursiveRoleSerialization.roles_update] using
      RecursiveShiftRoleBank.realizes r wire (roles data) hs (st.append aux) (data wire) rfl rfl hv hp
  | scale wire r hr target =>
    simpa only [actionSkeleton, RecursiveViewedAction.cost, bank, transform,
      SharedBankRawCompose.bank_eq_raw, RecursiveRoleSerialization.roles_update] using
      RecursiveScalingRoleBank.realizes hr target wire (roles data) hs (st.append aux) (data wire) rfl rfl hv hp

theorem roles_cast {v w : Descriptor} (he : volume prime w = volume prime v) (data : Data t v) :
    roles (fun wire => RecursiveAffineViews.array prime he (data wire)) = roles data := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext wire
    change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
        (List.ofFn (RecursiveAffineViews.array prime he (data wire)))) =
      FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0 (List.ofFn (data wire)))
    rw [RecursiveAffineViews.array_word]

/-- The acted array in the parent's type. -/
def array {v w : Descriptor} (he : volume prime w = volume prime v) (act : Action t)
    (data : Data t v) : Data t v := fun wire =>
  RecursiveAffineViews.array prime he.symm
    (transform act (fun x => RecursiveAffineViews.array prime he (data x)) wire)

/-- **The viewed atom action.** Given a preparation from the parent headers `hs` to headers `ch`
of a view `w` of the same volume, the machine runs the action on the view and returns the parent
bank with the acted payload. -/
theorem realizes {s : ℕ} (M : Program 47 s prime) (act : Action t) {v w : Descriptor}
    (he : volume prime w = volume prime v) (hs ch : Fin 6 → List Bool) (ws : Fin 5 → List Bool)
    (aux : Tapes u prime) (hw : RecursiveDimensionBank.Headers w ch) (hwp : w.Positive) (c : ℕ)
    (hM : HoareTime M (fun x => x = localBank hs ws) (fun x => x = localBank ch ws) c)
    (data : Data t v) :
    HoareTime (machine (u := u) M act).program
      (fun x => x = raw (bank (roles data) hs (SharedBank.empty 1 prime) ((counters ws).append aux))
        (machine (u := u) M act).tapes)
      (fun x => x = raw (bank (roles (array he act data)) hs (SharedBank.empty 1 prime)
        ((counters ws).append aux)) (machine (u := u) M act).tapes)
      (RecursiveViewFrame.pushCost hs+c+1+RecursiveViewedAction.cost w act+1+
        RecursiveViewFrame.restoreCost hs ch+1) := by
  let st := SharedBank.empty 1 prime
  let saved := RecursiveViewFrame.savedStack hs st
  let A := (counters ws).append aux
  have hpush := RecursiveViewFrameRoleBank.push_hoare (roles data) hs st A
  have hview := view_hoare M (roles data) hs ch saved ws aux c hM
  have hact := action_hoare (u := u) act ch saved A hw hwp
    (fun x => RecursiveAffineViews.array prime he (data x))
  have hrestore := RecursiveViewFrameRoleBank.restore_hoare
    (roles (transform act (fun x => RecursiveAffineViews.array prime he (data x)))) hs ch st A
    (RecursiveViewFrame.free_empty hs)
  simp only [SharedBankRawCompose.bank_eq_raw] at hpush hview hrestore
  rw [roles_cast he data] at hact
  have hfirst := SharedBankRawCompose.realizes
    (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := 5+u)) (viewSkeleton (t := t) (u := u) M)
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ hpush hview
  have hsecond := SharedBankRawCompose.realizes
    (SharedBankSkeleton.compose (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := 5+u))
      (viewSkeleton (t := t) (u := u) M))
    (actionSkeleton (u := 5+u) act) (fun _ => rfl) (action_slots act) _ _ _ _ _ hfirst hact
  have hthird := SharedBankRawCompose.realizes
    (SharedBankSkeleton.compose
      (SharedBankSkeleton.compose (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := 5+u))
        (viewSkeleton (t := t) (u := u) M))
      (actionSkeleton (u := 5+u) act)) (RecursiveViewFrameRoleBank.restoreSkeleton (t := t) (u := 5+u))
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ hsecond hrestore
  have hr : roles (transform act (fun x => RecursiveAffineViews.array prime he (data x))) =
      roles (array he act data) :=
    (roles_cast he.symm _).symm
  rw [hr] at hthird
  exact hthird

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomView
