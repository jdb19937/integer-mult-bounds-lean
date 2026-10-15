module

public import IntegerMultBounds.Networks.FramedCircuit

/-! Checked frame bookkeeping for literal, interleaved edge and scalar events.
Validity uses frame labels, while execution uses their actual linear equivalences. -/
@[expose] public section
namespace IntegerMultBounds.Networks.FramedEventTrace

open FramedCircuit

/-- A literal event retains both endpoint labels or its scalar incidence label. -/
inductive Event (ι L R : Type*) where
  | edge (wire : ι) (old next : L)
  | gate (g : Circuit.Gate ι R) (label : L)
  | clear (wire : ι) (next : L)
  | copy (source target : ι) (label : L)

variable {ι L R E : Type*} [DecidableEq ι]

/-- Edges and explicit assignments update one recorded label; other scalar events retain it. -/
def after (current : ι → L) : Event ι L R → ι → L
  | .edge i _ next => Function.update current i next
  | .gate _ _ => current
  | .clear i next => Function.update current i next
  | .copy _ target label => Function.update current target label

def StepValid (current : ι → L) : Event ι L R → Prop
  | .edge i old _ => old = current i
  | .gate g label => ∀ i ∈ touched g, current i = label
  | .clear _ _ => True
  | .copy source _ label => current source = label

/-- Every old label and every touched scalar incidence is checked in event order. -/
def Valid : (ι → L) → List (Event ι L R) → Prop
  | _, [] => True
  | current, e :: es => StepValid current e ∧ Valid (after current e) es

instance [DecidableEq L] (current : ι → L) (e : Event ι L R) :
    Decidable (StepValid current e) := by
  cases e <;> unfold StepValid <;> infer_instance

instance [DecidableEq L] (current : ι → L) (es : List (Event ι L R)) :
    Decidable (Valid current es) := by
  induction es generalizing current with
  | nil => exact isTrue trivial
  | cons e es ih =>
    haveI := ih (after current e)
    unfold Valid
    infer_instance

def finalProfile : (ι → L) → List (Event ι L R) → ι → L
  | current, [] => current
  | current, e :: es => finalProfile (after current e) es

variable [CommRing R] [AddCommGroup E] [Module R E]

/-- An actual zero assignment, including its effect on previously dirty data. -/
def clearGate (wire : ι) : Circuit.Gate ι R := ⟨wire, [(wire, -1)]⟩

/-- An actual copy assignment reads both operands from the pre-gate state. -/
def copyGate (source target : ι) : Circuit.Gate ι R :=
  ⟨target, [(target, -1), (source, 1)]⟩

/-- Erasure preserves every scalar row, reset and copy in its original order. -/
def erase : List (Event ι L R) → Circuit.Program ι R
  | [] => []
  | .edge _ _ _ :: es => erase es
  | .gate g _ :: es => g :: erase es
  | .clear i _ :: es => clearGate i :: erase es
  | .copy source target _ :: es => copyGate source target :: erase es

/-- The source frame label denotes an actual invertible linear operator. -/
def instruction (frameOf : L → Frame R E) : Event ι L R → Instruction ι R E
  | .edge i old next => .edge i (frameOf old) (frameOf next)
  | .gate g _ => .gate g
  | .clear i _ => .gate (clearGate i)
  | .copy source target _ => .gate (copyGate source target)

def lower (frameOf : L → Frame R E) (es : List (Event ι L R)) :
    List (Instruction ι R E) := es.map (instruction frameOf)

/-- The existing edge/gate invariants justify a checked literal event. -/
theorem step_invariant (frameOf : L → Frame R E) (current : ι → L)
    (e : Event ι L R) (h : StepValid current e) (x : ι → E) :
    execute (instruction frameOf e) (encode (fun i => frameOf (current i)) x) =
      encode (fun i => frameOf (after current e i))
        (moduleRun (erase [e]) x) := by
  cases e with
  | edge i old next =>
    change old = current i at h
    subst old
    have hp : Function.update (fun j => frameOf (current j)) i (frameOf next) =
        (fun j => frameOf (Function.update current i next j)) := by
      funext j
      by_cases hj : j=i <;> simp [hj]
    simpa only [instruction, after, erase, moduleRun_nil, hp] using
      edge_invariant (fun j => frameOf (current j)) (frameOf next) i x
  | gate g label =>
    exact gate_invariant g (fun i => frameOf (current i)) (frameOf label)
      (fun i hi => congrArg frameOf (h i hi)) x
  | clear i next =>
    funext j
    by_cases hj : j = i
    · subst j
      simp [instruction, erase, execute, moduleRun, moduleGate, clearGate, encode, after]
    · simp [instruction, erase, execute, moduleRun, moduleGate, clearGate, encode,
        after, Function.update_of_ne hj]
  | copy source target label =>
    change current source = label at h
    funext j
    by_cases hj : j = target
    · subst j
      simp [instruction, erase, execute, moduleRun, moduleGate, copyGate, encode,
        after, h]
    · simp [instruction, erase, execute, moduleRun, moduleGate, copyGate, encode,
        after, Function.update_of_ne hj]

/-- A checked trace acts on logical values by precisely its erased scalar word. -/
theorem run_encode (frameOf : L → Frame R E) (current : ι → L)
    (es : List (Event ι L R)) (h : Valid current es) (x : ι → E) :
    run (lower frameOf es) (encode (fun i => frameOf (current i)) x) =
      encode (fun i => frameOf (finalProfile current es i)) (moduleRun (erase es) x) := by
  induction es generalizing current x with
  | nil => rfl
  | cons e es ih =>
    change run (lower frameOf es)
      (execute (instruction frameOf e) (encode (fun i => frameOf (current i)) x)) = _
    rw [step_invariant frameOf current e h.1, ih _ h.2]
    cases e <;> rfl

/-- Arbitrary stored values, including dirty scratch and spectators, are preserved
according to the exact final frame profile and scalar action. -/
theorem valid_run (frameOf : L → Frame R E) (current : ι → L)
    (es : List (Event ι L R)) (h : Valid current es) (stored : ι → E) :
    run (lower frameOf es) stored =
      encode (fun i => frameOf (finalProfile current es i))
        (moduleRun (erase es) (decode (fun i => frameOf (current i)) stored)) := by
  simpa only [encode_decode] using
    run_encode frameOf current es h (decode (fun i => frameOf (current i)) stored)

end IntegerMultBounds.Networks.FramedEventTrace
