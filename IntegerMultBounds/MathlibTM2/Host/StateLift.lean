module

public import IntegerMultBounds.MathlibTM2.Host.StateTransport
public import IntegerMultBounds.MathlibTM2.Host.Core

/-! Increase a host program's simulated state capacity without changing its stacks or image-state timing. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

variable {T Q Q' A : ℕ} {U P P' : Type}

/-- Project a target state back to the old capacity, defaulting to zero off the old range. -/
def stateLiftFinDown (hQ : 0<Q) (s : Fin Q') : Fin Q :=
  if h : s.val<Q then ⟨s.val,h⟩ else ⟨0,hQ⟩

@[simp] theorem stateLiftFinDown_cast (h : Q≤Q') (hQ : 0<Q) (s : Fin Q) :
    stateLiftFinDown hQ (Fin.castLE h s)=s := by
  simp [stateLiftFinDown]

/-- Embed both the current and pending transition states, preserving all other local fields. -/
def stateLiftUp (h : Q≤Q') (v : HS T Q A U) : HS T Q' A U where
  flag := v.flag
  sym := v.sym
  st := Fin.castLE h v.st
  scan := v.scan
  nxt := v.nxt.map fun p => (Fin.castLE h p.1,p.2)
  user := v.user

def stateLiftDown (hQ : 0<Q) (v : HS T Q' A U) : HS T Q A U where
  flag := v.flag
  sym := v.sym
  st := stateLiftFinDown hQ v.st
  scan := v.scan
  nxt := v.nxt.map fun p => (stateLiftFinDown hQ p.1,p.2)
  user := v.user

@[simp] theorem stateLiftUp_user (h : Q≤Q') (v : HS T Q A U) : (stateLiftUp h v).user=v.user := rfl
@[simp] theorem stateLiftDown_user (hQ : 0<Q) (v : HS T Q' A U) : (stateLiftDown hQ v).user=v.user := rfl

/-- The state projection is a retraction on the embedded old host states. -/
theorem stateLiftDown_up (h : Q≤Q') (hQ : 0<Q) :
    Function.LeftInverse (stateLiftDown (T:=T) (A:=A) (U:=U) hQ) (stateLiftUp h) := by
  intro v
  cases v with
  | mk flag sym st scan nxt user =>
    cases nxt with
    | none => simp [stateLiftUp,stateLiftDown]
    | some p => simp [stateLiftUp,stateLiftDown]

/-- Capacity transport for a host action. -/
def stateLiftAct (h : Q≤Q') (hQ : 0<Q) : Act T Q A U → Act T Q' A U :=
  stateMapAct (stateLiftUp h) (stateLiftDown hQ)

/-- Capacity transport for a host program, with optional procedure-name embedding. -/
def stateLiftPr (h : Q≤Q') (hQ : 0<Q) (ι : P → P') : Pr P T Q A U → Pr P' T Q' A U :=
  stateMapProg (stateLiftUp h) (stateLiftDown hQ) ι

def stateLiftNormalize (h : Q≤Q') (hQ : 0<Q) : Pr P' T Q' A U :=
  stateNormalize (stateLiftUp h) (stateLiftDown hQ)

/-- A lifted execution has the same exact step count and the same complete stack frame. -/
theorem stateLift_exec (h : Q≤Q') (hQ : 0<Q) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T Q' A U}
    (hbody : ∀ f,body' (ι f)=stateLiftPr h hQ ι (body f))
    {p : Pr P T Q A U} {v w : HS T Q A U} {S S' : Stacks T A} {n : ℕ}
    (he : Exec body p (mk v S) n (mk w S')) :
    Exec body' (stateLiftPr h hQ ι p) (mk (stateLiftUp h v) S) n (mk (stateLiftUp h w) S') :=
  stateMap_exec (stateLiftUp h) (stateLiftDown hQ) (stateLiftDown_up h hQ) ι hbody he

/-- Arbitrary target states can enter an old program after one charged normalization step. -/
theorem stateLift_exec_normalized (h : Q≤Q') (hQ : 0<Q) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T Q' A U}
    (hbody : ∀ f,body' (ι f)=stateLiftPr h hQ ι (body f))
    {p : Pr P T Q A U} (v : HS T Q' A U) {w : HS T Q A U} {S S' : Stacks T A} {n : ℕ}
    (he : Exec body p (mk (stateLiftDown hQ v) S) n (mk w S')) :
    Exec body' (.seq (stateLiftNormalize h hQ) (stateLiftPr h hQ ι p))
      (mk v S) (1+n) (mk (stateLiftUp h w) S') :=
  stateMap_exec_normalized (stateLiftUp h) (stateLiftDown hQ) (stateLiftDown_up h hQ) ι hbody (mk v S) he

end IntegerMultBounds.MathlibTM2.Host
