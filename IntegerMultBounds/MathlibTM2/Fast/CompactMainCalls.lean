module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainLayer

/-! Changing the main entry leaves executions restricted to layer procedures unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
noncomputable section

/-- Every syntactic call targets the specified procedure set. -/
def callsWithin {I : Type} {Γ : I → Type} {V P : Type} (allowed : P → Prop) : Prog P Γ V → Prop
  | .act _ => True
  | .seq p q => callsWithin allowed p ∧ callsWithin allowed q
  | .cond _ p q => callsWithin allowed p ∧ callsWithin allowed q
  | .loop _ p => callsWithin allowed p
  | .call f => allowed f

/-- A program without calls calls only allowed procedures. -/
theorem callsWithin_of_noCalls {I : Type} {Γ : I → Type} {V P : Type} (allowed : P → Prop)
    (p : Prog P Γ V) (h : Host.WordCmd.NoCalls p) : callsWithin allowed p := by
  induction p with
  | act _ => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | cond _ _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | loop _ _ ih => exact ih h
  | call _ => exact h.elim

/-- A closed procedure subset suffices to transport exact execution between tables. -/
theorem exec_of_callsWithin {I : Type} [DecidableEq I] {Γ : I → Type} {V P : Type}
    {body body' : P → Prog P Γ V} (allowed : P → Prop)
    (hbody : ∀ f,allowed f → body' f=body f)
    (hclosed : ∀ f,allowed f → callsWithin allowed (body f))
    {p : Prog P Γ V} {s t : Store Γ V} {n : ℕ}
    (h : Exec body p s n t) (hp : callsWithin allowed p) : Exec body' p s n t := by
  induction h with
  | act a s => exact Exec.act a s
  | seq h₁ h₂ ih₁ ih₂ => exact (ih₁ hp.1).seq (ih₂ hp.2)
  | cond_true hf h ih => exact Exec.cond_true hf (ih hp.1)
  | cond_false hf h ih => exact Exec.cond_false hf (ih hp.2)
  | loop_false hf => exact Exec.loop_false hf
  | loop_true hf h₁ h₂ ih₁ ih₂ => exact Exec.loop_true hf (ih₁ hp) (ih₂ hp)
  | @call f s t n h ih =>
    apply Exec.call
    rw [hbody f hp]
    exact ih (hclosed f hp)

lemma callsWithin_embProg {T T' Q A : ℕ} {U P P' : Type}
    (e : Fin T → Fin T') (ι : P → P') (allowed : P' → Prop) (hι : ∀ f,allowed (ι f))
    (p : Pr P T Q A U) : callsWithin allowed (embProg e ι p) := by
  induction p with
  | act _ => trivial
  | seq p q hp hq => exact ⟨hp,hq⟩
  | cond f p q hp hq => exact ⟨hp,hq⟩
  | loop f p hp => exact hp
  | call f => exact hι f

lemma callsWithin_embProg_iff {T T' Q A : ℕ} {U P P' : Type}
    (e : Fin T → Fin T') (ι : P → P') (allowed : P' → Prop) (p : Pr P T Q A U) :
    callsWithin allowed (embProg e ι p) ↔ callsWithin (allowed ∘ ι) p := by
  induction p with
  | act _ => rfl
  | seq p q hp hq => exact and_congr hp hq
  | cond f p q hp hq => exact and_congr hp hq
  | loop f p hp => exact hp
  | call f => rfl

lemma callsWithin_stateLiftPr_iff {T Q Q' A : ℕ} {U P P' : Type}
    (h : Q≤Q') (hQ : 0<Q) (ι : P → P') (allowed : P' → Prop) (p : Pr P T Q A U) :
    callsWithin allowed (stateLiftPr h hQ ι p) ↔ callsWithin (allowed ∘ ι) p := by
  induction p with
  | act _ => rfl
  | seq p q hp hq => exact and_congr hp hq
  | cond f p q hp hq => exact and_congr hp hq
  | loop f p hp => exact hp
  | call f => rfl


end
end IntegerMultBounds.MathlibTM2.Fast.Main
