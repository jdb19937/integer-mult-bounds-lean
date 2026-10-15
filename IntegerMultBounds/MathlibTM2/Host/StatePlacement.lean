module

public import IntegerMultBounds.MathlibTM2.Host.StateLift
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Combined state-capacity and register placement with an exact full-stack frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
variable {T T' Q Q' A : ℕ} {U P P' : Type}

def statePlacedPr (e : Fin T → Fin T') (h : Q≤Q') (hQ : 0<Q) (ι : P → P')
    (p : Pr P T Q A U) : Pr P' T' Q' A U :=
  embProg e ι (stateLiftPr h hQ id p)

/-- Normalize the old-state projection before running a placed old program. -/
def statePlacedNormalized (e : Fin T → Fin T') (h : Q≤Q') (hQ : 0<Q) (ι : P → P')
    (p : Pr P T Q A U) : Pr P' T' Q' A U :=
  embProg e ι (.seq (stateLiftNormalize h hQ) (stateLiftPr h hQ id p))

/-- Image-state execution retains exact time, with all off-image stacks unchanged. -/
theorem statePlaced_exec (e : Fin T → Fin T') (he : Function.Injective e)
    (h : Q≤Q') (hQ : 0<Q) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q' A U}
    (hbody : ∀ f,body' (ι f)=statePlacedPr e h hQ ι (body f))
    {p : Pr P T Q A U} {v₀ w : HS T Q A U} {S₀ S₁ : Stacks T A} {n : ℕ}
    (hrun : Exec body p (mk v₀ S₀) n (mk w S₁))
    (v : HS T' Q' A U) (hv : embDn e v=stateLiftUp h v₀)
    (S : Stacks T' A) (hS : embStk e S=S₀) :
    ∃ v',embDn e v'=stateLiftUp h w ∧ v'.user=w.user ∧
      Exec body' (statePlacedPr e h hQ ι p) (mk v S) n (mk v' (embOvr e S₁.get S)) := by
  have hlift := stateLift_exec h hQ id
    (body':=fun f => stateLiftPr h hQ id (body f)) (fun _ => rfl) hrun
  exact exec_emb_ovr he hbody hlift v hv S hS

/-- Arbitrary target states incur exactly one normalization step before the old execution. -/
theorem statePlaced_exec_normalized (e : Fin T → Fin T') (he : Function.Injective e)
    (h : Q≤Q') (hQ : 0<Q) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q' A U}
    (hbody : ∀ f,body' (ι f)=statePlacedPr e h hQ ι (body f))
    {p : Pr P T Q A U} (v : HS T' Q' A U) (S : Stacks T' A)
    {w : HS T Q A U} {S₁ : Stacks T A} {n : ℕ}
    (hrun : Exec body p (mk (stateLiftDown hQ (embDn e v)) (embStk e S)) n (mk w S₁)) :
    ∃ v',embDn e v'=stateLiftUp h w ∧ v'.user=w.user ∧
      Exec body' (statePlacedNormalized e h hQ ι p) (mk v S) (1+n) (mk v' (embOvr e S₁.get S)) := by
  have hlift := stateLift_exec_normalized h hQ id
    (body':=fun f => stateLiftPr h hQ id (body f)) (fun _ => rfl) (embDn e v) hrun
  exact exec_emb_ovr he hbody hlift v rfl S rfl

end IntegerMultBounds.MathlibTM2.Host
