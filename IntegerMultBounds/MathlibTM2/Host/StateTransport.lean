module

public import IntegerMultBounds.MathlibTM2.Host.Core

/-! Exact stack-program transport along a local-state injection with a retraction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack

variable {K : Type} {Γ : K → Type} {σ σ' P P' : Type}

/-- Embed only the local state; every stack remains literally unchanged. -/
def stateMapStore (up : σ → σ') (s : Store Γ σ) : Store Γ σ' := ⟨up s.var,s.stk⟩

def stateMapAct (up : σ → σ') (down : σ' → σ) : Action Γ σ → Action Γ σ'
  | .done => .done
  | .push k f a => .push k (fun v => f (down v)) (stateMapAct up down a)
  | .peek k f a => .peek k (fun v o => up (f (down v) o)) (stateMapAct up down a)
  | .pop k f a => .pop k (fun v o => up (f (down v) o)) (stateMapAct up down a)
  | .load f a => .load (fun v => up (f (down v))) (stateMapAct up down a)
  | .branch f a b => .branch (fun v => f (down v)) (stateMapAct up down a) (stateMapAct up down b)

def stateMapProg (up : σ → σ') (down : σ' → σ) (ι : P → P') : Prog P Γ σ → Prog P' Γ σ'
  | .act a => .act (stateMapAct up down a)
  | .seq p q => .seq (stateMapProg up down ι p) (stateMapProg up down ι q)
  | .cond f p q => .cond (fun v => f (down v)) (stateMapProg up down ι p) (stateMapProg up down ι q)
  | .loop f p => .loop (fun v => f (down v)) (stateMapProg up down ι p)
  | .call f => .call (ι f)

variable [DecidableEq K]

theorem stateMapAct_run (up : σ → σ') (down : σ' → σ) (h : Function.LeftInverse down up)
    (a : Action Γ σ) (s : Store Γ σ) :
    (stateMapAct up down a).run (stateMapStore up s)=stateMapStore up (a.run s) := by
  have hdu (v : σ) : down (up v)=v := h v
  induction a generalizing s with
  | done => rfl
  | push k f a ih =>
    simp only [stateMapAct,stateMapStore,Action.run,hdu]
    exact ih ⟨s.var,Function.update s.stk k (f s.var::s.stk k)⟩
  | peek k f a ih =>
    simp only [stateMapAct,stateMapStore,Action.run,hdu]
    exact ih ⟨_,_⟩
  | pop k f a ih =>
    simp only [stateMapAct,stateMapStore,Action.run,hdu]
    exact ih ⟨_,_⟩
  | load f a ih =>
    simp only [stateMapAct,stateMapStore,Action.run,hdu]
    exact ih ⟨_,_⟩
  | branch f a b iha ihb =>
    simp only [stateMapAct,stateMapStore,Action.run,hdu]
    cases hf : f s.var
    · simpa only [hf,Bool.false_eq_true,ite_false,stateMapStore] using ihb s
    · simpa only [hf,ite_true,stateMapStore] using iha s

/-- The complete recursive execution retains its exact step count. -/
theorem stateMap_exec (up : σ → σ') (down : σ' → σ) (h : Function.LeftInverse down up)
    (ι : P → P') {body : P → Prog P Γ σ} {body' : P' → Prog P' Γ σ'}
    (hbody : ∀ f,body' (ι f)=stateMapProg up down ι (body f))
    {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ} (he : Exec body p s n t) :
    Exec body' (stateMapProg up down ι p) (stateMapStore up s) n (stateMapStore up t) := by
  have hdu (v : σ) : down (up v)=v := h v
  induction he with
  | act a s =>
    have ha := Exec.act (body:=body') (stateMapAct up down a) (stateMapStore up s)
    rwa [stateMapAct_run up down h] at ha
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | cond_true hf _ ih => exact .cond_true (by simpa only [stateMapStore,hdu] using hf) ih
  | cond_false hf _ ih => exact .cond_false (by simpa only [stateMapStore,hdu] using hf) ih
  | loop_false hf => exact .loop_false (by simpa only [stateMapStore,hdu] using hf)
  | loop_true hf _ _ ih₁ ih₂ => exact .loop_true (by simpa only [stateMapStore,hdu] using hf) ih₁ ih₂
  | call _ ih => exact .call (by rw [hbody]; exact ih)

/-- Normalize an arbitrary target local state into the embedded image in one host step. -/
def stateNormalize (up : σ → σ') (down : σ' → σ) : Prog P' Γ σ' :=
  .act (.load (fun v => up (down v)) .done)

theorem stateMap_exec_normalized (up : σ → σ') (down : σ' → σ)
    (h : Function.LeftInverse down up) (ι : P → P')
    {body : P → Prog P Γ σ} {body' : P' → Prog P' Γ σ'}
    (hbody : ∀ f,body' (ι f)=stateMapProg up down ι (body f))
    {p : Prog P Γ σ} (s : Store Γ σ') {t : Store Γ σ} {n : ℕ}
    (he : Exec body p ⟨down s.var,s.stk⟩ n t) :
    Exec body' (.seq (stateNormalize up down) (stateMapProg up down ι p)) s (1+n)
      (stateMapStore up t) :=
  .seq (Exec.act (body:=body') (.load (fun v => up (down v)) .done) s)
    (stateMap_exec up down h ι hbody he)

end IntegerMultBounds.MathlibTM2.Host
