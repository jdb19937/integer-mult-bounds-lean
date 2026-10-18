module

public import IntegerMultBounds.MathlibTM2.DFT.MulCall

/-!
# Single host steps on the DFT machine

`pushSym_run` and `push_exec` (push one symbol), `peek_exec` (test whether a register is
nonempty, into the flag) and `update3_idem` (three register updates over three earlier ones),
used by the loops over a unary counter.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

lemma pushSym_run {T Q A : ℕ} {U : Type} (i : Fin T) (x : Fin (A + 4)) (v : HS T Q A U)
    (S : Stacks T A) :
    (Action.push (.rt i) (fun _ => x) .done : Act T Q A U).run (mk v S) =
      mk v { S with R := Function.update S.R i (x :: S.R i) } := by
  simp [Action.run, update_rt]

theorem update3_idem {α β : Type} [DecidableEq α] (R : α → β) {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (x y z x' y' z' : β) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update R a x) b y) c z) a x') b y') c z' =
      Function.update (Function.update (Function.update R a x') b y') c z' := by
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

theorem peek_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B)) (i : Fin (M.T + D))
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A) (gi go : List Γ') :
    Exec (M.tab D B main) (hostCode (.act (peekR i))) (dmk v S gi go) 1
      (dmk { v with flag := (S.R i).head?.isSome } S gi go) := by
  have := exec_hostCode (body' := M.tab D B main)
    (Exec.act (body := (Empty.elim : Empty → Pr Empty (M.T + D) M.Q M.A (M.U × B)))
      (peekR i : Act (M.T + D) M.Q M.A (M.U × B)) (Host.mk v S)) gi go
  rwa [peekR_run] at this

theorem push_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B)) (i : Fin (M.T + D))
    (x : Fin (M.A + 4)) (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (gi go : List Γ') :
    Exec (M.tab D B main) (hostCode (.act (.push (.rt i) (fun _ => x) .done))) (dmk v S gi go) 1
      (dmk v { S with R := Function.update S.R i (x :: S.R i) } gi go) := by
  have := exec_hostCode (body' := M.tab D B main)
    (Exec.act (body := (Empty.elim : Empty → Pr Empty (M.T + D) M.Q M.A (M.U × B)))
      (Action.push (.rt i) (fun _ => x) .done : Act (M.T + D) M.Q M.A (M.U × B)) (Host.mk v S))
    gi go
  rwa [pushSym_run] at this

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
