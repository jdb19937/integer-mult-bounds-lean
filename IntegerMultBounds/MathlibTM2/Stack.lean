module

public import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.Ring.RingNF

/-!
# Structured stack programs with recursive procedures

A small imperative language over a finite family of stacks, with `while` loops and calls to a
finite table of (possibly recursive) procedures. Big-step semantics `Exec` carries an exact step
count. `Prog.machine` compiles a procedure table to a Mathlib `Turing.FinTM2`, and
`Exec.toOutputs` turns an execution of the main procedure into `Turing.TM2OutputsInTime` with
the same step count plus two.

The compiled machine has one extra stack, the return stack, whose symbols are continuation
labels. A call pushes its continuation and jumps; the shared return label pops a continuation
into an auxiliary state component and jumps to it.
-/

@[expose] public section

open Turing

namespace IntegerMultBounds.MathlibTM2.Stack

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- A store: the local state and the contents of every stack (head = top). -/
@[ext]
structure Store (Γ : K → Type) (σ : Type) where
  var : σ
  stk : ∀ k, List (Γ k)

/-- Straight-line stack code, executed by the machine in a single step. -/
inductive Action (Γ : K → Type) (σ : Type) where
  | done
  | push (k : K) (value : σ → Γ k) (next : Action Γ σ)
  | peek (k : K) (update : σ → Option (Γ k) → σ) (next : Action Γ σ)
  | pop (k : K) (update : σ → Option (Γ k) → σ) (next : Action Γ σ)
  | load (update : σ → σ) (next : Action Γ σ)
  | branch (test : σ → Bool) (yes no : Action Γ σ)

namespace Action

variable [DecidableEq K]

/-- The effect of an action on a store. -/
def run : Action Γ σ → Store Γ σ → Store Γ σ
  | .done, s => s
  | .push k f a, s => run a ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
  | .peek k f a, s => run a ⟨f s.var (s.stk k).head?, s.stk⟩
  | .pop k f a, s => run a ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .load f a, s => run a ⟨f s.var, s.stk⟩
  | .branch f a b, s => if f s.var then run a s else run b s

end Action

/-- Structured programs calling procedures named by `P`. -/
inductive Prog (P : Type) (Γ : K → Type) (σ : Type) where
  | act (a : Action Γ σ)
  | seq (p q : Prog P Γ σ)
  | cond (test : σ → Bool) (p q : Prog P Γ σ)
  | loop (test : σ → Bool) (body : Prog P Γ σ)
  | call (f : P)

variable {P P' : Type}

/-- Big-step semantics with exact step counts, relative to a procedure table `body`. -/
inductive Exec [DecidableEq K] (body : P → Prog P Γ σ) :
    Prog P Γ σ → Store Γ σ → ℕ → Store Γ σ → Prop
  | act (a : Action Γ σ) (s : Store Γ σ) : Exec body (.act a) s 1 (a.run s)
  | seq {p q s t u m n} : Exec body p s m t → Exec body q t n u → Exec body (.seq p q) s (m + n) u
  | cond_true {f p q s t n} : f s.var = true → Exec body p s n t →
      Exec body (.cond f p q) s (n + 1) t
  | cond_false {f p q s t n} : f s.var = false → Exec body q s n t →
      Exec body (.cond f p q) s (n + 1) t
  | loop_false {f p s} : f s.var = false → Exec body (.loop f p) s 1 s
  | loop_true {f p s t u m n} : f s.var = true → Exec body p s m t →
      Exec body (.loop f p) t n u → Exec body (.loop f p) s (m + n + 1) u
  | call {f s t n} : Exec body (body f) s n t → Exec body (.call f) s (n + 2) t

namespace Prog

/-- Control points of a program; each becomes one machine label. -/
def Labels : Prog P Γ σ → Type
  | .act _ => Unit
  | .seq p q => Labels p ⊕ Labels q
  | .cond _ p q => Unit ⊕ (Labels p ⊕ Labels q)
  | .loop _ p => Unit ⊕ Labels p
  | .call _ => Unit

instance instFintypeLabels : (p : Prog P Γ σ) → Fintype p.Labels
  | .act _ => inferInstanceAs (Fintype Unit)
  | .seq p q =>
      letI := instFintypeLabels p; letI := instFintypeLabels q
      inferInstanceAs (Fintype (p.Labels ⊕ q.Labels))
  | .cond _ p q =>
      letI := instFintypeLabels p; letI := instFintypeLabels q
      inferInstanceAs (Fintype (Unit ⊕ (p.Labels ⊕ q.Labels)))
  | .loop _ p =>
      letI := instFintypeLabels p
      inferInstanceAs (Fintype (Unit ⊕ p.Labels))
  | .call _ => inferInstanceAs (Fintype Unit)

/-- The entry control point. -/
def start : (p : Prog P Γ σ) → p.Labels
  | .act _ => ()
  | .seq p _ => .inl p.start
  | .cond _ _ _ => .inl ()
  | .loop _ _ => .inl ()
  | .call _ => ()

end Prog

/-! ### The compiled machine -/

/-- Machine labels: the entry point, the shared return point, and every control point of every
procedure body. -/
inductive Lbl (body : P → Prog P Γ σ) where
  | entry
  | ret
  | node (f : P) (l : (body f).Labels)

/-- Stack index of the compiled machine: `none` is the return stack. -/
abbrev MK (K : Type) := Option K

/-- Stack alphabets of the compiled machine. The return stack holds continuations, where `none`
means halt. -/
def MΓ (body : P → Prog P Γ σ) : MK K → Type
  | none => Option (Lbl body)
  | some k => Γ k

/-- Machine local state: the program state and the last popped continuation. -/
abbrev Mσ (body : P → Prog P Γ σ) := σ × Option (Option (Lbl body))

variable [DecidableEq K] {body : P → Prog P Γ σ}

namespace Lbl

/-- `Lbl body` as a sum type, for the `Fintype` instance. -/
def equivSum (body : P → Prog P Γ σ) :
    Lbl body ≃ Unit ⊕ Unit ⊕ (Σ f, (body f).Labels) where
  toFun
    | .entry => .inl ()
    | .ret => .inr (.inl ())
    | .node f l => .inr (.inr ⟨f, l⟩)
  invFun
    | .inl () => .entry
    | .inr (.inl ()) => .ret
    | .inr (.inr ⟨f, l⟩) => .node f l
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | ⟨f, l⟩ <;> rfl

instance [Fintype P] : Fintype (Lbl body) := Fintype.ofEquiv _ (equivSum body).symm

end Lbl

namespace Action

/-- An action lifted to the machine: it acts on the program state and leaves the auxiliary
component and the return stack alone. -/
def lift {Λ : Type} (exit : TM2.Stmt (MΓ body) Λ (Mσ body)) :
    Action Γ σ → TM2.Stmt (MΓ body) Λ (Mσ body)
  | .done => exit
  | .push k f a => .push (some k) (fun v => f v.1) (lift exit a)
  | .peek k f a => .peek (some k) (fun v x => (f v.1 x, v.2)) (lift exit a)
  | .pop k f a => .pop (some k) (fun v x => (f v.1 x, v.2)) (lift exit a)
  | .load f a => .load (fun v => (f v.1, v.2)) (lift exit a)
  | .branch f a b => .branch (fun v => f v.1) (lift exit a) (lift exit b)

end Action

/-- Machine stacks built from program stacks and a return stack. -/
def mstk (S : ∀ k, List (Γ k)) (R : List (Option (Lbl body))) : ∀ k : MK K, List (MΓ body k)
  | none => R
  | some k => S k

/-- Machine configuration at label `l`, program store `s`, auxiliary `x`, return stack `R`. -/
def cfg (l : Option (Lbl body)) (s : Store Γ σ) (x : Option (Option (Lbl body)))
    (R : List (Option (Lbl body))) : TM2.Cfg (MΓ body) (Lbl body) (Mσ body) :=
  ⟨l, (s.var, x), mstk s.stk R⟩

lemma mstk_update_some (S : ∀ k, List (Γ k)) (R : List (Option (Lbl body))) (k : K)
    (l : List (MΓ body (some k))) :
    Function.update (mstk (body := body) S R) (some k) l = mstk (Function.update S k l) R := by
  funext j
  rcases j with _ | j
  · rfl
  · by_cases h : j = k
    · subst h
      simp only [Function.update, mstk]
      simp
    · have h' : (some j : MK K) ≠ some k := fun e => h (Option.some_injective _ e)
      rw [Function.update_of_ne h']
      exact (Function.update_of_ne h l S).symm

lemma mstk_update_none (S : ∀ k, List (Γ k)) (R : List (Option (Lbl body)))
    (R' : List (MΓ body none)) :
    Function.update (mstk (body := body) S R) none R' = mstk S R' := by
  funext j
  rcases j with _ | j
  · rfl
  · rfl

namespace Action

lemma lift_stepAux {Λ : Type} (exit : TM2.Stmt (MΓ body) Λ (Mσ body)) (a : Action Γ σ)
    (s : Store Γ σ) (x : Option (Option (Lbl body))) (R : List (Option (Lbl body))) :
    TM2.stepAux (a.lift exit) (s.var, x) (mstk s.stk R) =
      TM2.stepAux exit ((a.run s).var, x) (mstk (a.run s).stk R) := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih =>
      simp only [lift, TM2.stepAux, run]
      rw [mstk_update_some]
      exact ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
  | peek k f a ih =>
      simp only [lift, TM2.stepAux, run]
      exact ih ⟨f s.var (s.stk k).head?, s.stk⟩
  | pop k f a ih =>
      simp only [lift, TM2.stepAux, run]
      rw [mstk_update_some]
      exact ih ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | load f a ih =>
      simp only [lift, TM2.stepAux, run]
      exact ih ⟨f s.var, s.stk⟩
  | branch f a b iha ihb =>
      simp only [lift, TM2.stepAux, run]
      cases f s.var <;> simp [iha, ihb]

end Action

/-- Jump to a continuation, halting on `none`. -/
def jump {Λ : Type} {Γ' : MK K → Type} {σ' : Type} : Option Λ → TM2.Stmt Γ' Λ σ'
  | none => .halt
  | some l => .goto (fun _ => l)

@[simp] lemma stepAux_jump {Λ : Type} {Γ' : MK K → Type} {σ' : Type} (l : Option Λ) (v : σ')
    (S : ∀ k, List (Γ' k)) : TM2.stepAux (jump l) v S = ⟨l, v, S⟩ := by
  cases l <;> rfl

namespace Prog

/-- Machine code for the control points of `p`, placed at labels `embed`, continuing at
`exit`. -/
def code (body : P → Prog P Γ σ) : (p : Prog P Γ σ) → (p.Labels → Lbl body) →
    Option (Lbl body) → p.Labels → TM2.Stmt (MΓ body) (Lbl body) (Mσ body)
  | .act a, _, exit, _ => a.lift (jump exit)
  | .seq p q, embed, _, .inl l => code body p (fun x => embed (.inl x)) (some (embed (.inr q.start))) l
  | .seq _ q, embed, exit, .inr l => code body q (fun x => embed (.inr x)) exit l
  | .cond f p q, embed, _, .inl _ => .branch (fun v => f v.1)
      (.goto fun _ => embed (.inr (.inl p.start))) (.goto fun _ => embed (.inr (.inr q.start)))
  | .cond _ p _, embed, exit, .inr (.inl l) => code body p (fun x => embed (.inr (.inl x))) exit l
  | .cond _ _ q, embed, exit, .inr (.inr l) => code body q (fun x => embed (.inr (.inr x))) exit l
  | .loop f p, embed, exit, .inl _ => .branch (fun v => f v.1)
      (.goto fun _ => embed (.inr p.start)) (jump exit)
  | .loop _ p, embed, _, .inr l => code body p (fun x => embed (.inr x)) (some (embed (.inl ()))) l
  | .call f, _, exit, _ =>
      .push none (fun _ => exit) (.goto fun _ => .node f (body f).start)

end Prog

/-- Is a popped return-stack value a label to jump to? -/
def isJump : Option (Option (Lbl body)) → Bool
  | some (some _) => true
  | _ => false

/-- The label to jump to after a return. -/
def retTarget : Option (Option (Lbl body)) → Lbl body
  | some (some l) => l
  | _ => .ret

/-- The whole machine's code. -/
def mcode (body : P → Prog P Γ σ) (main : P) : Lbl body → TM2.Stmt (MΓ body) (Lbl body) (Mσ body)
  | .entry => .push none (fun _ => none) (.goto fun _ => .node main (body main).start)
  | .ret => .pop none (fun v x => (v.1, x))
      (.branch (fun v => isJump v.2) (.goto fun v => retTarget v.2)
        (.load (fun v => (v.1, none)) .halt))
  | .node f l => Prog.code body (body f) (Lbl.node f) (some .ret) l

/-- `n` machine steps lead from `c` to `c'`. -/
def Reach {Λ σ' : Type} {Γ' : MK K → Type} (M : Λ → TM2.Stmt Γ' Λ σ') (c : TM2.Cfg Γ' Λ σ') (n : ℕ)
    (c' : TM2.Cfg Γ' Λ σ') : Prop :=
  (flip bind (TM2.step M))^[n] (some c) = some c'

namespace Reach

variable {Λ σ' : Type} {Γ' : MK K → Type} {M : Λ → TM2.Stmt Γ' Λ σ'}

lemma trans {c c' c'' : TM2.Cfg Γ' Λ σ'} {m n : ℕ} (h₁ : Reach M c m c') (h₂ : Reach M c' n c'') :
    Reach M c (m + n) c'' := by
  unfold Reach at *
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

lemma single {c c' : TM2.Cfg Γ' Λ σ'} (h : TM2.step M c = some c') : Reach M c 1 c' := by
  simp [Reach, flip, h]

end Reach

/-- Simulation: an execution of a subprogram whose code sits at `embed` runs on the machine in
exactly the same number of steps, for any auxiliary value and any return stack below. -/
theorem Exec.sim {main : P} {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ} (h : Exec body p s n t) :
    ∀ (embed : p.Labels → Lbl body) (exit : Option (Lbl body)),
      (∀ l, mcode body main (embed l) = Prog.code body p embed exit l) →
      ∀ x R, ∃ y, Reach (mcode body main) (cfg (some (embed p.start)) s x R) n (cfg exit t y R) := by
  induction h with
  | act a s =>
      intro embed exit hc x R
      refine ⟨x, Reach.single ?_⟩
      simp only [cfg, TM2.step, hc, Prog.code, Action.lift_stepAux, stepAux_jump]
  | @seq p q s t u m n _ _ ihp ihq =>
      intro embed exit hc x R
      obtain ⟨y, hy⟩ := ihp (fun l => embed (.inl l)) (some (embed (.inr q.start)))
        (fun l => hc (.inl l)) x R
      obtain ⟨z, hz⟩ := ihq (fun l => embed (.inr l)) exit (fun l => hc (.inr l)) y R
      exact ⟨z, hy.trans hz⟩
  | @cond_true f p q s t n hf _ ih =>
      intro embed exit hc x R
      obtain ⟨y, hy⟩ := ih (fun l => embed (.inr (.inl l))) exit (fun l => hc (.inr (.inl l))) x R
      refine ⟨y, Nat.add_comm n 1 ▸ (Reach.single ?_).trans hy⟩
      simp only [cfg, TM2.step]
      rw [hc]
      simp only [Prog.start, Prog.code, TM2.stepAux, hf]
      rfl
  | @cond_false f p q s t n hf _ ih =>
      intro embed exit hc x R
      obtain ⟨y, hy⟩ := ih (fun l => embed (.inr (.inr l))) exit (fun l => hc (.inr (.inr l))) x R
      refine ⟨y, Nat.add_comm n 1 ▸ (Reach.single ?_).trans hy⟩
      simp only [cfg, TM2.step]
      rw [hc]
      simp only [Prog.start, Prog.code, TM2.stepAux, hf]
      rfl
  | @loop_false f p s hf =>
      intro embed exit hc x R
      refine ⟨x, Reach.single ?_⟩
      simp only [cfg, TM2.step]
      rw [hc]
      simp only [Prog.start, Prog.code, TM2.stepAux, hf, stepAux_jump]
      rfl
  | @loop_true f p s t u m n hf _ _ ihp ihl =>
      intro embed exit hc x R
      obtain ⟨y, hy⟩ := ihp (fun l => embed (.inr l)) (some (embed (.inl ())))
        (fun l => hc (.inr l)) x R
      obtain ⟨z, hz⟩ := ihl embed exit hc y R
      refine ⟨z, ?_⟩
      have h₀ : Reach (mcode body main) (cfg (some (embed (Prog.loop f p).start)) s x R) 1
          (cfg (some (embed (.inr p.start))) s x R) := by
        apply Reach.single
        simp only [cfg, TM2.step]
        rw [hc]
        simp only [Prog.start, Prog.code, TM2.stepAux, hf]
        rfl
      have := h₀.trans (hy.trans hz)
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  | @call f s t n _ ih =>
      intro embed exit hc x R
      obtain ⟨y, hy⟩ := ih (Lbl.node f) (some .ret) (fun _ => rfl) x (exit :: R)
      have h₀ : Reach (mcode body main) (cfg (some (embed (Prog.call f).start)) s x R) 1
          (cfg (some (.node f (body f).start)) s x (exit :: R)) := by
        apply Reach.single
        simp only [cfg, TM2.step]
        rw [hc]
        simp only [Prog.code, TM2.stepAux]
        rw [show mstk (body := body) s.stk R none = R from rfl, mstk_update_none]
        rfl
      cases exit with
      | none =>
          refine ⟨none, ?_⟩
          have h₁ : Reach (mcode body main) (cfg (some .ret) t y (none :: R)) 1 (cfg none t none R) := by
            apply Reach.single
            simp only [cfg, TM2.step, mcode, TM2.stepAux]
            rw [show mstk (body := body) t.stk (none :: R) none = none :: R from rfl,
              mstk_update_none]
            rfl
          simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₀.trans (hy.trans h₁)
      | some l =>
          refine ⟨some (some l), ?_⟩
          have h₁ : Reach (mcode body main) (cfg (some .ret) t y (some l :: R)) 1
              (cfg (some l) t (some (some l)) R) := by
            apply Reach.single
            simp only [cfg, TM2.step, mcode, TM2.stepAux]
            rw [show mstk (body := body) t.stk (some l :: R) none = some l :: R from rfl,
              mstk_update_none]
            rfl
          simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₀.trans (hy.trans h₁)

/-- The procedure table run from `main`: one call of `main`, entered from the machine's entry
label, halting when `main` returns. -/
theorem Exec.run_main {main : P} {s t : Store Γ σ} {n : ℕ} (h : Exec body (body main) s n t) :
    Reach (mcode body main) (cfg (some .entry) s none []) (n + 2) (cfg none t none []) := by
  obtain ⟨y, hy⟩ := h.sim (main := main) (Lbl.node main) (some .ret) (fun _ => rfl) none [none]
  have h₀ : Reach (mcode body main) (cfg (some .entry) s none []) 1
      (cfg (some (.node main (body main).start)) s none [none]) := by
    apply Reach.single
    simp only [cfg, TM2.step, mcode, TM2.stepAux]
    rw [show mstk (body := body) s.stk [] none = [] from rfl, mstk_update_none]
    rfl
  have h₁ : Reach (mcode body main) (cfg (some .ret) t y [none]) 1 (cfg none t none []) := by
    apply Reach.single
    simp only [cfg, TM2.step, mcode, TM2.stepAux]
    rw [show mstk (body := body) t.stk [none] none = [none] from rfl, mstk_update_none]
    rfl
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₀.trans (hy.trans h₁)

/-! ### Reasoning about loops and sequences -/

/-- Rewrite the step count and final store of an execution. -/
theorem Exec.cast {body : P' → Prog P' Γ σ} {p : Prog P' Γ σ} {s t t' : Store Γ σ} {n n' : ℕ}
    (h : Exec body p s n t) (hn : n = n') (ht : t = t') : Exec body p s n' t' := hn ▸ ht ▸ h

/-- The sequence of a list of programs, ending with a no-op. -/
def Prog.seqList : List (Prog P' Γ σ) → Prog P' Γ σ
  | [] => .act .done
  | p :: ps => .seq p (seqList ps)

/-! ### Packaging as a Mathlib `FinTM2` -/

/-- The store with local state `v`, the list `l` on stack `k`, and every other stack empty. -/
def Store.only (v : σ) (k : K) (l : List (Γ k)) : Store Γ σ :=
  ⟨v, fun j => if h : j = k then (by subst h; exact l) else []⟩

section Package

variable [Fintype K] [Fintype P] [Fintype σ]

/-- The compiled machine of a procedure table, started at `main`, reading stack `kin` and
writing stack `kout`. -/
def machine (body : P → Prog P Γ σ) (main : P) (kin kout : K) (σ₀ : σ)
    [Fintype (Γ kin)] : FinTM2 where
  K := MK K
  k₀ := some kin
  k₁ := some kout
  Γ := MΓ body
  Λ := Lbl body
  main := .entry
  σ := Mσ body
  initialState := (σ₀, none)
  Γk₀Fin := inferInstanceAs (Fintype (Γ kin))
  m := mcode body main

variable (main : P) (kin kout : K) (σ₀ : σ) [Fintype (Γ kin)]

lemma initList_machine (l : List (Γ kin)) :
    initList (machine body main kin kout σ₀) l =
      cfg (some .entry) (Store.only σ₀ kin l) none [] := by
  simp only [initList, cfg, machine, Store.only]
  congr 1
  funext j
  rcases j with _ | j
  · rfl
  · by_cases h : j = kin
    · subst h; simp [mstk]; rfl
    · have h' : (some j : MK K) ≠ some kin := fun e => h (Option.some_injective _ e)
      simp [mstk, h, h']; rfl

lemma haltList_machine (l : List (Γ kout)) :
    haltList (machine body main kin kout σ₀) l = cfg none (Store.only σ₀ kout l) none [] := by
  simp only [haltList, cfg, machine, Store.only]
  congr 1
  funext j
  rcases j with _ | j
  · rfl
  · by_cases h : j = kout
    · subst h; simp [mstk]; rfl
    · have h' : (some j : MK K) ≠ some kout := fun e => h (Option.some_injective _ e)
      simp [mstk, h, h']; rfl

/-- An execution of `main` from the input store to the output store is a run of the compiled
machine within any bound at least two more than its step count. -/
def Exec.toOutputs {input : List (Γ kin)} {output : List (Γ kout)} {n m : ℕ}
    (h : Exec body (body main) (Store.only σ₀ kin input) n (Store.only σ₀ kout output))
    (hm : n + 2 ≤ m) :
    TM2OutputsInTime (machine body main kin kout σ₀) input (some output) m :=
  ⟨⟨n + 2, by
    have := h.run_main
    simp only [Reach] at this
    simp only [FinTM2.step, Option.map, initList_machine, haltList_machine]
    exact this⟩, hm⟩

end Package

end IntegerMultBounds.MathlibTM2.Stack
