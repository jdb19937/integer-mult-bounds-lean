module

public import IntegerMultBounds.MathlibTM2.Fast.MainProg

/-!
# Stack sizes along an execution, the cleanup and the reset

`mnSize s` is the total number of symbols on the stacks of a store. One run of an action pushes
at most `mnActPush a` symbols (`mn_act_size`), so an execution of `m` steps whose actions and
procedure bodies push at most `c` symbols each ends with at most `mnSize s + c m` symbols
(`mn_exec_size`): every executed action costs one step. `mnPushC body` bounds the push count of
every procedure body (`mn_progPush_le_pushC`). On host stores the registers hold at most
`mnSize` symbols (`mn_sumR_le_size`).

`mn_clear_exec`: the cleanup `mnClear` empties every register in
`2 ∑ |R i| + 2 mnT + 1` steps. `mn_reset_exec`: `mnReset` sets the local state to `mnV₀` in one
step.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

set_option linter.unusedSimpArgs false

/-! ### Stack sizes -/

section Size

variable {K' : Type} {Γ : K' → Type} {σ' P' : Type}

/-- The total number of symbols on the stacks of a store. -/
def mnSize [Fintype K'] (s : Store Γ σ') : ℕ := ∑ k, (s.stk k).length

variable [DecidableEq K'] [Fintype K']

/-- The size after replacing one stack. -/
lemma mn_size_update (s : Store Γ σ') (v : σ') (k : K') (l : List (Γ k)) :
    mnSize (⟨v, Function.update s.stk k l⟩ : Store Γ σ') + (s.stk k).length =
      mnSize s + l.length := by
  unfold mnSize
  have e : (fun j => (Function.update s.stk k l j).length) =
      Function.update (fun j => (s.stk j).length) k l.length := by
    funext j
    by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  simp only
  rw [e, Finset.sum_update_of_mem (Finset.mem_univ k)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

/-- One run of an action pushes at most `mnActPush a` symbols. -/
theorem mn_act_size (a : Action Γ σ') (s : Store Γ σ') :
    mnSize (a.run s) ≤ mnSize s + mnActPush a := by
  induction a generalizing s with
  | done => simp [Action.run, mnActPush]
  | push k f a ih =>
      have h1 := ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
      have h2 := mn_size_update s s.var k (f s.var :: s.stk k)
      simp only [Action.run, mnActPush]
      simp only [List.length_cons] at h2
      omega
  | peek k f a ih =>
      have h1 := ih ⟨f s.var (s.stk k).head?, s.stk⟩
      simp only [Action.run, mnActPush]
      exact h1
  | pop k f a ih =>
      have h1 := ih ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
      have h2 := mn_size_update s (f s.var (s.stk k).head?) k (s.stk k).tail
      have h3 : (s.stk k).tail.length ≤ (s.stk k).length := by simp
      simp only [Action.run, mnActPush]
      omega
  | load f a ih =>
      have h1 := ih ⟨f s.var, s.stk⟩
      simp only [Action.run, mnActPush]
      exact h1
  | branch f a b iha ihb =>
      simp only [Action.run, mnActPush]
      split
      · exact (iha s).trans (by have := le_max_left (mnActPush a) (mnActPush b); omega)
      · exact (ihb s).trans (by have := le_max_right (mnActPush a) (mnActPush b); omega)

/-- **Sizes along an execution.** If every action of the program and of the procedure bodies
pushes at most `c` symbols, an execution of `m` steps adds at most `c m` symbols. -/
theorem mn_exec_size {body : P' → Prog P' Γ σ'} {p : Prog P' Γ σ'} {s t : Store Γ σ'} {m c : ℕ}
    (h : Exec body p s m t) (hp : mnProgPush p ≤ c) (hb : ∀ f, mnProgPush (body f) ≤ c) :
    mnSize t ≤ mnSize s + c * m := by
  induction h with
  | act a s =>
      have := mn_act_size a s
      simp only [mnProgPush] at hp
      nlinarith
  | seq _ _ ih₁ ih₂ =>
      simp only [mnProgPush, max_le_iff] at hp
      have h1 := ih₁ hp.1
      have h2 := ih₂ hp.2
      nlinarith
  | cond_true _ _ ih =>
      simp only [mnProgPush, max_le_iff] at hp
      have h1 := ih hp.1
      nlinarith
  | cond_false _ _ ih =>
      simp only [mnProgPush, max_le_iff] at hp
      have h1 := ih hp.2
      nlinarith
  | loop_false _ => nlinarith
  | loop_true _ _ _ ih₁ ih₂ =>
      have h1 := ih₁ (by simpa only [mnProgPush] using hp)
      have h2 := ih₂ hp
      nlinarith
  | @call f _ _ _ _ ih =>
      have h1 := ih (hb f)
      nlinarith

omit [DecidableEq K'] [Fintype K'] in
/-- `mnPushC body` bounds the push count of every procedure body. -/
theorem mn_progPush_le_pushC [Fintype P'] (body : P' → Prog P' Γ σ') (f : P') :
    mnProgPush (body f) ≤ mnPushC body :=
  Finset.le_sup (f := fun f => mnProgPush (body f)) (Finset.mem_univ f)

end Size

/-! ### Host stores -/

section Host

variable {T Q A : ℕ} {U : Type}

/-- The registers of a host store hold at most `mnSize` symbols. -/
theorem mn_sumR_le_size (v : HS T Q A U) (S : Stacks T A) :
    ∑ i, (S.R i).length ≤ mnSize (mk v S) := by
  unfold mnSize
  have e : ∑ i, (S.R i).length = ∑ k ∈ Finset.univ.map ⟨HK.rt, fun _ _ h => HK.rt.inj h⟩,
      ((mk v S).stk k).length := by
    rw [Finset.sum_map]
    rfl
  rw [e]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end Host

/-! ### The cleanup and the reset -/

section ClearGen

variable {T Q A : ℕ} {U P : Type}

/-- Emptying the registers of a nodup list `l`, in `∑ (2 |R i| + 2) + 1` steps. -/
theorem mn_clearList_exec (body : P → Pr P T Q A U) :
    ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      ∃ v', Exec body (Prog.seqList (l.map emptyR)) (mk v S)
        ((l.map fun i => 2 * (S.R i).length + 2).sum + 1)
        (mk v' { S with R := fun k => if k ∈ l then [] else S.R k })
  | [], _, v, S => by
      refine ⟨v, Exec.cast (Exec.act (body := body) .done (mk v S)) (by simp) ?_⟩
      rfl
  | i :: l, hnd, v, S => by
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, -, he₁⟩ := emptyR_exec body i v S
      obtain ⟨v₂, he₂⟩ := mn_clearList_exec body l hnd.2 v₁
        { S with R := Function.update S.R i [] }
      refine ⟨v₂, Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
      · have e : (l.map fun j => 2 * (Function.update S.R i [] j).length + 2) =
            l.map fun j => 2 * (S.R j).length + 2 := by
          refine List.map_congr_left fun j hj => ?_
          rw [Function.update_of_ne (fun h => hnd.1 (by rw [← h]; exact hj))]
        simp only [List.map_cons, List.sum_cons, List.map_map]
        rw [e]
        ring
      · congr 2
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk, Function.update_of_ne hk]

/-- Emptying every register, in `2 ∑ |R i| + 2 T + 1` steps. -/
theorem mn_clearAll_exec (body : P → Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', Exec body (Prog.seqList ((List.finRange T).map emptyR)) (mk v S)
      (2 * ∑ i, (S.R i).length + 2 * T + 1) (mk v' { S with R := fun _ => [] }) := by
  obtain ⟨v', he⟩ := mn_clearList_exec body (List.finRange T) (List.nodup_finRange T) v S
  have e1 : ((List.finRange T).map fun i => 2 * (S.R i).length + 2).sum =
      2 * ∑ i, (S.R i).length + 2 * T := by
    rw [← Fin.sum_univ_def, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm T 2]
  have e2 : (fun k => if k ∈ List.finRange T then [] else S.R k) =
      fun _ => ([] : List (Fin (A + 4))) := by
    funext k
    exact ite_eq_left (List.mem_finRange k)
  rw [e1, e2] at he
  exact ⟨v', he⟩

end ClearGen

section Clear

variable {A : ℕ}

attribute [local irreducible] mnT mnQ

/-- **The cleanup** empties every register in `2 ∑ |R i| + 2 mnT + 1` steps. -/
theorem mn_clear_exec (body : MnProc → MnPr A) (v : HS mnT mnQ A Unit) (S : Stacks mnT A) :
    ∃ v', Exec body mnClear (mk v S) (2 * ∑ i, (S.R i).length + 2 * mnT + 1)
      (mk v' { S with R := fun _ => [] }) := by
  unfold mnClear
  exact mn_clearAll_exec body v S

/-- **The reset** sets the local state to `mnV₀` in one step. -/
theorem mn_reset_exec (body : MnProc → MnPr A) (v : HS mnT mnQ A Unit) (S : Stacks mnT A) :
    Exec body mnReset (mk v S) 1 (mk mnV₀ S) :=
  Exec.act (body := body) _ (mk v S)

end Clear

end IntegerMultBounds.MathlibTM2.Fast.Main
