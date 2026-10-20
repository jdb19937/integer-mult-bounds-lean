module

public import IntegerMultBounds.MathlibTM2.Host.Core
public import IntegerMultBounds.Machine.Hoare

/-!
# Calls to multitape subroutines

`foreign M` runs a multitape `IntegerMultBounds.Machine.Program T Q A` on the tape stacks, one
transition per loop iteration, and `foreign_exec` transfers a `HoareTime` contract of `M` to an
execution of `foreign M`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U : Type}

/-! ### Simulating a multitape program -/

/-- Read every scanned symbol and look up the transition. -/
def peekScan (M : Program T Q A) : Act T Q A U :=
  (List.finRange T).foldr
    (fun i acc => .peek (.rt i) (fun v o => { v with scan := Function.update v.scan i (o.getD blank) }) acc)
    (.load (fun v => { v with nxt := M.transition v.st v.scan }) .done)

/-- The symbol written on tape `i` by the pending transition. -/
def writeOf (i : Fin T) (v : HS T Q A U) : Fin (A + 4) := (v.nxt.map fun p => (p.2 i).1).getD blank

/-- The head move of tape `i` in the pending transition. -/
def moveOf (i : Fin T) (v : HS T Q A U) : Move := (v.nxt.map fun p => (p.2 i).2).getD .stay

/-- Apply the pending transition to tape `i`: write under the head and move. -/
def tapeAct (i : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v _ => v)
    (.branch (fun v => decide (moveOf i v = .right))
      (.push (.lt i) (writeOf i) .done)
      (.branch (fun v => decide (moveOf i v = .stay))
        (.push (.rt i) (writeOf i) .done)
        (.push (.rt i) (writeOf i)
          (.pop (.lt i) (fun v o => { v with sym := o })
            (.push (.rt i) (fun v => v.sym.getD blank) .done)))))

/-- Enter the pending transition's new state. -/
def setState : Act T Q A U := .load (fun v => { v with st := (v.nxt.map Prod.fst).getD v.st }) .done

/-- Stop the simulation loop. -/
def stopFlag : Act T Q A U := .load (fun v => { v with flag := false }) .done

/-- One simulated transition, or detection of halting. -/
def simIter {P : Type} (M : Program T Q A) : Pr P T Q A U :=
  .seq (.act (peekScan M))
    (.cond (fun v => v.nxt.isSome)
      (Prog.seqList ((List.finRange T).map (fun i => .act (tapeAct i)) ++ [.act setState]))
      (.act stopFlag))

/-- Run `M` from its start state until it halts. -/
def foreign {P : Type} (M : Program T Q A) : Pr P T Q A U :=
  .seq (.act (.load (fun v => { v with flag := true, st := M.start }) .done)) (.loop (·.flag) (simIter M))


variable {P : Type} (body : P → Pr P T Q A U)

lemma peekScan_run_aux (M : Program T Q A) (S : Stacks T A) :
    ∀ (l : List (Fin T)) (v : HS T Q A U),
      (l.foldr (fun i acc => Action.peek (.rt i)
          (fun v o => { v with scan := Function.update v.scan i (o.getD blank) }) acc)
        (.load (fun v => { v with nxt := M.transition v.st v.scan }) .done) : Act T Q A U).run (mk v S) =
      mk { v with
          scan := fun i => if i ∈ l then (S.R i).head?.getD blank else v.scan i
          nxt := M.transition v.st (fun i => if i ∈ l then (S.R i).head?.getD blank else v.scan i) } S := by
  intro l
  induction l with
  | nil => intro v; simp [Action.run]
  | cons i rest ih =>
      intro v
      simp only [List.foldr_cons, Action.run, mk_var, mk_stk, get_rt, store_mk]
      rw [ih]
      have hscan : (fun j => if j ∈ rest then (S.R j).head?.getD blank
          else Function.update v.scan i ((S.R i).head?.getD blank) j) =
          (fun j => if j ∈ i :: rest then (S.R j).head?.getD blank else v.scan j) := by
        funext j
        by_cases h : j = i
        · subst h; split_ifs <;> simp_all
        · simp [h]
      simp only [hscan]

lemma peekScan_run (M : Program T Q A) (v : HS T Q A U) (S : Stacks T A) :
    (peekScan M : Act T Q A U).run (mk v S) =
      mk { v with
          scan := fun i => (S.R i).head?.getD blank
          nxt := M.transition v.st (fun i => (S.R i).head?.getD blank) } S := by
  simpa [peekScan] using peekScan_run_aux M S (List.finRange T) v

/-- New left stack of tape `i` under a transition's actions. -/
def newL (S : Stacks T A) (act : Fin T → Fin (A + 4) × Move) (i : Fin T) : List (Fin (A + 4)) :=
  (stepStacks blank (S.L i) (S.R i) (act i).1 (act i).2).1

/-- New right stack of tape `i` under a transition's actions. -/
def newR (S : Stacks T A) (act : Fin T → Fin (A + 4) × Move) (i : Fin T) : List (Fin (A + 4)) :=
  (stepStacks blank (S.L i) (S.R i) (act i).1 (act i).2).2

lemma tapeAct_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) {st' : Fin Q}
    {act : Fin T → Fin (A + 4) × Move} (hv : v.nxt = some (st', act)) :
    ∃ o, (tapeAct i : Act T Q A U).run (mk v S) =
      mk { v with sym := o } { S with
        L := Function.update S.L i (newL S act i)
        R := Function.update S.R i (newR S act i) } := by
  have hw : writeOf i v = (act i).1 := by simp [writeOf, hv]
  have hm : moveOf i v = (act i).2 := by simp [moveOf, hv]
  rcases hmv : (act i).2 with _ | _ | _
  · -- left
    refine ⟨(S.L i).head?, ?_⟩
    simp [tapeAct, Action.run, hw, hm, hmv, newL, newR, stepStacks, update_lt, update_rt]
  · refine ⟨v.sym, ?_⟩
    simp [tapeAct, Action.run, hw, hm, hmv, newL, newR, stepStacks, update_rt]
  · refine ⟨v.sym, ?_⟩
    simp [tapeAct, Action.run, hw, hm, hmv, newL, newR, stepStacks, update_lt, update_rt]

theorem tapes_exec {st' : Fin Q} {act : Fin T → Fin (A + 4) × Move} :
    ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A), v.nxt = some (st', act) →
    ∃ v', v'.user = v.user ∧ v'.flag = v.flag ∧ v'.st = st' ∧
      Exec body (Prog.seqList (l.map (fun i => Prog.act (tapeAct i)) ++ [Prog.act setState]))
        (mk v S) (l.length + 2)
        (mk v' { S with
          L := fun i => if i ∈ l then newL S act i else S.L i
          R := fun i => if i ∈ l then newR S act i else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S hv
      refine ⟨{ v with st := st' }, rfl, rfl, rfl, ?_⟩
      have hS : ({ S with
          L := fun i => if i ∈ ([] : List (Fin T)) then newL S act i else S.L i
          R := fun i => if i ∈ ([] : List (Fin T)) then newR S act i else S.R i } : Stacks T A) = S := by
        cases S; simp
      rw [hS]
      have h₁ : (setState : Act T Q A U).run (mk v S) = mk { v with st := st' } S := by
        simp [setState, Action.run, hv]
      have := Exec.seq (h₁ ▸ Exec.act (body := body) setState (mk v S))
        (Exec.act (body := body) .done (mk { v with st := st' } S))
      simpa [Prog.seqList] using this
  | cons i rest ih =>
      intro hnd v S hv
      rw [List.nodup_cons] at hnd
      obtain ⟨o, ho⟩ := tapeAct_run i v S hv
      obtain ⟨v', h₁, h₂, h₃, he⟩ := ih hnd.2 { v with sym := o }
        { S with
          L := Function.update S.L i (newL S act i)
          R := Function.update S.R i (newR S act i) } (by simpa using hv)
      refine ⟨v', h₁, h₂, h₃, Exec.cast (Exec.seq (ho ▸ Exec.act (body := body) (tapeAct i) (mk v S)) he)
        (by simp; ring) ?_⟩
      congr 1
      refine Stacks.ext rfl rfl ?_ ?_
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1, newL]
        · simp [hj, newL]
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1, newR]
        · simp [hj, newR]

lemma scan_eq {c : Config T Q A} {S : Stacks T A} (h : Rep c S.L S.R) :
    (fun i => (S.R i).head?.getD blank) = fun i => c.tape i (c.head i) := by
  funext i; rw [rep_scan h i]

/-- One loop body when the multitape program takes a transition. -/
theorem simIter_step (M : Program T Q A) {c : Config T Q A} {v : HS T Q A U} {S : Stacks T A}
    (hrep : Rep c S.L S.R) (hst : v.st = c.state) {st' : Fin Q} {act : Fin T → Fin (A + 4) × Move}
    (ht : M.transition c.state (fun i => c.tape i (c.head i)) = some (st', act)) :
    ∃ v', v'.user = v.user ∧ v'.flag = v.flag ∧ v'.st = st' ∧
      Exec body (simIter M) (mk v S) (T + 4)
        (mk v' { S with
          L := newL S act
          R := newR S act }) := by
  have hrun := peekScan_run M v S
  have ht' : M.transition v.st (fun i => c.tape i (c.head i)) = some (st', act) := by rw [hst]; exact ht
  rw [scan_eq hrep, ht'] at hrun
  obtain ⟨v', h₁, h₂, h₃, he⟩ := tapes_exec (body := body) (List.finRange T) (List.nodup_finRange T)
    { v with
      scan := fun i => c.tape i (c.head i)
      nxt := some (st', act) } S rfl
  refine ⟨v', h₁, h₂, h₃, ?_⟩
  have he' := Exec.cond_true (body := body) (f := fun v => v.nxt.isSome)
    (q := .act stopFlag) (by simp) he
  refine Exec.cast (Exec.seq (hrun ▸ Exec.act (body := body) (peekScan M) (mk v S)) he')
    (by simp; ring) ?_
  congr 1
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext j <;> simp [List.mem_finRange]

/-- One loop body when the multitape program has halted. -/
theorem simIter_halt (M : Program T Q A) {c : Config T Q A} {v : HS T Q A U} {S : Stacks T A}
    (hrep : Rep c S.L S.R) (hst : v.st = c.state)
    (ht : M.transition c.state (fun i => c.tape i (c.head i)) = none) :
    ∃ v', v'.user = v.user ∧ v'.flag = false ∧ v'.st = v.st ∧
      Exec body (simIter M) (mk v S) 3 (mk v' S) := by
  have hrun := peekScan_run M v S
  have ht' : M.transition v.st (fun i => c.tape i (c.head i)) = none := by rw [hst]; exact ht
  rw [scan_eq hrep, ht'] at hrun
  refine ⟨{ v with
      scan := fun i => c.tape i (c.head i)
      nxt := none
      flag := false }, rfl, rfl, rfl, ?_⟩
  have h₁ : (stopFlag : Act T Q A U).run (mk { v with
      scan := fun i => c.tape i (c.head i)
      nxt := none } S) = mk { v with
      scan := fun i => c.tape i (c.head i)
      nxt := none
      flag := false } S := rfl
  have he' := Exec.cond_false (body := body) (f := fun v => v.nxt.isSome)
    (p := Prog.seqList ((List.finRange T).map (fun i => .act (tapeAct i)) ++ [.act setState]))
    (by simp) (h₁ ▸ Exec.act (body := body) stopFlag _)
  exact Exec.seq (hrun ▸ Exec.act (body := body) (peekScan M) (mk v S)) he'

lemma stepStacks_length (L R : List (Fin (A + 4))) (w : Fin (A + 4)) (m : Move) :
    (stepStacks blank L R w m).1.length + (stepStacks blank L R w m).2.length ≤
      L.length + R.length + 2 := by
  cases m <;> simp [stepStacks] <;> omega

/-- The simulation loop runs a halting computation to completion. -/
theorem sim_loop (M : Program T Q A) : ∀ (k : ℕ) (c : Config T Q A) (v : HS T Q A U) (S : Stacks T A),
    Rep c S.L S.R → v.st = c.state → v.flag = true →
    ∀ cf, run M k c = some cf → step M cf = none →
    ∃ v' S', Exec body (.loop (·.flag) (simIter M)) (mk v S) (k * (T + 5) + 5) (mk v' S') ∧
      Rep cf S'.L S'.R ∧ v'.user = v.user ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      ∀ i, (S'.L i).length + (S'.R i).length ≤ (S.L i).length + (S.R i).length + 2 * k := by
  intro k
  induction k with
  | zero =>
      intro c v S hrep hst hfl cf hrun hstep
      simp only [run, Option.some.injEq] at hrun
      subst hrun
      have ht : M.transition c.state (fun i => c.tape i (c.head i)) = none := by
        unfold step at hstep
        split at hstep
        · assumption
        · simp at hstep
      obtain ⟨v', h₁, h₂, h₃, he⟩ := simIter_halt (body := body) M hrep hst ht
      refine ⟨v', S, ?_, hrep, h₁, rfl, rfl, fun i => by omega⟩
      have := Exec.loop_true (body := body) (f := (·.flag)) hfl he (.loop_false (by simpa using h₂))
      simpa using this
  | succ k ih =>
      intro c v S hrep hst hfl cf hrun hstep
      simp only [run] at hrun
      cases hs : step M c with
      | none => simp [hs] at hrun
      | some c₁ =>
          rw [hs, Option.bind_some] at hrun
          obtain ⟨st', act, ht⟩ : ∃ st' act,
              M.transition c.state (fun i => c.tape i (c.head i)) = some (st', act) := by
            unfold step at hs
            split at hs
            · simp at hs
            · exact ⟨_, _, by assumption⟩
          obtain ⟨c', hc', hcs, hrep'⟩ := rep_step hrep ht
          rw [hs, Option.some.injEq] at hc'
          subst hc'
          obtain ⟨v₁, h₁, h₂, h₃, he⟩ := simIter_step (body := body) M hrep hst ht
          obtain ⟨v', S', he', hrep'', hl, hi, ho, hsz⟩ :=
            ih c₁ v₁ { S with
              L := newL S act
              R := newR S act } hrep' (by rw [h₃, hcs]) (by rw [h₂, hfl]) cf hrun hstep
          refine ⟨v', S', ?_, hrep'', hl.trans h₁, hi, ho, fun i => ?_⟩
          · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hfl he he') (by ring) rfl
          · have h₄ := hsz i
            have h₅ := stepStacks_length (S.L i) (S.R i) (act i).1 (act i).2
            simp only [newL, newR] at h₄ ⊢
            omega


/-! ### Transferring contracts -/

/-- Tapes represented by stacks. -/
def RepT (w : Tapes T A) (L R : Fin T → List (Fin (A + 4))) : Prop :=
  ∀ i j, w.tape i j = readAt blank (L i) (R i) (j - w.head i)

/-- A `HoareTime` contract of a multitape program gives an execution of `foreign` on stacks
representing its tapes. -/
theorem foreign_exec (M : Program T Q A) {pre post : TapePred T A} {k : ℕ}
    (h : HoareTime M pre post k) (v : HS T Q A U) (S : Stacks T A) (w : Tapes T A) (hw : pre w)
    (hrep : RepT w S.L S.R) :
    ∃ v' S' w', post w' ∧ RepT w' S'.L S'.R ∧ v'.user = v.user ∧ S'.inp = S.inp ∧
      S'.out = S.out ∧
      (∀ i, (S'.L i).length + (S'.R i).length ≤ (S.L i).length + (S.R i).length + 2 * k) ∧
      ∃ m ≤ k * (T + 5) + 6, Exec body (foreign M) (mk v S) m (mk v' S') := by
  obtain ⟨kk, c, hkk, hrun, hstep, hpost⟩ := h w hw
  obtain ⟨v', S', he, hrep', hu, hi, ho, hsz⟩ :=
    sim_loop body M kk (w.start M) { v with flag := true, st := M.start } S hrep rfl rfl c hrun hstep
  refine ⟨v', S', c.tapes, hpost, hrep', hu, hi, ho, fun i => ?_, _, ?_,
    Exec.seq (Exec.act (body := body) _ (mk v S)) he⟩
  · have := hsz i; omega
  · have : kk * (T + 5) ≤ k * (T + 5) := Nat.mul_le_mul_right _ hkk
    omega

end IntegerMultBounds.MathlibTM2.Host
