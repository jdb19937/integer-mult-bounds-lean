module

public import IntegerMultBounds.MathlibTM2.Sim

/-!
# Correctness and cost of the bridge phases

Each phase is a loop over a stack, proved by induction on that stack's contents. Phases change
the local state only in scratch fields, keeping `lead` and `st`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

variable {t q a : ℕ}

set_option linter.unusedSimpArgs false

@[simp] lemma store_mk (v : BS t q a) (S : Stacks t a) :
    (⟨v, S.get⟩ : Store (BΓ (t := t) a) (BS t q a)) = mk v S := rfl

/-- Two local states agree on the fields that carry information between phases. -/
def Keeps (v v' : BS t q a) : Prop := v'.lead = v.lead ∧ v'.st = v.st

lemma Keeps.refl (v : BS t q a) : Keeps v v := ⟨rfl, rfl⟩
lemma Keeps.trans {u v w : BS t q a} (h₁ : Keeps u v) (h₂ : Keeps v w) : Keeps u w :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

section
variable (body : Unit → Pr t q a)

/-! ### Splitting the input -/

theorem split_loop : ∀ (l : List (Bool ⊕ Bool)) (v : BS t q a) (S : Stacks t a),
    S.inp = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act splitStep)) (mk v S) (2 * l.length + 1)
      (mk v' { S with
        inp := []
        b0 := (l.filterMap Sum.getLeft?).reverse ++ S.b0
        b1 := (l.filterMap Sum.getRight?).reverse ++ S.b1 }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          inp := []
          b0 := (([] : List (Bool ⊕ Bool)).filterMap Sum.getLeft?).reverse ++ S.b0
          b1 := (([] : List (Bool ⊕ Bool)).filterMap Sum.getRight?).reverse ++ S.b1 } : Stacks t a) = S := by
        cases S; simp_all
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      cases e with
      | inl b =>
          obtain ⟨v', hk, he⟩ := ih { v with ib := some (.inl b), flag := rest.head?.isSome }
            { S with inp := rest, b0 := b :: S.b0 } rfl rfl
          refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
          have hrun : (splitStep : Act t q a).run (mk v S) =
              mk { v with ib := some (.inl b), flag := rest.head?.isSome }
                { S with inp := rest, b0 := b :: S.b0 } := by
            simp [splitStep, peekFlag, Action.run, hS, update_inp, update_b0, Sum.getLeft?]
          have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) splitStep (mk v S)) he
          convert this using 2
          · simp; ring
          · simp [List.filterMap_cons]
      | inr b =>
          obtain ⟨v', hk, he⟩ := ih { v with ib := some (.inr b), flag := rest.head?.isSome }
            { S with inp := rest, b1 := b :: S.b1 } rfl rfl
          refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
          have hrun : (splitStep : Act t q a).run (mk v S) =
              mk { v with ib := some (.inr b), flag := rest.head?.isSome }
                { S with inp := rest, b1 := b :: S.b1 } := by
            simp [splitStep, peekFlag, Action.run, hS, update_inp, update_b1, Sum.getLeft?,
              Sum.getRight?]
          have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) splitStep (mk v S)) he
          convert this using 2
          · simp; ring
          · simp [List.filterMap_cons]

theorem moveBit02_loop : ∀ (l : List Bool) (v : BS t q a) (S : Stacks t a),
    S.b0 = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (moveBit 0 2))) (mk v S) (2 * l.length + 1)
      (mk v' { S with
        b0 := []
        b2 := l.reverse ++ S.b2 }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          b0 := []
          b2 := ([] : List Bool).reverse ++ S.b2 } : Stacks t a) = S := by
        cases S; simp_all
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with x := some e, flag := rest.head?.isSome }
        { S with
          b0 := rest
          b2 := e :: S.b2 } rfl rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (moveBit 0 2 : Act t q a).run (mk v S) =
          mk { v with x := some e, flag := rest.head?.isSome }
            { S with
              b0 := rest
              b2 := e :: S.b2 } := by
        simp [moveBit, peekFlag, Action.run, hS, update_b0, update_b2]
      have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (moveBit 0 2) (mk v S)) he
      convert this using 2
      · simp; ring
      · simp

theorem moveBit13_loop : ∀ (l : List Bool) (v : BS t q a) (S : Stacks t a),
    S.b1 = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (moveBit 1 3))) (mk v S) (2 * l.length + 1)
      (mk v' { S with
        b1 := []
        b3 := l.reverse ++ S.b3 }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          b1 := []
          b3 := ([] : List Bool).reverse ++ S.b3 } : Stacks t a) = S := by
        cases S; simp_all
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with x := some e, flag := rest.head?.isSome }
        { S with
          b1 := rest
          b3 := e :: S.b3 } rfl rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (moveBit 1 3 : Act t q a).run (mk v S) =
          mk { v with x := some e, flag := rest.head?.isSome }
            { S with
              b1 := rest
              b3 := e :: S.b3 } := by
        simp [moveBit, peekFlag, Action.run, hS, update_b1, update_b3]
      have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (moveBit 1 3) (mk v S)) he
      convert this using 2
      · simp; ring
      · simp

theorem toTape2_loop (i : Fin t) : ∀ (l : List Bool) (v : BS t q a) (S : Stacks t a),
    S.b2 = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (toTape 2 i))) (mk v S) (2 * l.length + 1)
      (mk v' { S with
        b2 := []
        R := Function.update S.R i ((l.map bitSymbol).reverse ++ S.R i) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          b2 := []
          R := Function.update S.R i ((([] : List Bool).map bitSymbol).reverse ++ S.R i) } :
            Stacks t a) = S := by
        cases S; simp_all
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with x := some e, flag := rest.head?.isSome }
        { S with
          b2 := rest
          R := Function.update S.R i (bitSymbol e :: S.R i) } rfl rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (toTape 2 i : Act t q a).run (mk v S) =
          mk { v with x := some e, flag := rest.head?.isSome }
            { S with
              b2 := rest
              R := Function.update S.R i (bitSymbol e :: S.R i) } := by
        simp [toTape, peekFlag, Action.run, hS, update_b2, update_rt]
      have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (toTape 2 i) (mk v S)) he
      convert this using 2
      · simp; ring
      · simp

theorem toTape3_loop (i : Fin t) : ∀ (l : List Bool) (v : BS t q a) (S : Stacks t a),
    S.b3 = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (toTape 3 i))) (mk v S) (2 * l.length + 1)
      (mk v' { S with
        b3 := []
        R := Function.update S.R i ((l.map bitSymbol).reverse ++ S.R i) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          b3 := []
          R := Function.update S.R i ((([] : List Bool).map bitSymbol).reverse ++ S.R i) } :
            Stacks t a) = S := by
        cases S; simp_all
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with x := some e, flag := rest.head?.isSome }
        { S with
          b3 := rest
          R := Function.update S.R i (bitSymbol e :: S.R i) } rfl rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (toTape 3 i : Act t q a).run (mk v S) =
          mk { v with x := some e, flag := rest.head?.isSome }
            { S with
              b3 := rest
              R := Function.update S.R i (bitSymbol e :: S.R i) } := by
        simp [toTape, peekFlag, Action.run, hS, update_b3, update_rt]
      have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (toTape 3 i) (mk v S)) he
      convert this using 2
      · simp; ring
      · simp

/-- Pad `l` with `false` at the end to length `n`. -/
def padTo (n : ℕ) (l : List Bool) : List Bool := l ++ List.replicate (n - l.length) false

lemma padTo_succ (n : ℕ) (l : List Bool) :
    padTo (n + 1) l = l.head?.getD false :: padTo n l.tail := by
  cases l with
  | nil => simp [padTo, List.replicate_succ]
  | cons e r => simp [padTo, Nat.succ_sub_succ]

theorem lock_loop : ∀ (n : ℕ) (l₂ l₃ : List Bool) (v : BS t q a) (S : Stacks t a),
    max l₂.length l₃.length = n → S.b2 = l₂ → S.b3 = l₃ →
    v.flag = (l₂.head?.isSome || l₃.head?.isSome) →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act lockStep)) (mk v S) (2 * n + 1)
      (mk v' { S with
        b2 := []
        b3 := []
        b0 := (padTo n l₂).reverse ++ S.b0
        b1 := (padTo n l₃).reverse ++ S.b1 }) := by
  intro n
  induction n with
  | zero =>
      intro l₂ l₃ v S hn h₂ h₃ hf
      have e₂ : l₂ = [] := List.length_eq_zero_iff.1 (by omega)
      have e₃ : l₃ = [] := List.length_eq_zero_iff.1 (by omega)
      subst e₂ e₃
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          b2 := []
          b3 := []
          b0 := (padTo 0 []).reverse ++ S.b0
          b1 := (padTo 0 []).reverse ++ S.b1 } : Stacks t a) = S := by
        cases S; simp_all [padTo]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | succ n ih =>
      intro l₂ l₃ v S hn h₂ h₃ hf
      obtain ⟨v', hk, he⟩ := ih l₂.tail l₃.tail
        { v with
          x := l₂.tail.head?
          y := l₃.tail.head?
          flag := l₂.tail.head?.isSome || l₃.tail.head?.isSome }
        { S with
          b2 := l₂.tail
          b3 := l₃.tail
          b0 := l₂.head?.getD false :: S.b0
          b1 := l₃.head?.getD false :: S.b1 }
        (by simp; omega) rfl rfl rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (lockStep : Act t q a).run (mk v S) =
          mk { v with
              x := l₂.tail.head?
              y := l₃.tail.head?
              flag := l₂.tail.head?.isSome || l₃.tail.head?.isSome }
            { S with
              b2 := l₂.tail
              b3 := l₃.tail
              b0 := l₂.head?.getD false :: S.b0
              b1 := l₃.head?.getD false :: S.b1 } := by
        simp [lockStep, lockPeek, Action.run, h₂, h₃, update_b0, update_b1, update_b2, update_b3]
      have hpos : (l₂.head?.isSome || l₃.head?.isSome) = true := by
        cases l₂ <;> cases l₃ <;> simp_all
      have := Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hf] using hpos)
        (hrun ▸ Exec.act (body := body) lockStep (mk v S)) he
      convert this using 2
      · ring
      · simp [padTo_succ]

lemma padEmpty_run (v : BS t q a) (S : Stacks t a) :
    ∃ v', Keeps v v' ∧ (padEmpty : Act t q a).run (mk v S) =
      mk v' (if S.b0 = [] then { S with
        b0 := [false]
        b1 := false :: S.b1 } else S) := by
  by_cases h : S.b0 = []
  · exact ⟨{ v with x := none }, ⟨rfl, rfl⟩, by simp [padEmpty, Action.run, h, update_b0, update_b1]⟩
  · obtain ⟨e, r, he⟩ := List.exists_cons_of_ne_nil h
    exact ⟨{ v with x := some e }, ⟨rfl, rfl⟩, by simp [padEmpty, Action.run, he]⟩

/-! ### Simulating transitions -/

lemma peekScan_run_aux (M : Program t q a) (S : Stacks t a) :
    ∀ (l : List (Fin t)) (v : BS t q a),
      (l.foldr (fun i acc => Action.peek (.rt i)
          (fun v o => { v with scan := Function.update v.scan i (o.getD blank) }) acc)
        (.load (fun v => { v with nxt := M.transition v.st v.scan }) .done) : Act t q a).run (mk v S) =
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
        · simp [h, Function.update_of_ne h]
      simp only [hscan]

lemma peekScan_run (M : Program t q a) (v : BS t q a) (S : Stacks t a) :
    (peekScan M : Act t q a).run (mk v S) =
      mk { v with
          scan := fun i => (S.R i).head?.getD blank
          nxt := M.transition v.st (fun i => (S.R i).head?.getD blank) } S := by
  simpa [peekScan] using peekScan_run_aux M S (List.finRange t) v

/-- New left stack of tape `i` under a transition's actions. -/
def newL (S : Stacks t a) (act : Fin t → Fin (a + 4) × Move) (i : Fin t) : List (Fin (a + 4)) :=
  (stepStacks blank (S.L i) (S.R i) (act i).1 (act i).2).1

/-- New right stack of tape `i` under a transition's actions. -/
def newR (S : Stacks t a) (act : Fin t → Fin (a + 4) × Move) (i : Fin t) : List (Fin (a + 4)) :=
  (stepStacks blank (S.L i) (S.R i) (act i).1 (act i).2).2

lemma tapeAct_run (i : Fin t) (v : BS t q a) (S : Stacks t a) {st' : Fin q}
    {act : Fin t → Fin (a + 4) × Move} (hv : v.nxt = some (st', act)) :
    ∃ o, (tapeAct i : Act t q a).run (mk v S) =
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
    simp [tapeAct, Action.run, hw, hm, hmv, newL, newR, stepStacks, update_lt, update_rt]
  · refine ⟨v.sym, ?_⟩
    simp [tapeAct, Action.run, hw, hm, hmv, newL, newR, stepStacks, update_lt, update_rt]

theorem tapes_exec {st' : Fin q} {act : Fin t → Fin (a + 4) × Move} :
    ∀ (l : List (Fin t)), l.Nodup → ∀ (v : BS t q a) (S : Stacks t a), v.nxt = some (st', act) →
    ∃ v', v'.lead = v.lead ∧ v'.flag = v.flag ∧ v'.st = st' ∧
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
          L := fun i => if i ∈ ([] : List (Fin t)) then newL S act i else S.L i
          R := fun i => if i ∈ ([] : List (Fin t)) then newR S act i else S.R i } : Stacks t a) = S := by
        cases S; simp
      rw [hS]
      have h₁ : (setState : Act t q a).run (mk v S) = mk { v with st := st' } S := by
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
      refine Stacks.ext rfl rfl rfl rfl rfl rfl ?_ ?_
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1, newL]
        · simp [hj, Function.update_of_ne hj, newL]
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1, newR]
        · simp [hj, Function.update_of_ne hj, newR]

lemma scan_eq {c : Config t q a} {S : Stacks t a} (h : Rep c S.L S.R) :
    (fun i => (S.R i).head?.getD blank) = fun i => c.tape i (c.head i) := by
  funext i; rw [rep_scan h i]

/-- One loop body when the multitape program takes a transition. -/
theorem simIter_step (M : Program t q a) {c : Config t q a} {v : BS t q a} {S : Stacks t a}
    (hrep : Rep c S.L S.R) (hst : v.st = c.state) {st' : Fin q} {act : Fin t → Fin (a + 4) × Move}
    (ht : M.transition c.state (fun i => c.tape i (c.head i)) = some (st', act)) :
    ∃ v', v'.lead = v.lead ∧ v'.flag = v.flag ∧ v'.st = st' ∧
      Exec body (simIter M) (mk v S) (t + 4)
        (mk v' { S with
          L := newL S act
          R := newR S act }) := by
  have hrun := peekScan_run M v S
  have ht' : M.transition v.st (fun i => c.tape i (c.head i)) = some (st', act) := by rw [hst]; exact ht
  rw [scan_eq hrep, ht'] at hrun
  obtain ⟨v', h₁, h₂, h₃, he⟩ := tapes_exec (body := body) (List.finRange t) (List.nodup_finRange t)
    { v with
      scan := fun i => c.tape i (c.head i)
      nxt := some (st', act) } S rfl
  refine ⟨v', h₁, h₂, h₃, ?_⟩
  have he' := Exec.cond_true (body := body) (f := fun v => v.nxt.isSome)
    (q := .act stopFlag) (by simp) he
  refine Exec.cast (Exec.seq (hrun ▸ Exec.act (body := body) (peekScan M) (mk v S)) he')
    (by simp; ring) ?_
  congr 1
  refine Stacks.ext rfl rfl rfl rfl rfl rfl ?_ ?_ <;> funext j <;> simp [List.mem_finRange]

/-- One loop body when the multitape program has halted. -/
theorem simIter_halt (M : Program t q a) {c : Config t q a} {v : BS t q a} {S : Stacks t a}
    (hrep : Rep c S.L S.R) (hst : v.st = c.state)
    (ht : M.transition c.state (fun i => c.tape i (c.head i)) = none) :
    ∃ v', v'.lead = v.lead ∧ v'.flag = false ∧ v'.st = v.st ∧
      Exec body (simIter M) (mk v S) 3 (mk v' S) := by
  have hrun := peekScan_run M v S
  have ht' : M.transition v.st (fun i => c.tape i (c.head i)) = none := by rw [hst]; exact ht
  rw [scan_eq hrep, ht'] at hrun
  refine ⟨{ v with
      scan := fun i => c.tape i (c.head i)
      nxt := none
      flag := false }, rfl, rfl, rfl, ?_⟩
  have h₁ : (stopFlag : Act t q a).run (mk { v with
      scan := fun i => c.tape i (c.head i)
      nxt := none } S) = mk { v with
      scan := fun i => c.tape i (c.head i)
      nxt := none
      flag := false } S := rfl
  have he' := Exec.cond_false (body := body) (f := fun v => v.nxt.isSome)
    (p := Prog.seqList ((List.finRange t).map (fun i => .act (tapeAct i)) ++ [.act setState]))
    (by simp) (h₁ ▸ Exec.act (body := body) stopFlag _)
  exact Exec.seq (hrun ▸ Exec.act (body := body) (peekScan M) (mk v S)) he'

lemma stepStacks_length (L R : List (Fin (a + 4))) (w : Fin (a + 4)) (m : Move) :
    (stepStacks blank L R w m).1.length + (stepStacks blank L R w m).2.length ≤
      L.length + R.length + 2 := by
  cases m <;> simp [stepStacks] <;> omega

/-- The simulation loop runs a halting computation to completion. -/
theorem sim_loop (M : Program t q a) : ∀ (k : ℕ) (c : Config t q a) (v : BS t q a) (S : Stacks t a),
    Rep c S.L S.R → v.st = c.state → v.flag = true →
    ∀ cf, run M k c = some cf → step M cf = none →
    ∃ v' S', Exec body (.loop (·.flag) (simIter M)) (mk v S) (k * (t + 5) + 5) (mk v' S') ∧
      Rep cf S'.L S'.R ∧ v'.lead = v.lead ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.b0 = S.b0 ∧ S'.b1 = S.b1 ∧ S'.b2 = S.b2 ∧ S'.b3 = S.b3 ∧
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
      refine ⟨v', S, ?_, hrep, h₁, rfl, rfl, rfl, rfl, rfl, rfl, fun i => by omega⟩
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
          obtain ⟨v', S', he', hrep'', hl, hi, ho, hb0, hb1, hb2, hb3, hsz⟩ :=
            ih c₁ v₁ { S with
              L := newL S act
              R := newR S act } hrep' (by rw [h₃, hcs]) (by rw [h₂, hfl]) cf hrun hstep
          refine ⟨v', S', ?_, hrep'', hl.trans h₁, hi, ho, hb0, hb1, hb2, hb3, fun i => ?_⟩
          · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hfl he he') (by ring) rfl
          · have h₄ := hsz i
            have h₅ := stepStacks_length (S.L i) (S.R i) (act i).1 (act i).2
            simp only [newL, newR] at h₄ ⊢
            omega

/-! ### Reading the output -/

theorem leftToRight_loop (i : Fin t) : ∀ (l : List (Fin (a + 4))) (v : BS t q a) (S : Stacks t a),
    S.L i = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (leftToRight i))) (mk v S) (2 * l.length + 1)
      (mk v' { S with
        L := Function.update S.L i []
        R := Function.update S.R i (l.reverse ++ S.R i) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with
          L := Function.update S.L i []
          R := Function.update S.R i (([] : List (Fin (a + 4))).reverse ++ S.R i) } : Stacks t a) = S := by
        cases S; simp only [List.reverse_nil, List.nil_append, Function.update_eq_self] at hS ⊢
        rw [← hS, Function.update_eq_self]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with
          L := Function.update S.L i rest
          R := Function.update S.R i (e :: S.R i) } (by simp) rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (leftToRight i : Act t q a).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with
              L := Function.update S.L i rest
              R := Function.update S.R i (e :: S.R i) } := by
        simp [leftToRight, peekFlag, Action.run, hS, update_lt, update_rt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (leftToRight i) (mk v S)) he) (by simp; ring) ?_
      simp

/-- The output pushed while draining a list of cells with leading-zero state `lead`. -/
def emitted (lead : Bool) (W : List (Fin (a + 4))) : List Bool :=
  if lead then ((W.filterMap decodeBit).dropWhile (fun b => !b)).reverse
  else (W.filterMap decodeBit).reverse

lemma emitted_cons (lead : Bool) (s : Fin (a + 4)) (W : List (Fin (a + 4))) :
    emitted lead (s :: W) =
      match decodeBit s with
      | some b => if b || !lead then emitted false W ++ [b] else emitted lead W
      | none => emitted lead W := by
  rcases h : decodeBit s with _ | b
  · simp [emitted, List.filterMap_cons, h]
  · cases lead <;> cases b <;> simp [emitted, List.filterMap_cons, h, List.dropWhile_cons]

theorem extract_loop (i : Fin t) : ∀ (W : List (Fin (a + 4))) (v : BS t q a) (S : Stacks t a),
    S.R i = W → v.flag = W.head?.isSome →
    ∃ v', v'.st = v.st ∧ Exec body (.loop (·.flag) (.act (extractStep i))) (mk v S)
      (2 * W.length + 1)
      (mk v' { S with
        R := Function.update S.R i []
        out := emitted v.lead W ++ S.out }) := by
  intro W
  induction W with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have hS' : ({ S with
          R := Function.update S.R i []
          out := emitted v.lead ([] : List (Fin (a + 4))) ++ S.out } : Stacks t a) = S := by
        cases S; simp only [emitted, List.filterMap_nil, List.dropWhile_nil, List.reverse_nil,
          ite_self, List.nil_append] at hS ⊢
        rw [← hS, Function.update_eq_self]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      have hpos : v.flag = true := by simpa using hf
      rcases hd : decodeBit e with _ | b
      · -- not a bit: nothing is written
        obtain ⟨v', hk, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
          { S with R := Function.update S.R i rest } (by simp) rfl
        refine ⟨v', hk, ?_⟩
        have hrun : (extractStep i : Act t q a).run (mk v S) =
            mk { v with sym := some e, flag := rest.head?.isSome }
              { S with R := Function.update S.R i rest } := by
          simp [extractStep, emits, peekFlag, Action.run, hS, update_rt, hd]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hpos
          (hrun ▸ Exec.act (body := body) (extractStep i) (mk v S)) he) (by simp; ring) ?_
        simp [emitted_cons, hd]
      · by_cases hem : (b || !v.lead) = true
        · obtain ⟨v', hk, he⟩ := ih { v with sym := some e, lead := false, flag := rest.head?.isSome }
            { S with
              R := Function.update S.R i rest
              out := b :: S.out } (by simp) rfl
          refine ⟨v', hk, ?_⟩
          have hrun : (extractStep i : Act t q a).run (mk v S) =
              mk { v with sym := some e, lead := false, flag := rest.head?.isSome }
                { S with
                  R := Function.update S.R i rest
                  out := b :: S.out } := by
            simp [extractStep, emits, peekFlag, Action.run, hS, update_rt, update_out, hd, hem]
          refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hpos
            (hrun ▸ Exec.act (body := body) (extractStep i) (mk v S)) he) (by simp; ring) ?_
          simp [emitted_cons, hd, hem]
        · obtain ⟨v', hk, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update S.R i rest } (by simp) rfl
          refine ⟨v', hk, ?_⟩
          have hrun : (extractStep i : Act t q a).run (mk v S) =
              mk { v with sym := some e, flag := rest.head?.isSome }
                { S with R := Function.update S.R i rest } := by
            simp only [Bool.not_eq_true] at hem
            simp [extractStep, emits, peekFlag, Action.run, hS, update_rt, hd, hem]
          refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hpos
            (hrun ▸ Exec.act (body := body) (extractStep i) (mk v S)) he) (by simp; ring) ?_
          simp only [Bool.not_eq_true] at hem
          simp [emitted_cons, hd, hem]

/-! ### Cleaning up -/

theorem dropL_loop (i : Fin t) : ∀ (l : List (Fin (a + 4))) (v : BS t q a) (S : Stacks t a),
    S.L i = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (dropStep (.lt i)))) (mk v S)
      (2 * l.length + 1) (mk v' { S with L := Function.update S.L i [] }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with L := Function.update S.L i [] } : Stacks t a) = S := by
        cases S; simp only at hS ⊢; rw [← hS, Function.update_eq_self]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with flag := rest.head?.isSome }
        { S with L := Function.update S.L i rest } (by simp) rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (dropStep (.lt i) : Act t q a).run (mk v S) =
          mk { v with flag := rest.head?.isSome } { S with L := Function.update S.L i rest } := by
        simp [dropStep, peekFlag, Action.run, hS, update_lt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (dropStep (.lt i)) (mk v S)) he) (by simp; ring) ?_
      simp

theorem dropR_loop (i : Fin t) : ∀ (l : List (Fin (a + 4))) (v : BS t q a) (S : Stacks t a),
    S.R i = l → v.flag = l.head?.isSome →
    ∃ v', Keeps v v' ∧ Exec body (.loop (·.flag) (.act (dropStep (.rt i)))) (mk v S)
      (2 * l.length + 1) (mk v' { S with R := Function.update S.R i [] }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Keeps.refl v, ?_⟩
      have hS' : ({ S with R := Function.update S.R i [] } : Stacks t a) = S := by
        cases S; simp only at hS ⊢; rw [← hS, Function.update_eq_self]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hk, he⟩ := ih { v with flag := rest.head?.isSome }
        { S with R := Function.update S.R i rest } (by simp) rfl
      refine ⟨v', Keeps.trans ⟨rfl, rfl⟩ hk, ?_⟩
      have hrun : (dropStep (.rt i) : Act t q a).run (mk v S) =
          mk { v with flag := rest.head?.isSome } { S with R := Function.update S.R i rest } := by
        simp [dropStep, peekFlag, Action.run, hS, update_rt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (dropStep (.rt i)) (mk v S)) he) (by simp; ring) ?_
      simp

end

end IntegerMultBounds.MathlibTM2
