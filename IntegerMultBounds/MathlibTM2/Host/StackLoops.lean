module

public import IntegerMultBounds.MathlibTM2.Host.Stream

/-!
# Loops over host stacks

Whole-stack loops on one tape: `unload` moves the left stack onto the right one, `sieve` drops
blanks, `normTape` and `normList` normalize tapes, `shiftList` moves the top of each right stack
of a list onto its left stack, and `peekL` tests a left stack. `markList` and `dropList` push a
blank onto, or pop, the right stack of each tape of a list; `unplaced ι` lists the tapes outside
the range of `ι`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

section Loops

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether the left stack of tape `i` is nonempty. -/
def peekL (i : Fin T) : Act T Q A U :=
  .peek (.lt i) (fun v o => { v with flag := o.isSome }) .done

lemma peekL_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekL i : Act T Q A U).run (mk v S) = mk { v with flag := (S.L i).head?.isSome } S := rfl

/-- One step of `unload`: pop the left stack of tape `i` onto its right stack. -/
def unloadStep (i : Fin T) : Act T Q A U :=
  .pop (.lt i) (fun v o => { v with sym := o })
    (.push (.rt i) (fun v => v.sym.getD blank) (peekL i))

/-- Move the whole left stack of tape `i` onto its right stack. -/
def unload (i : Fin T) : Pr P T Q A U :=
  .seq (.act (peekL i)) (.loop (·.flag) (.act (unloadStep i)))

theorem unload_loop (i : Fin T) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.L i = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (unloadStep i))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            L := Function.update S.L i []
            R := Function.update S.R i (l.reverse ++ S.R i) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          L := Function.update S.L i []
          R := Function.update S.R i (([] : List (Fin (A + 4))).reverse ++ S.R i) } :
            Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          · funext k; by_cases hk : k = i
            · subst hk; simp [hS]
            · simp [hk]
          · funext k; by_cases hk : k = i
            · subst hk; simp
            · simp [hk]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with
          L := Function.update S.L i rest
          R := Function.update S.R i (e :: S.R i) }
        (by simp) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (unloadStep i : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with
              L := Function.update S.L i rest
              R := Function.update S.R i (e :: S.R i) } := by
        simp [unloadStep, peekL, Action.run, hS, update_rt, update_lt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (unloadStep i) (mk v S)) he) (by simp; ring) ?_
      congr 2
      · funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [hk]

theorem unload_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (unload i) (mk v S) (2 * (S.L i).length + 2)
        (mk v' { S with
          L := Function.update S.L i []
          R := Function.update S.R i ((S.L i).reverse ++ S.R i) }) := by
  obtain ⟨v', hu, he⟩ := unload_loop body i (S.L i) { v with flag := (S.L i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast
    (Exec.seq (peekL_run i v S ▸ Exec.act (body := body) (peekL i) (mk v S)) he) (by ring) rfl⟩

/-- One step of `sieve`: pop the right stack of tape `i`, keeping non-blank symbols on its left
stack. -/
def sieveStep (i : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.branch (fun v => decide (v.sym.getD blank ≠ blank))
      (.push (.lt i) (fun v => v.sym.getD blank) (peekR i))
      (peekR i))

/-- Move the right stack of tape `i` onto its left stack, dropping blanks. -/
def sieve (i : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR i)) (.loop (·.flag) (.act (sieveStep i)))

theorem sieve_loop (i : Fin T) :
    ∀ (r : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R i = r → v.flag = r.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (sieveStep i))) (mk v S) (2 * r.length + 1)
          (mk v' { S with
            L := Function.update S.L i ((r.filter (· ≠ blank)).reverse ++ S.L i)
            R := Function.update S.R i [] }) := by
  intro r
  induction r with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          L := Function.update S.L i
            ((([] : List (Fin (A + 4))).filter (· ≠ blank)).reverse ++ S.L i)
          R := Function.update S.R i [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          · funext k; by_cases hk : k = i
            · subst hk; simp
            · simp [hk]
          · funext k; by_cases hk : k = i
            · subst hk; simp [hS]
            · simp [hk]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      by_cases he : e = blank
      · obtain ⟨v', hu, hx⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
          { S with R := Function.update S.R i rest } (by simp) rfl
        refine ⟨v', hu, ?_⟩
        have hrun : (sieveStep i : Act T Q A U).run (mk v S) =
            mk { v with sym := some e, flag := rest.head?.isSome }
              { S with R := Function.update S.R i rest } := by
          simp [sieveStep, peekR, Action.run, hS, update_rt, he]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (sieveStep i) (mk v S)) hx) (by simp; ring) ?_
        congr 2
        · funext k; by_cases hk : k = i
          · subst hk; simp [he]
          · simp [hk]
        · funext k; by_cases hk : k = i
          · subst hk; simp
          · simp [hk]
      · obtain ⟨v', hu, hx⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
          { S with
            L := Function.update S.L i (e :: S.L i)
            R := Function.update S.R i rest }
          (by simp) rfl
        refine ⟨v', hu, ?_⟩
        have hrun : (sieveStep i : Act T Q A U).run (mk v S) =
            mk { v with sym := some e, flag := rest.head?.isSome }
              { S with
                L := Function.update S.L i (e :: S.L i)
                R := Function.update S.R i rest } := by
          simp [sieveStep, peekR, Action.run, hS, update_rt, update_lt, he]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (sieveStep i) (mk v S)) hx) (by simp; ring) ?_
        congr 2
        · funext k; by_cases hk : k = i
          · subst hk; simp [he]
          · simp [hk]
        · funext k; by_cases hk : k = i
          · subst hk; simp
          · simp [hk]

theorem sieve_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (sieve i) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with
          L := Function.update S.L i (((S.R i).filter (· ≠ blank)).reverse ++ S.L i)
          R := Function.update S.R i [] }) := by
  obtain ⟨v', hu, he⟩ := sieve_loop body i (S.R i) { v with flag := (S.R i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast
    (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S)) he) (by ring) rfl⟩

/-- The blank-free content of a tape stored as stacks `L`, `R`. -/
def sweep (L R : List (Fin (A + 4))) : List (Fin (A + 4)) := (L.reverse ++ R).filter (· ≠ blank)

/-- Normalize tape `i`: its blank-free content ends on the right stack, the left stack empty. -/
def normTape (i : Fin T) : Pr P T Q A U := .seq (unload i) (.seq (sieve i) (unload i))

theorem normTape_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6 * ((S.L i).length + (S.R i).length) + 6 ∧
      Exec body (normTape i) (mk v S) n
        (mk v' { S with
          L := Function.update S.L i []
          R := Function.update S.R i (sweep (S.L i) (S.R i)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := unload_exec body i v S
  obtain ⟨v₂, hu₂, he₂⟩ := sieve_exec body i v₁ _
  obtain ⟨v₃, hu₃, he₃⟩ := unload_exec body i v₂ _
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · simp only [Function.update_self, List.length_append, List.length_reverse, List.append_nil]
    have := List.length_filter_le (fun x => decide (x ≠ (blank : Fin (A + 4))))
      ((S.L i).reverse ++ S.R i)
    simp only [List.length_append, List.length_reverse] at this
    omega
  · congr 2
    · funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    · funext k; by_cases hk : k = i
      · subst hk; simp [sweep]
      · simp [hk]

/-- Normalize every tape of a list. -/
def normList (l : List (Fin T)) : Pr P T Q A U := Prog.seqList (l.map normTape)

theorem normList_exec : ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
    ∃ v' n, v'.user = v.user ∧
      n ≤ (l.map fun i => 6 * ((S.L i).length + (S.R i).length) + 6).sum + 1 ∧
      Exec body (normList l) (mk v S) n
        (mk v' { S with
          L := fun i => if i ∈ l then [] else S.L i
          R := fun i => if i ∈ l then sweep (S.L i) (S.R i) else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S
      refine ⟨v, 1, rfl, by simp, ?_⟩
      have : ({ S with
          L := fun i => if i ∈ ([] : List (Fin T)) then [] else S.L i
          R := fun i => if i ∈ ([] : List (Fin T)) then sweep (S.L i) (S.R i) else S.R i } :
            Stacks T A) = S := by cases S; simp
      rw [this]
      exact Exec.act .done (mk v S)
  | cons i rest ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := normTape_exec body i v S
      obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih hnd.2 v₁ _
      refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
      · have hsum : (rest.map fun j => 6 * ((Function.update S.L i [] j).length +
            (Function.update S.R i (sweep (S.L i) (S.R i)) j).length) + 6) =
            rest.map fun j => 6 * ((S.L j).length + (S.R j).length) + 6 := by
          apply List.map_congr_left
          intro j hj
          have hji : j ≠ i := fun h => hnd.1 (h ▸ hj)
          simp [Function.update_of_ne hji]
        simp only [hsum] at hn₂
        simp only [List.map_cons, List.sum_cons]
        omega
      · congr 2
        · funext j
          by_cases hj : j = i
          · subst hj; simp [hnd.1]
          · simp [hj]
        · funext j
          by_cases hj : j = i
          · subst hj; simp [hnd.1]
          · simp [hj]

/-- Move the top of the right stack of tape `i` to its left stack. -/
def shiftStep (i : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o }) (.push (.lt i) (fun v => v.sym.getD blank) .done)

/-- Shift every tape of a list one cell to the right. -/
def shiftList (l : List (Fin T)) : Pr P T Q A U :=
  Prog.seqList (l.map fun i => .act (shiftStep i))

theorem shiftList_exec : ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
    ∃ v', v'.user = v.user ∧
      Exec body (shiftList l) (mk v S) (l.length + 1)
        (mk v' { S with
          L := fun i => if i ∈ l then (S.R i).head?.getD blank :: S.L i else S.L i
          R := fun i => if i ∈ l then (S.R i).tail else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          L := fun i =>
            if i ∈ ([] : List (Fin T)) then (S.R i).head?.getD blank :: S.L i else S.L i
          R := fun i => if i ∈ ([] : List (Fin T)) then (S.R i).tail else S.R i } :
            Stacks T A) = S := by cases S; simp
      rw [this]
      exact Exec.act .done (mk v S)
  | cons i rest ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      have hrun : (shiftStep i : Act T Q A U).run (mk v S) =
          mk { v with sym := (S.R i).head? } { S with
            L := Function.update S.L i ((S.R i).head?.getD blank :: S.L i)
            R := Function.update S.R i (S.R i).tail } := by
        simp [shiftStep, Action.run, update_rt, update_lt]
      obtain ⟨v₂, hu₂, he₂⟩ := ih hnd.2 { v with sym := (S.R i).head? } _
      refine ⟨v₂, hu₂, Exec.cast
        (Exec.seq (hrun ▸ Exec.act (body := body) (shiftStep i) (mk v S)) he₂) (by simp; ring) ?_⟩
      congr 2
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1]
        · simp [hj]
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1]
        · simp [hj]

end Loops

section Marks

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Marking right stacks -/

/-- Run `a i` for each tape `i` of a list, where `a i` maps the right stack of tape `i` by `g`. -/
theorem eachR_exec (a : Fin T → Act T Q A U) (g : List (Fin (A + 4)) → List (Fin (A + 4)))
    (ha : ∀ i v S, (a i).run (mk v S) = mk v { S with R := Function.update S.R i (g (S.R i)) }) :
    ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      Exec body (Prog.seqList (l.map fun i => .act (a i))) (mk v S) (l.length + 1)
        (mk v { S with R := fun i => if i ∈ l then g (S.R i) else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S
      have : ({ S with R := fun i => if i ∈ ([] : List (Fin T)) then g (S.R i) else S.R i } :
          Stacks T A) = S := by cases S; simp
      rw [this]
      exact Exec.act .done (mk v S)
  | cons i rest ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      have he₂ := ih hnd.2 v { S with R := Function.update S.R i (g (S.R i)) }
      refine Exec.cast (Exec.seq ((ha i v S) ▸ Exec.act (body := body) (a i) (mk v S)) he₂)
        (by simp; ring) ?_
      congr 2
      funext j
      by_cases hj : j = i
      · subst hj; simp [hnd.1]
      · simp [hj]

/-- Push a blank onto the right stack of tape `i`. -/
def markStep (i : Fin T) : Act T Q A U := .push (.rt i) (fun _ => blank) .done

/-- Pop the right stack of tape `i`, discarding the symbol. -/
def dropStep (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) .done

/-- Push a blank onto the right stack of each tape of a list. -/
def markList (l : List (Fin T)) : Pr P T Q A U := Prog.seqList (l.map fun i => .act (markStep i))

/-- Pop the right stack of each tape of a list. -/
def dropList (l : List (Fin T)) : Pr P T Q A U := Prog.seqList (l.map fun i => .act (dropStep i))

theorem markList_exec (l : List (Fin T)) (hl : l.Nodup) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (markList l) (mk v S) (l.length + 1)
      (mk v { S with R := fun i => if i ∈ l then blank :: S.R i else S.R i }) :=
  eachR_exec body markStep (fun r => blank :: r)
    (fun i v S => by simp [markStep, Action.run, update_rt]) l hl v S

theorem dropList_exec (l : List (Fin T)) (hl : l.Nodup) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (dropList l) (mk v S) (l.length + 1)
      (mk v { S with R := fun i => if i ∈ l then (S.R i).tail else S.R i }) :=
  eachR_exec body dropStep List.tail
    (fun i v S => by simp [dropStep, Action.run, update_rt]) l hl v S

/-! ### Tapes outside a family -/

/-- The tapes outside the range of `ι`, in increasing order. -/
def unplaced {s : ℕ} (ι : Fin s → Fin T) : List (Fin T) :=
  (List.finRange T).filter fun x => decide (∀ j, ι j ≠ x)

lemma mem_unplaced {s : ℕ} (ι : Fin s → Fin T) (x : Fin T) :
    x ∈ unplaced ι ↔ ∀ j, ι j ≠ x := by
  simp [unplaced, List.mem_filter, List.mem_finRange]

lemma unplaced_nodup {s : ℕ} (ι : Fin s → Fin T) : (unplaced ι).Nodup :=
  (List.nodup_finRange T).filter _

lemma unplaced_length_le {s : ℕ} (ι : Fin s → Fin T) : (unplaced ι).length ≤ T :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

end Marks

end IntegerMultBounds.MathlibTM2.Host
