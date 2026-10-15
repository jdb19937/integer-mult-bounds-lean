module

public import IntegerMultBounds.MathlibTM2.Host.Stream

/-!
# Word automata on host registers

A word automaton reads one symbol from each input register per step, updates a state symbol and
pushes one symbol to each output register. The state is reset at every word boundary. `autoWords`
runs it over a whole stream: words of `len` steps, counted by a unary counter register.

The state symbol and the input symbols of a step live in scratch slots of `scan`; their values
after a pass are unspecified.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- A word automaton with `ni` input and `no` output registers over stack symbols. -/
structure Auto (A ni no : ℕ) where
  init : Fin (A + 4)
  step : Fin (A + 4) → (Fin ni → Fin (A + 4)) → Fin (A + 4) × (Fin no → Fin (A + 4))

namespace Auto

variable {ni no : ℕ} (M : Auto A ni no)

/-- Run the automaton on one word given as a list of input columns; returns output columns in
step order. -/
def runWord : Fin (A + 4) → List (Fin ni → Fin (A + 4)) → List (Fin no → Fin (A + 4))
  | _, [] => []
  | s, c :: cs => (M.step s c).2 :: runWord (M.step s c).1 cs

end Auto

/-- Decode a stack symbol as a bit (non-bit symbols read as `false`). -/
def symBit (x : Fin (A + 4)) : Bool := x = bitSymbol true

@[simp] lemma symBit_bitSymbol (b : Bool) : symBit (bitSymbol (a := A) b) = b := by
  cases b <;> simp [symBit, bitSymbol]

variable {ni no : ℕ}

/-! ### One automaton step -/

/-- The pending automaton step: the state in slot `st`, the inputs in slots `ins`. -/
def autoNext (ins : Fin ni → Fin T) (st : Fin T) (M : Auto A ni no) (v : HS T Q A U) :
    Fin (A + 4) × (Fin no → Fin (A + 4)) :=
  M.step (v.scan st) fun i => v.scan (ins i)

/-- Pop input register `ins i` into scan slot `ins i`, then run `a`. -/
def popIn (ins : Fin ni → Fin T) (i : Fin ni) (a : Act T Q A U) : Act T Q A U :=
  .pop (.rt (ins i))
    (fun v o => { v with scan := Function.update v.scan (ins i) (o.getD blank) }) a

/-- Push output `j` of the pending step onto register `outs j`, then run `a`. -/
def pushOut (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st : Fin T) (M : Auto A ni no)
    (j : Fin no) (a : Act T Q A U) : Act T Q A U :=
  .push (.rt (outs j)) (fun v => (autoNext ins st M v).2 j) a

/-- Store the state of the pending step in slot `st`. -/
def setAutoState (ins : Fin ni → Fin T) (st : Fin T) (M : Auto A ni no) : Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan st (autoNext ins st M v).1 }) .done

/-- One automaton step: pop every input register into its scan slot, push every output, store
the new state in slot `st`. -/
def autoStep (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st : Fin T) (M : Auto A ni no) :
    Act T Q A U :=
  (List.finRange ni).foldr (popIn ins)
    ((List.finRange no).foldr (pushOut ins outs st M) (setAutoState ins st M))

lemma popIn_run (ins : Fin ni → Fin T) (a : Act T Q A U) :
    ∀ (l : List (Fin ni)) (v : HS T Q A U) (S : Stacks T A), (l.map ins).Nodup →
      (l.foldr (popIn ins) a).run (mk v S) =
        a.run (mk
          { v with scan := fun k => if k ∈ l.map ins then (S.R k).head?.getD blank else v.scan k }
          { S with R := fun k => if k ∈ l.map ins then (S.R k).tail else S.R k }) := by
  intro l
  induction l with
  | nil => intro v S _; simp
  | cons i rest ih =>
      intro v S hnd
      rw [List.map_cons, List.nodup_cons] at hnd
      simp only [List.foldr_cons, popIn, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk]
      rw [ih _ _ hnd.2]
      congr 3
      · funext k
        by_cases hk : k = ins i
        · subst hk; simp [hnd.1]
        · simp [hk, Function.update_of_ne hk]
      · funext k
        by_cases hk : k = ins i
        · subst hk; simp [hnd.1]
        · simp [hk, Function.update_of_ne hk]

lemma pushOut_run (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st : Fin T) (M : Auto A ni no)
    (a : Act T Q A U) :
    ∀ (l : List (Fin no)) (v : HS T Q A U) (S : Stacks T A),
      (l.foldr (pushOut ins outs st M) a).run (mk v S) =
        a.run (mk v { S with R := fun k =>
          (((l.filter fun j => outs j = k).map fun j => (autoNext ins st M v).2 j).reverse ++
            S.R k) }) := by
  intro l
  induction l with
  | nil => intro v S; simp
  | cons j rest ih =>
      intro v S
      simp only [List.foldr_cons, pushOut, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk]
      rw [ih]
      congr 3
      funext k
      by_cases hk : outs j = k
      · subst hk; simp
      · simp [hk, Function.update_of_ne (Ne.symm hk)]

/-- Register layout of `autoWords`: injective input and output families, a counter `ctr` and a
spare register `tmp`, all pairwise disjoint, and a state slot `st` outside the input slots. -/
structure AutoLayout (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st ctr tmp : Fin T) :
    Prop where
  ins_inj : Function.Injective ins
  outs_inj : Function.Injective outs
  ins_outs : ∀ i j, ins i ≠ outs j
  ins_ctr : ∀ i, ins i ≠ ctr
  ins_tmp : ∀ i, ins i ≠ tmp
  outs_ctr : ∀ j, outs j ≠ ctr
  outs_tmp : ∀ j, outs j ≠ tmp
  ctr_tmp : ctr ≠ tmp
  ins_st : ∀ i, ins i ≠ st

/-- `S'` agrees with `S` outside the registers `ins`, `outs`, `ctr` and `tmp`. -/
def AutoFrame (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (ctr tmp : Fin T)
    (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
    ∀ k, k ∉ Set.range ins → k ∉ Set.range outs → k ≠ ctr → k ≠ tmp → S'.R k = S.R k

lemma AutoFrame.refl (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (ctr tmp : Fin T)
    (S : Stacks T A) : AutoFrame ins outs ctr tmp S S :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

lemma AutoFrame.trans {ins : Fin ni → Fin T} {outs : Fin no → Fin T} {ctr tmp : Fin T}
    {S₁ S₂ S₃ : Stacks T A} (h₁ : AutoFrame ins outs ctr tmp S₁ S₂)
    (h₂ : AutoFrame ins outs ctr tmp S₂ S₃) : AutoFrame ins outs ctr tmp S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k a b c d => (h₂.2.2.2 k a b c d).trans (h₁.2.2.2 k a b c d)⟩

/-- The input column of a step: the top of every input register. -/
def topCol (ins : Fin ni → Fin T) (S : Stacks T A) : Fin ni → Fin (A + 4) :=
  fun i => (S.R (ins i)).head?.getD blank

lemma filter_outs {outs : Fin no → Fin T} (houts : Function.Injective outs) (j : Fin no) :
    (List.finRange no).filter (fun j' => outs j' = outs j) = [j] := by
  have : (List.finRange no).filter (fun j' => outs j' = outs j) =
      (List.finRange no).filter (fun j' => j' = j) := by
    congr 1; funext j'; simp [houts.eq_iff]
  rw [this, List.filter_eq, List.count_eq_one_of_mem (List.nodup_finRange no) (List.mem_finRange j)]
  rfl

lemma filter_outs_nil {outs : Fin no → Fin T} {k : Fin T} (hk : k ∉ Set.range outs) :
    (List.finRange no).filter (fun j' => outs j' = k) = [] := by
  rw [List.filter_eq_nil_iff]
  intro j _ hj
  exact hk ⟨j, by simpa using hj⟩

/-- One automaton step on the register tops: every input register loses its top, every output
register gains the step's output, and slot `st` takes the step's new state. -/
theorem autoStep_run {ins : Fin ni → Fin T} {outs : Fin no → Fin T} {st : Fin T}
    (hins : Function.Injective ins) (houts : Function.Injective outs) (hio : ∀ i j, ins i ≠ outs j)
    (hst : ∀ i, ins i ≠ st) (M : Auto A ni no) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' S', (autoStep ins outs st M).run (mk v S) = mk v' S' ∧
      v'.user = v.user ∧ v'.flag = v.flag ∧ v'.scan st = (M.step (v.scan st) (topCol ins S)).1 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (ins i) = (S.R (ins i)).tail) ∧
      (∀ j, S'.R (outs j) = (M.step (v.scan st) (topCol ins S)).2 j :: S.R (outs j)) ∧
      ∀ k, k ∉ Set.range ins → k ∉ Set.range outs → S'.R k = S.R k := by
  have hnd : ((List.finRange ni).map ins).Nodup := (List.nodup_finRange ni).map hins
  have hmem : ∀ k, k ∈ (List.finRange ni).map ins ↔ k ∈ Set.range ins := by
    intro k; simp [List.mem_map, List.mem_finRange]
  have hst' : st ∉ (List.finRange ni).map ins := by
    rw [hmem]; rintro ⟨i, hi⟩; exact hst i hi
  have hst'' : ¬∃ i, ins i = st := by rintro ⟨i, hi⟩; exact hst i hi
  unfold autoStep
  rw [popIn_run ins _ _ v S hnd, pushOut_run]
  refine ⟨_, _, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [setAutoState, autoNext, Action.run, hst'']; rfl
  · intro i
    have h1 : ins i ∉ Set.range outs := by rintro ⟨j, hj⟩; exact hio i j hj.symm
    simp [filter_outs_nil h1, List.mem_map, List.mem_finRange]
  · intro j
    have h1 : ¬∃ i, ins i = outs j := by rintro ⟨i, hi⟩; exact hio i j hi
    simp [filter_outs houts, h1, autoNext, hst'', List.mem_map, List.mem_finRange]; rfl
  · intro k hk1 hk2
    have h1 : ¬∃ i, ins i = k := by rintro ⟨i, hi⟩; exact hk1 ⟨i, hi⟩
    simp [filter_outs_nil hk2, h1]

/-! ### Words of a stream -/

namespace Auto

variable (M : Auto A ni no)

/-- The `len` input columns of word `w` of the streams `L`: column `t` holds entry
`w * len + t` of every stream (`blank` past the end). -/
def cols (L : Fin ni → List (Fin (A + 4))) (len w : ℕ) : List (Fin ni → Fin (A + 4)) :=
  (List.range len).map fun t i => (L i).getD (w * len + t) blank

/-- Output `j` of `M` run from `M.init` on each of the first `nw` words of length `len` of the
streams `L`, concatenated in step order. -/
def outCol (L : Fin ni → List (Fin (A + 4))) (len nw : ℕ) (j : Fin no) : List (Fin (A + 4)) :=
  (List.range nw).flatMap fun w => (M.runWord M.init (cols L len w)).map (· j)

lemma cols_succ_zero (D : Fin ni → List (Fin (A + 4))) (n : ℕ) :
    cols D (n + 1) 0 = (fun i => (D i).head?.getD blank) :: cols (fun i => (D i).tail) n 0 := by
  simp only [cols, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.zero_mul,
    Nat.zero_add]
  congr 1
  · funext i; cases D i <;> rfl
  · apply List.map_congr_left
    intro t _
    funext i
    simp only [Function.comp_apply]
    generalize D i = l
    cases l <;> simp

lemma cols_succ (L : Fin ni → List (Fin (A + 4))) (len w : ℕ) :
    cols L len (w + 1) = cols (fun i => (L i).drop len) len w := by
  simp only [cols]
  apply List.map_congr_left
  intro t _
  funext i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  ring

/-- Inside a stream of `nw` words, the columns of word `w` are read off by plain indexing. -/
lemma getElem_cols {L : Fin ni → List (Fin (A + 4))} {len nw w t : ℕ}
    (hL : ∀ i, (L i).length = nw * len) (hw : w < nw) (ht : t < len) (i : Fin ni) :
    ((cols L len w)[t]'(by simpa [cols] using ht)) i =
      (L i)[w * len + t]'(by rw [hL]; nlinarith) := by
  have hb : w * len + t < (L i).length := by rw [hL]; nlinarith
  have h₁ : (cols L len w)[t]? = some fun i => (L i).getD (w * len + t) blank := by
    simp [cols, ht]
  rw [List.getElem?_eq_getElem (by simpa [cols] using ht), Option.some.injEq] at h₁
  rw [h₁]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]

@[simp] lemma outCol_zero (L : Fin ni → List (Fin (A + 4))) (len : ℕ) (j : Fin no) :
    M.outCol L len 0 j = [] := rfl

lemma outCol_succ (L : Fin ni → List (Fin (A + 4))) (len nw : ℕ) (j : Fin no) :
    M.outCol L len (nw + 1) j =
      (M.runWord M.init (cols L len 0)).map (· j) ++
        M.outCol (fun i => (L i).drop len) len nw j := by
  simp only [outCol, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, cols_succ]

end Auto

/-! ### The word loop and the stream loop -/

/-- The steps of one word: while `ctr` is nonempty, move one counter symbol onto `tmp` and take
one automaton step. -/
def autoInner (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st ctr tmp : Fin T)
    (M : Auto A ni no) : Pr P T Q A U :=
  .loop (·.flag) (.seq (.act (moveStep ctr tmp id)) (.act (autoStep ins outs st M)))

/-- Reset the automaton state and record in `flag` whether input register `ins i0` is
nonempty. -/
def autoReset (ins : Fin ni → Fin T) (i0 : Fin ni) (st : Fin T) (M : Auto A ni no) :
    Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan st M.init }) (peekR (ins i0))

/-- One word: one automaton step per counter symbol, then restore the counter and reset the
state. -/
def autoWord (i0 : Fin ni) (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st ctr tmp : Fin T)
    (M : Auto A ni no) : Pr P T Q A U :=
  .seq (.act (peekR ctr)) (.seq (autoInner ins outs st ctr tmp M)
    (.seq (moveR tmp ctr id) (.act (autoReset ins i0 st M))))

/-- Run the word automaton `M` over the input registers `ins`, word by word, while `ins 0` is
nonempty. Words have the length of the counter register `ctr`; `tmp` is a spare register and
scan slot `st` holds the automaton state. -/
def autoWords [NeZero ni] (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st ctr tmp : Fin T)
    (M : Auto A ni no) : Pr P T Q A U :=
  .seq (.act (autoReset ins 0 st M)) (.loop (·.flag) (autoWord 0 ins outs st ctr tmp M))

/-- Registers after `autoWords`: the inputs `ins` emptied and each output `outs j` topped by
`(out j).reverse`; all other registers unchanged. -/
noncomputable def autoRegs (R : Fin T → List (Fin (A + 4))) (ins : Fin ni → Fin T)
    (outs : Fin no → Fin T) (out : Fin no → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.extend ins (fun _ => [])
    (Function.extend outs (fun j => (out j).reverse ++ R (outs j)) R)

section Regs

variable {R : Fin T → List (Fin (A + 4))} {ins : Fin ni → Fin T} {outs : Fin no → Fin T}
  {out : Fin no → List (Fin (A + 4))}

@[simp] lemma autoRegs_ins (hins : Function.Injective ins) (i : Fin ni) :
    autoRegs R ins outs out (ins i) = [] :=
  hins.extend_apply _ _ i

lemma autoRegs_outs (houts : Function.Injective outs) (hio : ∀ i j, ins i ≠ outs j) (j : Fin no) :
    autoRegs R ins outs out (outs j) = (out j).reverse ++ R (outs j) := by
  rw [autoRegs, Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact hio i j hi),
    houts.extend_apply]

lemma autoRegs_of_notMem {k : Fin T} (h₁ : k ∉ Set.range ins) (h₂ : k ∉ Set.range outs) :
    autoRegs R ins outs out k = R k := by
  rw [autoRegs, Function.extend_apply' _ _ _ h₁, Function.extend_apply' _ _ _ h₂]

end Regs

section Exec

variable {ins : Fin ni → Fin T} {outs : Fin no → Fin T} {st ctr tmp : Fin T}

lemma AutoLayout.ctr_notMem_ins (h : AutoLayout ins outs st ctr tmp) : ctr ∉ Set.range ins := by
  rintro ⟨i, hi⟩; exact h.ins_ctr i hi

lemma AutoLayout.ctr_notMem_outs (h : AutoLayout ins outs st ctr tmp) : ctr ∉ Set.range outs := by
  rintro ⟨j, hj⟩; exact h.outs_ctr j hj

lemma AutoLayout.tmp_notMem_ins (h : AutoLayout ins outs st ctr tmp) : tmp ∉ Set.range ins := by
  rintro ⟨i, hi⟩; exact h.ins_tmp i hi

lemma AutoLayout.tmp_notMem_outs (h : AutoLayout ins outs st ctr tmp) : tmp ∉ Set.range outs := by
  rintro ⟨j, hj⟩; exact h.outs_tmp j hj

/-- The steps of one word, by induction on the counter list `c`: one automaton step per counter
symbol, starting from state `s`; the counter moves onto `tmp` reversed. -/
theorem autoInner_loop (h : AutoLayout ins outs st ctr tmp) (M : Auto A ni no) :
    ∀ (c : List (Fin (A + 4))) (s : Fin (A + 4)) (v : HS T Q A U) (S : Stacks T A),
      S.R ctr = c → v.flag = c.head?.isSome → v.scan st = s →
      ∃ v' S', v'.user = v.user ∧
        Exec body (autoInner ins outs st ctr tmp M) (mk v S) (3 * c.length + 1) (mk v' S') ∧
        AutoFrame ins outs ctr tmp S S' ∧ S'.R ctr = [] ∧ S'.R tmp = c.reverse ++ S.R tmp ∧
        (∀ i, S'.R (ins i) = (S.R (ins i)).drop c.length) ∧
        ∀ j, S'.R (outs j) =
          ((M.runWord s (Auto.cols (fun i => S.R (ins i)) c.length 0)).map (· j)).reverse ++
            S.R (outs j) := by
  intro c
  induction c with
  | nil =>
      intro s v S hc hf _
      refine ⟨v, S, rfl, .loop_false (by simpa using hf), AutoFrame.refl .., hc, by simp, by simp,
        fun j => by simp [Auto.cols, Auto.runWord]⟩
  | cons e rest ih =>
      intro s v S hc hf hs
      set S₁ : Stacks T A :=
        { S with R := Function.update (Function.update S.R ctr rest) tmp (e :: S.R tmp) }
      set v₁ : HS T Q A U := { v with sym := some e, flag := rest.head?.isSome }
      have hrun₁ : (moveStep ctr tmp id : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
        simp [moveStep, peekR, Action.run, hc, update_rt, Function.update_of_ne h.ctr_tmp,
          Function.update_of_ne h.ctr_tmp.symm, S₁, v₁]
      have hR₁ : ∀ k, k ≠ ctr → k ≠ tmp → S₁.R k = S.R k := fun k h1 h2 => by
        simp [S₁, Function.update_of_ne h1, Function.update_of_ne h2]
      have hin₁ : ∀ i, S₁.R (ins i) = S.R (ins i) := fun i => hR₁ _ (h.ins_ctr i) (h.ins_tmp i)
      have hout₁ : ∀ j, S₁.R (outs j) = S.R (outs j) :=
        fun j => hR₁ _ (h.outs_ctr j) (h.outs_tmp j)
      have htop : topCol ins S₁ = topCol ins S := by funext i; simp [topCol, hin₁]
      obtain ⟨v₂, S₂, hrun₂, hu₂, hf₂, hs₂, hi₂, ho₂, hl₂, hin₂, hout₂, hoth₂⟩ :=
        autoStep_run h.ins_inj h.outs_inj h.ins_outs h.ins_st M v₁ S₁
      have hc₂ : S₂.R ctr = rest := by
        rw [hoth₂ _ h.ctr_notMem_ins h.ctr_notMem_outs]
        simp [S₁, Function.update_of_ne h.ctr_tmp]
      have ht₂ : S₂.R tmp = e :: S.R tmp := by
        rw [hoth₂ _ h.tmp_notMem_ins h.tmp_notMem_outs]; simp [S₁]
      obtain ⟨v₃, S₃, hu₃, he₃, hfr₃, hc₃, ht₃, hin₃, hout₃⟩ :=
        ih _ v₂ S₂ hc₂ (by rw [hf₂]) hs₂
      refine ⟨v₃, S₃, by rw [hu₃, hu₂], ?_, ?_, hc₃, ?_, ?_, ?_⟩
      · refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (Exec.seq (hrun₁ ▸ Exec.act (body := body) (moveStep ctr tmp id) (mk v S))
            (hrun₂ ▸ Exec.act (body := body) (autoStep ins outs st M) (mk v₁ S₁))) he₃)
          (by simp; ring) rfl
      · exact AutoFrame.trans (S₂ := S₁) ⟨rfl, rfl, rfl, fun k _ _ h1 h2 => hR₁ k h1 h2⟩
          (AutoFrame.trans (S₂ := S₂) ⟨hi₂, ho₂, hl₂, fun k h1 h2 _ _ => hoth₂ k h1 h2⟩ hfr₃)
      · rw [ht₃, ht₂]; simp
      · intro i
        rw [hin₃, hin₂, hin₁, List.drop_tail]; rfl
      · intro j
        have hD : (fun i => S₂.R (ins i)) = fun i => (S.R (ins i)).tail := by
          funext i; rw [hin₂, hin₁]
        have hs₁ : v₁.scan st = s := hs
        rw [hout₃, hout₂, hout₁, hD, htop, hs₁, List.length_cons, Auto.cols_succ_zero]
        simp [Auto.runWord]
        rfl

/-- One word from state `M.init`: `cs.length` automaton steps, the counter restored, the state
reset, and `flag` set for the next word. -/
theorem autoWord_exec (h : AutoLayout ins outs st ctr tmp) (M : Auto A ni no) (i0 : Fin ni)
    {cs : List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A)
    (hctr : S.R ctr = cs) (htmp : S.R tmp = []) (hv : v.scan st = M.init) :
    ∃ v' S', v'.user = v.user ∧
      Exec body (autoWord i0 ins outs st ctr tmp M) (mk v S) (5 * cs.length + 5) (mk v' S') ∧
      v'.scan st = M.init ∧ v'.flag = (S'.R (ins i0)).head?.isSome ∧
      AutoFrame ins outs ctr tmp S S' ∧ S'.R ctr = cs ∧ S'.R tmp = [] ∧
      (∀ i, S'.R (ins i) = (S.R (ins i)).drop cs.length) ∧
      ∀ j, S'.R (outs j) =
        ((M.runWord M.init (Auto.cols (fun i => S.R (ins i)) cs.length 0)).map (· j)).reverse ++
          S.R (outs j) := by
  have hf₀ : ({ v with flag := (S.R ctr).head?.isSome } : HS T Q A U).flag = cs.head?.isSome := by
    simp [hctr]
  obtain ⟨v₁, S₁, hu₁, he₁, hfr₁, hc₁, ht₁, hin₁, hout₁⟩ :=
    autoInner_loop body h M cs M.init { v with flag := (S.R ctr).head?.isSome } S hctr hf₀ hv
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp ctr h.ctr_tmp.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R tmp ctr id (S₁.R tmp) }
  have hR₂ : ∀ k, k ≠ ctr → k ≠ tmp → S₂.R k = S₁.R k := fun k h1 h2 => by
    simp [S₂, movedR, Function.update_of_ne h1, Function.update_of_ne h2]
  have hc₂ : S₂.R ctr = cs := by simp [S₂, movedR, ht₁, htmp, hc₁]
  have ht₂ : S₂.R tmp = [] := by simp [S₂, movedR, Function.update_of_ne h.ctr_tmp.symm]
  have hin₂ : ∀ i, S₂.R (ins i) = S₁.R (ins i) := fun i => hR₂ _ (h.ins_ctr i) (h.ins_tmp i)
  have hout₂ : ∀ j, S₂.R (outs j) = S₁.R (outs j) :=
    fun j => hR₂ _ (h.outs_ctr j) (h.outs_tmp j)
  set v₃ : HS T Q A U := { v₂ with scan := Function.update v₂.scan st M.init
                                   flag := (S₂.R (ins i0)).head?.isSome }
  have hrun₃ : (autoReset ins i0 st M : Act T Q A U).run (mk v₂ S₂) = mk v₃ S₂ := rfl
  refine ⟨v₃, S₂, by simp [v₃, hu₂, hu₁], ?_, by simp [v₃], rfl, ?_, hc₂, ht₂, ?_, ?_⟩
  · have := Exec.seq (peekR_run ctr v S ▸ Exec.act (body := body) (peekR ctr) (mk v S))
      (Exec.seq he₁ (Exec.seq he₂
        (hrun₃ ▸ Exec.act (body := body) (autoReset ins i0 st M) (mk v₂ S₂))))
    refine Exec.cast this ?_ rfl
    rw [ht₁, htmp]; simp; ring
  · exact AutoFrame.trans hfr₁ ⟨rfl, rfl, rfl, fun k _ _ h1 h2 => hR₂ k h1 h2⟩
  · intro i; rw [hin₂, hin₁]
  · intro j; rw [hout₂, hout₁]

/-- The stream loop over `nw` words, by induction on `nw`. -/
theorem autoWords_loop (h : AutoLayout ins outs st ctr tmp) (M : Auto A ni no) (i0 : Fin ni)
    {cs : List (Fin (A + 4))} (hcs : cs ≠ []) :
    ∀ (nw : ℕ) (v : HS T Q A U) (S : Stacks T A), S.R ctr = cs → S.R tmp = [] →
      (∀ i, (S.R (ins i)).length = nw * cs.length) → v.scan st = M.init →
      v.flag = (S.R (ins i0)).head?.isSome →
      ∃ v' S', v'.user = v.user ∧
        Exec body (.loop (·.flag) (autoWord i0 ins outs st ctr tmp M)) (mk v S)
          (nw * (5 * cs.length + 6) + 1) (mk v' S') ∧
        AutoFrame ins outs ctr tmp S S' ∧ S'.R ctr = cs ∧ S'.R tmp = [] ∧
        (∀ i, S'.R (ins i) = []) ∧
        ∀ j, S'.R (outs j) =
          (M.outCol (fun i => S.R (ins i)) cs.length nw j).reverse ++ S.R (outs j) := by
  intro nw
  induction nw with
  | zero =>
      intro v S hctr htmp hlen _ hf
      have hnil : ∀ i, S.R (ins i) = [] := fun i => List.eq_nil_of_length_eq_zero (by simp [hlen])
      refine ⟨v, S, rfl, Exec.cast (.loop_false (by simp [hf, hnil])) (by simp) rfl,
        AutoFrame.refl .., hctr, htmp, hnil, fun j => by simp⟩
  | succ nw ih =>
      intro v S hctr htmp hlen hv hf
      have hpos : 0 < cs.length := List.length_pos_iff.mpr hcs
      have hne : S.R (ins i0) ≠ [] := by
        intro he
        have h2 : (nw + 1) * cs.length = 0 := by rw [← hlen i0, he]; rfl
        have h3 : 0 < (nw + 1) * cs.length := Nat.mul_pos (by omega) hpos
        omega
      have hft : v.flag = true := by
        rw [hf]; cases hR : S.R (ins i0) with
        | nil => exact absurd hR hne
        | cons _ _ => rfl
      obtain ⟨v₁, S₁, hu₁, he₁, hs₁, hf₁, hfr₁, hc₁, ht₁, hin₁, hout₁⟩ :=
        autoWord_exec body h M i0 v S hctr htmp hv
      obtain ⟨v₂, S₂, hu₂, he₂, hfr₂, hc₂, ht₂, hin₂, hout₂⟩ := ih v₁ S₁ hc₁ ht₁
        (fun i => by rw [hin₁, List.length_drop, hlen]; rw [Nat.succ_mul]; omega) hs₁ hf₁
      refine ⟨v₂, S₂, by rw [hu₂, hu₁], ?_, hfr₁.trans hfr₂, hc₂, ht₂, fun i => hin₂ i, ?_⟩
      · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft he₁ he₂) (by ring) rfl
      · intro j
        have hD : (fun i => S₁.R (ins i)) = fun i => (S.R (ins i)).drop cs.length := by
          funext i; rw [hin₁]
        rw [hout₂, hout₁, hD, Auto.outCol_succ]
        simp

end Exec

/-- `autoWords` over `nw` words of `len` steps: the input registers hold the streams `L`, the
counter register `ctr` holds `len` arbitrary symbols and `tmp` is empty. The inputs end empty,
each output register `outs j` gains `(M.outCol L len nw j).reverse` on top, and every other
register (`ctr` and `tmp` included) ends as it started. The step count is exactly
`nw * (5 * len + 6) + 2`. -/
theorem autoWords_exec [NeZero ni] {ins : Fin ni → Fin T} {outs : Fin no → Fin T}
    {st ctr tmp : Fin T} (h : AutoLayout ins outs st ctr tmp) (M : Auto A ni no) {len nw : ℕ}
    (hlen : 1 ≤ len)
    {cs : List (Fin (A + 4))} (hcs : cs.length = len) (L : Fin ni → List (Fin (A + 4)))
    (hL : ∀ i, (L i).length = nw * len) (v : HS T Q A U) (S : Stacks T A)
    (hctr : S.R ctr = cs) (htmp : S.R tmp = []) (hin : ∀ i, S.R (ins i) = L i) :
    ∃ v' m, v'.user = v.user ∧ m ≤ nw * (5 * len + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp M) (mk v S) m
        (mk v' { S with R := autoRegs S.R ins outs (M.outCol L len nw) }) := by
  have hcs' : cs ≠ [] := by rintro rfl; simp at hcs; omega
  set v₀ : HS T Q A U := { v with scan := Function.update v.scan st M.init
                                  flag := (S.R (ins 0)).head?.isSome }
  have hrun₀ : (autoReset ins 0 st M : Act T Q A U).run (mk v S) = mk v₀ S := rfl
  obtain ⟨v', S', hu, he, hfr, hc', ht', hin', hout'⟩ :=
    autoWords_loop body h M 0 hcs' nw v₀ S hctr htmp (fun i => by rw [hin, hL, hcs])
      (by simp [v₀]) rfl
  refine ⟨v', _, hu, le_refl _, ?_⟩
  refine Exec.cast
    (Exec.seq (hrun₀ ▸ Exec.act (body := body) (autoReset ins 0 st M) (mk v S)) he)
    (by rw [hcs]; ring) ?_
  obtain ⟨hi, ho, hl, hoth⟩ := hfr
  congr 1
  refine Stacks.ext hi ho hl ?_
  funext k
  dsimp only
  by_cases hk : k ∈ Set.range ins
  · obtain ⟨i, rfl⟩ := hk
    rw [hin', autoRegs_ins h.ins_inj]
  by_cases hk' : k ∈ Set.range outs
  · obtain ⟨j, rfl⟩ := hk'
    have hD : (fun i => S.R (ins i)) = L := funext hin
    rw [hout', autoRegs_outs h.outs_inj h.ins_outs, hD, hcs]
  rw [autoRegs_of_notMem hk hk']
  by_cases hkc : k = ctr
  · subst hkc; rw [hc', hctr]
  by_cases hkt : k = tmp
  · subst hkt; rw [ht', htmp]
  exact hoth k hk hk' hkc hkt

/-! ### Streams given as lists of words -/

namespace Auto

variable (M : Auto A ni no)

/-- Input register `i` of a stream given as a list of words, each a list of input columns. -/
def stream (W : List (List (Fin ni → Fin (A + 4)))) (i : Fin ni) : List (Fin (A + 4)) :=
  W.flatMap fun w => w.map (· i)

lemma stream_length {len : ℕ} (W : List (List (Fin ni → Fin (A + 4))))
    (hW : ∀ w ∈ W, w.length = len) (i : Fin ni) : (stream W i).length = W.length * len := by
  induction W with
  | nil => simp [stream]
  | cons w W ih =>
      simp only [stream, List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons] at ih ⊢
      rw [ih (fun w' hw' => hW w' (List.mem_cons_of_mem _ hw')), hW w List.mem_cons_self]
      ring

lemma cols_stream {len : ℕ} (w : List (Fin ni → Fin (A + 4)))
    (W : List (List (Fin ni → Fin (A + 4)))) (hw : w.length = len) :
    cols (stream (w :: W)) len 0 = w := by
  subst hw
  apply List.ext_getElem?
  intro t
  by_cases ht : t < w.length
  · simp only [cols, List.getElem?_map, List.getElem?_range ht, Option.map_some,
      List.getElem?_eq_getElem ht, Option.some.injEq]
    funext i
    simp [stream, List.getD_eq_getElem?_getD, List.getElem?_append_left, ht]
  · simp [cols, List.getElem?_eq_none (Nat.le_of_not_lt ht), ht]

/-- Output `j` of `M` run from `M.init` on each word of `W`, concatenated in step order. -/
def outWords (W : List (List (Fin ni → Fin (A + 4)))) (j : Fin no) : List (Fin (A + 4)) :=
  W.flatMap fun w => (M.runWord M.init w).map (· j)

lemma outCol_stream {len : ℕ} (W : List (List (Fin ni → Fin (A + 4))))
    (hW : ∀ w ∈ W, w.length = len) (j : Fin no) :
    M.outCol (stream W) len W.length j = M.outWords W j := by
  unfold outWords
  induction W with
  | nil => rfl
  | cons w W ih =>
      have hw := hW w List.mem_cons_self
      have hdrop : (fun i => (stream (w :: W) i).drop len) = stream W := by
        funext i
        simp only [stream, List.flatMap_cons]
        exact List.drop_left' (by simp [hw])
      rw [List.length_cons, outCol_succ, cols_stream w W hw, hdrop,
        ih (fun w' hw' => hW w' (List.mem_cons_of_mem _ hw')), List.flatMap_cons]

end Auto

/-- `autoWords_exec` for a stream given as a list `W` of words of `len` input columns each. -/
theorem autoWords_exec_words [NeZero ni] {ins : Fin ni → Fin T} {outs : Fin no → Fin T}
    {st ctr tmp : Fin T} (h : AutoLayout ins outs st ctr tmp) (M : Auto A ni no) {len : ℕ}
    (hlen : 1 ≤ len) {cs : List (Fin (A + 4))} (hcs : cs.length = len)
    (W : List (List (Fin ni → Fin (A + 4)))) (hW : ∀ w ∈ W, w.length = len) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = cs) (htmp : S.R tmp = [])
    (hin : ∀ i, S.R (ins i) = Auto.stream W i) :
    ∃ v' m, v'.user = v.user ∧ m ≤ W.length * (5 * len + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp M) (mk v S) m
        (mk v' { S with R := autoRegs S.R ins outs (M.outWords W) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := autoWords_exec body h M hlen hcs (Auto.stream W)
    (Auto.stream_length W hW) v S hctr htmp hin
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  congr 3
  funext j
  exact M.outCol_stream W hW j

end IntegerMultBounds.MathlibTM2.Host
