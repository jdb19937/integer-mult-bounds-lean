module

public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
public import IntegerMultBounds.MathlibTM2.Host.Auto
public import IntegerMultBounds.MathlibTM2.Layer.Format
public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# Two-carry bit automata and the sign selection

**Two-carry automata** (`Duo`). A `Duo A ni no` reads one symbol from each of `ni` registers per
step and runs two columns of the signed-carry adder `carryRun` of `Layer/Carry`: from the input
column it forms two column sums (`sums`, each in `[-2, 2]`, depending on two mode bits fixed for
the run), and emits one symbol on each of `no` registers (`out`, a function of the input column
and the two emitted bits). Its state symbol codes the two mode bits and the two carries
(`duoSym`, `duoDec`; `100` codes, so `96 ≤ A`). `Duo.runWord_ofFn`: from carries `0`, the outputs
are the emitted bits of `carryRun` on the column sums, so `carryRun_nat` turns them into the
bits of an integer combination modulo `2^K`.

**Counted pass** (`dpass`). `initDuo` peeks four registers `r₁ … r₄`, computes the mode bits
`f (top r₁) (top r₂) (top r₃) (top r₄)` from their top bits, loads the initial state into the scan
slot of the spare register `tmp` and tests the counter `ctr`; then `autoInner` runs one step per
counter symbol and `moveR` restores the counter. `dpass_exec`: exactly `5 K + 4` steps for a
counter of `K` symbols; the inputs lose their first `K` symbols, each output gains its `K` output
symbols in reverse (the last on top), every other register ends as it started.

**Sign selection** (`selectP X Y M Sg`). `X` and `Y` hold the residues of `x` and `-x`, most
significant bit on top. The top bit of `X` is pushed onto `Sg` and selects the register that
moves onto `M` (least significant bit on top again); the other is cleared. `selectP_exec`:
exactly `2 |X| + 2 |Y| + 6` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

set_option linter.unusedSimpArgs false

/-! ### State codes -/

/-- The code of two mode bits and two carries in `[-2, 2]`. -/
def duoCode (m₁ m₂ : Bool) (c₁ c₂ : ℤ) : ℕ :=
  m₁.toNat + 2 * m₂.toNat + 4 * (c₁ + 2).toNat + 20 * (c₂ + 2).toNat

/-- The state symbol of two mode bits and two carries. -/
def duoSym (A : ℕ) (m₁ m₂ : Bool) (c₁ c₂ : ℤ) : Fin (A + 4) :=
  ⟨duoCode m₁ m₂ c₁ c₂ % (A + 4), Nat.mod_lt _ (by omega)⟩

/-- Decode a state symbol: mode bits and carries. -/
def duoDec {A : ℕ} (x : Fin (A + 4)) : Bool × Bool × ℤ × ℤ :=
  (decide (x.val % 2 = 1), decide (x.val / 2 % 2 = 1), ((x.val / 4 % 5 : ℕ) : ℤ) - 2,
    ((x.val / 20 % 5 : ℕ) : ℤ) - 2)

lemma duoDec_duoSym {A : ℕ} (hA : 96 ≤ A) (m₁ m₂ : Bool) {c₁ c₂ : ℤ} (h₁ : |c₁| ≤ 2)
    (h₂ : |c₂| ≤ 2) : duoDec (duoSym A m₁ m₂ c₁ c₂) = (m₁, m₂, c₁, c₂) := by
  rw [abs_le] at h₁ h₂
  have hlt : duoCode m₁ m₂ c₁ c₂ < A + 4 := by
    unfold duoCode; cases m₁ <;> cases m₂ <;> simp <;> omega
  have hv : (duoSym A m₁ m₂ c₁ c₂).val = duoCode m₁ m₂ c₁ c₂ := Nat.mod_eq_of_lt hlt
  simp only [duoDec, hv, duoCode, Prod.mk.injEq]
  cases m₁ <;> cases m₂ <;> simp <;> omega

/-! ### Two-carry automata -/

/-- A two-carry bit automaton: two column sums from the mode bits and the input column, and the
output symbols from the input column and the two emitted bits. -/
structure Duo (A ni no : ℕ) where
  sums : Bool → Bool → (Fin ni → Fin (A + 4)) → ℤ × ℤ
  out : (Fin ni → Fin (A + 4)) → Bool → Bool → Fin no → Fin (A + 4)

namespace Duo

variable {A ni no : ℕ} (D : Duo A ni no)

/-- One step: decode, one column of each carry adder, encode. -/
def step (s : Fin (A + 4)) (col : Fin ni → Fin (A + 4)) : Fin (A + 4) × (Fin no → Fin (A + 4)) :=
  let d := duoDec s
  let r₁ := cstep d.2.2.1 (D.sums d.1 d.2.1 col).1
  let r₂ := cstep d.2.2.2 (D.sums d.1 d.2.1 col).2
  (duoSym A d.1 d.2.1 r₁.2 r₂.2, D.out col r₁.1 r₂.1)

/-- The word automaton of a two-carry automaton. -/
def auto : Auto A ni no := ⟨blank, D.step⟩

/-- Column sums lie in `[-2, 2]`. -/
def Bounded : Prop := ∀ m₁ m₂ col, |(D.sums m₁ m₂ col).1| ≤ 2 ∧ |(D.sums m₁ m₂ col).2| ≤ 2

/-- The bits emitted by the first carry adder from carry `c`. -/
def bitsA (m₁ m₂ : Bool) {K : ℕ} (col : Fin K → Fin ni → Fin (A + 4)) (c : ℤ) : List Bool :=
  (carryRun c (List.ofFn fun t => (D.sums m₁ m₂ (col t)).1)).1

/-- The bits emitted by the second carry adder from carry `c`. -/
def bitsB (m₁ m₂ : Bool) {K : ℕ} (col : Fin K → Fin ni → Fin (A + 4)) (c : ℤ) : List Bool :=
  (carryRun c (List.ofFn fun t => (D.sums m₁ m₂ (col t)).2)).1

lemma bitsA_succ (m₁ m₂ : Bool) {K : ℕ} (col : Fin (K + 1) → Fin ni → Fin (A + 4)) (c : ℤ) :
    D.bitsA m₁ m₂ col c = (cstep c (D.sums m₁ m₂ (col 0)).1).1 ::
      D.bitsA m₁ m₂ (fun t => col t.succ) (cstep c (D.sums m₁ m₂ (col 0)).1).2 := by
  simp only [bitsA, List.ofFn_succ, carryRun_cons_fst]

lemma bitsB_succ (m₁ m₂ : Bool) {K : ℕ} (col : Fin (K + 1) → Fin ni → Fin (A + 4)) (c : ℤ) :
    D.bitsB m₁ m₂ col c = (cstep c (D.sums m₁ m₂ (col 0)).2).1 ::
      D.bitsB m₁ m₂ (fun t => col t.succ) (cstep c (D.sums m₁ m₂ (col 0)).2).2 := by
  simp only [bitsB, List.ofFn_succ, carryRun_cons_fst]

/-- The outputs of a run: one output column per input column, from the emitted bits. -/
theorem runWord_ofFn (hA : 96 ≤ A) (hD : D.Bounded) (m₁ m₂ : Bool) :
    ∀ (K : ℕ) (col : Fin K → Fin ni → Fin (A + 4)) (c₁ c₂ : ℤ), |c₁| ≤ 2 → |c₂| ≤ 2 →
      D.auto.runWord (duoSym A m₁ m₂ c₁ c₂) (List.ofFn col) =
        List.ofFn fun t => D.out (col t) ((D.bitsA m₁ m₂ col c₁).getD t false)
          ((D.bitsB m₁ m₂ col c₂).getD t false) := by
  intro K
  induction K with
  | zero => intro col c₁ c₂ _ _; rfl
  | succ K ih =>
      intro col c₁ c₂ h₁ h₂
      rw [List.ofFn_succ, Auto.runWord]
      have hs : D.auto.step (duoSym A m₁ m₂ c₁ c₂) (col 0) =
          (duoSym A m₁ m₂ (cstep c₁ (D.sums m₁ m₂ (col 0)).1).2
              (cstep c₂ (D.sums m₁ m₂ (col 0)).2).2,
            D.out (col 0) (cstep c₁ (D.sums m₁ m₂ (col 0)).1).1
              (cstep c₂ (D.sums m₁ m₂ (col 0)).2).1) := by
        simp only [auto, step, duoDec_duoSym hA m₁ m₂ h₁ h₂]
      rw [hs]
      dsimp only
      rw [ih (fun t => col t.succ) _ _ (cstep_bound h₁ (hD _ _ _).1)
        (cstep_bound h₂ (hD _ _ _).2), List.ofFn_succ, bitsA_succ, bitsB_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]

end Duo

/-! ### Columns of registers -/

/-- The columns read from registers whose first `K` symbols are given by `col`. -/
lemma cols_eq_ofFn {A ni : ℕ} (L : Fin ni → List (Fin (A + 4))) (K : ℕ)
    (col : Fin K → Fin ni → Fin (A + 4)) (h : ∀ i (t : Fin K), (L i).getD t blank = col t i) :
    Auto.cols L K 0 = List.ofFn col := by
  apply List.ext_getElem
  · simp [Auto.cols]
  · intro t h₁ h₂
    simp only [Auto.cols, List.getElem_map, List.getElem_range, List.getElem_ofFn, zero_mul,
      zero_add]
    funext i
    exact h i ⟨t, by simpa using h₂⟩

/-! ### The counted pass -/

section Pass

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {ni no : ℕ}

/-- Peek register `r` into its scan slot, then run `a`. -/
def peekSlot (r : Fin T) (a : Act T Q A U) : Act T Q A U :=
  .peek (.rt r) (fun v o => { v with scan := Function.update v.scan r (o.getD blank) }) a

/-- The mode bits from the scan slots `r₁ … r₄`. -/
def modeOf (f : Bool → Bool → Bool → Bool → Bool × Bool) (r₁ r₂ r₃ r₄ : Fin T)
    (v : HS T Q A U) : Bool × Bool :=
  f (symBit (v.scan r₁)) (symBit (v.scan r₂)) (symBit (v.scan r₃)) (symBit (v.scan r₄))

/-- Start a pass: peek `r₁ … r₄`, load the initial state with the mode bits into slot `st`, and
test the counter `ctr`. -/
def initDuo (f : Bool → Bool → Bool → Bool → Bool × Bool) (r₁ r₂ r₃ r₄ st ctr : Fin T) :
    Act T Q A U :=
  peekSlot r₁ (peekSlot r₂ (peekSlot r₃ (peekSlot r₄
    (.load (fun v => { v with
      scan := Function.update v.scan st
        (duoSym A (modeOf f r₁ r₂ r₃ r₄ v).1 (modeOf f r₁ r₂ r₃ r₄ v).2 0 0) })
      (peekR ctr)))))

/-- The top bit of a register (`false` when it is empty or its top is not a bit). -/
def topBit (S : Stacks T A) (r : Fin T) : Bool := symBit ((S.R r).head?.getD blank)

lemma update4_apply {α β : Type} [DecidableEq α] (g h : α → β) (r₁ r₂ r₃ r₄ : α) {x : α}
    (hx : x = r₁ ∨ x = r₂ ∨ x = r₃ ∨ x = r₄) :
    Function.update (Function.update (Function.update (Function.update g r₁ (h r₁)) r₂ (h r₂))
      r₃ (h r₃)) r₄ (h r₄) x = h x := by
  simp only [Function.update_apply]
  split_ifs with h4 h3 h2 h1 <;> subst_vars <;> first | rfl | (rcases hx with rfl | rfl | rfl | rfl <;> simp_all)

lemma initDuo_run (f : Bool → Bool → Bool → Bool → Bool × Bool) (r₁ r₂ r₃ r₄ st ctr : Fin T)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', (initDuo f r₁ r₂ r₃ r₄ st ctr).run (mk v S) = mk v' S ∧ v'.user = v.user ∧
      v'.flag = (S.R ctr).head?.isSome ∧
      v'.scan st = duoSym A (f (topBit S r₁) (topBit S r₂) (topBit S r₃) (topBit S r₄)).1
        (f (topBit S r₁) (topBit S r₂) (topBit S r₃) (topBit S r₄)).2 0 0 := by
  set g : Fin T → Fin (A + 4) := fun r => (S.R r).head?.getD blank with hg
  set sc := Function.update (Function.update (Function.update (Function.update v.scan r₁ (g r₁))
    r₂ (g r₂)) r₃ (g r₃)) r₄ (g r₄) with hsc
  have hm : modeOf f r₁ r₂ r₃ r₄ { v with scan := sc } =
      f (topBit S r₁) (topBit S r₂) (topBit S r₃) (topBit S r₄) := by
    simp only [modeOf, topBit]
    rw [hsc, update4_apply v.scan g r₁ r₂ r₃ r₄ (by simp),
      update4_apply v.scan g r₁ r₂ r₃ r₄ (by simp), update4_apply v.scan g r₁ r₂ r₃ r₄ (by simp),
      update4_apply v.scan g r₁ r₂ r₃ r₄ (by simp)]
  refine ⟨{ v with
      scan := Function.update sc st (duoSym A (modeOf f r₁ r₂ r₃ r₄ { v with scan := sc }).1
        (modeOf f r₁ r₂ r₃ r₄ { v with scan := sc }).2 0 0)
      flag := (S.R ctr).head?.isSome }, ?_, rfl, rfl, by simp [hm]⟩
  simp only [initDuo, peekSlot, Action.run, peekR, mk_var, mk_stk, get_rt, store_mk]
  rfl

/-- A counted pass of a two-carry automaton: initial state with mode bits from `r₁ … r₄`, one
step per counter symbol, counter restored. The state lives in the scan slot of `tmp`. -/
def dpass (D : Duo A ni no) (f : Bool → Bool → Bool → Bool → Bool × Bool) (r₁ r₂ r₃ r₄ : Fin T)
    (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (ctr tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (initDuo f r₁ r₂ r₃ r₄ tmp ctr))
    (.seq (autoInner ins outs tmp ctr tmp D.auto) (moveR tmp ctr id))

/-- Running a counted pass. -/
theorem dpass_exec (D : Duo A ni no) (hA : 96 ≤ A) (hD : D.Bounded)
    (f : Bool → Bool → Bool → Bool → Bool × Bool) (r₁ r₂ r₃ r₄ : Fin T)
    {ins : Fin ni → Fin T} {outs : Fin no → Fin T} {ctr tmp : Fin T}
    (h : AutoLayout ins outs tmp ctr tmp) (v : HS T Q A U) (S : Stacks T A) {K : ℕ}
    (hctr : (S.R ctr).length = K) (htmp : S.R tmp = [])
    (col : Fin K → Fin ni → Fin (A + 4))
    (hcol : ∀ i (t : Fin K), (S.R (ins i)).getD t blank = col t i)
    (m : Bool × Bool) (hm : f (topBit S r₁) (topBit S r₂) (topBit S r₃) (topBit S r₄) = m) :
    ∃ v' S', v'.user = v.user ∧
      Exec body (dpass D f r₁ r₂ r₃ r₄ ins outs ctr tmp) (mk v S) (5 * K + 4) (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (ins i) = (S.R (ins i)).drop K) ∧
      (∀ j, S'.R (outs j) = (List.ofFn fun t => D.out (col t)
          ((D.bitsA m.1 m.2 col 0).getD t false) ((D.bitsB m.1 m.2 col 0).getD t false) j).reverse ++
        S.R (outs j)) ∧
      ∀ k, k ∉ Set.range ins → k ∉ Set.range outs → S'.R k = S.R k := by
  obtain ⟨v₁, hrun₁, hu₁, hf₁, hs₁⟩ := initDuo_run f r₁ r₂ r₃ r₄ tmp ctr v S
  rw [hm] at hs₁
  obtain ⟨v₂, S₂, hu₂, he₂, hfr₂, hc₂, ht₂, hin₂, hout₂⟩ :=
    autoInner_loop body h D.auto (S.R ctr) _ v₁ S rfl hf₁ hs₁
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body tmp ctr h.ctr_tmp.symm id v₂ S₂
  have hcols := cols_eq_ofFn (fun i => S.R (ins i)) K col hcol
  have hrw := D.runWord_ofFn hA hD m.1 m.2 K col 0 0 (by simp) (by simp)
  refine ⟨v₃, { S₂ with R := movedR S₂.R tmp ctr id (S₂.R tmp) }, by rw [hu₃, hu₂, hu₁], ?_,
    hfr₂.1, hfr₂.2.1, hfr₂.2.2.1, ?_, ?_, ?_⟩
  · refine Exec.cast (Exec.seq (hrun₁ ▸ Exec.act (body := body) _ (mk v S))
      (Exec.seq he₂ he₃)) ?_ rfl
    simp only [ht₂, htmp, List.append_nil, List.length_reverse, hctr]; ring
  · intro i
    simp only [movedR, Function.update_of_ne (h.ins_ctr i), Function.update_of_ne (h.ins_tmp i)]
    rw [hin₂, hctr]
  · intro j
    simp only [movedR, Function.update_of_ne (h.outs_ctr j), Function.update_of_ne (h.outs_tmp j)]
    rw [hout₂, hctr, hcols, hrw, List.map_ofFn]
    rfl
  · intro k hk1 hk2
    by_cases hkc : k = ctr
    · rw [hkc]; simp [movedR, ht₂, htmp, hc₂]
    by_cases hkt : k = tmp
    · rw [hkt]; simp [movedR, Function.update_of_ne h.ctr_tmp.symm, htmp]
    · simp only [movedR, Function.update_of_ne hkc, Function.update_of_ne hkt]
      exact hfr₂.2.2.2 k hk1 hk2 hkc hkt

end Pass

/-! ### Sign selection -/

section Select

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Record the top bit of `X` in `flag` and push the top symbol onto `Sg`. -/
def signStep (X Sg : Fin T) : Act T Q A U :=
  .peek (.rt X) (fun v o => { v with flag := symBit (o.getD blank), sym := o })
    (.push (.rt Sg) (fun v => v.sym.getD blank) .done)

/-- Select by the top bit of `X`: move `Y` (bit set) or `X` (bit clear) onto `M` and clear the
other; the top symbol of `X` goes onto `Sg`. -/
def selectP (X Y M Sg : Fin T) : Pr P T Q A U :=
  .seq (.act (signStep X Sg))
    (.cond (·.flag) (.seq (moveR Y M id) (uclear X)) (.seq (moveR X M id) (uclear Y)))

/-- Running a sign selection. -/
theorem selectP_exec {X Y M Sg : Fin T} (hd : [X, Y, M, Sg].Nodup) (v : HS T Q A U)
    (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (selectP X Y M Sg) (mk v S) (2 * (S.R X).length + 2 * (S.R Y).length + 6)
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R X []) Y [])
            M ((if topBit S X then (S.R Y).reverse else (S.R X).reverse) ++ S.R M))
            Sg ((S.R X).head?.getD blank :: S.R Sg) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hXY, hXM, hXS⟩, ⟨hYM, hYS⟩, hMS, -⟩ := hd
  set v₁ : HS T Q A U := { v with flag := topBit S X, sym := (S.R X).head? }
  set S₁ : Stacks T A := { S with R := Function.update S.R Sg ((S.R X).head?.getD blank :: S.R Sg) }
  have hrun : (signStep X Sg : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
    simp [signStep, Action.run, update_rt, v₁, S₁, topBit]
  have e₁ := hrun ▸ Exec.act (body := body) (signStep X Sg) (mk v S)
  have hX₁ : S₁.R X = S.R X := by simp [S₁, Function.update_of_ne hXS]
  have hY₁ : S₁.R Y = S.R Y := by simp [S₁, Function.update_of_ne hYS]
  have hM₁ : S₁.R M = S.R M := by simp [S₁, Function.update_of_ne hMS]
  by_cases hs : topBit S X = true
  · obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body Y M hYM id v₁ S₁
    obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body X v₂ { S₁ with R := movedR S₁.R Y M id (S₁.R Y) }
    refine ⟨v₃, by rw [hu₃, hu₂], Exec.cast (Exec.seq e₁ (Exec.cond_true (by simp [v₁, hs])
      (Exec.seq e₂ e₃))) ?_ ?_⟩
    · simp [movedR, hY₁, Function.update_of_ne hXY, Function.update_of_ne hXM, hX₁]; ring
    · congr 2
      funext k
      simp only [movedR, S₁, Function.update_apply, hs, if_true, List.map_id]
      by_cases k1 : k = Sg
      · rw [k1]; simp [Ne.symm hXS, Ne.symm hYS, Ne.symm hMS]
      by_cases k2 : k = M
      · rw [k2]; simp [Ne.symm hXM, Ne.symm hYM, hMS, hYS, hXS]
      by_cases k3 : k = Y
      · rw [k3]; simp [Ne.symm hXY, hYM, hYS]
      by_cases k4 : k = X
      · rw [k4]; simp [hXY, hXM, hXS]
      · simp [k1, k2, k3, k4]
  · obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body X M hXM id v₁ S₁
    obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body Y v₂ { S₁ with R := movedR S₁.R X M id (S₁.R X) }
    refine ⟨v₃, by rw [hu₃, hu₂], Exec.cast (Exec.seq e₁ (Exec.cond_false (by simp [v₁, hs])
      (Exec.seq e₂ e₃))) ?_ ?_⟩
    · simp [movedR, hY₁, Function.update_of_ne (Ne.symm hXY), Function.update_of_ne hYM, hX₁]; ring
    · congr 2
      funext k
      simp only [movedR, S₁, Function.update_apply, hs, List.map_id]
      by_cases k1 : k = Sg
      · rw [k1]; simp [Ne.symm hXS, Ne.symm hYS, Ne.symm hMS]
      by_cases k2 : k = M
      · rw [k2]; simp [Ne.symm hXM, Ne.symm hYM, hMS, hYS, hXS]
      by_cases k3 : k = Y
      · rw [k3]; simp [Ne.symm hXY, hYM, hYS]
      by_cases k4 : k = X
      · rw [k4]; simp [hXY, hXM, hXS]
      · simp [k1, k2, k3, k4]

end Select

end IntegerMultBounds.MathlibTM2.Fast
