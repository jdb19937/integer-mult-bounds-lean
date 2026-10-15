module

public import IntegerMultBounds.MathlibTM2.Fast.RingProdBase

/-!
# Registers of the ring-product stage and register-level contracts

**Registers.** The stage uses the host registers `rg r`, `r : RpReg` (`rg` injective), and the
91 registers `ι j` of the placed vendored ring product (`ι` injective):

* `xs`, `ys`: the operand streams (restored); `out`: the destination of the result stream;
* `wn`: `w` in unary (any symbols; restored), the word counter of every automaton pass;
* `sv`: the consumed operand symbols; `ta`, `tb`: the real and imaginary bits of one
  coefficient; `acc`: results, latest on top; `tmp`: an empty spare whose scan slot holds the
  automaton state. All five are empty before and after the stage;
* `d0 … d3`: the vendored program's data tapes 0–3, the registers `ι 0 … ι 3` (`RpLayout`):
  the header, the two operand arrays and the output array. The other registers `ι j`, `j ≥ 4`,
  are the vendored program's private tapes, outside the family `rg`.

**Contracts.** A register file is `ρ : RpReg → List`; `RpHolds rg S ρ` says the stacks `S`
carry it. `RpFr rg S S'`: `S'` agrees with `S` on `inp`, `out`, every left stack and every
register outside the family `rg`. `RpClean ι S`: every left stack of `ι` is empty and so is every
private register `ι j`, `j ≥ 4`. `RpRuns body rg ι p ρ ρ' b`: from any clean stacks carrying `ρ`,
`p` runs in at most `b` steps to stacks carrying `ρ'`, framed by `RpFr`, with the `user` component
unchanged; frames keep the stacks clean (`RpClean.of_fr`), so contracts compose (`RpRuns.seq`).

**Primitive contracts.** `rp_moveR_runs`, `rp_uclear_runs`; `rp_word_runs`: one word of an
automaton (`rpWord`: reset the state, then `autoWord` counted by `wn`), the inputs losing their
first `w` symbols and every output gaining its outputs in reverse; `rpWhile_runs`: a loop
`rpWhile src p` that runs `p` while register `src` is nonempty, through register files
`F 0, F 1, …, F K` with `F K src = []`, within `K (b + 2) + 2` steps.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

noncomputable section

/-- The registers of the ring-product stage. -/
inductive RpReg
  | xs | ys | out | wn | sv | ta | tb | acc | tmp | d0 | d1 | d2 | d3
  deriving DecidableEq

section Contracts

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) (rg : RpReg → Fin T)
  (ι : Fin 91 → Fin T)

/-- The register layout: `rg` and `ι` injective, the data registers `d0 … d3` are `ι 0 … ι 3`,
and the private registers `ι j`, `j ≥ 4`, lie outside `rg`. -/
structure RpLayout : Prop where
  rg_inj : Function.Injective rg
  ι_inj : Function.Injective ι
  d0 : rg .d0 = ι 0
  d1 : rg .d1 = ι 1
  d2 : rg .d2 = ι 2
  d3 : rg .d3 = ι 3
  priv : ∀ r (j : Fin 91), 4 ≤ j.val → rg r ≠ ι j

/-- The stacks `S` carry the register file `ρ`. -/
def RpHolds (S : Stacks T A) (ρ : RpReg → List (Fin (A + 4))) : Prop := ∀ r, S.R (rg r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `rg`. -/
def RpFr (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, rg r ≠ k) → S'.R k = S.R k

/-- The left stacks of `ι` and the private registers are empty. -/
def RpClean (S : Stacks T A) : Prop :=
  (∀ j, S.L (ι j) = []) ∧ ∀ j : Fin 91, 4 ≤ j.val → S.R (ι j) = []

/-- The contract of a program on the register file: from `ρ` to `ρ'` within `b` steps. -/
def RpRuns (p : Pr P T Q A U) (ρ ρ' : RpReg → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, RpClean ι S → RpHolds rg S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ RpHolds rg S' ρ' ∧ RpFr rg S S'

variable {body rg ι}

lemma RpFr.refl (S : Stacks T A) : RpFr rg S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

lemma RpFr.trans {S₁ S₂ S₃ : Stacks T A} (h₁ : RpFr rg S₁ S₂) (h₂ : RpFr rg S₂ S₃) :
    RpFr rg S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

lemma RpClean.of_fr (h : RpLayout rg ι) {S S' : Stacks T A} (hc : RpClean ι S)
    (hf : RpFr rg S S') : RpClean ι S' :=
  ⟨fun j => by rw [hf.2.2.1]; exact hc.1 j,
    fun j hj => by rw [hf.2.2.2 _ (fun r => h.priv r j hj)]; exact hc.2 j hj⟩

theorem RpRuns.seq (h : RpLayout rg ι) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : RpReg → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : RpRuns body rg ι p ρ₁ ρ₂ b₁)
    (h₂ : RpRuns body rg ι q ρ₂ ρ₃ b₂) : RpRuns body rg ι (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ (hc.of_fr h hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

theorem RpRuns.mono {p : Pr P T Q A U} {ρ ρ' : RpReg → List (Fin (A + 4))} {b b' : ℕ}
    (h : RpRuns body rg ι p ρ ρ' b) (hb : b ≤ b') : RpRuns body rg ι p ρ ρ' b' := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

theorem RpRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : RpReg → List (Fin (A + 4))} {b : ℕ}
    (h : RpRuns body rg ι p ρ ρ' b) (he : ρ' = ρ'') : RpRuns body rg ι p ρ ρ'' b := he ▸ h

/-! ### Register files under updates -/

lemma rp_upd_comp (hrg : Function.Injective rg) {β : Type} (g : Fin T → β) (a : RpReg) (x : β)
    (r : RpReg) : Function.update g (rg a) x (rg r) = Function.update (fun r => g (rg r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (hrg.ne h), Function.update_of_ne h]

lemma rp_holds_upd (hrg : Function.Injective rg) {R : Fin T → List (Fin (A + 4))}
    {ρ : RpReg → List (Fin (A + 4))} (h : ∀ r, R (rg r) = ρ r) (a : RpReg)
    (x : List (Fin (A + 4))) :
    ∀ r, Function.update R (rg a) x (rg r) = Function.update ρ a x r := by
  intro r
  rw [rp_upd_comp hrg]
  have : (fun r => R (rg r)) = ρ := funext h
  rw [this]

lemma rp_upd_off {β : Type} (g : Fin T → β) (a : RpReg) (x : β) {k : Fin T}
    (hk : ∀ r, rg r ≠ k) : Function.update g (rg a) x k = g k := Function.update_of_ne (hk a).symm _ _

/-! ### Primitive contracts -/

theorem rp_moveR_runs (h : RpLayout rg ι) {a b : RpReg} (hab : a ≠ b)
    {ρ : RpReg → List (Fin (A + 4))} {n : ℕ} (hn : (ρ a).length = n) :
    RpRuns body rg ι (moveR (rg a) (rg b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b)) (2 * n + 2) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := moveR_exec body (rg a) (rg b) (h.rg_inj.ne hab) id v S
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · intro r
    simp only [movedR, List.map_id]
    rw [rp_holds_upd h.rg_inj (rp_holds_upd h.rg_inj hS a []) b, hS, hS]
  · simp only [movedR, rp_upd_off _ _ _ hk]

theorem rp_uclear_runs (h : RpLayout rg ι) (a : RpReg) {ρ : RpReg → List (Fin (A + 4))} {n : ℕ}
    (hn : (ρ a).length = n) :
    RpRuns body rg ι (uclear (rg a)) ρ (Function.update ρ a []) (2 * n + 2) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := uclear_exec body (rg a) v S
  exact ⟨v', _, _, hu, by rw [hS, hn], he, rp_holds_upd h.rg_inj hS a [],
    ⟨rfl, rfl, rfl, fun k hk => rp_upd_off _ _ _ hk⟩⟩

/-! ### One automaton word -/

variable (rg) in
/-- One word of the automaton `M` on the registers `ins`, `outs`, counted by `wn`: reset the
state in the scan slot of `tmp`, then `autoWord`. -/
def rpWord {ni no : ℕ} [NeZero ni] (ins : Fin ni → RpReg) (outs : Fin no → RpReg)
    (M : Auto A ni no) : Pr P T Q A U :=
  .seq (.act (autoReset (rg ∘ ins) 0 (rg .tmp) M))
    (autoWord 0 (rg ∘ ins) (rg ∘ outs) (rg .tmp) (rg .wn) (rg .tmp) M)

/-- One word: the inputs lose their first `n = |wn|` symbols, each output gains the word's
outputs in reverse, every other register is unchanged; `5 n + 6` steps. -/
theorem rp_word_runs (h : RpLayout rg ι) {ni no : ℕ} [NeZero ni] {ins : Fin ni → RpReg}
    {outs : Fin no → RpReg} (hins : Function.Injective ins) (houts : Function.Injective outs)
    (hio : ∀ i j, ins i ≠ outs j) (hiw : ∀ i, ins i ≠ .wn) (hit : ∀ i, ins i ≠ .tmp)
    (how : ∀ j, outs j ≠ .wn) (hot : ∀ j, outs j ≠ .tmp) (M : Auto A ni no)
    {ρ ρ' : RpReg → List (Fin (A + 4))} {n : ℕ} (hn : (ρ .wn).length = n) (ht : ρ .tmp = [])
    (hin : ∀ i, ρ' (ins i) = (ρ (ins i)).drop n)
    (hout : ∀ j, ρ' (outs j) =
      ((M.runWord M.init (Auto.cols (fun i => ρ (ins i)) n 0)).map (· j)).reverse ++ ρ (outs j))
    (hoth : ∀ r, (∀ i, ins i ≠ r) → (∀ j, outs j ≠ r) → ρ' r = ρ r) :
    RpRuns body rg ι (rpWord rg ins outs M) ρ ρ' (5 * n + 6) := by
  intro v S _ hS
  have hlay : AutoLayout (rg ∘ ins) (rg ∘ outs) (rg .tmp) (rg .wn) (rg .tmp) :=
    ⟨h.rg_inj.comp hins, h.rg_inj.comp houts, fun i j => h.rg_inj.ne (hio i j),
      fun i => h.rg_inj.ne (hiw i), fun i => h.rg_inj.ne (hit i), fun j => h.rg_inj.ne (how j),
      fun j => h.rg_inj.ne (hot j), h.rg_inj.ne (by decide), fun i => h.rg_inj.ne (hit i)⟩
  set v₀ : HS T Q A U := { v with scan := Function.update v.scan (rg .tmp) M.init
                                  flag := (S.R ((rg ∘ ins) 0)).head?.isSome }
  have hrun₀ : (autoReset (rg ∘ ins) 0 (rg .tmp) M : Act T Q A U).run (mk v S) = mk v₀ S := rfl
  obtain ⟨v', S', hu, he, -, -, hfr, hc', ht', hin', hout'⟩ :=
    autoWord_exec body hlay M 0 v₀ S (hS .wn) (by rw [hS, ht]) (by simp [v₀])
  have hD : (fun i => S.R (rg (ins i))) = fun i => ρ (ins i) := funext fun i => hS _
  refine ⟨v', S', _, hu, ?_, Exec.seq (hrun₀ ▸ Exec.act (body := body) _ (mk v S)) he, ?_, ?_⟩
  · rw [hn]; omega
  · intro r
    by_cases hr₁ : ∃ i, ins i = r
    · obtain ⟨i, rfl⟩ := hr₁
      have := hin' i
      simp only [Function.comp_apply] at this
      rw [this, hS, hn, hin]
    by_cases hr₂ : ∃ j, outs j = r
    · obtain ⟨j, rfl⟩ := hr₂
      have := hout' j
      simp only [Function.comp_apply] at this
      rw [this, hD, hS, hn, hout]
    have hr₁' : ∀ i, ins i ≠ r := fun i hi => hr₁ ⟨i, hi⟩
    have hr₂' : ∀ j, outs j ≠ r := fun j hj => hr₂ ⟨j, hj⟩
    rw [hoth r hr₁' hr₂']
    by_cases hw : r = .wn
    · subst hw; rw [hc']
    by_cases hT : r = .tmp
    · subst hT; rw [ht', ht]
    rw [hfr.2.2.2 (rg r) (by rintro ⟨i, hi⟩; exact hr₁' i (h.rg_inj hi))
      (by rintro ⟨j, hj⟩; exact hr₂' j (h.rg_inj hj)) (h.rg_inj.ne hw) (h.rg_inj.ne hT), hS]
  · refine ⟨hfr.1, hfr.2.1, hfr.2.2.1, fun k hk => hfr.2.2.2 k ?_ ?_ (hk _).symm (hk _).symm⟩
    · rintro ⟨i, hi⟩; exact hk _ hi
    · rintro ⟨j, hj⟩; exact hk _ hj

/-- The outputs of a stateless automaton on a word. -/
lemma rp_word_out {ni no : ℕ} (M : Auto A ni no) (hM : ∀ s c, (M.step s c).1 = s)
    (cs : List (Fin ni → Fin (A + 4))) (j : Fin no) :
    (M.runWord M.init cs).map (· j) = cs.map fun c => (M.step M.init c).2 j := by
  rw [rp_runWord_stateless M hM, List.map_map]
  rfl

/-! ### Loops over a register -/

variable (rg) in
/-- Run `p` while register `src` is nonempty. -/
def rpWhile (src : RpReg) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR (rg src))) (.loop (·.flag) (.seq p (.act (peekR (rg src)))))

theorem rp_loop (h : RpLayout rg ι) {src : RpReg} {p : Pr P T Q A U} {b : ℕ} :
    ∀ (K : ℕ) (F : ℕ → RpReg → List (Fin (A + 4))), (∀ k < K, F k src ≠ []) → F K src = [] →
      (∀ k < K, RpRuns body rg ι p (F k) (F (k + 1)) b) →
      ∀ v S, RpClean ι S → RpHolds rg S (F 0) → v.flag = (S.R (rg src)).head?.isSome →
        ∃ v' S' n, v'.user = v.user ∧ n ≤ K * (b + 2) + 1 ∧
          Exec body (.loop (·.flag) (.seq p (.act (peekR (rg src))))) (mk v S) n (mk v' S') ∧
          RpHolds rg S' (F K) ∧ RpFr rg S S' := by
  intro K
  induction K with
  | zero =>
      intro F _ hend _ v S _ hS hf
      have : v.flag = false := by rw [hf, hS, hend]; rfl
      exact ⟨v, S, 1, rfl, by omega, .loop_false (by simpa using this), hS, RpFr.refl S⟩
  | succ K ih =>
      intro F hne hend hstep v S hc hS hf
      have hft : v.flag = true := by
        rw [hf, hS]
        cases hF : F 0 src with
        | nil => exact absurd hF (hne 0 (by omega))
        | cons _ _ => rfl
      obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := hstep 0 (by omega) v S hc hS
      set v₂ : HS T Q A U := { v₁ with flag := (S₁.R (rg src)).head?.isSome }
      have he₂ := Exec.seq he₁ (peekR_run (rg src) v₁ S₁ ▸ Exec.act (body := body) _ (mk v₁ S₁))
      obtain ⟨v', S', n', hu', hn', he', hS', hf'⟩ := ih (fun k => F (k + 1))
        (fun k hk => hne (k + 1) (by omega)) hend (fun k hk => hstep (k + 1) (by omega)) v₂ S₁
        (hc.of_fr h hf₁) hS₁ rfl
      refine ⟨v', S', n₁ + 1 + n' + 1, hu'.trans hu₁, ?_,
        Exec.loop_true (body := body) (f := (·.flag)) hft he₂ he', hS', hf₁.trans hf'⟩
      have : (K + 1) * (b + 2) = K * (b + 2) + b + 2 := by ring
      omega

/-- A loop through the register files `F 0, …, F K`: `K (b + 2) + 2` steps. -/
theorem rpWhile_runs (h : RpLayout rg ι) {src : RpReg} {p : Pr P T Q A U} {b : ℕ} (K : ℕ)
    (F : ℕ → RpReg → List (Fin (A + 4))) (hne : ∀ k < K, F k src ≠ []) (hend : F K src = [])
    (hstep : ∀ k < K, RpRuns body rg ι p (F k) (F (k + 1)) b) :
    RpRuns body rg ι (rpWhile rg src p) (F 0) (F K) (K * (b + 2) + 2) := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := rp_loop h K F hne hend hstep
    { v with flag := (S.R (rg src)).head?.isSome } S hc hS rfl
  exact ⟨v', S', 1 + n, hu, by omega,
    Exec.seq (peekR_run (rg src) v S ▸ Exec.act (body := body) _ (mk v S)) he, hS', hf⟩

end Contracts

end

end IntegerMultBounds.MathlibTM2.Fast
