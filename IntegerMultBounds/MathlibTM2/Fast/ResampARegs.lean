module

public import IntegerMultBounds.MathlibTM2.Layer.GaussStream
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip
public import IntegerMultBounds.MathlibTM2.Fast.CMulPass
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat

/-!
# Register-file contracts for the resampling machines

The resampling machines run on host registers `rg r`, `r : R`, for an injective layout
`rg : R → Fin T`, next to the 64 registers `ι j` of the Schönhage–Strassen multiplier
(`Host/SSMul`), disjoint from the layout. This file states their contracts and lifts the host
library to them.

**Contracts.** `rsaHolds rg S ρ`: the stacks `S` carry the register file `ρ : R → List`.
`rsaClean ι S`: every left stack and every multiplier register is empty. `rsaFr rg S S'`: `S'`
agrees with `S` on `inp`, `out`, the left stacks and every register outside the layout.
`RsaRuns body rg ι p ρ ρ' b`: from any clean stacks carrying `ρ`, `p` runs in at most `b`
steps to stacks carrying `ρ'`, framed by `rsaFr`, with the `user` component unchanged.
`RsaRuns.seq` composes contracts.

**Lifts.** `RsaRuns.of_c` lifts a contract `CRuns` of the complex-product library
(`Fast/CMulRegs`) for the register family `rg ∘ c`: the registers `c x` change as in the `CRuns`
contract (`Function.extend c ρC' ρ`), all others are kept. Contracts of host primitives:
`rsa_moveR`, `rsa_uclear`, `rsa_usub`, `rsa_umulSym`, `rsa_bcopy`, `rsa_popPush`,
`rsa_add` (one coefficient addition modulo `2^W` by the Gaussian automaton of `Layer/GaussStream`
with matrix `[[1, 1]]`), and `rsa_baddTo_cond` (binary addition `a := (a + b) mod 2^L` followed by
a branch on its carry).

**Loops.** `rsa_scanP_runs`: `scanP a t p` (`Node/Params`) runs `p` once per symbol of the
counter `a`, specified by register files `Φ j` (the counter and its spare `t` at their
intermediate contents), and restores the counter. `rsa_cwhileP_runs`: `cwhileP g p`
(`Fast/CMulPass`) runs `p` once per element of a list while register `g` is nonempty.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast


section Contracts

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] (body : P → Pr P T Q A U) (rg : R → Fin T)
  (ι : Fin 64 → Fin T)

/-- The stacks `S` carry the register file `ρ`. -/
def rsaHolds (S : Stacks T A) (ρ : R → List (Fin (A + 4))) : Prop := ∀ r, S.R (rg r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `rg`. -/
def rsaFr (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, rg r ≠ k) → S'.R k = S.R k

/-- Every left stack and every multiplier register is empty. -/
def rsaClean (S : Stacks T A) : Prop := (∀ y, S.L y = []) ∧ ∀ j, S.R (ι j) = []

/-- The contract of a program on the register file: from `ρ` to `ρ'` within `b` steps. -/
def RsaRuns (p : Pr P T Q A U) (ρ ρ' : R → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, rsaClean ι S → rsaHolds rg S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ rsaHolds rg S' ρ' ∧ rsaFr rg S S'

variable {body rg ι}

omit [DecidableEq R] in
lemma rsaFr.refl (S : Stacks T A) : rsaFr rg S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

omit [DecidableEq R] in
lemma rsaFr.trans {S₁ S₂ S₃ : Stacks T A} (h₁ : rsaFr rg S₁ S₂) (h₂ : rsaFr rg S₂ S₃) :
    rsaFr rg S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

omit [DecidableEq R] in
lemma rsaClean.of_fr (hdisj : ∀ r j, rg r ≠ ι j) {S S' : Stacks T A} (hc : rsaClean ι S)
    (h : rsaFr rg S S') : rsaClean ι S' :=
  ⟨fun y => by rw [h.2.2.1]; exact hc.1 y,
    fun j => by rw [h.2.2.2 _ (fun r => hdisj r j)]; exact hc.2 j⟩

omit [DecidableEq R] in
theorem RsaRuns.seq (hdisj : ∀ r j, rg r ≠ ι j) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : R → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : RsaRuns body rg ι p ρ₁ ρ₂ b₁)
    (h₂ : RsaRuns body rg ι q ρ₂ ρ₃ b₂) : RsaRuns body rg ι (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

omit [DecidableEq R] in
theorem RsaRuns.mono {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b b' : ℕ}
    (h : RsaRuns body rg ι p ρ ρ' b) (hb : b ≤ b') : RsaRuns body rg ι p ρ ρ' b' := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

omit [DecidableEq R] in
theorem RsaRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsaRuns body rg ι p ρ ρ' b) (he : ρ' = ρ'') : RsaRuns body rg ι p ρ ρ'' b := he ▸ h

omit [DecidableEq R] in
theorem RsaRuns.congr_pre {p : Pr P T Q A U} {ρ₀ ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsaRuns body rg ι p ρ ρ' b) (he : ρ₀ = ρ) : RsaRuns body rg ι p ρ₀ ρ' b := he ▸ h

omit [DecidableEq R] in
/-- A contract from a raw execution whose final right stacks `R'` carry `ρ'` on the layout and
agree with `S` off it. -/
theorem RsaRuns.of_raw {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : ∀ v S, rsaClean ι S → rsaHolds rg S ρ →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (n : ℕ), v'.user = v.user ∧ n ≤ b ∧
        Exec body p (mk v S) n (mk v' { S with R := R' }) ∧ (∀ r, R' (rg r) = ρ' r) ∧
        ∀ k, (∀ r, rg r ≠ k) → R' k = S.R k) :
    RsaRuns body rg ι p ρ ρ' b := by
  intro v S hc hS
  obtain ⟨v', R', n, hu, hn, he, h₁, h₂⟩ := h v S hc hS
  exact ⟨v', _, n, hu, hn, he, h₁, rfl, rfl, rfl, h₂⟩

/-! ### Register files under updates -/

lemma rsa_upd_comp (hrg : Function.Injective rg) {β : Type} (g : Fin T → β) (a : R) (x : β)
    (r : R) : Function.update g (rg a) x (rg r) = Function.update (fun r => g (rg r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (hrg.ne h), Function.update_of_ne h]

lemma rsa_holds_upd (hrg : Function.Injective rg) {S : Fin T → List (Fin (A + 4))}
    {ρ : R → List (Fin (A + 4))} (h : ∀ r, S (rg r) = ρ r) (a : R) (x : List (Fin (A + 4))) :
    ∀ r, Function.update S (rg a) x (rg r) = Function.update ρ a x r := by
  intro r
  rw [rsa_upd_comp hrg]
  have : (fun r => S (rg r)) = ρ := funext h
  rw [this]

omit [DecidableEq R] in
lemma rsa_upd_off {β : Type} (g : Fin T → β) (a : R) (x : β) {k : Fin T} (hk : ∀ r, rg r ≠ k) :
    Function.update g (rg a) x k = g k := Function.update_of_ne (hk a).symm _ _

/-! ### Primitive contracts -/

variable (hrg : Function.Injective rg)
include hrg

theorem rsa_moveR {a b : R} (hab : a ≠ b) (ρ : R → List (Fin (A + 4))) :
    RsaRuns body rg ι (moveR (rg a) (rg b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b))
      (2 * (ρ a).length + 2) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', hu, he⟩ := moveR_exec body (rg a) (rg b) (hrg.ne hab) id v S
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, fun k hk => ?_⟩
  · intro r
    simp only [movedR, List.map_id]
    rw [rsa_holds_upd hrg (rsa_holds_upd hrg hS a []) b, hS, hS]
  · simp only [movedR, rsa_upd_off _ _ _ hk]

theorem rsa_uclear (a : R) (ρ : R → List (Fin (A + 4))) :
    RsaRuns body rg ι (uclear (rg a)) ρ (Function.update ρ a []) (2 * (ρ a).length + 2) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', hu, he⟩ := uclear_exec body (rg a) v S
  exact ⟨v', _, _, hu, by rw [hS], he, rsa_holds_upd hrg hS a [],
    fun k hk => rsa_upd_off _ _ _ hk⟩

theorem rsa_usub {a b t : R} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    RsaRuns body rg ι (usub (rg a) (rg b) (rg t)) ρ
      (Function.update ρ b ((ρ b).drop (ρ a).length)) (4 * (ρ a).length + 4) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', hu, he⟩ := usub_exec body (hrg.ne hab) (hrg.ne hat) (hrg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, fun k hk => rsa_upd_off _ _ _ hk⟩
  intro r
  rw [rsa_holds_upd hrg hS b, hS, hS]

theorem rsa_umulSym (c : ℕ) (y : Fin (A + 4)) {a b t : R} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    RsaRuns body rg ι (umulSym c y (rg a) (rg b) (rg t)) ρ
      (Function.update ρ b (List.replicate (c * (ρ a).length) y ++ ρ b))
      (4 * (ρ a).length + 4) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', hu, he⟩ := umulSym_exec body c y (hrg.ne hab) (hrg.ne hat) (hrg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, fun k hk => rsa_upd_off _ _ _ hk⟩
  intro r
  rw [rsa_holds_upd hrg hS b, hS, hS]

theorem rsa_bcopy {a c t₁ t₂ : R} (hd : [a, c, t₁, t₂].Nodup) (ρ : R → List (Fin (A + 4)))
    (h₁ : ρ t₁ = []) (h₂ : ρ t₂ = []) :
    RsaRuns body rg ι (bcopy (rg a) (rg c) (rg t₁) (rg t₂)) ρ (Function.update ρ c (ρ a ++ ρ c))
      (6 * (ρ a).length + 6) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', hu, he⟩ := bcopy_exec body (hd.map hrg) v S (by rw [hS, h₁]) (by rw [hS, h₂])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, fun k hk => rsa_upd_off _ _ _ hk⟩
  intro r
  rw [rsa_holds_upd hrg hS c, hS, hS]

theorem rsa_popPush {a b : R} (hab : a ≠ b) (ρ : R → List (Fin (A + 4))) (x : Fin (A + 4))
    (l : List (Fin (A + 4))) (ha : ρ a = x :: l) :
    RsaRuns body rg ι (.act (popPush (rg a) (rg b))) ρ
      (Function.update (Function.update ρ a l) b (x :: ρ b)) 1 := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  have hS' : S.R (rg a) = x :: l := by rw [hS, ha]
  refine ⟨{ v with sym := some x }, Function.update (Function.update S.R (rg a) l) (rg b)
    (x :: S.R (rg b)), 1, rfl, le_rfl, ?_, ?_, fun k hk => ?_⟩
  · have h := Exec.act (body := body) (popPush (rg a) (rg b)) (mk v S)
    convert h using 1
    simp [popPush, Action.run, hS', update_rt, Function.update_of_ne (hrg.ne hab).symm]
  · intro r
    rw [rsa_holds_upd hrg (rsa_holds_upd hrg hS a l) b, hS]
  · rw [rsa_upd_off _ _ _ hk, rsa_upd_off _ _ _ hk]

omit [DecidableEq R] in
/-- Lift a contract of the complex-product library for the register family `rg ∘ c`. -/
theorem RsaRuns.of_c {c : CR → R} (hc : Function.Injective c) {p : Pr P T Q A U}
    {ρC ρC' : CR → List (Fin (A + 4))} {b : ℕ} (h : CRuns body (fun x => rg (c x)) ι p ρC ρC' b)
    (ρ : R → List (Fin (A + 4))) (hρ : ∀ x, ρ (c x) = ρC x) :
    RsaRuns body rg ι p ρ (Function.extend c ρC' ρ) b := by
  intro v S hcl hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S (fun j => ⟨hcl.1 _, hcl.2 j⟩)
    (fun x => by rw [hS, hρ])
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, hf.1, hf.2.1, hf.2.2.1, fun k hk =>
    hf.2.2.2 k (fun x => hk (c x))⟩
  by_cases hr : ∃ x, c x = r
  · obtain ⟨x, rfl⟩ := hr
    rw [hc.extend_apply, hS' x]
  · rw [Function.extend_apply' _ _ _ hr]
    rw [hf.2.2.2 (rg r) (fun x hx => hr ⟨x, hrg hx⟩), hS]

end Contracts

/-! ### Addition of one coefficient -/

section Add

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

/-- The Gaussian automaton of the sum of two coefficients. -/
def rsaAddAuto (A : ℕ) : Auto A 2 1 := gaussAuto A ![![(1, 0), (1, 0)]] 2 false

variable (hrg : Function.Injective rg)
include hrg

/-- One coefficient addition: `o` gains the coefficient `z₁ + z₂` (reversed) on top, the inputs
`x`, `y` end empty, in at most `5 W + 8` steps. The word counter `ctr` holds `W` symbols, `tmp`
is an empty spare, and the automaton state lives in the scan slot of `st`. -/
theorem rsa_add {x y o ctr tmp st : R} (hd : [x, y, o, ctr, tmp].Nodup) (hxs : x ≠ st)
    (hys : y ≠ st) (hA : 96 ≤ A) {W : ℕ} (hW : 1 ≤ W) (ρ : R → List (Fin (A + 4)))
    (hctr : (ρ ctr).length = W) (htmp : ρ tmp = []) (z₁ z₂ : GR W)
    (hx : ρ x = coeffSyms A W z₁) (hy : ρ y = coeffSyms A W z₂) :
    RsaRuns body rg ι (autoWords ![rg x, rg y] ![rg o] (rg st) (rg ctr) (rg tmp) (rsaAddAuto A))
      ρ (Function.update (Function.update (Function.update ρ x []) y []) o
        ((coeffSyms A W (z₁ + z₂)).reverse ++ ρ o)) (5 * W + 8) := by
  have hd' := hd
  regs_ne hd'
  have hL : AutoLayout ![rg x, rg y] ![rg o] (rg st) (rg ctr) (rg tmp) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hrg.ne ‹ctr ≠ tmp›, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [hrg.ne ‹x ≠ y›, (hrg.ne ‹x ≠ y›).symm]
    · intro i j _; exact Subsingleton.elim i j
    · intro i j; fin_cases i <;> fin_cases j <;> simp [hrg.ne ‹x ≠ o›, hrg.ne ‹y ≠ o›]
    · intro i; fin_cases i <;> simp [hrg.ne ‹x ≠ ctr›, hrg.ne ‹y ≠ ctr›]
    · intro i; fin_cases i <;> simp [hrg.ne ‹x ≠ tmp›, hrg.ne ‹y ≠ tmp›]
    · intro j; fin_cases j; simp [hrg.ne ‹o ≠ ctr›]
    · intro j; fin_cases j; simp [hrg.ne ‹o ≠ tmp›]
    · intro i; fin_cases i <;> simp [hrg.ne hxs, hrg.ne hys]
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', m, S', hu, hm, he, hi, ho, hl, hins, houts, hoth⟩ :=
    gaussAuto_exec_list body hL (by omega)
      (B := 2) (g := ![![((1 : ℤ), (0 : ℤ)), (1, 0)]])
      (by intro j; fin_cases j; simp [Fin.sum_univ_two])
      (by norm_num; omega) false hW (ctrs := S.R (rg ctr)) (by rw [hS, hctr])
      ![[z₁], [z₂]] (n := 1) (by intro i; fin_cases i <;> rfl) v S rfl (by rw [hS, htmp])
      (by intro i; fin_cases i <;> simp [hS x, hS y, hx, hy])
  have hS'e : S' = { S with R := S'.R } := by
    cases S'; cases S; simp only at hi ho hl; subst hi ho hl; rfl
  rw [hS'e] at he
  refine ⟨v', S'.R, m, hu, by omega, he, fun r => ?_, fun k hk => ?_⟩
  · by_cases h1 : r = o
    · subst h1
      have := houts 0
      simp only [Matrix.cons_val_fin_one] at this
      rw [this, hS]
      have hg : ∀ f : Fin 2 → GR W, f 0 = z₁ → f 1 = z₂ →
          glin ![![((1 : ℤ), (0 : ℤ)), (1, 0)]] f 0 = z₁ + z₂ := by
        intro f h0 h1
        rw [glin_eq_sum_mulG]
        simp [Fin.sum_univ_two, GR.mulG, h0, h1]
      simp only [Function.update_self, List.ofFn_succ, List.ofFn_zero, swapGR,
        Bool.false_eq_true, ↓reduceIte]
      rw [hg _ rfl rfl]
      simp
    · by_cases h2 : r = y
      · subst h2
        have := hins 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
        rw [this, Function.update_of_ne h1, Function.update_self]
      · by_cases h3 : r = x
        · subst h3
          have := hins 0
          simp only [Matrix.cons_val_zero] at this
          rw [this, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_self]
        · rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
            ← hS]
          apply hoth
          · rintro ⟨i, hi⟩; fin_cases i
            · exact h3 (hrg hi).symm
            · exact h2 (hrg hi).symm
          · rintro ⟨j, hj⟩; fin_cases j; exact h1 (hrg hj).symm
  · apply hoth
    · rintro ⟨i, hi⟩; fin_cases i
      · exact hk x hi
      · exact hk y hi
    · rintro ⟨j, hj⟩; fin_cases j; exact hk o hj

end Add

/-! ### Binary addition with a branch on the carry -/

section Carry

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg)
include hrg

/-- `a := (a + b) mod 2^L`, then `p` if the addition carried and `q` otherwise. -/
theorem rsa_baddTo_cond (hdisj : ∀ r j, rg r ≠ ι j) {a b tx ty tz cy : R}
    (hd : [a, b, tx, ty, tz].Nodup) (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L)
    (hy : y < 2 ^ L) (ρ : R → List (Fin (A + 4))) (ha : ρ a = binSyms L x)
    (hb : ρ b = binSyms L y) (htx : ρ tx = []) (hty : ρ ty = []) (htz : ρ tz = [])
    {p q : Pr P T Q A U} {ρp ρq : R → List (Fin (A + 4))} {bp bq : ℕ}
    (hp : RsaRuns body rg ι p (Function.update ρ a (binSyms L ((x + y) % 2 ^ L))) ρp bp)
    (hq : RsaRuns body rg ι q (Function.update ρ a (binSyms L ((x + y) % 2 ^ L))) ρq bq) :
    RsaRuns body rg ι (.seq (baddTo (rg a) (rg b) (rg tx) (rg ty) (rg tz) (rg cy))
        (.cond (fun v => symBit (v.scan (rg cy))) p q)) ρ
      (if 2 ^ L ≤ x + y then ρp else ρq) (8 * L + 8 + (max bp bq + 1)) := by
  intro v S hc hS
  obtain ⟨v₁, hu₁, hcy₁, -, he₁⟩ := baddTo_exec body (hd.map hrg) (hrg.ne hca) (hrg.ne hcb) hx hy
    v S (by rw [hS, ha]) (by rw [hS, hb]) (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg a) (binSyms L ((x + y) % 2 ^ L)) }
  have hS₁ : rsaHolds rg S₁ (Function.update ρ a (binSyms L ((x + y) % 2 ^ L))) :=
    rsa_holds_upd hrg hS a _
  have hf₁ : rsaFr rg S S₁ := ⟨rfl, rfl, rfl, fun k hk => rsa_upd_off _ _ _ hk⟩
  have hc₁ := hc.of_fr hdisj hf₁
  by_cases hcar : 2 ^ L ≤ x + y
  · obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := hp v₁ S₁ hc₁ hS₁
    refine ⟨v₂, S₂, 8 * L + 8 + (n₂ + 1), hu₂.trans hu₁, ?_, Exec.seq he₁ (Exec.cond_true ?_ he₂),
      by rw [ite_eq_left hcar]; exact hS₂, hf₁.trans hf₂⟩
    · have := le_max_left bp bq; omega
    · simp [hcy₁, hcar]
  · obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := hq v₁ S₁ hc₁ hS₁
    refine ⟨v₂, S₂, 8 * L + 8 + (n₂ + 1), hu₂.trans hu₁, ?_,
      Exec.seq he₁ (Exec.cond_false ?_ he₂), by rw [ite_eq_right hcar]; exact hS₂, hf₁.trans hf₂⟩
    · have := le_max_right bp bq; omega
    · simp [hcy₁, hcar]

omit hrg [DecidableEq R] in
/-- The no-op. -/
theorem rsa_done (ρ : R → List (Fin (A + 4))) :
    RsaRuns body rg ι (.act .done) ρ ρ 1 := by
  intro v S _ hS
  exact ⟨v, S, 1, rfl, le_rfl, Exec.act _ _, hS, rsaFr.refl S⟩

end Carry

/-! ### Loops -/

section Loops

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- `scanP a t p`: iteration `j` of `p` runs with the counter `a` holding `cs.drop (j + 1)` and
its spare `t` holding `(cs.take (j + 1)).reverse`, and takes the other registers from `Φ j` to
`Φ (j + 1)`; the counter is restored. -/
theorem rsa_scanP_runs {a t : R} (hat : a ≠ t) {p : Pr P T Q A U}
    (Φ : ℕ → R → List (Fin (A + 4))) {b : ℕ} (cs : List (Fin (A + 4)))
    (hstep : ∀ j, j < cs.length → RsaRuns body rg ι p
      (Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t
        (cs.take (j + 1)).reverse) b) :
    RsaRuns body rg ι (scanP (rg a) (rg t) p)
      (Function.update (Function.update (Φ 0) a cs) t [])
      (Function.update (Function.update (Φ cs.length) a cs) t [])
      (cs.length * (b + 3) + 2 * cs.length + 4) := by
  set St : ℕ → R → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse with hSt
  have key : ∀ n j, j + n = cs.length → ∀ (v : HS T Q A U) (S : Stacks T A),
      rsaClean ι S → rsaHolds rg S (St j) → v.flag = (S.R (rg a)).head?.isSome →
      ∃ v' S' k, v'.user = v.user ∧ k ≤ n * (b + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush (rg a) (rg t)))
          (.seq p (.act (peekR (rg a)))))) (mk v S) k (mk v' S') ∧
        rsaHolds rg S' (St cs.length) ∧ rsaFr rg S S' := by
    intro n
    induction n with
    | zero =>
        intro j hj v S _ hS hf
        have hj' : j = cs.length := by omega
        subst hj'
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, hS, rsaFr.refl S⟩
        rw [mk_var, hf, hS a]
        show (Function.update (Function.update (Φ cs.length) a (cs.drop cs.length)) t
          (cs.take cs.length).reverse a).head?.isSome = false
        rw [Function.update_of_ne hat, Function.update_self, List.drop_length]
        rfl
    | succ n ih =>
        intro j hj v S hc hS hf
        have hjl : j < cs.length := by omega
        have hcons : cs.drop j = cs[j] :: cs.drop (j + 1) := List.drop_eq_getElem_cons hjl
        have hSa : St j a = cs[j] :: cs.drop (j + 1) := by
          show Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse a = _
          rw [Function.update_of_ne hat, Function.update_self, hcons]
        have h1 := rsa_popPush (body := body) (ι := ι) hrg hat (St j) cs[j] _ hSa
        have heq : Function.update (Function.update (St j) a (cs.drop (j + 1))) t
            (cs[j] :: St j t) =
            Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t
              (cs.take (j + 1)).reverse := by
          have hSt' : St j t = (cs.take j).reverse := by
            show Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse t = _
            rw [Function.update_self]
          have htk : (cs.take (j + 1)).reverse = cs[j] :: (cs.take j).reverse := by
            rw [List.take_add_one, List.getElem?_eq_getElem hjl]; simp
          funext r
          by_cases h₁ : r = t
          · subst h₁; rw [Function.update_self, Function.update_self, hSt', htk]
          · rw [Function.update_of_ne h₁, Function.update_of_ne h₁]
            by_cases h₂ : r = a
            · subst h₂; rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne h₂, Function.update_of_ne h₂]
              show Function.update (Function.update (Φ j) a (cs.drop j)) t _ r = _
              rw [Function.update_of_ne h₁, Function.update_of_ne h₂]
        rw [heq] at h1
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h1 v S hc hS
        obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ :=
          hstep j hjl v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
        have e₃ := peekR_run (rg a) v₂ S₂ ▸ Exec.act (body := body) (peekR (rg a)) (mk v₂ S₂)
        have hS₂' : rsaHolds rg S₂ (St (j + 1)) := by
          intro r; rw [hS₂ r]
        obtain ⟨v₄, S₄, n₄, hu₄, hn₄, he₄, hS₄, hf₄⟩ := ih (j + 1) (by omega)
          { v₂ with flag := (S₂.R (rg a)).head?.isSome } S₂
          ((hc.of_fr hdisj hf₁).of_fr hdisj hf₂) hS₂' rfl
        have hft : v.flag = true := by rw [hf, hS a, hSa]; rfl
        refine ⟨v₄, S₄, n₁ + (n₂ + 1) + n₄ + 1, hu₄.trans (hu₂.trans hu₁), ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ (Exec.seq he₂ e₃)) he₄, hS₄,
          hf₁.trans (hf₂.trans hf₄)⟩
        nlinarith
  intro v S hc hS
  have hS0 : rsaHolds rg S (St 0) := by
    intro r; rw [hS r]; simp [hSt]
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := key cs.length 0 (by omega)
    { v with flag := (S.R (rg a)).head?.isSome } S hc hS0 rfl
  have hmv := rsa_moveR (body := body) (ι := ι) hrg hat.symm (St cs.length)
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := hmv v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
  refine ⟨v₂, S₂, 1 + (n₁ + n₂), hu₂.trans hu₁, ?_,
    Exec.seq (peekR_run (rg a) v S ▸ Exec.act (body := body) (peekR (rg a)) (mk v S))
      (Exec.seq he₁ he₂), fun r => ?_, hf₁.trans hf₂⟩
  · have : (St cs.length t).length = cs.length := by simp [hSt]
    rw [this] at hn₂
    nlinarith
  · rw [hS₂ r]
    simp only [hSt, Function.update_apply]
    split_ifs <;> simp_all

/-- `rsa_scanP_runs` with a step bound `b j` for iteration `j`. Iteration `j` of `p` runs with the counter `a` holding `cs.drop (j + 1)` and
its spare `t` holding `(cs.take (j + 1)).reverse`, and takes the other registers from `Φ j` to
`Φ (j + 1)`; the counter is restored. -/
theorem rsa_scanP_sum {a t : R} (hat : a ≠ t) {p : Pr P T Q A U}
    (Φ : ℕ → R → List (Fin (A + 4))) {b : ℕ → ℕ} (cs : List (Fin (A + 4)))
    (hstep : ∀ j, j < cs.length → RsaRuns body rg ι p
      (Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t
        (cs.take (j + 1)).reverse) (b j)) :
    RsaRuns body rg ι (scanP (rg a) (rg t) p)
      (Function.update (Function.update (Φ 0) a cs) t [])
      (Function.update (Function.update (Φ cs.length) a cs) t [])
      (∑ j ∈ Finset.range cs.length, (b j + 3) + 2 * cs.length + 4) := by
  set St : ℕ → R → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse with hSt
  have key : ∀ n j, j + n = cs.length → ∀ (v : HS T Q A U) (S : Stacks T A),
      rsaClean ι S → rsaHolds rg S (St j) → v.flag = (S.R (rg a)).head?.isSome →
      ∃ v' S' k, v'.user = v.user ∧ k ≤ ∑ i ∈ Finset.Ico j (j + n), (b i + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush (rg a) (rg t)))
          (.seq p (.act (peekR (rg a)))))) (mk v S) k (mk v' S') ∧
        rsaHolds rg S' (St cs.length) ∧ rsaFr rg S S' := by
    intro n
    induction n with
    | zero =>
        intro j hj v S _ hS hf
        have hj' : j = cs.length := by omega
        subst hj'
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, hS, rsaFr.refl S⟩
        rw [mk_var, hf, hS a]
        show (Function.update (Function.update (Φ cs.length) a (cs.drop cs.length)) t
          (cs.take cs.length).reverse a).head?.isSome = false
        rw [Function.update_of_ne hat, Function.update_self, List.drop_length]
        rfl
    | succ n ih =>
        intro j hj v S hc hS hf
        have hjl : j < cs.length := by omega
        have hcons : cs.drop j = cs[j] :: cs.drop (j + 1) := List.drop_eq_getElem_cons hjl
        have hSa : St j a = cs[j] :: cs.drop (j + 1) := by
          show Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse a = _
          rw [Function.update_of_ne hat, Function.update_self, hcons]
        have h1 := rsa_popPush (body := body) (ι := ι) hrg hat (St j) cs[j] _ hSa
        have heq : Function.update (Function.update (St j) a (cs.drop (j + 1))) t
            (cs[j] :: St j t) =
            Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t
              (cs.take (j + 1)).reverse := by
          have hSt' : St j t = (cs.take j).reverse := by
            show Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse t = _
            rw [Function.update_self]
          have htk : (cs.take (j + 1)).reverse = cs[j] :: (cs.take j).reverse := by
            rw [List.take_add_one, List.getElem?_eq_getElem hjl]; simp
          funext r
          by_cases h₁ : r = t
          · subst h₁; rw [Function.update_self, Function.update_self, hSt', htk]
          · rw [Function.update_of_ne h₁, Function.update_of_ne h₁]
            by_cases h₂ : r = a
            · subst h₂; rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne h₂, Function.update_of_ne h₂]
              show Function.update (Function.update (Φ j) a (cs.drop j)) t _ r = _
              rw [Function.update_of_ne h₁, Function.update_of_ne h₂]
        rw [heq] at h1
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h1 v S hc hS
        obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ :=
          hstep j hjl v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
        have e₃ := peekR_run (rg a) v₂ S₂ ▸ Exec.act (body := body) (peekR (rg a)) (mk v₂ S₂)
        have hS₂' : rsaHolds rg S₂ (St (j + 1)) := by
          intro r; rw [hS₂ r]
        obtain ⟨v₄, S₄, n₄, hu₄, hn₄, he₄, hS₄, hf₄⟩ := ih (j + 1) (by omega)
          { v₂ with flag := (S₂.R (rg a)).head?.isSome } S₂
          ((hc.of_fr hdisj hf₁).of_fr hdisj hf₂) hS₂' rfl
        have hft : v.flag = true := by rw [hf, hS a, hSa]; rfl
        refine ⟨v₄, S₄, n₁ + (n₂ + 1) + n₄ + 1, hu₄.trans (hu₂.trans hu₁), ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ (Exec.seq he₂ e₃)) he₄, hS₄,
          hf₁.trans (hf₂.trans hf₄)⟩
        rw [show j + (n + 1) = (j + 1) + n by omega, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        omega
  intro v S hc hS
  have hS0 : rsaHolds rg S (St 0) := by
    intro r; rw [hS r]; simp [hSt]
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := key cs.length 0 (by omega)
    { v with flag := (S.R (rg a)).head?.isSome } S hc hS0 rfl
  have hmv := rsa_moveR (body := body) (ι := ι) hrg hat.symm (St cs.length)
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := hmv v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
  refine ⟨v₂, S₂, 1 + (n₁ + n₂), hu₂.trans hu₁, ?_,
    Exec.seq (peekR_run (rg a) v S ▸ Exec.act (body := body) (peekR (rg a)) (mk v S))
      (Exec.seq he₁ he₂), fun r => ?_, hf₁.trans hf₂⟩
  · have : (St cs.length t).length = cs.length := by simp [hSt]
    rw [this] at hn₂
    rw [Finset.range_eq_Ico]
    simp only [Nat.zero_add] at hn₁
    omega
  · rw [hS₂ r]
    simp only [hSt, Function.update_apply]
    split_ifs <;> simp_all

/-- Counted transfer: `src` loses its first `n = |a|` symbols and `dst` gains them reversed on
top, the counter `a` is restored, in `6 n + 4` steps. -/
theorem rsa_xfer {a sp src dst : R} (hd : [a, sp, src, dst].Nodup)
    (ρ : R → List (Fin (A + 4))) (hsp : ρ sp = []) (hn : (ρ a).length ≤ (ρ src).length) :
    RsaRuns body rg ι (scanP (rg a) (rg sp) (.act (popPush (rg src) (rg dst)))) ρ
      (Function.update (Function.update ρ src ((ρ src).drop (ρ a).length)) dst
        (((ρ src).take (ρ a).length).reverse ++ ρ dst)) (6 * (ρ a).length + 4) := by
  have hd' := hd
  regs_ne hd'
  set cs := ρ a with hcs
  set Φ : ℕ → R → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update ρ src ((ρ src).drop j)) dst
      (((ρ src).take j).reverse ++ ρ dst) with hΦ
  have H := rsa_scanP_runs (body := body) (ι := ι) hrg hdisj ‹a ≠ sp› Φ (b := 1) cs
    (fun j hj => by
      have hj' : j < (ρ src).length := by omega
      have hsrc : Function.update (Function.update (Φ j) a (cs.drop (j + 1))) sp
          (cs.take (j + 1)).reverse src = (ρ src)[j] :: (ρ src).drop (j + 1) := by
        rw [Function.update_of_ne ‹sp ≠ src›.symm, Function.update_of_ne ‹a ≠ src›.symm]
        show Function.update (Function.update ρ src ((ρ src).drop j)) dst
          (((ρ src).take j).reverse ++ ρ dst) src = _
        rw [Function.update_of_ne ‹src ≠ dst›, Function.update_self,
          List.drop_eq_getElem_cons hj']
      refine (rsa_popPush (body := body) (ι := ι) hrg ‹src ≠ dst› _ _ _ hsrc).congr ?_
      have htk : ((ρ src).take (j + 1)).reverse = (ρ src)[j] :: ((ρ src).take j).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj']; simp
      funext r
      by_cases h1 : r = dst
      · rw [h1]
        rw [Function.update_self, Function.update_of_ne ‹sp ≠ dst›.symm,
          Function.update_of_ne ‹a ≠ dst›.symm, Function.update_of_ne ‹sp ≠ dst›.symm,
          Function.update_of_ne ‹a ≠ dst›.symm]
        show (ρ src)[j] :: (Function.update (Function.update ρ src ((ρ src).drop j)) dst
          (((ρ src).take j).reverse ++ ρ dst) dst) = Function.update (Function.update ρ src
            ((ρ src).drop (j + 1))) dst (((ρ src).take (j + 1)).reverse ++ ρ dst) dst
        rw [Function.update_self, Function.update_self, htk, List.cons_append]
      · rw [Function.update_of_ne h1]
        by_cases h2 : r = src
        · rw [h2]
          rw [Function.update_self, Function.update_of_ne ‹sp ≠ src›.symm,
            Function.update_of_ne ‹a ≠ src›.symm]
          show _ = Function.update (Function.update ρ src ((ρ src).drop (j + 1))) dst
            (((ρ src).take (j + 1)).reverse ++ ρ dst) src
          rw [Function.update_of_ne ‹src ≠ dst›, Function.update_self]
        · rw [Function.update_of_ne h2]
          by_cases h3 : r = sp
          · rw [h3, Function.update_self, Function.update_self]
          · rw [Function.update_of_ne h3, Function.update_of_ne h3]
            by_cases h4 : r = a
            · rw [h4, Function.update_self, Function.update_self]
            · rw [Function.update_of_ne h4, Function.update_of_ne h4]
              show Function.update (Function.update ρ src ((ρ src).drop j)) dst _ r =
                Function.update (Function.update ρ src ((ρ src).drop (j + 1))) dst _ r
              rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_of_ne h2,
                Function.update_of_ne h2])
  have e₀ : Function.update (Function.update (Φ 0) a cs) sp [] = ρ := by
    funext r
    simp only [hΦ, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have e₁ : Function.update (Function.update (Φ cs.length) a cs) sp [] =
      Function.update (Function.update ρ src ((ρ src).drop (ρ a).length)) dst
        (((ρ src).take (ρ a).length).reverse ++ ρ dst) := by
    funext r
    simp only [hΦ, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [e₀, e₁] at H
  exact H.mono (by omega)

omit hrg [DecidableEq R] in
/-- `cwhileP g p` over a list: the register file `st l done` holds the remaining elements `l`
and the processed ones `done`; register `g` is nonempty exactly while elements remain. -/
theorem rsa_cwhileP_runs {α : Type} (g : R) (p : Pr P T Q A U) (ok : α → Prop)
    (st : List α → List α → R → List (Fin (A + 4))) (b : ℕ)
    (hstep : ∀ a rest done, ok a →
      RsaRuns body rg ι p (st (a :: rest) done) (st rest (done ++ [a])) b)
    (hne : ∀ a rest done, ok a → st (a :: rest) done g ≠ [])
    (hend : ∀ done, st [] done g = []) :
    ∀ l done, (∀ a ∈ l, ok a) →
      RsaRuns body rg ι (cwhileP (rg g) p) (st l done) (st [] (done ++ l))
        (l.length * (b + 2) + 2) := by
  have key : ∀ (l done : List α), (∀ a ∈ l, ok a) → ∀ (v : HS T Q A U) (S : Stacks T A),
      rsaClean ι S → rsaHolds rg S (st l done) → v.flag = (S.R (rg g)).head?.isSome →
      ∃ v' S' n, v'.user = v.user ∧ n ≤ l.length * (b + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq p (.act (peekR (rg g))))) (mk v S) n (mk v' S') ∧
        rsaHolds rg S' (st [] (done ++ l)) ∧ rsaFr rg S S' := by
    intro l
    induction l with
    | nil =>
        intro done _ v S _ hS hf
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, by simpa using hS, rsaFr.refl S⟩
        rw [mk_var, hf, hS g, hend]; rfl
    | cons a rest ih =>
        intro done hok v S hc hS hf
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ :=
          hstep a rest done (hok a (by simp)) v S hc hS
        have e₂ := peekR_run (rg g) v₁ S₁ ▸ Exec.act (body := body) (peekR (rg g)) (mk v₁ S₁)
        obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hS₃, hf₃⟩ := ih (done ++ [a])
          (fun x hx => hok x (by simp [hx])) { v₁ with flag := (S₁.R (rg g)).head?.isSome } S₁
          (hc.of_fr hdisj hf₁) hS₁ rfl
        have hft : v.flag = true := by
          rw [hf, hS g]
          cases h : st (a :: rest) done g with
          | nil => exact absurd h (hne a rest done (hok a (by simp)))
          | cons _ _ => rfl
        refine ⟨v₃, S₃, n₁ + 1 + n₃ + 1, hu₃.trans hu₁, ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ e₂) he₃, ?_, hf₁.trans hf₃⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa using hS₃
  intro l done hok v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ :=
    key l done hok { v with flag := (S.R (rg g)).head?.isSome } S hc hS rfl
  exact ⟨v', S', 1 + n, hu, by omega,
    Exec.seq (peekR_run (rg g) v S ▸ Exec.act (body := body) (peekR (rg g)) (mk v S)) he, hS', hf⟩

end Loops

end IntegerMultBounds.MathlibTM2.Fast.ResampA
