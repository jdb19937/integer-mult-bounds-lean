module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Layer.GaussStream

/-!
# Register-file contracts for the twiddle pass

The twiddle machines (`Fast/TwiddleRec.lean`, `Fast/TwiddleExp.lean`, `Fast/Twiddle.lean`) run on
the host registers `tg r`, `r : R`, for an injective layout `tg : R → Fin T`. A register file is a
function `ρ : R → List (Fin (A + 4))`.

**Contracts.** `TwHolds tg S ρ`: the stacks `S` carry `ρ`. `TwFr tg S S'`: `S'` agrees with `S`
on `inp`, `out`, the left stacks and every register outside the layout. `TwRuns body tg p ρ ρ' b`:
from any stacks carrying `ρ`, `p` runs in at most `b` steps to stacks carrying `ρ'`, framed by
`TwFr`, with the `user` component unchanged. `TwRunsS … x …` is the same contract for runs that
start with the symbol `x` in the scratch slot `sym` (the bodies of symbol loops).
`twRuns_seq`, `twRuns_mono`, `twRuns_congr` compose and adjust contracts.

**Primitives.** Contracts of host programs on the layout: `moveR` (`twRuns_moveR`), `uclear`,
`ucopy`, `udbl`, `zeroBits`, `baddTo`, `bsub`, `countIter`, single actions (`twRuns_act`), the
counted move `twCMv c src dst t` (`|c|` symbols from `src` onto `dst`, `twRuns_cmv`), the
negation of every coefficient of a register by the Gaussian automaton of `Layer/GaussStream`
(`twNeg`, `twRuns_neg`), and the branch on the top bit of a register (`twIfTop`,
`twRuns_ifTop`).

**Loops.** `twRuns_scanP`: `scanP a t p` (`Node/Params`) runs `p` once per symbol `l[j]` of `a`,
with the symbol in `sym`; the iteration contracts may cost differently per iteration.
`twRuns_while`: `twWhile g p` repeats `p` while `g` is nonempty.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node


section Contracts

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R]

/-- The stacks `S` carry the register file `ρ`. -/
def TwHolds (tg : R → Fin T) (S : Stacks T A) (ρ : R → List (Fin (A + 4))) : Prop :=
  ∀ r, S.R (tg r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `tg`. -/
def TwFr (tg : R → Fin T) (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, tg r ≠ k) → S'.R k = S.R k

/-- `p` takes the register file `ρ` to `ρ'` within `b` steps, keeping `user` and everything
outside the layout. -/
def TwRuns (body : P → Pr P T Q A U) (tg : R → Fin T) (p : Pr P T Q A U)
    (ρ ρ' : R → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S ρ → ∃ (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ),
    v'.user = v.user ∧ n ≤ b ∧ Exec body p (mk v S) n (mk v' S') ∧ TwHolds tg S' ρ' ∧
      TwFr tg S S'

/-- `TwRuns` for runs started with the symbol `x` in `sym`. -/
def TwRunsS (body : P → Pr P T Q A U) (tg : R → Fin T) (p : Pr P T Q A U) (x : Fin (A + 4))
    (ρ ρ' : R → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), v.sym = some x → TwHolds tg S ρ →
    ∃ (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ),
      v'.user = v.user ∧ n ≤ b ∧ Exec body p (mk v S) n (mk v' S') ∧ TwHolds tg S' ρ' ∧
        TwFr tg S S'

variable {body : P → Pr P T Q A U} {tg : R → Fin T}

omit [DecidableEq R] in
lemma twFr_refl (S : Stacks T A) : TwFr tg S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

omit [DecidableEq R] in
lemma twFr_trans {S₁ S₂ S₃ : Stacks T A} (h₁ : TwFr tg S₁ S₂) (h₂ : TwFr tg S₂ S₃) :
    TwFr tg S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

omit [DecidableEq R] in
theorem twRuns_seq {p q : Pr P T Q A U} {ρ₁ ρ₂ ρ₃ : R → List (Fin (A + 4))} {b₁ b₂ : ℕ}
    (h₁ : TwRuns body tg p ρ₁ ρ₂ b₁) (h₂ : TwRuns body tg q ρ₂ ρ₃ b₂) :
    TwRuns body tg (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, twFr_trans hf₁ hf₂⟩

omit [DecidableEq R] in
theorem twRuns_mono {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b b' : ℕ}
    (h : TwRuns body tg p ρ ρ' b) (hb : b ≤ b') : TwRuns body tg p ρ ρ' b' := by
  intro v S hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

omit [DecidableEq R] in
theorem twRuns_congr {p : Pr P T Q A U} {ρ ρ' ρ'' : R → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body tg p ρ ρ' b) (he : ρ' = ρ'') : TwRuns body tg p ρ ρ'' b := he ▸ h

omit [DecidableEq R] in
theorem twRuns_congr_left {p : Pr P T Q A U} {ρ ρ₀ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body tg p ρ₀ ρ' b) (he : ρ = ρ₀) : TwRuns body tg p ρ ρ' b := he ▸ h

omit [DecidableEq R] in
theorem twRunsS_of {p : Pr P T Q A U} {x : Fin (A + 4)} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body tg p ρ ρ' b) : TwRunsS body tg p x ρ ρ' b :=
  fun v S _ hS => h v S hS

omit [DecidableEq R] in
theorem twRunsS_seq {p q : Pr P T Q A U} {x : Fin (A + 4)} {ρ₁ ρ₂ ρ₃ : R → List (Fin (A + 4))}
    {b₁ b₂ : ℕ} (h₁ : TwRunsS body tg p x ρ₁ ρ₂ b₁) (h₂ : TwRuns body tg q ρ₂ ρ₃ b₂) :
    TwRunsS body tg (.seq p q) x ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hx hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hx hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, twFr_trans hf₁ hf₂⟩

omit [DecidableEq R] in
theorem twRunsS_mono {p : Pr P T Q A U} {x : Fin (A + 4)} {ρ ρ' : R → List (Fin (A + 4))}
    {b b' : ℕ} (h : TwRunsS body tg p x ρ ρ' b) (hb : b ≤ b') : TwRunsS body tg p x ρ ρ' b' := by
  intro v S hx hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hx hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

omit [DecidableEq R] in
theorem twRunsS_congr {p : Pr P T Q A U} {x : Fin (A + 4)} {ρ ρ' ρ'' : R → List (Fin (A + 4))}
    {b : ℕ} (h : TwRunsS body tg p x ρ ρ' b) (he : ρ' = ρ'') : TwRunsS body tg p x ρ ρ'' b :=
  he ▸ h

omit [DecidableEq R] in
/-- A branch on a test of the symbol in `sym`, taken. -/
theorem twRunsS_cond_true {f : HS T Q A U → Bool} {p q : Pr P T Q A U} {x : Fin (A + 4)}
    {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (hf : ∀ v : HS T Q A U, v.sym = some x → f v = true) (h : TwRunsS body tg p x ρ ρ' b) :
    TwRunsS body tg (.cond f p q) x ρ ρ' (b + 1) := by
  intro v S hx hS
  obtain ⟨v', S', n, hu, hn, he, hS', hfr⟩ := h v S hx hS
  exact ⟨v', S', n + 1, hu, by omega, Exec.cond_true (hf v hx) he, hS', hfr⟩

omit [DecidableEq R] in
/-- A branch on a test of the symbol in `sym`, not taken. -/
theorem twRunsS_cond_false {f : HS T Q A U → Bool} {p q : Pr P T Q A U} {x : Fin (A + 4)}
    {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (hf : ∀ v : HS T Q A U, v.sym = some x → f v = false) (h : TwRunsS body tg q x ρ ρ' b) :
    TwRunsS body tg (.cond f p q) x ρ ρ' (b + 1) := by
  intro v S hx hS
  obtain ⟨v', S', n, hu, hn, he, hS', hfr⟩ := h v S hx hS
  exact ⟨v', S', n + 1, hu, by omega, Exec.cond_false (hf v hx) he, hS', hfr⟩

/-! ### Register files under updates -/

lemma tw_upd_comp (htg : Function.Injective tg) {β : Type} (g : Fin T → β) (a : R) (x : β)
    (r : R) : Function.update g (tg a) x (tg r) = Function.update (fun r => g (tg r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (htg.ne h), Function.update_of_ne h]

lemma twHolds_upd (htg : Function.Injective tg) {S : Stacks T A} {ρ : R → List (Fin (A + 4))}
    (h : TwHolds tg S ρ) (a : R) (x : List (Fin (A + 4))) :
    TwHolds tg { S with R := Function.update S.R (tg a) x } (Function.update ρ a x) := by
  intro r
  show Function.update S.R (tg a) x (tg r) = _
  rw [tw_upd_comp htg]
  have : (fun r => S.R (tg r)) = ρ := funext h
  rw [this]

omit [DecidableEq R] in
lemma twFr_upd (S : Stacks T A) (a : R) (x : List (Fin (A + 4))) :
    TwFr tg S { S with R := Function.update S.R (tg a) x } :=
  ⟨rfl, rfl, rfl, fun _ hk => Function.update_of_ne (hk a).symm _ _⟩

omit [DecidableEq R] in
/-- Stacks with an updated register file. -/
lemma twRuns_of_exec {p : Pr P T Q A U} {ρ : R → List (Fin (A + 4))} (Φ : Regs T A → Regs T A)
    (ρ' : R → List (Fin (A + 4))) (b : ℕ)
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S ρ →
      ∃ (v' : HS T Q A U) (n : ℕ), v'.user = v.user ∧ n ≤ b ∧
        Exec body p (mk v S) n (mk v' { S with R := Φ S.R }))
    (hΦ : ∀ S : Stacks T A, TwHolds tg S ρ → TwHolds tg { S with R := Φ S.R } ρ' ∧
      ∀ k, (∀ r, tg r ≠ k) → Φ S.R k = S.R k) :
    TwRuns body tg p ρ ρ' b := by
  intro v S hS
  obtain ⟨v', n, hu, hn, he⟩ := h v S hS
  obtain ⟨h1, h2⟩ := hΦ S hS
  exact ⟨v', _, n, hu, hn, he, h1, ⟨rfl, rfl, rfl, h2⟩⟩

omit [DecidableEq R] in
lemma tw_upd_off {β : Type} (g : Fin T → β) (a : R) (x : β) {k : Fin T} (hk : ∀ r, tg r ≠ k) :
    Function.update g (tg a) x k = g k :=
  Function.update_of_ne (hk a).symm _ _

/-! ### Primitive contracts -/

variable (htg : Function.Injective tg)
include htg

theorem twRuns_moveR {a b : R} (hab : a ≠ b) (ρ : R → List (Fin (A + 4))) :
    TwRuns body tg (moveR (tg a) (tg b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b))
      (2 * (ρ a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := moveR_exec body (tg a) (tg b) (htg.ne hab) id v S
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · have h1 := twHolds_upd htg (twHolds_upd htg hS a []) b ((ρ a).reverse ++ ρ b)
    simp only [movedR, List.map_id]
    rw [hS a, hS b]
    exact h1
  · simp only [movedR, tw_upd_off _ _ _ hk]

theorem twRuns_uclear (a : R) (ρ : R → List (Fin (A + 4))) :
    TwRuns body tg (uclear (tg a)) ρ (Function.update ρ a []) (2 * (ρ a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := uclear_exec body (tg a) v S
  exact ⟨v', _, _, hu, by rw [hS], he, twHolds_upd htg hS a [], twFr_upd S a []⟩

theorem twRuns_ucopy {a b t : R} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (ucopy (tg a) (tg b) (tg t)) ρ
      (Function.update ρ b (List.replicate (ρ a).length tick ++ ρ b)) (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := ucopy_exec body (htg.ne hab) (htg.ne hat) (htg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, twFr_upd S b _⟩
  rw [hS a, hS b]
  exact twHolds_upd htg hS b _

theorem twRuns_udbl {b t : R} (hbt : b ≠ t) (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (udbl (tg b) (tg t)) ρ
      (Function.update ρ b ((ρ b).flatMap (List.replicate 2))) (4 * (ρ b).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := udbl_exec body (htg.ne hbt) v S (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, twFr_upd S b _⟩
  rw [hS b]
  exact twHolds_upd htg hS b _

theorem twRuns_zeroBits {len z t : R} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (zeroBits (tg len) (tg z) (tg t)) ρ
      (Function.update ρ z (binSyms (ρ len).length 0 ++ ρ z)) (4 * (ρ len).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := zeroBits_exec body (htg.ne hlz) (htg.ne hlt) (htg.ne hzt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, twFr_upd S z _⟩
  rw [hS len, hS z]
  exact twHolds_upd htg hS z _

theorem twRuns_baddTo {a b tx ty tz : R} (hreg : [a, b, tx, ty, tz].Nodup) {cy : Fin T}
    (hca : cy ≠ tg a) (hcb : cy ≠ tg b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (ρ : R → List (Fin (A + 4))) (ha : ρ a = binSyms L x) (hb : ρ b = binSyms L y)
    (htx : ρ tx = []) (hty : ρ ty = []) (htz : ρ tz = []) :
    TwRuns body tg (baddTo (tg a) (tg b) (tg tx) (tg ty) (tg tz) cy) ρ
      (Function.update ρ a (binSyms L ((x + y) % 2 ^ L))) (8 * L + 8) := by
  have hreg' : [tg a, tg b, tg tx, tg ty, tg tz].Nodup := by
    simpa [List.map] using hreg.map htg
  intro v S hS
  obtain ⟨v', hu, -, -, he⟩ := baddTo_exec body hreg' hca hcb hx hy v S (by rw [hS, ha])
    (by rw [hS, hb]) (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  exact ⟨v', _, _, hu, le_rfl, he, twHolds_upd htg hS a _, twFr_upd S a _⟩

theorem twRuns_bsub {a b c tx ty tz : R} (hreg : [a, b, c, tx, ty, tz].Nodup) {cy : Fin T}
    (hca : cy ≠ tg a) (hcb : cy ≠ tg b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (ρ : R → List (Fin (A + 4))) (ha : ρ a = binSyms L x) (hb : ρ b = binSyms L y)
    (htx : ρ tx = []) (hty : ρ ty = []) (htz : ρ tz = []) :
    TwRuns body tg (bsub (tg a) (tg b) (tg c) (tg tx) (tg ty) (tg tz) cy) ρ
      (Function.update ρ c (binSyms L ((x + 2 ^ L - y) % 2 ^ L) ++ ρ c)) (8 * L + 8) := by
  have hreg' : [tg a, tg b, tg c, tg tx, tg ty, tg tz].Nodup := by
    simpa [List.map] using hreg.map htg
  intro v S hS
  obtain ⟨v', hu, -, -, he⟩ := bsub_exec body hreg' hca hcb hx hy v S (by rw [hS, ha])
    (by rw [hS, hb]) (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  refine ⟨v', _, _, hu, le_rfl, he, ?_, twFr_upd S c _⟩
  rw [hS c]
  exact twHolds_upd htg hS c _

theorem twRuns_countIter {c tmp : R} (hct : c ≠ tmp) (cy : Fin T) {W j : ℕ}
    (ρ : R → List (Fin (A + 4))) (hc : ρ c = binSyms W j) (ht : ρ tmp = []) :
    TwRuns body tg (countIter (tg c) (tg tmp) cy) ρ (Function.update ρ c (binSyms W (j + 1)))
      (4 * W + 5) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := countIter_exec body (htg.ne hct) cy v S (by rw [hS, hc])
    (by rw [hS, ht])
  exact ⟨v', _, _, hu, le_rfl, he, twHolds_upd htg hS c _, twFr_upd S c _⟩

omit [DecidableEq R] htg in
/-- A single action with a known effect on the register file. -/
theorem twRuns_act (a : Act T Q A U) {ρ ρ' : R → List (Fin (A + 4))}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S ρ →
      ∃ (v' : HS T Q A U) (S' : Stacks T A), v'.user = v.user ∧ a.run (mk v S) = mk v' S' ∧
        TwHolds tg S' ρ' ∧ TwFr tg S S') :
    TwRuns body tg (.act a) ρ ρ' 1 := by
  intro v S hS
  obtain ⟨v', S', hu, hrun, hS', hf⟩ := h v S hS
  exact ⟨v', S', 1, hu, le_rfl, hrun ▸ Exec.act (body := body) a (mk v S), hS', hf⟩

omit htg [DecidableEq R] in
/-- An action followed by a program that reads the symbol the action leaves in `sym`. -/
theorem twRuns_act_seqS (a : Act T Q A U) {q : Pr P T Q A U} {y : Fin (A + 4)}
    {ρ ρ₁ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S ρ →
      ∃ (v' : HS T Q A U) (S' : Stacks T A), v'.user = v.user ∧ v'.sym = some y ∧
        a.run (mk v S) = mk v' S' ∧ TwHolds tg S' ρ₁ ∧ TwFr tg S S')
    (hq : TwRunsS body tg q y ρ₁ ρ' b) :
    TwRuns body tg (.seq (.act a) q) ρ ρ' (1 + b) := by
  intro v S hS
  obtain ⟨v₁, S₁, hu₁, hy, hrun, hS₁, hf₁⟩ := h v S hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := hq v₁ S₁ hy hS₁
  exact ⟨v₂, S₂, 1 + n₂, hu₂.trans hu₁, by omega,
    Exec.seq (hrun ▸ Exec.act (body := body) a (mk v S)) he₂, hS₂, twFr_trans hf₁ hf₂⟩

end Contracts

/-! ### Moving the top symbol -/

section Moves

variable {T Q A : ℕ} {U P : Type}

/-- Pop `src` into `sym` and push the symbol onto `dst`, then continue with `k`. -/
def twMvTop (src dst : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o }) (.push (.rt dst) (fun v => v.sym.getD blank) k)

/-- Pop `src` into `sym` and push the symbol onto `d₁` and `d₂`. -/
def twMvTop2 (src d₁ d₂ : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt d₁) (fun v => v.sym.getD blank) (.push (.rt d₂) (fun v => v.sym.getD blank) .done))

/-- The register effect of `twMvTop`. -/
def twMvFx (src dst : Fin T) (R : Regs T A) : Regs T A :=
  Function.update (Function.update R src (R src).tail) dst ((R src).head?.getD blank :: R dst)

lemma twMvTop_run {src dst : Fin T} (hsd : src ≠ dst) (k : Act T Q A U) (v : HS T Q A U)
    (S : Stacks T A) :
    (twMvTop src dst k).run (mk v S) =
      k.run (mk { v with sym := (S.R src).head? } { S with R := twMvFx src dst S.R }) := by
  simp [twMvTop, Action.run, update_rt, twMvFx, Function.update_of_ne hsd.symm]

lemma twMvTop2_run {src d₁ d₂ : Fin T} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (v : HS T Q A U) (S : Stacks T A) :
    (twMvTop2 src d₁ d₂).run (mk v S) =
      mk { v with sym := (S.R src).head? }
        { S with
          R := Function.update (twMvFx src d₁ S.R) d₂ ((S.R src).head?.getD blank :: S.R d₂) } := by
  simp [twMvTop2, Action.run, update_rt, twMvFx, Function.update_of_ne h1.symm,
    Function.update_of_ne h2.symm, Function.update_of_ne h12.symm]

lemma regFx_twMvTop {src dst : Fin T} (hsd : src ≠ dst) :
    RegFx (Q := Q) (U := U) (twMvTop src dst) (fun _ => twMvFx (A := A) src dst) := by
  intro x k v S _
  exact ⟨{ v with sym := (S.R src).head? }, rfl, twMvTop_run hsd k v S⟩

lemma frame_twMvFx {a src dst : Fin T} (h1 : a ≠ src) (h2 : a ≠ dst) :
    Frame a (fun _ => twMvFx (T := T) (A := A) src dst) := by
  intro x R l
  funext k
  simp only [twMvFx, Function.update_apply]
  split_ifs <;> simp_all

lemma twMvFx_iter {src dst : Fin T} (hsd : src ≠ dst) :
    ∀ (n : ℕ) (R : Regs T A), n ≤ (R src).length →
      (twMvFx src dst)^[n] R = Function.update (Function.update R src ((R src).drop n)) dst
        (((R src).take n).reverse ++ R dst) := by
  intro n
  induction n with
  | zero => intro R _; simp
  | succ n ih =>
      intro R hn
      obtain ⟨y, l, hl⟩ : ∃ y l, R src = y :: l := by
        cases h : R src with
        | nil => rw [h] at hn; simp at hn
        | cons y l => exact ⟨y, l, rfl⟩
      rw [Function.iterate_succ_apply,
        ih _ (by simp [twMvFx, Function.update_of_ne hsd, hl]; simp [hl] at hn; omega)]
      funext k
      simp only [twMvFx, Function.update_apply, hl]
      split_ifs <;> simp_all

lemma tw_foldl_const_iter {α β : Type} (Φ : β → β) :
    ∀ (l : List α) (R : β), l.foldl (fun R _ => Φ R) R = Φ^[l.length] R
  | [], _ => rfl
  | x :: l, R => by
      rw [List.foldl_cons, tw_foldl_const_iter Φ l, List.length_cons, Function.iterate_succ_apply]

/-- Counted move: `|c|` symbols from `src` onto `dst` (reversed), `c` kept through the empty `t`. -/
def twCMv (c src dst t : Fin T) : Pr P T Q A U := scanR c t (twMvTop src dst)

end Moves

section Prims

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T} (htg : Function.Injective tg)
include htg

theorem twRuns_cmv {c src dst t : R} (hreg : [c, src, dst, t].Nodup) (ρ : R → List (Fin (A + 4)))
    (ht : ρ t = []) (hn : (ρ c).length ≤ (ρ src).length) :
    TwRuns body tg (twCMv (tg c) (tg src) (tg dst) (tg t)) ρ
      (Function.update (Function.update ρ src ((ρ src).drop (ρ c).length)) dst
        (((ρ src).take (ρ c).length).reverse ++ ρ dst)) (4 * (ρ c).length + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  intro v S hS
  obtain ⟨v', hu, he⟩ := scanR_exec' body (htg.ne ‹c ≠ t›) (regFx_twMvTop (htg.ne ‹src ≠ dst›))
    (frame_twMvFx (htg.ne ‹c ≠ src›) (htg.ne ‹c ≠ dst›))
    (frame_twMvFx (htg.ne ‹src ≠ t›.symm) (htg.ne ‹dst ≠ t›.symm)) v S (by rw [hS, ht])
  rw [tw_foldl_const_iter, twMvFx_iter (htg.ne ‹src ≠ dst›) _ _ (by rw [hS, hS]; exact hn)] at he
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · have h1 := twHolds_upd htg (twHolds_upd htg hS src ((ρ src).drop (ρ c).length)) dst
      (((ρ src).take (ρ c).length).reverse ++ ρ dst)
    simp only [hS c, hS src, hS dst]
    exact h1
  · simp only [tw_upd_off _ _ _ hk]

/-- `twMvTop` as a single action: one symbol from `src` onto `dst`, the symbol in `sym`. -/
theorem twRuns_mvTop_seqS {src dst : R} (hsd : src ≠ dst) {q : Pr P T Q A U} {y : Fin (A + 4)}
    {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ} {rest : List (Fin (A + 4))}
    (hsrc : ρ src = y :: rest)
    (hq : TwRunsS body tg q y
      (Function.update (Function.update ρ src rest) dst (y :: ρ dst)) ρ' b) :
    TwRuns body tg (.seq (.act (twMvTop (tg src) (tg dst) .done)) q) ρ ρ' (1 + b) := by
  refine twRuns_act_seqS _ (fun v S hS => ?_) hq
  refine ⟨{ v with sym := (S.R (tg src)).head? }, { S with R := twMvFx (tg src) (tg dst) S.R },
    rfl, by simp [hS src, hsrc], by rw [twMvTop_run (htg.ne hsd)]; rfl, ?_,
    ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · have h1 := twHolds_upd htg (twHolds_upd htg hS src rest) dst (y :: ρ dst)
    simpa [twMvFx, hS src, hS dst, hsrc] using h1
  · simp only [twMvFx, tw_upd_off _ _ _ hk]

theorem twRuns_mvTop {src dst : R} (hsd : src ≠ dst) {ρ : R → List (Fin (A + 4))}
    {y : Fin (A + 4)} {rest : List (Fin (A + 4))} (hsrc : ρ src = y :: rest) :
    TwRuns body tg (.act (twMvTop (tg src) (tg dst) .done)) ρ
      (Function.update (Function.update ρ src rest) dst (y :: ρ dst)) 1 := by
  refine twRuns_act _ (fun v S hS => ?_)
  refine ⟨{ v with sym := (S.R (tg src)).head? }, { S with R := twMvFx (tg src) (tg dst) S.R },
    rfl, by rw [twMvTop_run (htg.ne hsd)]; rfl, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · have h1 := twHolds_upd htg (twHolds_upd htg hS src rest) dst (y :: ρ dst)
    simpa [twMvFx, hS src, hS dst, hsrc] using h1
  · simp only [twMvFx, tw_upd_off _ _ _ hk]

theorem twRuns_mvTop2 {src d₁ d₂ : R} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    {ρ : R → List (Fin (A + 4))} {y : Fin (A + 4)} {rest : List (Fin (A + 4))}
    (hsrc : ρ src = y :: rest) :
    TwRuns body tg (.act (twMvTop2 (tg src) (tg d₁) (tg d₂))) ρ
      (Function.update (Function.update (Function.update ρ src rest) d₁ (y :: ρ d₁)) d₂
        (y :: ρ d₂)) 1 := by
  refine twRuns_act _ (fun v S hS => ?_)
  refine ⟨{ v with sym := (S.R (tg src)).head? }, _, rfl,
    twMvTop2_run (htg.ne h1) (htg.ne h2) (htg.ne h12) v S, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · have e := twHolds_upd htg (twHolds_upd htg (twHolds_upd htg hS src rest) d₁ (y :: ρ d₁)) d₂
      (y :: ρ d₂)
    have hd2 : S.R (tg d₂) = ρ d₂ := hS d₂
    simp only [twMvFx, hS src, hsrc, List.tail_cons, List.head?_cons, Option.getD_some, hd2,
      hS d₁] at e ⊢
    exact e
  · simp only [twMvFx, tw_upd_off _ _ _ hk]

/-- Push one symbol onto a register. -/
theorem twRuns_push (a : R) (y : Fin (A + 4)) (ρ : R → List (Fin (A + 4))) :
    TwRuns body tg (.act (.push (.rt (tg a)) (fun _ => y) .done)) ρ
      (Function.update ρ a (y :: ρ a)) 1 := by
  refine twRuns_act _ (fun v S hS => ?_)
  refine ⟨v, { S with R := Function.update S.R (tg a) (y :: S.R (tg a)) }, rfl, ?_, ?_,
    twFr_upd S a _⟩
  · simp [Action.run, update_rt]
  · rw [hS a]; exact twHolds_upd htg hS a _

end Prims

/-! ### Negation of coefficient streams -/

section Neg

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T}

/-- Negate every coefficient of `ins` (moving it onto `outs`, reversed) with the Gaussian
automaton of `[[−1]]`; words of `|ctr|` symbols, spare `tmp`, state slot `st`. -/
def twNeg (ins outs st ctr tmp : Fin T) : Pr P T Q A U :=
  autoWords (fun _ : Fin 1 => ins) (fun _ : Fin 1 => outs) st ctr tmp
    (gaussAuto A ![![(-1, 0)]] 1 false)

variable (htg : Function.Injective tg)
include htg

theorem twRuns_neg {ins outs ctr tmp : R} (hreg : [ins, outs, ctr, tmp].Nodup) {st : Fin T}
    (hst : tg ins ≠ st) (hA : 5 ≤ A) {W : ℕ} (hW : 1 ≤ W) (ρ : R → List (Fin (A + 4)))
    (zs : List (GR W)) (hin : ρ ins = zs.flatMap (coeffSyms A W)) (hctr : (ρ ctr).length = W)
    (htmp : ρ tmp = []) :
    TwRuns body tg (twNeg (tg ins) (tg outs) st (tg ctr) (tg tmp)) ρ
      (Function.update (Function.update ρ ins []) outs
        (((zs.map fun z => -z).flatMap (coeffSyms A W)).reverse ++ ρ outs))
      (zs.length * (5 * W + 6) + 2) := by
  have hreg' := hreg
  regs_ne hreg'
  have hL : AutoLayout (fun _ : Fin 1 => tg ins) (fun _ : Fin 1 => tg outs) st (tg ctr) (tg tmp) :=
    { ins_inj := fun a b _ => Subsingleton.elim a b
      outs_inj := fun a b _ => Subsingleton.elim a b
      ins_outs := fun _ _ => htg.ne ‹ins ≠ outs›
      ins_ctr := fun _ => htg.ne ‹ins ≠ ctr›
      ins_tmp := fun _ => htg.ne ‹ins ≠ tmp›
      outs_ctr := fun _ => htg.ne ‹outs ≠ ctr›
      outs_tmp := fun _ => htg.ne ‹outs ≠ tmp›
      ctr_tmp := htg.ne ‹ctr ≠ tmp›
      ins_st := fun _ => hst }
  intro v S hS
  obtain ⟨v', m, S', hu, hm, he, hi, ho, hL', hins, houts, hoth⟩ := neg_exec body hL
    (by omega) hW (ctrs := S.R (tg ctr)) (by rw [hS, hctr]) zs v S rfl (by rw [hS, htmp])
    (by rw [hS, hin])
  refine ⟨v', S', m, hu, hm, he, fun r => ?_, ⟨hi, ho, hL', fun k hk => hoth k
    (fun h => hk ins h.symm) (fun h => hk outs h.symm)⟩⟩
  by_cases h1 : r = outs
  · subst h1; rw [houts, hS]; simp
  · by_cases h2 : r = ins
    · subst h2; rw [hins]; simp [Function.update_of_ne h1]
    · rw [hoth _ (htg.ne h2) (htg.ne h1), hS]
      simp [Function.update_of_ne h1, Function.update_of_ne h2]

end Neg

/-! ### Branching on the top bit of a register -/

section IfTop

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T}

/-- Peek the top of `g` into `sym`, then run `p` if it is the bit `true` and `q` otherwise. -/
def twIfTop (g : Fin T) (p q : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (.peek (.rt g) (fun v o => { v with sym := o }) .done))
    (.cond (fun v => symBit (v.sym.getD blank)) p q)

omit [DecidableEq R] in
theorem twRuns_ifTop {g : R} {p q : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {bt : Bool}
    {rest : List (Fin (A + 4))} (hg : ρ g = bitSymbol bt :: rest) {b : ℕ}
    (hp : bt = true → TwRuns body tg p ρ ρ' b) (hq : bt = false → TwRuns body tg q ρ ρ' b) :
    TwRuns body tg (twIfTop (tg g) p q) ρ ρ' (b + 2) := by
  intro v S hS
  have hrun : (Action.peek (.rt (tg g)) (fun v o => { v with sym := o }) .done :
      Act T Q A U).run (mk v S) = mk { v with sym := some (bitSymbol bt) } S := by
    simp [Action.run, hS g, hg]
  have e₁ := hrun ▸ Exec.act (body := body)
    (Action.peek (.rt (tg g)) (fun v o => { v with sym := o }) .done) (mk v S)
  cases bt with
  | true =>
      obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := hp rfl { v with sym := some (bitSymbol true) } S hS
      exact ⟨v', S', 1 + (n + 1), hu, by omega,
        Exec.seq e₁ (Exec.cond_true (by simp) he), hS', hf⟩
  | false =>
      obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := hq rfl { v with sym := some (bitSymbol false) } S hS
      exact ⟨v', S', 1 + (n + 1), hu, by omega,
        Exec.seq e₁ (Exec.cond_false (by simp) he), hS', hf⟩

end IfTop

/-! ### Loops -/

section Loops

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T}

/-- The register file of a symbol loop over `l` on `a` (spare `t`) after `k` iterations: `Ψ k`
off `a` and `t`. -/
def twAT (a t : R) (l : List (Fin (A + 4))) (Ψ : ℕ → R → List (Fin (A + 4))) (k : ℕ) :
    R → List (Fin (A + 4)) :=
  Function.update (Function.update (Ψ k) a (l.drop k)) t ((l.take k).reverse)

/-- The register file inside iteration `k` of a symbol loop, after the symbol is popped. -/
def twATin (a t : R) (l : List (Fin (A + 4))) (Ψ : ℕ → R → List (Fin (A + 4))) (k : ℕ) :
    R → List (Fin (A + 4)) :=
  Function.update (Function.update (Ψ k) a (l.drop (k + 1))) t ((l.take (k + 1)).reverse)

variable (htg : Function.Injective tg)
include htg

theorem twRuns_scanP_loop {a t : R} (hat : a ≠ t) {p : Pr P T Q A U} (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (c : ℕ → ℕ)
    (hp : ∀ j (hj : j < l.length), TwRunsS body tg p l[j] (twATin a t l Ψ j)
      (twAT a t l Ψ (j + 1)) (c j)) :
    ∀ (n k : ℕ), k + n = l.length → ∀ (v : HS T Q A U) (S : Stacks T A),
      TwHolds tg S (twAT a t l Ψ k) → v.flag = (l.drop k).head?.isSome →
      ∃ (v' : HS T Q A U) (S' : Stacks T A) (m : ℕ), v'.user = v.user ∧
        m ≤ ∑ i ∈ Finset.range n, (c (k + i) + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush (tg a) (tg t))) (.seq p (.act (peekR (tg a))))))
          (mk v S) m (mk v' S') ∧ TwHolds tg S' (twAT a t l Ψ l.length) ∧ TwFr tg S S' := by
  intro n
  induction n with
  | zero =>
      intro k hk v S hS hf
      have hd : l.drop k = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨v, S, 1, rfl, by simp, .loop_false (by simpa [hd] using hf), ?_, twFr_refl S⟩
      rw [show l.length = k by omega]; exact hS
  | succ n ih =>
      intro k hk v S hS hf
      have hkl : k < l.length := by omega
      have hdrop : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hkl
      have hSa : S.R (tg a) = l[k] :: l.drop (k + 1) := by
        rw [hS a, ← hdrop]; unfold twAT; rw [Function.update_of_ne hat, Function.update_self]
      have hSt : S.R (tg t) = (l.take k).reverse := by
        rw [hS t]; unfold twAT; rw [Function.update_self]
      have hrun : (popPush (tg a) (tg t) : Act T Q A U).run (mk v S) =
          mk { v with sym := some l[k] } { S with R := twMvFx (tg a) (tg t) S.R } := by
        have := twMvTop_run (htg.ne hat) .done v S
        rw [hSa] at this
        exact this
      have htk : (l.take (k + 1)).reverse = l[k] :: (l.take k).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkl]; simp
      have hS₁ : TwHolds tg { S with R := twMvFx (tg a) (tg t) S.R } (twATin a t l Ψ k) := by
        intro r
        show twMvFx (tg a) (tg t) S.R (tg r) = _
        unfold twMvFx twATin
        rw [hSa, hSt, List.tail_cons, List.head?_cons, Option.getD_some]
        by_cases hr : r = t
        · subst hr
          rw [Function.update_self, Function.update_self, htk]
        · rw [Function.update_of_ne (htg.ne hr), Function.update_of_ne hr]
          by_cases hra : r = a
          · subst hra
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (htg.ne hra), Function.update_of_ne hra, hS r]
            unfold twAT
            rw [Function.update_of_ne hr, Function.update_of_ne hra]
      have hfr₀ : TwFr tg S { S with R := twMvFx (tg a) (tg t) S.R } :=
        ⟨rfl, rfl, rfl, fun k' hk' => by
          show twMvFx (tg a) (tg t) S.R k' = S.R k'
          unfold twMvFx
          rw [tw_upd_off _ _ _ hk', tw_upd_off _ _ _ hk']⟩
      obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₂, hf₁⟩ := hp k hkl { v with sym := some l[k] }
        { S with R := twMvFx (tg a) (tg t) S.R } rfl hS₁
      have he₂ := Exec.act (body := body) (peekR (tg a)) (mk v₁ S₁)
      rw [peekR_run] at he₂
      have hS₂a : S₁.R (tg a) = l.drop (k + 1) := by
        rw [hS₂ a]; unfold twAT; rw [Function.update_of_ne hat, Function.update_self]
      obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hS₃, hf₃⟩ := ih (k + 1) (by omega)
        { v₁ with flag := (S₁.R (tg a)).head?.isSome } S₁ hS₂ (by rw [hS₂a])
      have hft : v.flag = true := by rw [hf, hdrop]; rfl
      refine ⟨v₃, S₃, 1 + (m₁ + 1) + m₃ + 1, by rw [hu₃, hu₁], ?_,
        Exec.loop_true hft
          (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq he₁ he₂)) he₃, hS₃,
        twFr_trans hfr₀ (twFr_trans hf₁ hf₃)⟩
      rw [Finset.sum_range_succ']
      have : ∑ i ∈ Finset.range n, (c (k + 1 + i) + 3) =
          ∑ i ∈ Finset.range n, (c (k + (i + 1)) + 3) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.add_assoc, Nat.add_comm 1 i]
      rw [← this]
      simp only [Nat.add_zero]
      omega

/-- **Symbol loop.** `scanP a t p` with `a` holding `l` and `t` empty: iteration `j` runs `p`
with `l[j]` in `sym`, from `Ψ j` to `Ψ (j + 1)` off `a` and `t`, in at most `c j` steps; at the
end `a` holds `l` again and `t` is empty. -/
theorem twRuns_scanP {a t : R} (hat : a ≠ t) {p : Pr P T Q A U} (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (c : ℕ → ℕ)
    (hp : ∀ j (hj : j < l.length), TwRunsS body tg p l[j] (twATin a t l Ψ j)
      (twAT a t l Ψ (j + 1)) (c j)) :
    TwRuns body tg (scanP (tg a) (tg t) p) (twAT a t l Ψ 0)
      (Function.update (Function.update (Ψ l.length) a l) t [])
      (∑ j ∈ Finset.range l.length, (c j + 3) + 2 * l.length + 4) := by
  intro v S hS
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := twRuns_scanP_loop htg hat l Ψ c hp l.length 0
    (by omega) { v with flag := (S.R (tg a)).head?.isSome } S hS
    (by rw [hS a]; unfold twAT; rw [Function.update_of_ne hat, Function.update_self])
  have hl := twRuns_moveR (body := body) htg hat.symm (twAT a t l Ψ l.length)
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := hl v₁ S₁ hS₁
  refine ⟨v₂, S₂, 1 + (m₁ + m₂), by rw [hu₂, hu₁], ?_,
    Exec.seq (peekR_run (tg a) v S ▸ Exec.act (body := body) (peekR (tg a)) (mk v S))
      (Exec.seq he₁ he₂), ?_, twFr_trans hf₁ hf₂⟩
  · simp only [Nat.zero_add] at hm₁
    simp [twAT] at hm₂
    omega
  · intro r
    rw [hS₂ r]
    by_cases hr : r = t
    · subst hr; simp [twAT, hat, hat.symm]
    · by_cases hra : r = a
      · subst hra; simp [twAT, hat]
      · simp [twAT, Function.update_of_ne hr, Function.update_of_ne hra]

/-- Repeat `p` while register `g` is nonempty. -/
def twWhile (g : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR g)) (.loop (·.flag) (.seq p (.act (peekR g))))

omit htg [DecidableEq R] in
/-- **While loop.** Iteration `j < M` takes `st j` to `st (j + 1)`; `g` is nonempty before every
iteration and empty after the last. -/
theorem twRuns_while (g : R) (p : Pr P T Q A U) (st : ℕ → R → List (Fin (A + 4))) (M b : ℕ)
    (hstep : ∀ j < M, TwRuns body tg p (st j) (st (j + 1)) b) (hne : ∀ j < M, st j g ≠ [])
    (hend : st M g = []) :
    TwRuns body tg (twWhile (tg g) p) (st 0) (st M) (M * (b + 2) + 2) := by
  have key : ∀ n k, k + n = M → ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S (st k) →
      v.flag = (S.R (tg g)).head?.isSome →
      ∃ (v' : HS T Q A U) (S' : Stacks T A) (m : ℕ), v'.user = v.user ∧ m ≤ n * (b + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq p (.act (peekR (tg g))))) (mk v S) m (mk v' S') ∧
        TwHolds tg S' (st M) ∧ TwFr tg S S' := by
    intro n
    induction n with
    | zero =>
        intro k hk v S hS hf
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, by rw [show M = k by omega]; exact hS,
          twFr_refl S⟩
        rw [mk_var, hf, hS g, show k = M by omega, hend]; rfl
    | succ n ih =>
        intro k hk v S hS hf
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := hstep k (by omega) v S hS
        have e₂ := peekR_run (tg g) v₁ S₁ ▸ Exec.act (body := body) (peekR (tg g)) (mk v₁ S₁)
        obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hS₃, hf₃⟩ := ih (k + 1) (by omega)
          { v₁ with flag := (S₁.R (tg g)).head?.isSome } S₁ hS₁ rfl
        have hft : v.flag = true := by
          rw [hf, hS g]
          cases h : st k g with
          | nil => exact absurd h (hne k (by omega))
          | cons _ _ => rfl
        refine ⟨v₃, S₃, n₁ + 1 + n₃ + 1, hu₃.trans hu₁, ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ e₂) he₃, hS₃, twFr_trans hf₁ hf₃⟩
        nlinarith
  intro v S hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ :=
    key M 0 (by omega) { v with flag := (S.R (tg g)).head?.isSome } S hS rfl
  exact ⟨v', S', 1 + n, hu, by omega,
    Exec.seq (peekR_run (tg g) v S ▸ Exec.act (body := body) (peekR (tg g)) (mk v S)) he, hS', hf⟩

end Loops

end IntegerMultBounds.MathlibTM2.Fast
