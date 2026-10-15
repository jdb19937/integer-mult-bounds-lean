module

public import IntegerMultBounds.MathlibTM2.Node.SwapPass
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-!
# Register-file contracts for the CRT layout machines

The CRT layout machines (`Fast/CRTPad.lean`, `Fast/CRTSwap.lean`, `Fast/CRTRot.lean`,
`Fast/CRTMachine.lean`) are host programs on the registers `S.R i` (right stacks). Their
contracts are stated on whole register files.

**Contract.** `crtRuns body p R R' b`: from any stacks whose registers are `R` and whose left
stacks are all empty, `p` runs in at most `b` steps to the same stacks with registers `R'`; the
input stack, the output stack and the left stacks are unchanged, and so is the `user` component
of the local state. `crtRuns_seq` composes contracts, `crtRuns_mono` weakens the bound and
`crtRuns_congr` rewrites the final file.

**Loops.**
* `crtFor c t p` (`= scanP c t p`) runs `p` once per symbol of register `c`, keeping the symbols
  on the empty register `t` and moving them back at the end. `crtIter` states the iteration
  contracts off `c` and `t` (as `IterSpec` does); `crtFor_runs`: `N (b + 3) + 2 N + 4` steps for
  `N = |c|` and iteration bound `b`.
* `crtWhile r p` repeats `p` while register `r` is nonempty; `crtWhile_runs` takes a sequence of
  register files `Ψ j` with exact iteration contracts.
* `crtIfR r p q` runs `p` when register `r` is nonempty and `q` otherwise.

**Primitives.** `crtMv` (= `moveR … id`), `crtCMv c t src dst` (move `|c|` symbols from `src` to
`dst`, counted by `c`), `crtCMv2` (move `|c| |r|` symbols, a counted move per symbol of `c`),
`crtCpy` (copy `|c|` symbols of `src` onto `dst`, keeping `src`), `crtDrop` (pop `|c|` symbols),
`crtMvWhile src dst x` (move while the top symbol is `x`), `crtPush j x` (push one symbol), and
contracts for `uclear`, `ucopy`, `usub`, `upow2`, `bcopy`, `zeroBits`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

set_option linter.unusedSimpArgs false

open Lean Elab Tactic Meta in
/-- Add the symmetric form `b ≠ a` of every hypothesis `a ≠ b` of the main goal. -/
elab "crt_ne_symm" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if ty.isAppOfArity ``Ne 3 then
      let pf ← mkAppM ``Ne.symm #[ldecl.toExpr]
      let pfTy ← inferType pf
      let g ← goal.assert `hsymm pfTy pf
      let (_, g) ← g.intro1
      goal := g
  replaceMainGoal [goal]

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### Contracts -/

/-- `p` takes stacks with registers `R` and empty left stacks to the same stacks with registers
`R'`, within `b` steps, keeping `user`. -/
def crtRuns (p : Pr P T Q A U) (R R' : Regs T A) (b : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R → (∀ y, S.L y = []) →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ b ∧
      Exec body p (mk v S) m (mk v' { S with R := R' })

variable {body}

theorem crtRuns_seq {p q : Pr P T Q A U} {R₁ R₂ R₃ : Regs T A} {b₁ b₂ : ℕ}
    (h₁ : crtRuns body p R₁ R₂ b₁) (h₂ : crtRuns body q R₂ R₃ b₂) :
    crtRuns body (.seq p q) R₁ R₃ (b₁ + b₂) := by
  intro v S hS hL
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := h₁ v S hS hL
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := h₂ v₁ { S with R := R₂ } rfl hL
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

theorem crtRuns_mono {p : Pr P T Q A U} {R R' : Regs T A} {b b' : ℕ}
    (h : crtRuns body p R R' b) (hb : b ≤ b') : crtRuns body p R R' b' := by
  intro v S hS hL
  obtain ⟨v', m, hu, hm, he⟩ := h v S hS hL
  exact ⟨v', m, hu, hm.trans hb, he⟩

theorem crtRuns_congr {p : Pr P T Q A U} {R R' R'' : Regs T A} {b : ℕ}
    (h : crtRuns body p R R' b) (he : R' = R'') : crtRuns body p R R'' b := he ▸ h

theorem crtRuns_congr_left {p : Pr P T Q A U} {R R₀ R' : Regs T A} {b : ℕ}
    (h : crtRuns body p R₀ R' b) (he : R = R₀) : crtRuns body p R R' b := he ▸ h

/-- An action whose effect on stacks with registers `R` is a register file `R'`. -/
theorem crtRuns_act (a : Act T Q A U) {R R' : Regs T A}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ a.run (mk v S) = mk v' { S with R := R' }) :
    crtRuns body (.act a) R R' 1 := by
  intro v S hS _
  obtain ⟨v', hu, hrun⟩ := h v S hS
  exact ⟨v', 1, hu, le_rfl, hrun ▸ Exec.act (body := body) a (mk v S)⟩

/-- An exact execution lemma as a contract. -/
theorem crtRuns_of_exec {p : Pr P T Q A U} {R R' : Regs T A} {b : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ b ∧
        Exec body p (mk v S) m (mk v' { S with R := R' })) :
    crtRuns body p R R' b :=
  fun v S hS _ => h v S hS

/-! ### Branching on a register -/

/-- Run `p` if register `r` is nonempty, `q` otherwise. -/
def crtIfR (r : Fin T) (p q : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR r)) (.cond (·.flag) p q)

theorem crtIfR_runs {r : Fin T} {p q : Pr P T Q A U} {R R' : Regs T A} {b : ℕ}
    (hp : R r ≠ [] → crtRuns body p R R' b) (hq : R r = [] → crtRuns body q R R' b) :
    crtRuns body (crtIfR r p q) R R' (b + 2) := by
  intro v S hS hL
  have he₀ := Exec.act (body := body) (peekR r) (mk v S)
  rw [peekR_run] at he₀
  by_cases hr : R r = []
  · obtain ⟨v', m, hu, hm, he⟩ := hq hr { v with flag := (S.R r).head?.isSome } S hS hL
    refine ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₀ (Exec.cond_false ?_ he)⟩
    simp [hS, hr]
  · obtain ⟨v', m, hu, hm, he⟩ := hp hr { v with flag := (S.R r).head?.isSome } S hS hL
    refine ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₀ (Exec.cond_true ?_ he)⟩
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hr
    simp [hS, hx]

/-! ### While a register is nonempty -/

/-- Repeat `p` while register `r` is nonempty. -/
def crtWhile (r : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR r)) (.loop (·.flag) (.seq p (.act (peekR r))))

theorem crtWhile_loop {r : Fin T} {p : Pr P T Q A U} {Ψ : ℕ → Regs T A} {N b : ℕ}
    (hp : ∀ j < N, (Ψ j) r ≠ [] ∧ crtRuns body p (Ψ j) (Ψ (j + 1)) b) (hN : (Ψ N) r = []) :
    ∀ k j (v : HS T Q A U) (S : Stacks T A), j + k = N → S.R = Ψ j → (∀ y, S.L y = []) →
      v.flag = (S.R r).head?.isSome →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ k * (b + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq p (.act (peekR r)))) (mk v S) m
          (mk v' { S with R := Ψ N }) := by
  intro k
  induction k with
  | zero =>
      intro j v S hj hS _ hf
      rw [Nat.add_zero] at hj
      subst hj
      refine ⟨v, 1, rfl, by omega, ?_⟩
      have : ({ S with R := Ψ j } : Stacks T A) = S := by rw [← hS]
      rw [this]
      exact .loop_false (by simp [hf, hS, hN])
  | succ k ih =>
      intro j v S hj hS hL hf
      obtain ⟨hne, hrun⟩ := hp j (by omega)
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := hrun v S hS hL
      have he₂ := Exec.act (body := body) (peekR r) (mk v₁ { S with R := Ψ (j + 1) })
      rw [peekR_run] at he₂
      obtain ⟨v', m', hu', hm', he'⟩ := ih (j + 1)
        { v₁ with flag := (Ψ (j + 1) r).head?.isSome } { S with R := Ψ (j + 1) } (by omega) rfl
        hL rfl
      refine ⟨v', m₁ + 1 + m' + 1, hu'.trans hu₁, ?_, ?_⟩
      · rw [Nat.add_mul]; nlinarith
      · refine Exec.loop_true ?_ (Exec.seq he₁ he₂) he'
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        simp [hf, hS, hx]

/-- `crtWhile r p` from `Ψ 0` to `Ψ N`: iteration `j < N` starts with `r` nonempty and runs `p`
from `Ψ j` to `Ψ (j + 1)` within `b` steps; `r` is empty in `Ψ N`. -/
theorem crtWhile_runs {r : Fin T} {p : Pr P T Q A U} {Ψ : ℕ → Regs T A} {N b : ℕ}
    (hp : ∀ j < N, (Ψ j) r ≠ [] ∧ crtRuns body p (Ψ j) (Ψ (j + 1)) b) (hN : (Ψ N) r = []) :
    crtRuns body (crtWhile r p) (Ψ 0) (Ψ N) (N * (b + 2) + 2) := by
  intro v S hS hL
  have he₀ := Exec.act (body := body) (peekR r) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v', m, hu, hm, he⟩ := crtWhile_loop hp hN N 0 { v with flag := (S.R r).head?.isSome } S
    (by omega) hS hL rfl
  exact ⟨v', 1 + m, hu, by omega, Exec.seq he₀ he⟩

/-! ### For each symbol of a register -/

/-- Run `p` once per symbol of `c`, keeping the symbols on `t`. -/
def crtFor (c t : Fin T) (p : Pr P T Q A U) : Pr P T Q A U := scanP c t p

/-- Iteration contracts of a loop body off the registers `c` and `t`: for `j < N`, from any file
agreeing with `Ψ j` off `c` and `t`, `p` ends agreeing with `Ψ (j + 1)` off `c` and `t`, keeps
`c` and `t`, within `b` steps. -/
def crtIter (p : Pr P T Q A U) (c t : Fin T) (Ψ : ℕ → Regs T A) (b N : ℕ) : Prop :=
  ∀ j < N, ∀ R : Regs T A, (∀ k, k ≠ c → k ≠ t → R k = Ψ j k) →
    crtRuns body p R (fun k => if k = c ∨ k = t then R k else Ψ (j + 1) k) b

/-- The register file during a `crtFor` loop: `c` holds `rest`, `t` holds `acc`, every other
register agrees with `Ψ`. -/
def crtForRegs (c t : Fin T) (Ψ : Regs T A) (rest acc : List (Fin (A + 4))) : Regs T A :=
  fun k => if k = c then rest else if k = t then acc else Ψ k

theorem crtFor_loop {c t : Fin T} (hct : c ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A}
    {b N : ℕ} (hp : crtIter (body := body) p c t Ψ b N) :
    ∀ (rest : List (Fin (A + 4))) (j : ℕ) (acc : List (Fin (A + 4))) (v : HS T Q A U)
      (S : Stacks T A), j + rest.length = N → S.R = crtForRegs c t (Ψ j) rest acc →
      (∀ y, S.L y = []) → v.flag = rest.head?.isSome →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ rest.length * (b + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush c t)) (.seq p (.act (peekR c)))))
          (mk v S) m (mk v' { S with R := crtForRegs c t (Ψ N) [] (rest.reverse ++ acc) })
  | [], j, acc, v, S, hj, hS, _, hf => by
      simp only [List.length_nil, Nat.add_zero] at hj
      subst hj
      refine ⟨v, 1, rfl, by simp, ?_⟩
      have : ({ S with R := crtForRegs c t (Ψ j) [] ([].reverse ++ acc) } : Stacks T A) = S := by
        cases S; simp only at hS; subst hS; simp
      rw [this]
      exact .loop_false (by simpa using hf)
  | x :: rest, j, acc, v, S, hj, hS, hL, hf => by
      have hrun : (popPush c t : Act T Q A U).run (mk v S) = mk { v with sym := some x }
          { S with R := crtForRegs c t (Ψ j) rest (x :: acc) } := by
        have hc : S.R c = x :: rest := by rw [hS]; simp [crtForRegs]
        have ht : S.R t = acc := by rw [hS]; simp [crtForRegs, hct.symm]
        simp only [popPush, Action.run, mk_var, mk_stk, get_rt, hc, List.head?_cons,
          Option.getD_some, update_rt, store_mk, List.tail_cons]
        congr 2
        funext k
        by_cases hk : k = t
        · subst hk; simp [crtForRegs, hct.symm, ht]
        · by_cases hk' : k = c
          · subst hk'; simp [crtForRegs, hk]
          · simp [crtForRegs, hk, hk', hS]
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := hp j (by simp at hj; omega)
        (crtForRegs c t (Ψ j) rest (x :: acc))
        (fun k hkc hkt => by simp [crtForRegs, hkc, hkt]) { v with sym := some x }
        { S with R := crtForRegs c t (Ψ j) rest (x :: acc) } rfl hL
      have hR₁ : (fun k => if k = c ∨ k = t then crtForRegs c t (Ψ j) rest (x :: acc) k
          else Ψ (j + 1) k) = crtForRegs c t (Ψ (j + 1)) rest (x :: acc) := by
        funext k
        by_cases hk : k = c
        · subst hk; simp [crtForRegs]
        · by_cases hk' : k = t
          · subst hk'; simp [crtForRegs, hct.symm]
          · simp [crtForRegs, hk, hk']
      rw [hR₁] at he₁
      have he₂ := Exec.act (body := body) (peekR c)
        (mk v₁ { S with R := crtForRegs c t (Ψ (j + 1)) rest (x :: acc) })
      rw [peekR_run] at he₂
      obtain ⟨v', m', hu', hm', he'⟩ := crtFor_loop hct hp rest (j + 1) (x :: acc)
        { v₁ with flag := (crtForRegs c t (Ψ (j + 1)) rest (x :: acc) c).head?.isSome }
        { S with R := crtForRegs c t (Ψ (j + 1)) rest (x :: acc) }
        (by simp at hj; omega) rfl hL (by simp [crtForRegs])
      refine ⟨v', 1 + (m₁ + 1) + m' + 1, hu'.trans hu₁, ?_, ?_⟩
      · simp only [List.length_cons]; nlinarith
      · have hfx : v.flag = true := by simp [hf]
        refine Exec.cast (Exec.loop_true hfx (Exec.seq
          (hrun ▸ Exec.act (body := body) (popPush c t) (mk v S)) (Exec.seq he₁ he₂)) he') rfl ?_
        simp

/-- `crtFor c t p` with `c` holding `l` (`|l| = N`) and `t` empty, the other registers starting
at `Ψ 0`: they end at `Ψ N`, with `c` and `t` restored. -/
theorem crtFor_runs {c t : Fin T} (hct : c ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A}
    {b N : ℕ} (hp : crtIter (body := body) p c t Ψ b N) (l : List (Fin (A + 4)))
    (hl : l.length = N) :
    crtRuns body (crtFor c t p) (crtForRegs c t (Ψ 0) l []) (crtForRegs c t (Ψ N) l [])
      (N * (b + 3) + 2 * N + 4) := by
  intro v S hS hL
  have he₀ := Exec.act (body := body) (peekR c) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := crtFor_loop hct hp l 0 [] { v with flag := (S.R c).head?.isSome }
    S (by omega) hS hL (by rw [hS]; simp [crtForRegs])
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t c hct.symm id v₁
    { S with R := crtForRegs c t (Ψ N) [] (l.reverse ++ []) }
  refine ⟨v₂, 1 + (m₁ + (2 * l.length + 2)), hu₂.trans hu₁, ?_, ?_⟩
  · rw [hl] at hm₁ ⊢; nlinarith
  · refine Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.cast he₂ ?_ ?_))) rfl rfl
    · simp [crtForRegs, hct.symm]
    · congr 2
      funext k
      by_cases hk : k = c
      · subst hk; simp [crtForRegs, movedR, hct, Ne.symm hct]
      · by_cases hk' : k = t
        · subst hk'; simp [crtForRegs, movedR, hct.symm]
        · simp [crtForRegs, movedR, hk, hk']

/-! ### Moves and unary primitives as contracts -/

/-- Move register `i` onto register `j` (reversing it). -/
abbrev crtMv (i j : Fin T) : Pr P T Q A U := moveR i j id

theorem crtMv_runs {i j : Fin T} (hij : i ≠ j) (R : Regs T A) :
    crtRuns body (crtMv i j) R
      (Function.update (Function.update R i []) j ((R i).reverse ++ R j))
      (2 * (R i).length + 2) := by
  refine crtRuns_of_exec fun v S hS => ?_
  obtain ⟨v', hu, he⟩ := moveR_exec body i j hij id v S
  subst hS
  exact ⟨v', _, hu, le_rfl, Exec.cast he rfl (by simp [movedR])⟩

theorem crtClear_runs (a : Fin T) (R : Regs T A) :
    crtRuns body (uclear a) R (Function.update R a []) (2 * (R a).length + 2) := by
  refine crtRuns_of_exec fun v S hS => ?_
  obtain ⟨v', hu, he⟩ := uclear_exec body a v S
  subst hS
  exact ⟨v', _, hu, le_rfl, he⟩

theorem crtUcopy_runs {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (R : Regs T A)
    (ht : R t = []) :
    crtRuns body (ucopy a b t) R
      (Function.update R b (List.replicate (R a).length tick ++ R b)) (4 * (R a).length + 4) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := ucopy_exec body hab hat hbt v S ht
  exact ⟨v', _, hu, le_rfl, he⟩

theorem crtUmul_runs (c : ℕ) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (R : Regs T A) (ht : R t = []) :
    crtRuns body (umul c a b t) R
      (Function.update R b (List.replicate (c * (R a).length) tick ++ R b))
      (4 * (R a).length + 4) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := umul_exec body c hab hat hbt v S ht
  exact ⟨v', _, hu, le_rfl, he⟩

theorem crtUsub_runs {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (R : Regs T A)
    (ht : R t = []) :
    crtRuns body (usub a b t) R (Function.update R b ((R b).drop (R a).length))
      (4 * (R a).length + 4) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := usub_exec body hab hat hbt v S ht
  exact ⟨v', _, hu, le_rfl, he⟩

theorem crtUpow2_runs {a b t₁ t₂ : Fin T} (hreg : [a, b, t₁, t₂].Nodup) (R : Regs T A)
    (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    crtRuns body (upow2 a b t₁ t₂) R
      (Function.update R b ((R b).flatMap (List.replicate (2 ^ (R a).length))))
      (4 * (2 ^ (R a).length * (R b).length) + 9 * (R a).length + 4) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  exact upow2_exec body hreg v S ht₁ ht₂

theorem crtBcopy_runs {a c t₁ t₂ : Fin T} (hreg : [a, c, t₁, t₂].Nodup) (R : Regs T A)
    (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    crtRuns body (bcopy a c t₁ t₂) R (Function.update R c (R a ++ R c)) (6 * (R a).length + 6) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := bcopy_exec body hreg v S ht₁ ht₂
  exact ⟨v', _, hu, le_rfl, he⟩

theorem crtZeroBits_runs {len z t : Fin T} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    (R : Regs T A) (ht : R t = []) :
    crtRuns body (zeroBits len z t) R (Function.update R z (binSyms (R len).length 0 ++ R z))
      (4 * (R len).length + 4) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := zeroBits_exec body hlz hlt hzt v S ht
  exact ⟨v', _, hu, le_rfl, he⟩

/-- Push the symbol `x` onto register `j`. -/
def crtPush (j : Fin T) (x : Fin (A + 4)) : Pr P T Q A U := .act (.push (.rt j) (fun _ => x) .done)

theorem crtPush_runs (j : Fin T) (x : Fin (A + 4)) (R : Regs T A) :
    crtRuns body (crtPush j x) R (Function.update R j (x :: R j)) 1 := by
  refine crtRuns_act _ fun v S hS => ⟨v, rfl, ?_⟩
  subst hS
  simp [Action.run, update_rt]

/-- Pop register `j`, discarding the symbol. -/
def crtPop (j : Fin T) : Pr P T Q A U := .act (.pop (.rt j) (fun v _ => v) .done)

theorem crtPop_runs (j : Fin T) (R : Regs T A) :
    crtRuns body (crtPop j) R (Function.update R j (R j).tail) 1 := by
  refine crtRuns_act _ fun v S hS => ⟨v, rfl, ?_⟩
  subst hS
  simp [Action.run, update_rt]

/-! ### Counted moves -/

/-- Pop `src` and push the symbol onto `dst`, then continue with `k`. -/
def crtPopPush (src dst : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o }) (.push (.rt dst) (fun v => v.sym.getD blank) k)

/-- The effect of `crtPopPush src dst` on a register file. -/
def crtPPFx (src dst : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update R src (R src).tail) dst
    (((R src).head?.getD blank) :: R dst)

lemma crtRegFx_popPush {src dst : Fin T} (hsd : src ≠ dst) :
    RegFx (crtPopPush (T := T) (Q := Q) (A := A) (U := U) src dst) (crtPPFx src dst) := by
  intro x k v S _
  refine ⟨{ v with sym := (S.R src).head? }, rfl, ?_⟩
  simp only [crtPopPush, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, crtPPFx]
  congr 3
  funext y
  by_cases hy : y = dst
  · subst hy; simp [Function.update_of_ne hsd.symm]
  · simp [hy]

lemma crtFrame_ppFx {a src dst : Fin T} (has : a ≠ src) (had : a ≠ dst) :
    Frame a (crtPPFx (T := T) (A := A) src dst) := by
  intro x R l
  simp only [crtPPFx]
  rw [Function.update_of_ne has.symm, Function.update_of_ne (Ne.symm had)]
  rw [Function.update_comm has, Function.update_comm had]

lemma crtFoldl_ppFx {src dst : Fin T} (hsd : src ≠ dst) :
    ∀ (c : List (Fin (A + 4))) (R : Regs T A), c.length ≤ (R src).length →
      c.foldl (fun R x => crtPPFx src dst x R) R =
        Function.update (Function.update R src ((R src).drop c.length)) dst
          (((R src).take c.length).reverse ++ R dst)
  | [], R, _ => by simp
  | x :: rest, R, hc => by
      simp only [List.foldl_cons, List.length_cons] at hc ⊢
      obtain ⟨y, ys, hy⟩ : ∃ y ys, R src = y :: ys := by
        cases h : R src with
        | nil => rw [h] at hc; simp at hc
        | cons y ys => exact ⟨y, ys, rfl⟩
      rw [crtFoldl_ppFx hsd rest]
      · simp only [crtPPFx, hy, List.tail_cons, List.head?_cons, Option.getD_some]
        funext k
        by_cases hk : k = dst
        · subst hk
          simp [Function.update_of_ne hsd.symm, hsd, List.take_succ_cons]
        · by_cases hk' : k = src
          · subst hk'; simp [hk]
          · simp [hk, hk']
      · simp [crtPPFx, hy, Function.update_of_ne hsd]; simp [hy] at hc; omega

/-- Move `|c|` symbols from `src` to `dst` (reversing them), counted by `c` through `t`. -/
def crtCMv (c t src dst : Fin T) : Pr P T Q A U := scanR c t (crtPopPush src dst)

theorem crtCMv_runs {c t src dst : Fin T} (hreg : [c, t, src, dst].Nodup) (R : Regs T A)
    (ht : R t = []) (hlen : (R c).length ≤ (R src).length) :
    crtRuns body (crtCMv c t src dst) R
      (Function.update (Function.update R src ((R src).drop (R c).length)) dst
        (((R src).take (R c).length).reverse ++ R dst)) (4 * (R c).length + 4) := by
  regs_ne hreg
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := scanR_exec' body ‹c ≠ t› (crtRegFx_popPush ‹src ≠ dst›)
    (crtFrame_ppFx ‹c ≠ src› ‹c ≠ dst›) (crtFrame_ppFx ‹t ≠ src› ‹t ≠ dst›) v S ht
  exact ⟨v', _, hu, le_rfl, Exec.cast he rfl (by rw [crtFoldl_ppFx ‹src ≠ dst› _ _ hlen])⟩

/-- Drop `|c|` symbols of `src` (`= usub`). -/
abbrev crtDrop (c t src : Fin T) : Pr P T Q A U := usub c src t

/-! ### Copies -/

/-- Push `sym` onto `d₁` and onto `d₂`, then continue with `k`. -/
def crtPush2 (d₁ d₂ : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .push (.rt d₁) (fun v => v.sym.getD blank) (.push (.rt d₂) (fun v => v.sym.getD blank) k)

/-- The effect of `crtPush2 d₁ d₂` with the symbol `x`. -/
def crtP2Fx (d₁ d₂ : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun x R => Function.update (Function.update R d₁ (x :: R d₁)) d₂ (x :: R d₂)

lemma crtRegFx_push2 {d₁ d₂ : Fin T} (hd : d₁ ≠ d₂) :
    RegFx (crtPush2 (T := T) (Q := Q) (A := A) (U := U) d₁ d₂) (crtP2Fx d₁ d₂) := by
  intro x k v S hx
  refine ⟨v, rfl, ?_⟩
  simp only [crtPush2, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, crtP2Fx, hx,
    Option.getD_some]
  congr 3
  funext y
  by_cases hy : y = d₂
  · subst hy; simp [Function.update_of_ne hd.symm]
  · simp [hy]

lemma crtFrame_p2Fx {a d₁ d₂ : Fin T} (h₁ : a ≠ d₁) (h₂ : a ≠ d₂) :
    Frame a (crtP2Fx (T := T) (A := A) d₁ d₂) := by
  intro x R l
  simp only [crtP2Fx]
  rw [Function.update_of_ne h₁.symm, Function.update_of_ne h₂.symm,
    Function.update_comm h₁, Function.update_comm h₂]

lemma crtFoldl_p2Fx {d₁ d₂ : Fin T} (hd : d₁ ≠ d₂) :
    ∀ (l : List (Fin (A + 4))) (R : Regs T A), l.foldl (fun R x => crtP2Fx d₁ d₂ x R) R =
      Function.update (Function.update R d₁ (l.reverse ++ R d₁)) d₂ (l.reverse ++ R d₂)
  | [], R => by simp
  | x :: rest, R => by
      simp only [List.foldl_cons]
      rw [crtFoldl_p2Fx hd rest]
      funext k
      by_cases hk : k = d₂
      · subst hk; simp [crtP2Fx, Function.update_of_ne hd.symm]
      · by_cases hk' : k = d₁
        · subst hk'; simp [crtP2Fx, hk]
        · simp [crtP2Fx, hk, hk']

/-- Pop `u` until empty, pushing each symbol onto `d₁` and `d₂`. -/
theorem crtDrain2_runs {u d₁ d₂ : Fin T} (h₁ : u ≠ d₁) (h₂ : u ≠ d₂) (hd : d₁ ≠ d₂)
    (R : Regs T A) :
    crtRuns body (drainR u (crtPush2 d₁ d₂)) R
      (Function.update (Function.update (Function.update R d₁ ((R u).reverse ++ R d₁)) d₂
        ((R u).reverse ++ R d₂)) u []) (2 * (R u).length + 2) := by
  refine crtRuns_of_exec fun v S hS => ?_
  obtain ⟨v', hu', he⟩ := drainR_exec body u (crtRegFx_push2 hd) (crtFrame_p2Fx h₁ h₂) v S
  rw [crtFoldl_p2Fx hd, hS] at he
  exact ⟨v', _, hu', le_rfl, he⟩

/-- Copy the top `|c|` symbols of `src` onto `dst` (in order), keeping `src`: move them onto the
empty `u` (counted by `c` through `t`), then pop `u` pushing each symbol onto `src` and `dst`. -/
def crtCpy (c t src dst u : Fin T) : Pr P T Q A U :=
  .seq (crtCMv c t src u) (drainR u (crtPush2 src dst))

theorem crtCpy_runs {c t src dst u : Fin T} (hreg : [c, t, src, dst, u].Nodup)
    (R : Regs T A) (ht : R t = []) (hu : R u = []) (hlen : (R c).length ≤ (R src).length) :
    crtRuns body (crtCpy c t src dst u) R
      (Function.update R dst ((R src).take (R c).length ++ R dst))
      (6 * (R c).length + 6) := by
  have hreg' := hreg
  regs_ne hreg'
  have h₁ := crtCMv_runs (body := body) (src := src) (dst := u) (by regs_nodup) R ht hlen
  have h₂ := crtDrain2_runs (body := body) (Ne.symm ‹src ≠ u›) (Ne.symm ‹dst ≠ u›) ‹src ≠ dst›
    (Function.update (Function.update R src ((R src).drop (R c).length)) u
      (((R src).take (R c).length).reverse ++ R u))
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ h₂) ?_) ?_
  · funext k
    by_cases k1 : k = u
    · rw [k1]; simp [hu, Ne.symm ‹dst ≠ u›]
    · by_cases k2 : k = dst
      · rw [k2]; simp [hu, ‹src ≠ dst›, Ne.symm ‹src ≠ dst›, ‹dst ≠ u›]
      · by_cases k3 : k = src
        · rw [k3]; simp [hu, ‹src ≠ u›, ‹src ≠ dst›, List.take_append_drop]
        · simp [k1, k2, k3]
  · simp only [Function.update_self, hu, List.append_nil, List.length_reverse, List.length_take]
    omega

/-! ### Moving while the top symbol is fixed -/

lemma crt_replicate_cons {α : Type*} (n : ℕ) (x : α) (l : List α) :
    List.replicate n x ++ x :: l = x :: (List.replicate n x ++ l) := by
  rw [show List.replicate n x ++ x :: l = (List.replicate n x ++ [x]) ++ l by simp,
    ← List.replicate_succ', List.replicate_succ, List.cons_append]

/-- Record in `flag` whether the top symbol of `i` is `x`. -/
def crtPeekIs (i : Fin T) (x : Fin (A + 4)) : Act T Q A U :=
  .peek (.rt i) (fun v o => { v with flag := decide (o = some x) }) .done

/-- Move symbols from `src` onto `dst` while the top symbol of `src` is `x`. -/
def crtMvWhile (src dst : Fin T) (x : Fin (A + 4)) : Pr P T Q A U :=
  .seq (.act (crtPeekIs src x))
    (.loop (·.flag) (.act (crtPopPush src dst (crtPeekIs src x))))

theorem crtMvWhile_loop {src dst : Fin T} (hsd : src ≠ dst) (x : Fin (A + 4))
    (rest : List (Fin (A + 4))) (hrest : rest.head? ≠ some x) :
    ∀ (n : ℕ) (v : HS T Q A U) (S : Stacks T A), S.R src = List.replicate n x ++ rest →
      v.flag = decide ((S.R src).head? = some x) →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (crtPopPush src dst (crtPeekIs src x)))) (mk v S)
          (2 * n + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R src rest) dst
              (List.replicate n x ++ S.R dst) }) := by
  intro n
  induction n with
  | zero =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          R := Function.update (Function.update S.R src rest) dst
            (List.replicate 0 x ++ S.R dst) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = dst
          · subst hk; simp
          · by_cases hk' : k = src
            · subst hk'; simp [hk, hS]
            · simp [hk, hk']
      rw [this]
      exact .loop_false (by simp [hf, hS, hrest])
  | succ n ih =>
      intro v S hS hf
      set S₁ : Stacks T A := { S with
        R := Function.update (Function.update S.R src (List.replicate n x ++ rest)) dst
          (x :: S.R dst) } with hS₁
      set fl := decide ((List.replicate n x ++ rest).head? = some x) with hfl
      have hrun : (crtPopPush src dst (crtPeekIs src x) : Act T Q A U).run (mk v S) =
          mk { v with sym := some x, flag := fl } S₁ := by
        simp [crtPopPush, crtPeekIs, Action.run, hS, update_rt, S₁, List.replicate_succ,
          Function.update_of_ne hsd, Function.update_of_ne hsd.symm, hfl]
      obtain ⟨v', hu, he⟩ := ih { v with sym := some x, flag := fl } S₁
        (by simp [S₁, Function.update_of_ne hsd]) (by simp [S₁, Function.update_of_ne hsd, hfl])
      refine ⟨v', hu, Exec.cast (Exec.loop_true (by simp [hf, hS, List.replicate_succ])
        (hrun ▸ Exec.act (body := body) _ (mk v S)) he) (by ring) ?_⟩
      congr 2
      funext k
      by_cases hk : k = dst
      · subst hk; simp [S₁, Function.update_of_ne hsd.symm, crt_replicate_cons, List.replicate_succ]
      · by_cases hk' : k = src
        · subst hk'; simp [S₁, hk]
        · simp [S₁, hk, hk']

/-- `crtMvWhile src dst x` on `src = replicate n x ++ rest` (`rest` not starting with `x`):
`dst` gains `replicate n x`. -/
theorem crtMvWhile_runs {src dst : Fin T} (hsd : src ≠ dst) (x : Fin (A + 4)) (n : ℕ)
    (rest : List (Fin (A + 4))) (hrest : rest.head? ≠ some x) (R : Regs T A)
    (hR : R src = List.replicate n x ++ rest) :
    crtRuns body (crtMvWhile src dst x) R
      (Function.update (Function.update R src rest) dst (List.replicate n x ++ R dst))
      (2 * n + 2) := by
  refine crtRuns_of_exec fun v S hS => ?_
  subst hS
  obtain ⟨v', hu, he⟩ := crtMvWhile_loop (body := body) hsd x rest hrest n
    { v with flag := decide ((S.R src).head? = some x) } S hR rfl
  exact ⟨v', 1 + (2 * n + 1), hu, by omega,
    Exec.seq (Exec.act (body := body) (crtPeekIs src x) (mk v S)) he⟩

end IntegerMultBounds.MathlibTM2.Fast
