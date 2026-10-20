module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# Runs between register files

`LayRuns body p R₀ R₁ c`: from every store with empty left stacks and register file `R₀`, the
program `p` reaches the same store with register file `R₁` within `c` steps. `layScan_exec` runs
a scan loop; the `lr_` lemmas are the run contracts of the unary host utilities, unary products
(`synMulR`) and unary division (`synDivModR`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

/-! ### Runs between register files -/

section Runs

variable {T Q A : ℕ} {U F : Type} (body : F → Pr F T Q A U)

/-- The program `p` takes every store with empty left stacks and register file `R₀` to the same
store with register file `R₁`, the user component unchanged, within `c` steps. -/
def LayRuns (p : Pr F T Q A U) (R₀ R₁ : Fin T → List (Fin (A + 4))) (c : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), (∀ y, S.L y = []) → S.R = R₀ →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧
      Exec body p (mk v S) m (mk v' { S with R := R₁ })

variable {body}

theorem LayRuns.seq {p q : Pr F T Q A U} {R₀ R₁ R₂ : Fin T → List (Fin (A + 4))} {c₁ c₂ : ℕ}
    (h₁ : LayRuns body p R₀ R₁ c₁) (h₂ : LayRuns body q R₁ R₂ c₂) :
    LayRuns body (.seq p q) R₀ R₂ (c₁ + c₂) := by
  intro v S hL hS
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := h₁ v S hL hS
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := h₂ v₁ { S with R := R₁ } hL rfl
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

theorem LayRuns.mono {p : Pr F T Q A U} {R₀ R₁ : Fin T → List (Fin (A + 4))} {c c' : ℕ}
    (h : LayRuns body p R₀ R₁ c) (hc : c ≤ c') : LayRuns body p R₀ R₁ c' := by
  intro v S hL hS
  obtain ⟨v', m, hu, hm, he⟩ := h v S hL hS
  exact ⟨v', m, hu, hm.trans hc, he⟩

/-- **The scan loop.** `scanP a t p` with the counter `a` holding `cs`: if iteration `j` of `p`
takes the registers `Φ j` to `Φ (j + 1)` (the counter holding `cs.drop (j + 1)`, the spare
`(cs.take (j + 1)).reverse`) within `b j` steps, the loop takes `Φ 0` to `Φ |cs|` and restores the
counter. -/
theorem layScan_exec {a t : Fin T} (hat : a ≠ t) {p : Pr F T Q A U}
    (Φ : ℕ → Fin T → List (Fin (A + 4))) (cs : List (Fin (A + 4))) (b : ℕ → ℕ)
    (hstep : ∀ j < cs.length, LayRuns body p
      (Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t
        (cs.take (j + 1)).reverse) (b j)) :
    LayRuns body (scanP a t p)
      (Function.update (Function.update (Φ 0) a cs) t [])
      (Function.update (Function.update (Φ cs.length) a cs) t [])
      (∑ j ∈ Finset.range cs.length, (b j + 3) + 2 * cs.length + 4) := by
  set St : ℕ → Fin T → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update (Φ j) a (cs.drop j)) t (cs.take j).reverse with hSt
  have key : ∀ k j, j + k = cs.length → ∀ (v : HS T Q A U) (S : Stacks T A),
      (∀ y, S.L y = []) → S.R = St j → v.flag = (S.R a).head?.isSome →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
        m ≤ ∑ i ∈ Finset.Ico j (j + k), (b i + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk v' { S with R := St cs.length }) := by
    intro k
    induction k with
    | zero =>
        intro j hj v S _ hS hf
        have hj' : j = cs.length := by omega
        subst hj'
        refine ⟨v, 1, rfl, by simp, ?_⟩
        have hS' : ({ S with R := St cs.length } : Stacks T A) = S := by
          cases S; simp_all
        rw [hS']
        refine .loop_false ?_
        rw [mk_var, hf, hS]
        simp [hSt, Function.update_of_ne hat]
    | succ k ih =>
        intro j hj v S hL hS hf
        have hjl : j < cs.length := by omega
        obtain ⟨x, hx⟩ : ∃ x, cs.drop j = x :: cs.drop (j + 1) := by
          refine ⟨cs[j], ?_⟩
          rw [List.drop_eq_getElem_cons hjl]
        have hSa : S.R a = x :: cs.drop (j + 1) := by
          rw [hS]; simp [hSt, Function.update_of_ne hat, hx]
        have hrun : (popPush a t : Act T Q A U).run (mk v S) = mk { v with sym := some x }
            { S with
              R := Function.update (Function.update S.R a (cs.drop (j + 1))) t (x :: S.R t) } := by
          simp [popPush, Action.run, hSa, update_rt, Function.update_of_ne hat.symm]
        have hR1 : Function.update (Function.update S.R a (cs.drop (j + 1))) t (x :: S.R t) =
            Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t
              (cs.take (j + 1)).reverse := by
          have htake : cs.take (j + 1) = cs.take j ++ [x] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hjl]
            have : cs[j] = x := by
              have := List.drop_eq_getElem_cons hjl
              rw [hx] at this
              exact (List.cons.inj this).1.symm
            rw [this]; rfl
          have hSt' : S.R t = (cs.take j).reverse := by rw [hS]; simp [hSt]
          rw [hSt', htake, List.reverse_append]
          funext y
          by_cases hyt : y = t
          · subst hyt; simp
          · by_cases hya : y = a
            · subst hya; simp [hyt]
            · simp [hyt, hya, hS, hSt]
        obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := hstep j hjl { v with sym := some x }
          { S with
            R := Function.update (Function.update S.R a (cs.drop (j + 1))) t (x :: S.R t) } hL hR1
        have hR2 : Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t
            (cs.take (j + 1)).reverse = St (j + 1) := rfl
        rw [hR2] at he₁
        have he₂ := Exec.act (body := body) (peekR a) (mk v₁ { S with R := St (j + 1) })
        rw [peekR_run] at he₂
        obtain ⟨v', m', hu', hm', he'⟩ := ih (j + 1) (by omega)
          { v₁ with flag := (St (j + 1) a).head?.isSome } { S with R := St (j + 1) } hL rfl rfl
        refine ⟨v', 1 + (m₁ + 1) + m' + 1, by rw [hu', ← hu₁], ?_, ?_⟩
        · have e : ∑ i ∈ Finset.Ico j (j + (k + 1)), (b i + 3) =
              (b j + 3) + ∑ i ∈ Finset.Ico (j + 1) (j + 1 + k), (b i + 3) := by
            rw [show j + (k + 1) = j + 1 + k by omega, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
          rw [e]
          omega
        · have hft : v.flag = true := by rw [hf, hSa]; rfl
          have := Exec.loop_true (body := body) (f := (·.flag)) hft
            (Exec.seq (hrun ▸ Exec.act (body := body) (popPush a t) (mk v S))
              (Exec.seq he₁ he₂)) he'
          exact this
  intro v S hL hS
  have hS0 : S.R = St 0 := by rw [hS]; simp [hSt]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := key cs.length 0 (by omega)
    { v with flag := (S.R a).head?.isSome } S hL hS0 rfl
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t a hat.symm id v₁ { S with R := St cs.length }
  refine ⟨v₂, 1 + (m₁ + (2 * (St cs.length t).length + 2)), by rw [hu₂, hu₁], ?_, ?_⟩
  · have ht : St cs.length t = cs.reverse := by simp [hSt]
    rw [ht, List.length_reverse]
    simp only [Nat.zero_add, Finset.range_eq_Ico] at hm₁ ⊢
    omega
  · have hfin : movedR (St cs.length) t a id (St cs.length t) =
        Function.update (Function.update (Φ cs.length) a cs) t [] := by
      funext y
      by_cases hyt : y = t
      · subst hyt; simp [movedR, hSt, hat.symm]
      · by_cases hya : y = a
        · subst hya; simp [movedR, hSt, hat]
        · simp [movedR, hSt, hyt, hya]
    rw [← hfin]
    exact Exec.seq (peekR_run a v S ▸ Exec.act (body := body) (peekR a) (mk v S))
      (Exec.seq he₁ he₂)

end Runs

/-! ### Run contracts of the host utilities -/

section Kit


variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

theorem lr_weaken {p : Pr P T Q A U} {R₀ R₁ R₁' : Fin T → List (Fin (A + 4))} {c c' : ℕ}
    (h : LayRuns body p R₀ R₁ c) (hR : R₁ = R₁') (hc : c ≤ c') : LayRuns body p R₀ R₁' c' :=
  hR ▸ h.mono hc

theorem lr_congr_left {p : Pr P T Q A U} {R₀ R₀' R₁ : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (hR : R₀' = R₀) : LayRuns body p R₀' R₁ c := hR ▸ h

theorem lr_of_exec {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ → ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body p (mk v S) c (mk v' { S with R := R₁ })) : LayRuns body p R₀ R₁ c := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := h v S hS
  exact ⟨v', c, hu, le_rfl, he⟩

theorem lr_of_exec_le {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ → ∃ (v' : HS T Q A U) (m : ℕ),
      v'.user = v.user ∧ m ≤ c ∧ Exec body p (mk v S) m (mk v' { S with R := R₁ })) :
    LayRuns body p R₀ R₁ c := by
  intro v S _ hS
  exact h v S hS

/-- The empty program. -/
def synSkip : Pr P T Q A U := .act .done

theorem lr_skip (R : Fin T → List (Fin (A + 4))) : LayRuns body synSkip R R 1 :=
  lr_of_exec body fun v S hS => ⟨v, rfl, by
    have := Exec.act (body := body) (Action.done : Act T Q A U) (mk v S)
    rw [run_done] at this
    have hS' : ({ S with R := R } : Stacks T A) = S := by cases S; simp_all
    rw [hS']
    exact this⟩

variable {R : Fin T → List (Fin (A + 4))}

theorem lr_ucopy {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : R t = []) :
    LayRuns body (ucopy a b t) R
      (Function.update R b (List.replicate (R a).length tick ++ R b)) (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact ucopy_exec body hab hat hbt v S ht

theorem lr_umul (c : ℕ) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : R t = []) :
    LayRuns body (umul c a b t) R
      (Function.update R b (List.replicate (c * (R a).length) tick ++ R b))
      (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact umul_exec body c hab hat hbt v S ht

theorem lr_umulSym (c : ℕ) (y : Fin (A + 4)) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ht : R t = []) :
    LayRuns body (umulSym c y a b t) R
      (Function.update R b (List.replicate (c * (R a).length) y ++ R b))
      (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact umulSym_exec body c y hab hat hbt v S ht

theorem lr_usub {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : R t = []) :
    LayRuns body (usub a b t) R (Function.update R b ((R b).drop (R a).length))
      (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact usub_exec body hab hat hbt v S ht

theorem lr_uclear (a : Fin T) :
    LayRuns body (uclear a) R (Function.update R a []) (2 * (R a).length + 2) :=
  lr_of_exec body fun v S hS => by subst hS; exact uclear_exec body a v S

theorem lr_udiv {c : ℕ} (hc : 1 ≤ c) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : R t = []) :
    LayRuns body (udiv c a b t) R
      (Function.update R b (List.replicate ((R a).length / c) tick ++ R b))
      (4 * (R a).length + 4) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact udiv_exec body hc hab hat hbt v S ht

theorem lr_moveR (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) :
    LayRuns body (moveR i j f) R (movedR R i j f (R i)) (2 * (R i).length + 2) :=
  lr_of_exec body fun v S hS => by subst hS; exact moveR_exec body i j hij f v S

theorem lr_moveR_id {i j : Fin T} (hij : i ≠ j) :
    LayRuns body (moveR i j id) R
      (Function.update (Function.update R i []) j ((R i).reverse ++ R j))
      (2 * (R i).length + 2) := by
  have := lr_moveR body (R := R) i j hij id
  simpa [movedR] using this

theorem lr_upow2 {a b t₁ t₂ : Fin T} (hreg : [a, b, t₁, t₂].Nodup) (ht₁ : R t₁ = [])
    (ht₂ : R t₂ = []) :
    LayRuns body (upow2 a b t₁ t₂) R
      (Function.update R b ((R b).flatMap (List.replicate (2 ^ (R a).length))))
      (4 * (2 ^ (R a).length * (R b).length) + 9 * (R a).length + 4) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact upow2_exec body hreg v S ht₁ ht₂

theorem lr_expProg (G F : ℕ) {uR jR eR t₁ t₂ t₃ : Fin T}
    (hreg : [uR, jR, eR, t₁, t₂, t₃].Nodup) (he : R eR = []) (ht₁ : R t₁ = [])
    (ht₂ : R t₂ = []) (ht₃ : R t₃ = []) :
    LayRuns body (expProg G F uR jR eR t₁ t₂ t₃) R
      (Function.update R eR (List.replicate (expSeq G F (R uR).length (R jR).length) tick))
      (4 * (R uR).length + 2 * (R jR).length + 8 +
        ∑ i ∈ Finset.range (R jR).length, (8 * expSeq G F (R uR).length i + 12)) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact expProg_exec body G F hreg v S he ht₁ ht₂ ht₃

theorem lr_zeroBits {len z t : Fin T} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    (ht : R t = []) :
    LayRuns body (zeroBits len z t) R
      (Function.update R z (binSyms (R len).length 0 ++ R z)) (4 * (R len).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact zeroBits_exec body hlz hlt hzt v S ht


/-! ### Single actions and branches -/

/-- Push the symbol `s` onto register `x`. -/
def synPush (x : Fin T) (s : Fin (A + 4)) : Pr P T Q A U :=
  .act (.push (.rt x) (fun _ => s) .done)

/-- Drop the top symbol of register `x`. -/
def synPop (x : Fin T) : Pr P T Q A U := .act (.pop (.rt x) (fun v _ => v) .done)

theorem lr_push (x : Fin T) (s : Fin (A + 4)) :
    LayRuns body (synPush x s) R (Function.update R x (s :: R x)) 1 :=
  lr_of_exec body fun v S hS => by
    subst hS
    refine ⟨v, rfl, ?_⟩
    have := Exec.act (body := body) (Action.push (.rt x) (fun _ => s) .done : Act T Q A U)
      (mk v S)
    simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at this
    exact this

theorem lr_pop (x : Fin T) :
    LayRuns body (synPop x) R (Function.update R x (R x).tail) 1 :=
  lr_of_exec body fun v S hS => by
    subst hS
    refine ⟨v, rfl, ?_⟩
    have := Exec.act (body := body) (Action.pop (.rt x) (fun v _ => v) .done : Act T Q A U)
      (mk v S)
    simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at this
    exact this

/-- `p` if register `x` is nonempty, else `q`. -/
def synIfNE (x : Fin T) (p q : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR x)) (.cond (·.flag) p q)

theorem lr_ifNE_pos {x : Fin T} {p q : Pr P T Q A U} {R' : Fin T → List (Fin (A + 4))} {c : ℕ}
    (hx : R x ≠ []) (hp : LayRuns body p R R' c) : LayRuns body (synIfNE x p q) R R' (c + 2) := by
  intro v S hL hS
  have he₁ := Exec.act (body := body) (peekR x : Act T Q A U) (mk v S)
  rw [peekR_run] at he₁
  obtain ⟨v', m, hu, hm, he⟩ := hp { v with flag := (S.R x).head?.isSome } S hL hS
  refine ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₁ (Exec.cond_true ?_ he)⟩
  rw [hS]
  cases h : R x with
  | nil => exact absurd h hx
  | cons y l => simp

theorem lr_ifNE_neg {x : Fin T} {p q : Pr P T Q A U} {R' : Fin T → List (Fin (A + 4))} {c : ℕ}
    (hx : R x = []) (hq : LayRuns body q R R' c) : LayRuns body (synIfNE x p q) R R' (c + 2) := by
  intro v S hL hS
  have he₁ := Exec.act (body := body) (peekR x : Act T Q A U) (mk v S)
  rw [peekR_run] at he₁
  obtain ⟨v', m, hu, hm, he⟩ := hq { v with flag := (S.R x).head?.isSome } S hL hS
  refine ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₁ (Exec.cond_false ?_ he)⟩
  rw [hS, hx]
  rfl

/-! ### Compound programs -/

/-- `c` gains `|a| |b|` ticks: `|b|` ticks per symbol of `a` (kept on `t₁`), through `t₂`. -/
def synMulR (a b c t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (ucopy b c t₂)

/-- The step bound of `synMulR`. -/
def synMulRCost (x y : ℕ) : ℕ := x * (4 * y + 7) + 2 * x + 4

theorem lr_synMulR {a b c t₁ t₂ : Fin T} (hreg : [a, b, c, t₁, t₂].Nodup) (ht₁ : R t₁ = [])
    (ht₂ : R t₂ = []) :
    LayRuns body (synMulR a b c t₁ t₂) R
      (Function.update R c (List.replicate ((R a).length * (R b).length) tick ++ R c))
      (synMulRCost (R a).length (R b).length) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hab, hac, hat₁, hat₂⟩, ⟨hbc, hbt₁, hbt₂⟩, ⟨hct₁, hct₂⟩, ht₁t₂⟩ := hreg
  set cs := R a with hcs
  set y := (R b).length with hy
  let Φ : ℕ → Fin T → List (Fin (A + 4)) := fun j =>
    Function.update R c (List.replicate (j * y) tick ++ R c)
  have hstep : ∀ j < cs.length, LayRuns body (ucopy b c t₂)
      (Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t₁ (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t₁
        (cs.take (j + 1)).reverse) (4 * y + 4) := by
    intro j _
    refine lr_weaken body (lr_ucopy body hbc hbt₂ hct₂ (by
      simp [Φ, Function.update_of_ne hat₂.symm, Function.update_of_ne ht₁t₂.symm,
        Function.update_of_ne hct₂.symm, ht₂])) ?_ (by
      simp [Φ, Function.update_of_ne hab.symm, Function.update_of_ne hbt₁, Function.update_of_ne hbc,
        hy])
    have e : List.replicate y tick ++ (List.replicate (j * y) tick ++ R c) =
        List.replicate ((j + 1) * y) tick ++ R c := by
      rw [← List.append_assoc, List.replicate_append_replicate]
      congr 2
      ring
    funext k
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  have h := layScan_exec hat₁ Φ cs (fun _ => 4 * y + 4) hstep
  refine lr_weaken body (lr_congr_left body h ?_) ?_ ?_
  · funext k
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · funext k
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · simp [synMulRCost]

/-- `x` becomes `k |x|` ticks, through the empty `t` and `t'`. -/
def synMulIn (k : ℕ) (x t t' : Fin T) : Pr P T Q A U :=
  .seq (moveR x t id) (.seq (umul k t x t') (uclear t))

theorem lr_synMulIn (k : ℕ) {x t t' : Fin T} (hreg : [x, t, t'].Nodup) (ht : R t = [])
    (ht' : R t' = []) :
    LayRuns body (synMulIn k x t t') R
      (Function.update R x (List.replicate (k * (R x).length) tick)) (8 * (R x).length + 8) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hxt, hxt'⟩, htt'⟩ := hreg
  refine lr_weaken body ((lr_moveR_id body (R := R) hxt).seq
    ((lr_umul body k hxt.symm htt' hxt' (by simp [Function.update_of_ne htt'.symm,
      Function.update_of_ne hxt'.symm, ht'])).seq (lr_uclear body t))) ?_ ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp [Function.update_of_ne hxt.symm, ht]
    omega

/-- One symbol of the dividend: `r` gains a tick; if it reaches `|k|` ticks, `r` is emptied and
`q` gains a tick. -/
def synDivStep (k q r t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (synPush r tick) (.seq (ucopy k t₂ t₃) (.seq (usub r t₂ t₃)
    (synIfNE t₂ (uclear t₂) (.seq (uclear r) (synPush q tick)))))

/-- `q` gains `|x| / |k|` ticks and the empty `r` ends with `|x| mod |k|` ticks; `x` is kept on
`t₁` and restored. -/
def synDivModR (x k q r t₁ t₂ t₃ : Fin T) : Pr P T Q A U := scanP x t₁ (synDivStep k q r t₂ t₃)

/-- The step bound of `synDivModR`. -/
def synDivModCost (x K : ℕ) : ℕ := x * (10 * K + 17) + 2 * x + 4

/-- **One step of the unary division**: the remainder `r` holding `j mod K` ticks and the
quotient `q` holding `j / K` ticks above `base` advance to `j + 1`. -/
theorem lr_synDivStep {k q r t₂ t₃ : Fin T} (hreg : [k, q, r, t₂, t₃].Nodup)
    {R₀ : Fin T → List (Fin (A + 4))} {K j : ℕ} (hk : (R₀ k).length = K) (hK : 1 ≤ K)
    {base : List (Fin (A + 4))} (hr : R₀ r = List.replicate (j % K) tick)
    (hq : R₀ q = List.replicate (j / K) tick ++ base) (ht₂ : R₀ t₂ = []) (ht₃ : R₀ t₃ = []) :
    LayRuns body (synDivStep k q r t₂ t₃) R₀
      (Function.update (Function.update R₀ r (List.replicate ((j + 1) % K) tick)) q
        (List.replicate ((j + 1) / K) tick ++ base)) (10 * K + 14) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hkq, hkr, hkt₂, hkt₃⟩, ⟨hqr, hqt₂, hqt₃⟩, ⟨hrt₂, hrt₃⟩, ht₂t₃⟩ := hreg
  have hjK : j % K < K := Nat.mod_lt _ (by omega)
  have h1 := lr_push body (R := R₀) r tick
  set R₁ := Function.update R₀ r (tick :: R₀ r) with hR₁
  have h2 := lr_ucopy body (R := R₁) hkt₂ hkt₃ ht₂t₃ (by
    rw [hR₁, Function.update_of_ne hrt₃.symm, ht₃])
  have ek₁ : (R₁ k).length = K := by rw [hR₁, Function.update_of_ne hkr, hk]
  rw [ek₁] at h2
  set R₂ := Function.update R₁ t₂ (List.replicate K tick ++ R₁ t₂) with hR₂
  have h3 := lr_usub body (R := R₂) hrt₂ hrt₃ ht₂t₃ (by
    rw [hR₂, Function.update_of_ne ht₂t₃.symm, hR₁, Function.update_of_ne hrt₃.symm, ht₃])
  have er₂ : R₂ r = List.replicate (j % K + 1) tick := by
    rw [hR₂, Function.update_of_ne hrt₂, hR₁, Function.update_self, hr, ← List.replicate_succ]
  have et₂' : R₂ t₂ = List.replicate K tick := by
    rw [hR₂, Function.update_self, hR₁, Function.update_of_ne hrt₂.symm, ht₂, List.append_nil]
  rw [er₂, et₂', List.length_replicate, List.drop_replicate] at h3
  set R₃ := Function.update R₂ t₂ (List.replicate (K - (j % K + 1)) tick) with hR₃
  have eq₃ : R₃ q = R₀ q := by
    rw [hR₃, Function.update_of_ne hqt₂, hR₂, Function.update_of_ne hqt₂, hR₁,
      Function.update_of_ne hqr]
  by_cases hlt : j % K + 1 < K
  · have hne : R₃ t₂ ≠ [] := by
      rw [hR₃, Function.update_self]; simp; omega
    have h4 := lr_ifNE_pos body (q := .seq (uclear r) (synPush q tick)) hne
      (lr_uclear body (R := R₃) t₂)
    have hm : (j + 1) % K = j % K + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < K by omega)]
      exact Nat.mod_eq_of_lt hlt
    have hd : (j + 1) / K = j / K := by
      have e1 := Nat.div_add_mod j K
      have e2 := Nat.div_add_mod (j + 1) K
      rw [hm] at e2
      have : K * ((j + 1) / K) = K * (j / K) := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    refine lr_weaken body (h1.seq (h2.seq (h3.seq h4))) ?_ ?_
    · funext z
      rw [hm, hd, ← hq]
      by_cases hz2 : z = t₂
      · subst hz2
        rw [Function.update_self, Function.update_of_ne hqt₂.symm, Function.update_of_ne hrt₂.symm,
          ht₂]
      rw [Function.update_of_ne hz2]
      by_cases hzq : z = q
      · subst hzq; rw [eq₃, Function.update_self]
      rw [Function.update_of_ne hzq]
      by_cases hzr : z = r
      · subst hzr
        rw [hR₃, Function.update_of_ne hrt₂, er₂, Function.update_self]
      rw [Function.update_of_ne hzr, hR₃, Function.update_of_ne hz2, hR₂,
        Function.update_of_ne hz2, hR₁, Function.update_of_ne hzr]
    · simp only [hR₃, Function.update_self, List.length_replicate]
      omega
  · have hKe : j % K + 1 = K := by omega
    have he : R₃ t₂ = [] := by
      rw [hR₃, Function.update_self]; simp; omega
    have h4 := lr_ifNE_neg body (p := uclear t₂) he
      ((lr_uclear body (R := R₃) r).seq (lr_push body q tick))
    have hm : (j + 1) % K = 0 := by
      have := Nat.div_add_mod j K
      rw [show j + 1 = K * (j / K + 1) by rw [Nat.mul_add, Nat.mul_one]; omega]
      exact Nat.mul_mod_right _ _
    have hd : (j + 1) / K = j / K + 1 := by
      rw [show j + 1 = K * (j / K + 1) by
        have := Nat.div_add_mod j K
        rw [Nat.mul_add, Nat.mul_one]; omega]
      exact Nat.mul_div_cancel_left _ (by omega)
    refine lr_weaken body (h1.seq (h2.seq (h3.seq h4))) ?_ ?_
    · funext z
      rw [hm, hd]
      by_cases hzq : z = q
      · subst hzq
        rw [Function.update_self, Function.update_self, Function.update_of_ne hqr, eq₃, hq,
          List.replicate_succ, List.cons_append]
      rw [Function.update_of_ne hzq, Function.update_of_ne hzq]
      by_cases hzr : z = r
      · subst hzr; rw [Function.update_self, Function.update_self, List.replicate_zero]
      rw [Function.update_of_ne hzr, Function.update_of_ne hzr]
      by_cases hz2 : z = t₂
      · subst hz2
        rw [hR₃, Function.update_self, show K - (j % K + 1) = 0 by omega, List.replicate_zero, ht₂]
      rw [hR₃, Function.update_of_ne hz2, hR₂, Function.update_of_ne hz2, hR₁,
        Function.update_of_ne hzr]
    · have er₃ : (R₃ r).length = j % K + 1 := by
        rw [hR₃, Function.update_of_ne hrt₂, er₂, List.length_replicate]
      rw [er₃]
      omega

theorem lr_synDivModR {x k q r t₁ t₂ t₃ : Fin T} (hreg : [x, k, q, r, t₁, t₂, t₃].Nodup)
    (hk : 1 ≤ (R k).length) (hr : R r = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = [])
    (ht₃ : R t₃ = []) :
    LayRuns body (synDivModR x k q r t₁ t₂ t₃) R
      (Function.update (Function.update R r (List.replicate ((R x).length % (R k).length) tick)) q
        (List.replicate ((R x).length / (R k).length) tick ++ R q))
      (synDivModCost (R x).length (R k).length) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hxk, hxq, hxr, hxt₁, hxt₂, hxt₃⟩, ⟨hkq, hkr, hkt₁, hkt₂, hkt₃⟩, ⟨hqr, hqt₁, hqt₂, hqt₃⟩,
    ⟨hrt₁, hrt₂, hrt₃⟩, ⟨ht₁t₂, ht₁t₃⟩, ht₂t₃⟩ := hreg'
  set cs := R x with hcs
  set K := (R k).length with hK
  let Φ : ℕ → Fin T → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update R r (List.replicate (j % K) tick)) q
      (List.replicate (j / K) tick ++ R q)
  have hstep : ∀ j < cs.length, LayRuns body (synDivStep k q r t₂ t₃)
      (Function.update (Function.update (Φ j) x (cs.drop (j + 1))) t₁ (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) x (cs.drop (j + 1))) t₁
        (cs.take (j + 1)).reverse) (10 * K + 14) := by
    intro j _
    have h := lr_synDivStep body (k := k) (q := q) (r := r) (t₂ := t₂) (t₃ := t₃)
      (by simp [hkq, hkr, hkt₂, hkt₃, hqr, hqt₂, hqt₃, hrt₂, hrt₃, ht₂t₃]) (R₀ := Function.update (Function.update (Φ j) x (cs.drop (j + 1))) t₁
        (cs.take (j + 1)).reverse) (K := K) (j := j) (base := R q)
      (by simp [Φ, Function.update_of_ne hkt₁, Function.update_of_ne hxk.symm,
        Function.update_of_ne hkq, Function.update_of_ne hkr, hK]) (by omega)
      (by simp [Φ, Function.update_of_ne hrt₁, Function.update_of_ne hxr.symm,
        Function.update_of_ne hqr.symm])
      (by simp [Φ, Function.update_of_ne hqt₁, Function.update_of_ne hxq.symm])
      (by simp [Φ, Function.update_of_ne ht₁t₂.symm, Function.update_of_ne hxt₂.symm,
        Function.update_of_ne hqt₂.symm, Function.update_of_ne hrt₂.symm, ht₂])
      (by simp [Φ, Function.update_of_ne ht₁t₃.symm, Function.update_of_ne hxt₃.symm,
        Function.update_of_ne hqt₃.symm, Function.update_of_ne hrt₃.symm, ht₃])
    refine lr_weaken body h ?_ le_rfl
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  have h := layScan_exec hxt₁ Φ cs (fun _ => 10 * K + 14) hstep
  refine lr_weaken body (lr_congr_left body h ?_) ?_ ?_
  · funext z
    simp only [Φ, Function.update_apply, Nat.zero_mod, Nat.zero_div]
    split_ifs <;> simp_all
  · funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul,
      synDivModCost]
    ring_nf
    omega

end Kit

end IntegerMultBounds.MathlibTM2.Fast
