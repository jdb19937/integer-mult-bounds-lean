module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# Unary division by a register value

`udivU a b q c s t`, for `|b| ≥ 1`, pushes `|a| / |b|` ticks onto `q`. The empty `c` first
receives a copy of `b` (`ucopy b c t`); then `udivStep q c s` runs once per symbol of `a`
(`scanP a t`): it pops one symbol of `c` onto `s` and, when `c` has become empty, pushes one
tick onto `q` and moves `s` back onto `c`; finally `c` and `s` are emptied. Before iteration
`j` the registers hold `|b| - j % |b|` ticks on `c`, `j % |b|` ticks on `s` and `j / |b|` new
ticks on `q` (`udivRegs`). Iteration `j` costs `3` steps unless it refills `c`, which costs
`2 |b| + 5`; the refills happen `|a| / |b|` times (`sum_udivCost`), so `udivU` runs in at most
`12 (|a| + |b|) + 12` steps (`udivU_exec`). `a` and `b` are restored; `c`, `s`, `t` start and
end empty.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Quotient and remainder of a successor -/

lemma succ_div_mod_of_lt {j nb : ℕ} (h : j % nb + 1 < nb) :
    (j + 1) / nb = j / nb ∧ (j + 1) % nb = j % nb + 1 := by
  have hnb : 0 < nb := by omega
  rw [Nat.div_mod_unique hnb]
  have := Nat.div_add_mod j nb
  exact ⟨by omega, h⟩

lemma succ_div_mod_of_eq {j nb : ℕ} (h : j % nb + 1 = nb) :
    (j + 1) / nb = j / nb + 1 ∧ (j + 1) % nb = 0 := by
  have hnb : 0 < nb := by omega
  rw [Nat.div_mod_unique hnb]
  have h₁ := Nat.div_add_mod j nb
  have h₂ : nb * (j / nb + 1) = nb * (j / nb) + nb := by ring
  exact ⟨by omega, hnb⟩

/-! ### The iteration cost -/

/-- The cost of iteration `j` of `udivU` with `|b| = nb`: `3` steps, plus `2 nb + 2` when the
iteration refills `c`, which is when `(j + 1) / nb` exceeds `j / nb`. -/
def udivCost (nb j : ℕ) : ℕ := 3 + (2 * nb + 2) * ((j + 1) / nb - j / nb)

lemma sum_udivCost (nb : ℕ) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, (udivCost nb i + 3) = 6 * n + (2 * nb + 2) * (n / nb)
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_udivCost nb n, udivCost]
      obtain ⟨d, hd⟩ :=
        Nat.exists_eq_add_of_le (Nat.div_le_div_right (c := nb) (by omega : n ≤ n + 1))
      rw [hd, Nat.add_sub_cancel_left]
      ring

lemma sum_udivCost_le (nb n : ℕ) :
    ∑ i ∈ Finset.range n, (udivCost nb i + 3) ≤ 10 * n := by
  rw [sum_udivCost]
  have h₁ := Nat.mul_div_le n nb
  have h₂ := Nat.div_le_self n nb
  have h₃ : (2 * nb + 2) * (n / nb) = 2 * (nb * (n / nb)) + 2 * (n / nb) := by ring
  omega

/-! ### One iteration -/

/-- One iteration of `udivU`: pop one symbol of `c` onto `s`; if `c` has become empty, push a
tick onto `q` and move `s` back onto `c`. -/
def udivStep (q c s : Fin T) : Pr P T Q A U :=
  .seq (.act (moveStep c s id))
    (.cond (·.flag) (.act .done)
      (.seq (.act (.push (.rt q) (fun _ => tick) .done)) (moveR s c id)))

lemma moveStep_run_cons {c s : Fin T} (hcs : c ≠ s) (v : HS T Q A U) (S : Stacks T A)
    {x : Fin (A + 4)} {rest : List (Fin (A + 4))} (hc : S.R c = x :: rest) :
    (moveStep c s id : Act T Q A U).run (mk v S) =
      mk { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R c rest) s (x :: S.R s) } := by
  simp [moveStep, peekR, Action.run, hc, update_rt, Function.update_of_ne hcs,
    Function.update_of_ne hcs.symm]

/-- `udivStep` when `c` keeps a symbol: `3` steps. -/
theorem udivStep_exec_cons {q c s : Fin T} (hcs : c ≠ s) (v : HS T Q A U) (S : Stacks T A)
    {x y : Fin (A + 4)} {rest : List (Fin (A + 4))} (hc : S.R c = x :: y :: rest) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (udivStep q c s) (mk v S) 3
        (mk v' { S with
          R := Function.update (Function.update S.R c (y :: rest)) s (x :: S.R s) }) := by
  refine ⟨{ v with sym := some x, flag := (y :: rest).head?.isSome }, rfl, ?_⟩
  have he₁ := Exec.cast (Exec.act (body := body) (moveStep c s id) (mk v S)) rfl
    (moveStep_run_cons hcs v S hc)
  have he₂ := Exec.act (body := body) .done
    (mk { v with sym := some x, flag := (y :: rest).head?.isSome }
      { S with R := Function.update (Function.update S.R c (y :: rest)) s (x :: S.R s) })
  rw [run_done] at he₂
  exact Exec.cast (Exec.seq he₁ (Exec.cond_true (by simp) he₂)) (by norm_num) rfl

/-- `udivStep` when `c` empties: a tick onto `q` and `s` moved back onto `c`, in `2 |s| + 7`
steps. -/
theorem udivStep_exec_nil {q c s : Fin T} (hqc : q ≠ c) (hqs : q ≠ s) (hcs : c ≠ s)
    (v : HS T Q A U) (S : Stacks T A) {x : Fin (A + 4)} (hc : S.R c = [x]) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (udivStep q c s) (mk v S) (2 * (S.R s).length + 7)
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R q (tick :: S.R q)) c
            ((S.R s).reverse ++ [x])) s [] }) := by
  have he₁ := Exec.cast (Exec.act (body := body) (moveStep c s id) (mk v S)) rfl
    (moveStep_run_cons hcs v S hc)
  have he₂ := Exec.act (body := body) (.push (.rt q) (fun _ => tick) .done)
    (mk { v with sym := some x, flag := ([] : List (Fin (A + 4))).head?.isSome }
      { S with R := Function.update (Function.update S.R c []) s (x :: S.R s) })
  simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, run_done] at he₂
  obtain ⟨v', hu, he₃⟩ := moveR_exec body s c hcs.symm id
    { v with sym := some x, flag := ([] : List (Fin (A + 4))).head?.isSome }
    { S with
      R := Function.update (Function.update (Function.update S.R c []) s (x :: S.R s)) q
        (tick :: Function.update (Function.update S.R c []) s (x :: S.R s) q) }
  refine ⟨v', by rw [hu], Exec.cast (Exec.seq he₁ (Exec.cond_false (by simp)
    (Exec.seq he₂ he₃))) ?_ ?_⟩
  · simp only [Function.update_of_ne hqs.symm, Function.update_self, List.length_cons]
    omega
  · congr 2
    funext k
    simp only [movedR, Function.update_apply, List.map_id, List.reverse_cons]
    split_ifs <;> simp_all

/-! ### The iteration specification -/

/-- Registers before iteration `j` of `udivU` with `|b| = nb`: `q` holds `j / nb` new ticks,
`c` the `nb - j % nb` ticks left of the current copy of `b`, and `s` the `j % nb` ticks moved
off it. -/
def udivRegs (q c s : Fin T) (nb : ℕ) (R : Regs T A) (j : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update R q (List.replicate (j / nb) tick ++ R q)) c
    (List.replicate (nb - j % nb) tick)) s (List.replicate (j % nb) tick)

theorem udivStep_iterSpec {a q c s t : Fin T} (haq : a ≠ q) (hac : a ≠ c) (has : a ≠ s)
    (hqc : q ≠ c) (hqs : q ≠ s) (hqt : q ≠ t) (hcs : c ≠ s) (hct : c ≠ t) (hst : s ≠ t)
    {nb : ℕ} (hnb : 1 ≤ nb) (R : Regs T A) (N : ℕ) :
    IterSpec body (udivStep q c s) a t (udivRegs q c s nb R) (udivCost nb) N := by
  intro j _ v S hS
  have hq : S.R q = List.replicate (j / nb) tick ++ R q := by
    rw [hS q haq.symm hqt]
    simp [udivRegs, Function.update_of_ne hqs, Function.update_of_ne hqc]
  have hc : S.R c = List.replicate (nb - j % nb) tick := by
    rw [hS c hac.symm hct]
    simp [udivRegs, Function.update_of_ne hcs]
  have hs : S.R s = List.replicate (j % nb) tick := by
    rw [hS s has.symm hst]
    simp [udivRegs]
  have hother : ∀ k, k ≠ a → k ≠ t → k ≠ q → k ≠ c → k ≠ s → S.R k = R k := by
    intro k hka hkt hkq hkc hks
    rw [hS k hka hkt]
    simp [udivRegs, Function.update_of_ne hks, Function.update_of_ne hkc,
      Function.update_of_ne hkq]
  have hr : j % nb < nb := Nat.mod_lt j (by omega)
  obtain ⟨m, hm⟩ : ∃ m, nb - j % nb = m + 1 := ⟨nb - j % nb - 1, by omega⟩
  rw [hm, List.replicate_succ] at hc
  cases m with
  | zero =>
      rw [List.replicate_zero] at hc
      obtain ⟨hdiv, hmod⟩ := succ_div_mod_of_eq (j := j) (nb := nb) (by omega)
      obtain ⟨v', hu, he⟩ := udivStep_exec_nil body hqc hqs hcs v S hc
      refine ⟨v', _, _, hu, ?_, he, ?_, ?_, ?_⟩
      · rw [hs, List.length_replicate, udivCost, hdiv, Nat.add_sub_cancel_left]
        omega
      · simp [Function.update_of_ne hac, Function.update_of_ne has, Function.update_of_ne haq]
      · simp [Function.update_of_ne hct.symm, Function.update_of_ne hst.symm,
          Function.update_of_ne hqt.symm]
      · intro k hka hkt
        by_cases hks : k = s
        · subst hks
          simp [udivRegs, hmod]
        by_cases hkc : k = c
        · subst hkc
          simp only [udivRegs, Function.update_of_ne hcs, Function.update_self]
          rw [hs, List.reverse_replicate, ← List.replicate_succ', hmod, Nat.sub_zero]
          congr 1
          omega
        by_cases hkq : k = q
        · subst hkq
          simp only [udivRegs, Function.update_of_ne hqs, Function.update_of_ne hqc,
            Function.update_self]
          rw [hq, hdiv, List.replicate_succ, List.cons_append]
        · simp only [udivRegs, Function.update_of_ne hks, Function.update_of_ne hkc,
            Function.update_of_ne hkq]
          exact hother k hka hkt hkq hkc hks
  | succ m =>
      rw [List.replicate_succ] at hc
      obtain ⟨hdiv, hmod⟩ := succ_div_mod_of_lt (j := j) (nb := nb) (by omega)
      obtain ⟨v', hu, he⟩ := udivStep_exec_cons body (q := q) hcs v S hc
      refine ⟨v', _, _, hu, ?_, he, ?_, ?_, ?_⟩
      · simp only [udivCost]
        omega
      · simp [Function.update_of_ne hac, Function.update_of_ne has]
      · simp [Function.update_of_ne hct.symm, Function.update_of_ne hst.symm]
      · intro k hka hkt
        by_cases hks : k = s
        · subst hks
          simp only [udivRegs, Function.update_self]
          rw [hs, hmod, List.replicate_succ]
        by_cases hkc : k = c
        · subst hkc
          simp only [udivRegs, Function.update_of_ne hcs, Function.update_self]
          rw [hmod, ← List.replicate_succ]
          congr 1
          omega
        by_cases hkq : k = q
        · subst hkq
          simp only [udivRegs, Function.update_of_ne hqs, Function.update_of_ne hqc,
            Function.update_self]
          rw [hq, hdiv]
        · simp only [udivRegs, Function.update_of_ne hks, Function.update_of_ne hkc,
            Function.update_of_ne hkq]
          exact hother k hka hkt hkq hkc hks

/-! ### The division program -/

/-- `q` gains `|a| / |b|` ticks: copy `b` onto the empty `c` (through the empty `t`), run
`udivStep q c s` once per symbol of `a` (kept on `t`), then empty `c` and `s`. -/
def udivU (a b q c s t : Fin T) : Pr P T Q A U :=
  .seq (ucopy b c t) (.seq (scanP a t (udivStep q c s)) (.seq (uclear c) (uclear s)))

/-- `udivU` for `|b| ≥ 1`: `q` gains `|a| / |b|` ticks in at most `12 (|a| + |b|) + 12`
steps; every other register ends as it started. -/
theorem udivU_exec {a b q c s t : Fin T} (hreg : [a, b, q, c, s, t].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (hb : 1 ≤ (S.R b).length) (hc : S.R c = []) (hs : S.R s = [])
    (ht : S.R t = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 12 * ((S.R a).length + (S.R b).length) + 12 ∧
      Exec body (udivU a b q c s t) (mk v S) m
        (mk v' { S with
          R := Function.update S.R q
            (List.replicate ((S.R a).length / (S.R b).length) tick ++ S.R q) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hab, haq, hac, has, hat⟩, ⟨hbq, hbc, hbs, hbt⟩, ⟨hqc, hqs, hqt⟩, ⟨hcs, hct⟩, hst⟩ :=
    hreg
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hbc hbt hct v S ht
  rw [hc, List.append_nil] at he₁
  have hp := udivStep_iterSpec body haq hac has hqc hqs hqt hcs hct hst hb S.R (S.R a).length
  have hΨ₀ : ∀ k, k ≠ a → k ≠ t →
      Function.update S.R c (List.replicate (S.R b).length tick) k =
        udivRegs q c s (S.R b).length S.R 0 k := by
    intro k _ _
    simp only [udivRegs, Nat.zero_div, Nat.zero_mod, Nat.sub_zero, List.replicate_zero,
      List.nil_append, Function.update_eq_self]
    by_cases hks : k = s
    · subst hks
      simp [hs, Function.update_of_ne hcs.symm]
    · rw [Function.update_of_ne hks]
  obtain ⟨v₂, R', m, hu₂, hm, he₂, ha', ht', hΨ'⟩ := scanP_exec body hat hp 0 v₁
    { S with R := Function.update S.R c (List.replicate (S.R b).length tick) }
    (by simp [Function.update_of_ne hac]) hΨ₀
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body c v₂ { S with R := R' }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body s v₃ { S with R := Function.update R' c [] }
  have hRc : R' c = List.replicate ((S.R b).length - (S.R a).length % (S.R b).length) tick := by
    rw [hΨ' c hac.symm hct]
    simp [udivRegs, Function.update_of_ne hcs, Function.update_of_ne hac]
  have hRs : R' s = List.replicate ((S.R a).length % (S.R b).length) tick := by
    rw [hΨ' s has.symm hst]
    simp [udivRegs, Function.update_of_ne hac]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · simp only [Function.update_of_ne hac, Function.update_of_ne hct.symm, ht, List.length_nil,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hm
    have hsum := sum_udivCost_le (S.R b).length (S.R a).length
    have hmod := Nat.mod_lt (S.R a).length (by omega : 0 < (S.R b).length)
    simp only [hRc, hRs, Function.update_of_ne hcs.symm, List.length_replicate]
    omega
  · congr 2
    funext k
    by_cases hka : k = a
    · subst hka
      simp [Function.update_of_ne has, Function.update_of_ne hac, Function.update_of_ne haq,
        Function.update_of_ne hct.symm, ha', ht]
    by_cases hkt : k = t
    · subst hkt
      simp [Function.update_of_ne hst.symm, Function.update_of_ne hct.symm,
        Function.update_of_ne hqt.symm, ht', ht]
    by_cases hkc : k = c
    · subst hkc
      simp [Function.update_of_ne hcs, Function.update_of_ne hqc.symm, hc]
    by_cases hks : k = s
    · subst hks
      simp [Function.update_of_ne hqs.symm, hs]
    simp only [Function.update_of_ne hks, Function.update_of_ne hkc, hΨ' k hka hkt, udivRegs,
      Nat.zero_add, Function.update_of_ne hac]

end IntegerMultBounds.MathlibTM2.Node
