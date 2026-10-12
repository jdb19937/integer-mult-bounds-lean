module

public import IntegerMultBounds.Schoenhage.RecordBridge

/-! Refitting the lines of an array: cut a bit array into lines of width `u`
and bring every line to width `v`, truncating or padding with zero bits
(`Rules.fit`). On the padded box of the tensor interface this drops the
padding of every line before a one-dimensional map (`v < u`) and restores it
afterwards (`v > u`); zero bits are the zero component. `fitLoop` refits
every word of a tape (`runs_fitLoop`); `refit` does the whole array on five
word tapes (`runs_refit`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct

variable {a : ℕ}

/-- Refit every word of tape `3` to the width on tape `2`, onto tape `4`. -/
noncomputable def fitLoop : Cmd a 5 :=
  .loop 3 (.seq (op1 Rules.take false 2 3 4 (by decide) (by decide) (by decide)) (rewind 2))

theorem runs_fitLoop {v W : ℕ} :
    ∀ (ls : List (List Bool)) (σ : Fin 5 → WTape) (Ls Os : List (List Bool)),
      (∀ x ∈ ls, x.length ≤ W) → σ 2 = reg (ones v) → σ 3 = ⟨Ls, ls⟩ → σ 4 = ⟨Os, []⟩ →
      Runs (a := a) fitLoop σ (· = Function.update (Function.update σ 3 ⟨ls.reverse ++ Ls, []⟩) 4
        ⟨(ls.map (Rules.fit v)).reverse ++ Os, []⟩) (ls.length * (3 * v + W + 20))
  | [], σ, Ls, Os, _, _, h3, h4 => by
    refine (Runs.loop_done (by simp [h3]) rfl).mono (fun σ' e => ?_) (by simp)
    rw [← e]; funext y
    by_cases a1 : y = 3 <;> by_cases a2 : y = 4 <;> simp_all
  | l :: ls, σ, Ls, Os, hW, h2, h3, h4 => by
    have hl := hW l (by simp)
    have s1 : Runs (a := a) (.seq (op1 Rules.take false 2 3 4 (by decide) (by decide) (by decide)) (rewind 2)) σ
        (· = Function.update (Function.update σ 3 ⟨l :: Ls, ls⟩) 4 ⟨[Rules.fit v l] ++ Os, []⟩) (2 * v + l.length + 12) := by
      apply Runs.of_wp
      simp only [WP, wp_op1, wp_rewind]
      have c2 : (σ 2).cur = ones v := by rw [h2]; rfl
      have c3 : (σ 3).cur = l := by rw [h3]; rfl
      rw [c2, c3, Rules.output_take, parse_syms, length_ones]
      refine ⟨⟨by simp [h2, reg], by simp [h3], by simp [h4], rfl, by simp⟩, ?_, ?_⟩
      · funext y
        by_cases a1 : y = 2
        · subst a1; simp [h2, reg, WTape.next, WTape.cur]
        · by_cases a3 : y = 3
          · subst a3; simp [h3, WTape.next, WTape.cur]
          · by_cases a4 : y = 4
            · subst a4; simp [h4, WTape.put]
            · simp [a1, a3, a4]
      · have t1 := time_le Rules.take (ones v) (fun _ => l) l.length (fun _ => le_rfl)
        simp only [length_ones] at t1
        simp [h2, reg, WTape.next, WTape.cur, clen] at t1 ⊢
        omega
    have ih := runs_fitLoop (v := v) (W := W) ls (Function.update (Function.update σ 3 ⟨l :: Ls, ls⟩) 4 ⟨[Rules.fit v l] ++ Os, []⟩)
      (l :: Ls) (Rules.fit v l :: Os) (fun y hy => hW y (by simp [hy])) (by simp [h2]) (by simp) (by simp)
    refine (Runs.loop_step (by simp [h3]) (s1.mono (fun σ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun σ' e => ?_) ?_
    · rw [e]; funext y
      by_cases a1 : y = 3 <;> by_cases a2 : y = 4 <;> simp_all
    · simp only [List.length_cons]; nlinarith

theorem clen_map_fit (v : ℕ) (L : List (List Bool)) : clen (L.map (Rules.fit v)) = L.length * (v + 1) := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih]; ring

/-- Tape `0`: the array; `1`: the old line width; `2`: the new line width; `3`, `4`: scratch. -/
noncomputable def refit : Cmd a 5 :=
  .seq (chunkw 0 1 3 (by decide) (by decide) (by decide)) <| .seq (rewind 3) <| .seq fitLoop <|
  .seq (clear 3) <| .seq (rewind 4) <| .seq (clear 0) <| .seq (emit [[]] 0) <|
  .seq (joinLoop 4 0 (by decide)) <| .seq (rewind 0) (clear 4)

/-- `refit` with pieces of length at most `W`. -/
theorem runs_refitW {u v W : ℕ} (hu : 1 ≤ u) (A : List Bool) (hle : ∀ x ∈ cut u A, x.length ≤ W)
    (σ : Fin 5 → WTape)
    (h0 : σ 0 = reg A) (h1 : σ 1 = reg (ones u)) (h2 : σ 2 = reg (ones v)) (h3 : σ 3 = emp) (h4 : σ 4 = emp) :
    Runs (a := a) refit σ (· = Function.update σ 0 (reg ((cut u A).map (Rules.fit v)).flatten))
      ((cut u A).length * (4 * v + 2 * W + 40) + 20 * A.length + 10 * v * (cut u A).length + 60) := by
  set C := cut u A
  set F := C.map (Rules.fit v)
  have hFl : ∀ x ∈ F, x.length ≤ v := fun x hx => by
    simp only [F, List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; simp
  have hcl : clen C = A.length + C.length := by rw [clen_eq, cut_flatten]
  have hF : clen F = C.length * (v + 1) := clen_map_fit v C
  have hFf : F.flatten.length = C.length * v := by
    have := clen_eq F; rw [hF] at this; simp [F] at this ⊢; nlinarith
  have s1 := runs_chunkw (a := a) (s := 0) (r := 1) (d := 3) (by decide) (by decide) (by decide) σ
    (L := []) (R := []) (x := A) (by rw [h0]; rfl) h1 hu (by rw [h3]; rfl)
  set σ₁ := Function.update (Function.update σ 0 ⟨[A], []⟩) 3 ⟨C.reverse ++ (σ 3).left, []⟩
  have s2 := runs_rewind (a := a) 3 σ₁
  set σ₂ := Function.update σ₁ 3 ⟨[], (σ₁ 3).left.reverse ++ (σ₁ 3).right⟩
  have s3 := runs_fitLoop (a := a) (v := v) (W := W) C σ₂ [] [] hle
    (by simp [σ₂, σ₁, h2]) (by simp [σ₂, σ₁, h3, emp]) (by simp [σ₂, σ₁, h4, emp])
  set σ₃ := Function.update (Function.update σ₂ 3 ⟨C.reverse ++ [], []⟩) 4 ⟨F.reverse ++ [], []⟩
  have s4 := runs_clear (a := a) 3 σ₃
  set σ₄ := Function.update σ₃ 3 ⟨[], []⟩
  have s5 := runs_rewind (a := a) 4 σ₄
  set σ₅ := Function.update σ₄ 4 ⟨[], (σ₄ 4).left.reverse ++ (σ₄ 4).right⟩
  have s6 := runs_clear (a := a) 0 σ₅
  set σ₆ := Function.update σ₅ 0 ⟨[], []⟩
  have s7 := runs_emit (a := a) [[]] 0 σ₆ (by simp [σ₆])
  set σ₇ := Function.update σ₆ 0 ⟨[[]].reverse ++ (σ₆ 0).left, []⟩
  have s8 := runs_joinLoop (a := a) (show (4 : Fin 5) ≠ 0 by decide) (W := v) F σ₇ [] [] hFl
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃]) (by simp [σ₇, σ₆])
  set σ₈ := Function.update (Function.update σ₇ 4 ⟨F.reverse ++ [], []⟩) 0 ⟨[[] ++ F.flatten], []⟩
  have s9 := runs_rewind (a := a) 0 σ₈
  set σ₉ := Function.update σ₈ 0 ⟨[], (σ₈ 0).left.reverse ++ (σ₈ 0).right⟩
  have s10 := runs_clear (a := a) 4 σ₉
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 s10))))))))).mono (fun σ' e => ?_) ?_
  · rw [e]; funext y
    fin_cases y <;> simp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, h3, h4, emp, reg]
  · simp only [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, Function.update_self, Function.update_of_ne,
      ne_eq, Fin.reduceEq, not_false_eq_true, h3, emp, WTape.words, List.append_nil, List.nil_append,
      List.reverse_nil, clen_reverse, clen_cons, clen_nil, List.reverse_cons, hcl, hF,
      List.length_nil]
    have hFn : F.length = C.length := by simp [F]
    rw [hFn]
    nlinarith


theorem runs_refit {u v : ℕ} (hu : 1 ≤ u) (A : List Bool) (σ : Fin 5 → WTape)
    (h0 : σ 0 = reg A) (h1 : σ 1 = reg (ones u)) (h2 : σ 2 = reg (ones v)) (h3 : σ 3 = emp) (h4 : σ 4 = emp) :
    Runs (a := a) refit σ (· = Function.update σ 0 (reg ((cut u A).map (Rules.fit v)).flatten))
      ((cut u A).length * (4 * v + 2 * A.length + 40) + 20 * A.length + 10 * v * (cut u A).length + 60) :=
  runs_refitW hu A (fun x hx => by
    have := List.Sublist.length_le (List.sublist_flatten_of_mem hx)
    rwa [cut_flatten] at this) σ h0 h1 h2 h3 h4

/-! ### Lines -/

theorem fit_take (v : ℕ) (x : List Bool) (h : v ≤ x.length) : Rules.fit v x = x.take v := by
  induction v generalizing x with
  | zero => rfl
  | succ v ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      simp only [Rules.fit, List.headD_cons, List.tail_cons, List.take_succ_cons]
      rw [ih x (by simp at h; omega)]

theorem fit_pad (v : ℕ) (x : List Bool) (h : x.length ≤ v) :
    Rules.fit v x = x ++ List.replicate (v - x.length) false := by
  induction v generalizing x with
  | zero => simp at h; subst h; rfl
  | succ v ih =>
    rcases x with _ | ⟨b, x⟩
    · simp only [Rules.fit, List.headD_nil, List.tail_nil, List.nil_append, List.length_nil, Nat.sub_zero]
      rw [ih [] (by simp)]; simp [List.replicate_succ]
    · simp only [Rules.fit, List.headD_cons, List.tail_cons, List.cons_append, List.length_cons]
      rw [ih x (by simp at h; omega)]
      congr 2; simp

/-- The lines of an array of `u`-bit lines, each brought to `v` bits. -/
theorem refit_lines {u : ℕ} (hu : 1 ≤ u) (v : ℕ) (L : List (List Bool)) (hL : ∀ l ∈ L, l.length = u) :
    ((cut u L.flatten).map (Rules.fit v)).flatten = (L.map (Rules.fit v)).flatten := by
  rw [cut_flatten_words hu L hL]

/-! ### On raw arrays -/

/-- Five tapes at cell zero. -/
def bank5 (f0 f1 f2 f3 f4 : ℤ → Fin 4) : Tapes 5 0 := ⟨fun _ => 0, ![f0, f1, f2, f3, f4]⟩

/-- The compiled word program. -/
noncomputable def refitProg : Program 5 (compile (a := 0) (by decide) refit).1 0 :=
  (compile (a := 0) (by decide) refit).2

/-- Seal, refit, unseal. -/
noncomputable def refitRaw :=
  Machine.seq (sealAt (a := 0) (0 : Fin 5)) <| Machine.seq (sealAt (a := 0) (1 : Fin 5)) <|
  Machine.seq (sealAt (a := 0) (2 : Fin 5)) <| Machine.seq refitProg <|
  Machine.seq (unsealAt (a := 0) (0 : Fin 5)) <| Machine.seq (unsealAt (a := 0) (1 : Fin 5))
    (unsealAt (a := 0) (2 : Fin 5))

/-- The refitted array. -/
def refitted (u v : ℕ) (A : List Bool) : List Bool := ((cut u A).map (Rules.fit v)).flatten

set_option maxHeartbeats 8000000 in
theorem refitRaw_hoare {u v : ℕ} (hu : 1 ≤ u) (A : List Bool) :
    HoareTime refitRaw
      (· = bank5 (wordAt A) (wordAt (ones u)) (wordAt (ones v)) (fun _ => blank) (fun _ => blank))
      (· = bank5 (wordAt (refitted u v A)) (wordAt (ones u)) (wordAt (ones v)) (fun _ => blank) (fun _ => blank))
      ((cut u A).length * (4 * v + 2 * A.length + 40) + 20 * A.length + 10 * v * (cut u A).length +
        6 * ((cut u A).length * v) + 4 * A.length + 6 * u + 6 * v + 120) := by
  set v0 := bank5 (wordAt A) (wordAt (ones u)) (wordAt (ones v)) (fun _ => blank) (fun _ => blank)
  have h1 := sealAt_hoare (a := 0) (0 : Fin 5) A v0 rfl (by simp [v0, bank5])
  set v1 : Tapes 5 0 := ⟨v0.head, Function.update v0.tape 0 (⟨[], [A]⟩ : WTape).tape⟩
  have h2 := sealAt_hoare (a := 0) (1 : Fin 5) (ones u) v1 rfl (by simp [v1, v0, bank5])
  set v2 : Tapes 5 0 := ⟨v1.head, Function.update v1.tape 1 (⟨[], [ones u]⟩ : WTape).tape⟩
  have h3 := sealAt_hoare (a := 0) (2 : Fin 5) (ones v) v2 rfl (by simp [v2, v1, v0, bank5])
  set σ0 : Fin 5 → WTape := ![reg A, reg (ones u), reg (ones v), emp, emp]
  have e3 : (⟨v2.head, Function.update v2.tape 2 (⟨[], [ones v]⟩ : WTape).tape⟩ : Tapes 5 0) = enc σ0 := by
    simp only [enc]
    congr 1 <;> funext i <;> fin_cases i <;> simp [v2, v1, v0, bank5, σ0, reg, WTape.pos, emp_tape0]
  rw [e3] at h3
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_refit (a := 0) (v := v) hu A σ0 rfl rfl rfl rfl rfl
  subst hq
  have h4 := (compile_correct (by decide) hx).consequence (fun v e => e) (fun v e => e) hk
  set σ1 := Function.update σ0 0 (reg (refitted u v A))
  have h5 := unsealAt_hoare (a := 0) (0 : Fin 5) (refitted u v A) (enc σ1) (by simp [enc, σ1, σ0, reg, WTape.pos])
    (by simp [enc, σ1, σ0, reg])
  set u5 : Tapes 5 0 := ⟨(enc σ1).head, Function.update (enc σ1).tape 0 (wordAt (refitted u v A))⟩
  have h6 := unsealAt_hoare (a := 0) (1 : Fin 5) (ones u) u5 (by simp [u5, enc, σ1, σ0, reg, WTape.pos])
    (by simp [u5, enc, σ1, σ0, reg])
  set u6 : Tapes 5 0 := ⟨u5.head, Function.update u5.tape 1 (wordAt (ones u))⟩
  have h7 := unsealAt_hoare (a := 0) (2 : Fin 5) (ones v) u6 (by simp [u6, u5, enc, σ1, σ0, reg, WTape.pos])
    (by simp [u6, u5, enc, σ1, σ0, reg])
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).consequence (fun v e => e)
    (fun v e => e.trans ?_) ?_
  · simp only [u6, u5, bank5, enc, σ1, σ0]
    congr 1
    · funext i; fin_cases i <;> simp [reg, emp, WTape.pos]
    · funext i; fin_cases i <;> simp [reg, emp_tape0]
  · have hr : (refitted u v A).length = (cut u A).length * v := by
      have := clen_eq ((cut u A).map (Rules.fit v))
      rw [clen_map_fit] at this; simp only [refitted, List.length_map] at this ⊢; nlinarith
    simp only [length_ones, hr]
    omega

end IntegerMultBounds.Schoenhage
