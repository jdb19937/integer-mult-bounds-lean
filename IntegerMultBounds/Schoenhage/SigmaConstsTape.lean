module

public import IntegerMultBounds.Schoenhage.SigmaTableTape

/-! The constants of the §6 exponent tables, computed on tapes from `ℓ - 1`,
`K`, `D` and the long-axis flags: `b = (ℓ - 1) mod K` and `q = (ℓ - 1) div K`
as tick tapes (by repeated subtraction, `runs_divLoop`), the products `DK`,
`qDK` and `bD` (by repeated addition), the number `L` of long axes, and the
starts `A₀ = qDK + D - 1`, `B₀ = DK - K` and `T₀ = qDK + bD + L - 1` of the
axis rows and the top bits (`runs_consts`). A last loop writes the top bits
`T₀, T₀ - 1, …` of the long axes (`runs_topBits`). -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm SigmaRowsTape TwistDescriptors

namespace SigmaConstsTape

/-! ### The bank -/

/-- The value being divided (a register). -/
abbrev kX : Fin 20 := 0
/-- `ones K`. -/
abbrev kK : Fin 20 := 1
/-- `ones D`. -/
abbrev kD : Fin 20 := 2
/-- The long-axis flags. -/
abbrev kF : Fin 20 := 3
/-- The division's fuel. -/
abbrev kFuel : Fin 20 := 4
/-- `q` ticks. -/
abbrev kQt : Fin 20 := 5
/-- `b` ticks. -/
abbrev kBt : Fin 20 := 6
/-- `D` ticks. -/
abbrev kDt : Fin 20 := 7
/-- `DK`. -/
abbrev kDK : Fin 20 := 8
/-- `qDK`. -/
abbrev kDqK : Fin 20 := 9
/-- `bD`. -/
abbrev kDb : Fin 20 := 10
/-- The number of long axes. -/
abbrev kLc : Fin 20 := 11
/-- `ones 1`. -/
abbrev kOne : Fin 20 := 12
/-- A test result. -/
abbrev kG : Fin 20 := 13
/-- Scratch. -/
abbrev kS : Fin 20 := 14
/-- The junk tape. -/
abbrev kJ : Fin 20 := 15
/-- `A₀`. -/
abbrev kA0 : Fin 20 := 16
/-- `B₀`. -/
abbrev kB0 : Fin 20 := 17
/-- `T₀`. -/
abbrev kT0 : Fin 20 := 18
/-- The top bits. -/
abbrev kTop : Fin 20 := 19

/-! ### Division by repeated subtraction -/

/-- Test whether the value is below `K`. -/
noncomputable def testX : Cmd 0 20 :=
  .seq (op1 geq false kK kX kG (by decide) (by decide) (by decide)) <| .seq (rewind kK) <| .seq (rewind kX)
    (rewind kG)

/-- Subtract `K` from the value and record a tick of the quotient. -/
noncomputable def subK : Cmd 0 20 :=
  .seq (op1 Rules.drop false kX kK kS (by decide) (by decide) (by decide)) <| .seq (rewind kK) <|
  .seq (clear kX) <| .seq (rewind kS) <| .seq (cpy kS kX (by decide)) <| .seq (clear kS) <|
  .seq (rewind kX) (emit [[]] kQt)

/-- One division step: subtract `K` when the value is at least `K`. -/
noncomputable def divStep : Cmd 0 20 :=
  .seq testX <| .seq (.cond kG (rewind kJ) subK) <| .seq (clear kG) (skp kFuel kJ (by decide))

/-- The division loop. -/
noncomputable def divLoop : Cmd 0 20 := .loop kFuel divStep

theorem output_geq_ones (K x : ℕ) :
    output geq (ones K) (fun _ => ones x) = syms [[decide (x < K)]] := by
  rw [output_geq]; simp

set_option maxHeartbeats 8000000 in
theorem runs_testX {K x : ℕ} (σ : Fin 20 → WTape) (hK : σ kK = reg (ones K)) (hX : σ kX = reg (ones x))
    (hG : σ kG = emp) :
    Runs testX σ (· = Function.update σ kG ⟨[], [[decide (x < K)]]⟩) (4 * K + 4 * x + 30) := by
  have t1 : time geq (ones K) (fun _ => ones x) ≤ K + x + 7 :=
    (time_le geq (ones K) (fun _ => ones x) x (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [testX, WP, wp_op1, wp_rewind]
  tsimp [hK, hX, hG, emp, reg, output_geq_ones]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hK, hX, hG, emp, reg]
  · omega

set_option maxHeartbeats 8000000 in
theorem runs_subK {K x : ℕ} (σ : Fin 20 → WTape) (hK : σ kK = reg (ones K)) (hX : σ kX = reg (ones x))
    (hS : σ kS = emp) {LQ : List (List Bool)} (hQ : σ kQt = ⟨LQ, []⟩) :
    Runs subK σ (· = Function.update (Function.update σ kX (reg (ones (x - K)))) kQt ⟨[] :: LQ, []⟩)
      (10 * x + 4 * K + 60) := by
  have t1 : time Rules.drop (ones x) (fun _ => ones K) ≤ x + K + 6 :=
    (time_le Rules.drop (ones x) (fun _ => ones K) K (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [subK, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear, wp_emit]
  tsimp [hK, hX, hS, hQ, emp, reg, Rules.output_drop, Rules.output_copy, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hK, hX, hS, hQ, emp, reg, ones]
  · simp [time_copy, clen, ones, WTape.words] at t1 ⊢; omega

/-- `x` after `n` division steps. -/
def divRes (K : ℕ) (n x : ℕ) : ℕ := x - min n (x / K) * K

set_option maxHeartbeats 16000000 in
/-- `runs_divLoop`: `n` division steps subtract `K` exactly `min n (x / K)` times. -/
theorem runs_divLoop {K : ℕ} (hKpos : 0 < K) : ∀ (n x : ℕ) (σ : Fin 20 → WTape) (Lf LQ : List (List Bool)),
    σ kFuel = ⟨Lf, List.replicate n []⟩ → σ kK = reg (ones K) → σ kX = reg (ones x) → σ kG = emp →
    σ kS = emp → σ kJ = emp → σ kQt = ⟨LQ, []⟩ →
    Runs divLoop σ (· = Function.update (Function.update (Function.update σ kX (reg (ones (divRes K n x))))
        kQt ⟨List.replicate (min n (x / K)) [] ++ LQ, []⟩) kFuel ⟨List.replicate n [] ++ Lf, []⟩)
      (n * (16 * x + 10 * K + 110))
  | 0, x, σ, Lf, LQ, hFuel, hK, hX, hG, hS, hJ, hQ => by
    refine (Runs.loop_done (by simp [hFuel]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hFuel, hX, hQ, divRes]
  | n + 1, x, σ, Lf, LQ, hFuel, hK, hX, hG, hS, hJ, hQ => by
    have s1 := runs_testX σ hK hX hG
    set σ₁ := Function.update σ kG ⟨[], [[decide (x < K)]]⟩ with hσ₁
    by_cases hlt : x < K
    · -- no subtraction
      have hG₁ : σ₁ kG = ⟨[], [[decide (x < K)]]⟩ := by tsimp [hσ₁]
      have hst : StartsOne (σ₁ kG) := by rw [hG₁]; exact (startsOne_reg _).mpr (by simpa using hlt)
      have s2 := Runs.cond_true (c := rewind kJ) (d := subK) (i := kG) hst (runs_rewind (a := 0) kJ σ₁)
      set σ₂ := Function.update σ₁ kJ ⟨[], (σ₁ kJ).left.reverse ++ (σ₁ kJ).right⟩ with hσ₂
      have s3 := runs_clear (a := 0) kG σ₂
      set σ₃ := Function.update σ₂ kG ⟨[], []⟩ with hσ₃
      have s4 := runs_skp (a := 0) (show kFuel ≠ kJ by decide) σ₃ (by tsimp [hσ₃, hσ₂, hσ₁, hFuel, List.replicate_succ])
        (by tsimp [hσ₃, hσ₂, hσ₁, hJ, emp])
      set σ₄ := Function.update σ₃ kFuel (σ₃ kFuel).next with hσ₄
      have ih := runs_divLoop hKpos n x σ₄ ([] :: Lf) LQ (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hFuel, List.replicate_succ])
        (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hK]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hX]) (by tsimp [hσ₄, hσ₃, emp])
        (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hS]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hJ, emp])
        (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hQ])
      have hdiv : x / K = 0 := Nat.div_eq_of_lt hlt
      refine (Runs.loop_step (by simp [hFuel]) ((Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono
        (fun τ h => by rw [h]; exact ih) le_rfl)).mono (fun τ h => ?_) ?_
      · rw [h]; funext i; fin_cases i <;> first | rfl |
          tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hG, hJ, emp, replicate_cons, divRes, hdiv]
      · tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hFuel, hJ, emp, clen, WTape.words, List.replicate_succ]
        nlinarith
    · -- subtract `K`
      have hge : K ≤ x := by omega
      have hG₁ : σ₁ kG = ⟨[], [[decide (x < K)]]⟩ := by tsimp [hσ₁]
      have hst : ¬ StartsOne (σ₁ kG) := by
        rw [hG₁]; intro h; exact hlt (by simpa using (startsOne_reg _).mp h)
      have s2 := Runs.cond_false (c := rewind kJ) (d := subK) (i := kG) hst
        (runs_subK (K := K) (x := x) (LQ := LQ) σ₁ (by tsimp [hσ₁, hK]) (by tsimp [hσ₁, hX]) (by tsimp [hσ₁, hS]) (by tsimp [hσ₁, hQ]))
      set σ₂ := Function.update (Function.update σ₁ kX (reg (ones (x - K)))) kQt ⟨[] :: LQ, []⟩ with hσ₂
      have s3 := runs_clear (a := 0) kG σ₂
      set σ₃ := Function.update σ₂ kG ⟨[], []⟩ with hσ₃
      have s4 := runs_skp (a := 0) (show kFuel ≠ kJ by decide) σ₃ (by tsimp [hσ₃, hσ₂, hσ₁, hFuel, List.replicate_succ])
        (by tsimp [hσ₃, hσ₂, hσ₁, hJ, emp])
      set σ₄ := Function.update σ₃ kFuel (σ₃ kFuel).next with hσ₄
      have ih := runs_divLoop hKpos n (x - K) σ₄ ([] :: Lf) ([] :: LQ) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hFuel, List.replicate_succ])
        (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hK]) (by tsimp [hσ₄, hσ₃, hσ₂]) (by tsimp [hσ₄, hσ₃, emp])
        (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hS]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hJ, emp])
        (by tsimp [hσ₄, hσ₃, hσ₂])
      have hdiv : x / K = (x - K) / K + 1 := by
        rw [Nat.div_eq_sub_div hKpos hge]
      have hmin : min (n + 1) (x / K) = min n ((x - K) / K) + 1 := by rw [hdiv]; omega
      have hres : divRes K (n + 1) x = divRes K n (x - K) := by
        unfold divRes; rw [hmin, Nat.add_mul, one_mul]; omega
      refine (Runs.loop_step (by simp [hFuel]) ((Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono
        (fun τ h => by rw [h]; exact ih) le_rfl)).mono (fun τ h => ?_) ?_
      · rw [h]; funext i; fin_cases i <;> first | rfl |
          tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hG, emp, replicate_cons, hres, hmin]
      · tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hFuel, clen, WTape.words, List.replicate_succ]
        have : n * (16 * (x - K) + 10 * K + 110) ≤ n * (16 * x + 10 * K + 110) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith

theorem divRes_full {K x n : ℕ} (hn : x / K ≤ n) : divRes K n x = x % K := by
  unfold divRes
  rw [Nat.min_eq_right hn]
  have h1 := Nat.div_add_mod x K
  have h2 : x / K * K = K * (x / K) := Nat.mul_comm _ _
  omega

/-! ### Repeated addition -/

/-- Add the constant on `src` to `dst` and step the tick tape. -/
noncomputable def addBody (src dst tk : Fin 20) (h1 : src ≠ dst) (h2 : tk ≠ kJ) : Cmd 0 20 :=
  .seq (op0 Rules.copy true src dst h1) (.seq (rewind src) (skp tk kJ h2))

/-- Add the constant on `src` to `dst` once per tick of `tk`. -/
noncomputable def addLoop (src dst tk : Fin 20) (h1 : src ≠ dst) (h2 : tk ≠ kJ) : Cmd 0 20 :=
  .loop tk (addBody src dst tk h1 h2)

set_option maxHeartbeats 8000000 in
theorem runs_addBody {src dst tk : Fin 20} (h1 : src ≠ dst) (h2 : tk ≠ kJ) (h3 : src ≠ tk) (h4 : dst ≠ tk)
    (h5 : src ≠ kJ) (h6 : dst ≠ kJ) {c v : ℕ} (σ : Fin 20 → WTape) (hs : σ src = reg (ones c))
    (hd : σ dst = endv v) {L R : List (List Bool)} (ht : σ tk = ⟨L, [] :: R⟩) (hJ : σ kJ = emp) :
    Runs (addBody src dst tk h1 h2) σ
      (· = Function.update (Function.update σ dst (endv (v + c))) tk ⟨[] :: L, R⟩) (2 * c + 20) := by
  apply Runs.of_wp
  simp only [addBody, skp, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, ht, hJ, h3.symm, h4.symm, h5.symm, h6.symm, ↓reduceIte, endv, reg, emp, WTape.next_mk, WTape.cur_mk, List.headD_cons, List.tail_cons,
    Rules.output_copy, Rules.output_skip, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ⟨by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [TwistDescriptors.ones_append, WTape.put, reg, endv, emp]
  · simp [time_copy, time_skip, clen, h1]; omega

set_option maxHeartbeats 8000000 in
/-- `n` ticks add `n c` to `dst`. -/
theorem runs_addLoop {src dst tk : Fin 20} (h1 : src ≠ dst) (h2 : tk ≠ kJ) (h3 : src ≠ tk) (h4 : dst ≠ tk)
    (h5 : src ≠ kJ) (h6 : dst ≠ kJ) {c : ℕ} :
    ∀ (n v : ℕ) (σ : Fin 20 → WTape) (L : List (List Bool)), σ tk = ⟨L, List.replicate n []⟩ →
      σ src = reg (ones c) → σ dst = endv v → σ kJ = emp →
      Runs (addLoop src dst tk h1 h2) σ (· = Function.update (Function.update σ dst (endv (v + n * c)))
        tk ⟨List.replicate n [] ++ L, []⟩) (n * (2 * c + 22))
  | 0, v, σ, L, ht, hs, hd, hJ => by
    refine (Runs.loop_done (by simp [ht]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  | n + 1, v, σ, L, ht, hs, hd, hJ => by
    have s1 := runs_addBody h1 h2 h3 h4 h5 h6 σ hs hd (show σ tk = ⟨L, [] :: List.replicate n []⟩ by
      rw [ht]; rfl) hJ
    set σ₁ := Function.update (Function.update σ dst (endv (v + c))) tk ⟨[] :: L, List.replicate n []⟩ with hσ₁
    have ih := runs_addLoop h1 h2 h3 h4 h5 h6 n (v + c) σ₁ ([] :: L)
      (by rw [hσ₁, Function.update_self]) (by rw [hσ₁, Function.update_of_ne h3, Function.update_of_ne h1, hs])
      (by rw [hσ₁, Function.update_of_ne h4, Function.update_self])
      (by rw [hσ₁, Function.update_of_ne h2.symm, Function.update_of_ne h6.symm, hJ])
    refine (Runs.loop_step (by simp [ht]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h, hσ₁]
      have e : v + c + n * c = v + (n + 1) * c := by ring
      funext i
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [replicate_cons]
    · nlinarith

/-! ### Subtraction, copies and the long-axis count -/

/-- Subtract the constant on `k` from the value on `dst`. -/
noncomputable def subC (dst k : Fin 20) (h1 : dst ≠ k) (h2 : dst ≠ kS) (h3 : k ≠ kS) (h4 : kS ≠ dst) : Cmd 0 20 :=
  .seq (rewind dst) <| .seq (op1 Rules.drop false dst k kS h1 h2 h3) <| .seq (rewind k) <|
  .seq (clear dst) <| .seq (rewind kS) <| .seq (cpy kS dst h4) (clear kS)

set_option maxHeartbeats 8000000 in
theorem runs_subC {dst k : Fin 20} (h1 : dst ≠ k) (h2 : dst ≠ kS) (h3 : k ≠ kS) (h4 : kS ≠ dst) {x c : ℕ}
    (σ : Fin 20 → WTape) (hd : σ dst = endv x) (hk : σ k = reg (ones c)) (hS : σ kS = emp) :
    Runs (subC dst k h1 h2 h3 h4) σ (· = Function.update σ dst (endv (x - c))) (8 * x + 4 * c + 50) := by
  have t1 : time Rules.drop (ones x) (fun _ => ones c) ≤ x + c + 6 :=
    (time_le Rules.drop (ones x) (fun _ => ones c) c (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [subC, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  simp only [Function.update_apply, hd, hk, hS, h1, h2, h3, h4, h1.symm, h3.symm,
    ↓reduceIte, endv, reg, emp, WTape.next_mk, WTape.cur_mk, List.headD_cons, List.tail_cons,
    Rules.output_copy, Rules.output_drop, ↓parse_syms, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, ne_eq, List.cons_ne_nil, not_false_eq_true, true_and]
  refine ⟨by simp, by simp [WTape.put], ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [WTape.put, ones, List.drop_replicate, endv, emp, reg]
  · simp only [time_copy, clen, length_ones, List.length_drop, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, WTape.words, WTape.put_false, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.append_nil, List.headD_cons, List.tail_cons, List.length_drop]
    omega

/-- Copy the value on `src` to the empty `dst`. -/
noncomputable def copyTo (src dst : Fin 20) (h : src ≠ dst) : Cmd 0 20 := .seq (rewind src) (cpy src dst h)

set_option maxHeartbeats 4000000 in
theorem runs_copyTo {src dst : Fin 20} (h : src ≠ dst) {x : ℕ} (σ : Fin 20 → WTape) {L R : List (List Bool)}
    (hs : σ src = ⟨L, R⟩) (hLR : L.reverse ++ R = [ones x]) (hd : σ dst = emp) :
    Runs (copyTo src dst h) σ (· = Function.update (Function.update σ src (endv x)) dst (endv x))
      (2 * x + 10 + clen L) := by
  apply Runs.of_wp
  simp only [copyTo, cpy, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h.symm, ↓reduceIte, hLR, endv, emp, WTape.next_mk, WTape.cur_mk,
    List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [WTape.put, emp]
  · simp [time_copy, clen]; omega

/-- Count the long axes into `kLc`. -/
noncomputable def countLoop : Cmd 0 20 :=
  .loop kF (.seq (.cond kF (.seq (op0 Rules.copy true kOne kLc (by decide)) (rewind kOne)) (rewind kJ))
    (skp kF kJ (by decide)))

set_option maxHeartbeats 8000000 in
theorem runs_countLoop : ∀ (flags : List Bool) (v : ℕ) (σ : Fin 20 → WTape) (LF : List (List Bool)),
    σ kF = ⟨LF, flags.map fun b => [b]⟩ → σ kOne = reg (ones 1) → σ kLc = endv v → σ kJ = emp →
    Runs countLoop σ (· = Function.update (Function.update σ kLc (endv (v + (flags.filter id).length)))
      kF ⟨(flags.map fun b => [b]).reverse ++ LF, []⟩) (flags.length * 40)
  | [], v, σ, LF, hF, hOne, hL, hJ => by
    refine (Runs.loop_done (by simp [hF]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hF, hL]
  | b :: flags, v, σ, LF, hF, hOne, hL, hJ => by
    have sk : ∀ τ : Fin 20 → WTape, τ kF = ⟨LF, [b] :: flags.map fun b => [b]⟩ → τ kJ = emp →
        Runs (skp (a := 0) kF kJ (by decide)) τ (· = Function.update τ kF ⟨[b] :: LF, flags.map fun b => [b]⟩) 6 :=
      fun τ hτ hτJ => (runs_skp (a := 0) (show kF ≠ kJ by decide) τ (by simp [hτ]) (by simp [hτJ, emp])).mono
        (fun τ' e => by rw [e, hτ]; rfl) (by simp [hτ])
    cases b with
    | true =>
      have s1 : Runs (.seq (op0 (a := 0) Rules.copy true kOne kLc (by decide)) (rewind kOne)) σ
          (· = Function.update σ kLc (endv (v + 1))) 20 := by
        apply Runs.of_wp
        simp only [WP, wp_op0, wp_rewind]
        tsimp [hOne, hL, endv, reg, Rules.output_copy]
        funext i; fin_cases i <;> first | rfl | tsimp [hOne, hL, endv, reg, TwistDescriptors.ones_append]
      have sc := Runs.cond_true (c := .seq (op0 (a := 0) Rules.copy true kOne kLc (by decide)) (rewind kOne))
        (d := rewind kJ) (i := kF) (by rw [hF]; exact (startsOne_mk _ _ _ _).mpr rfl) s1
      set σ₁ := Function.update σ kLc (endv (v + 1)) with hσ₁
      have s2 := sk σ₁ (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hJ])
      set σ₂ := Function.update σ₁ kF ⟨[true] :: LF, flags.map fun b => [b]⟩ with hσ₂
      have ih := runs_countLoop flags (v + 1) σ₂ ([true] :: LF) (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁, hOne])
        (by tsimp [hσ₂, hσ₁]) (by tsimp [hσ₂, hσ₁, hJ])
      refine (Runs.loop_step (by simp [hF]) ((Runs.then sc s2).mono (fun τ h => by rw [h]; exact ih)
        le_rfl)).mono (fun τ h => ?_) ?_
      · rw [h]
        have e : v + 1 + (flags.filter id).length = v + ((true :: flags).filter id).length := by
          simp; ring
        funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, e]
      · simp only [List.length_cons]; nlinarith
    | false =>
      have sc := Runs.cond_false (c := .seq (op0 (a := 0) Rules.copy true kOne kLc (by decide)) (rewind kOne))
        (d := rewind kJ) (i := kF) (by rw [hF]; intro h; have := (startsOne_mk _ _ _ _).mp h; simp at this)
        (runs_rewind (a := 0) kJ σ)
      set σ₁ := Function.update σ kJ ⟨[], (σ kJ).left.reverse ++ (σ kJ).right⟩ with hσ₁
      have s2 := sk σ₁ (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hJ, emp])
      set σ₂ := Function.update σ₁ kF ⟨[false] :: LF, flags.map fun b => [b]⟩ with hσ₂
      have ih := runs_countLoop flags v σ₂ ([false] :: LF) (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁, hOne])
        (by tsimp [hσ₂, hσ₁, hL]) (by tsimp [hσ₂, hσ₁, hJ, emp])
      refine (Runs.loop_step (by simp [hF]) ((Runs.then sc s2).mono (fun τ h => by rw [h]; exact ih)
        le_rfl)).mono (fun τ h => ?_) ?_
      · rw [h]
        funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hJ, emp]
      · tsimp [hJ, emp]; nlinarith

/-! ### The phases -/

/-- Unary to ticks: the word on `src` becomes that many empty words on `dst`. -/
noncomputable def toTicks (src dst : Fin 20) (h : src ≠ dst) : Cmd 0 20 :=
  .seq (op0 Rules.ticks false src dst h) (.seq (rewind src) (rewind dst))

set_option maxHeartbeats 4000000 in
theorem runs_toTicks {src dst : Fin 20} (h : src ≠ dst) {x : ℕ} (σ : Fin 20 → WTape) (hs : σ src = reg (ones x))
    (hd : σ dst = emp) :
    Runs (toTicks src dst h) σ (· = Function.update σ dst (ticks x)) (4 * x + 20) := by
  apply Runs.of_wp
  simp only [toTicks, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h, h.symm, ↓reduceIte, reg, emp, WTape.next_mk, WTape.cur_mk,
    List.headD_cons, List.tail_cons, Rules.output_ticks, ↓parse_syms, length_ones]
  refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [WTape.put, ticks, reg, emp]
  · simp [time, rest, clen]; omega

/-- Add the value on `src` (any head position) to `dst`, leaving `src` a register. -/
noncomputable def addOnce (src dst : Fin 20) (h : src ≠ dst) : Cmd 0 20 :=
  .seq (rewind src) (.seq (op0 Rules.copy true src dst h) (rewind src))

set_option maxHeartbeats 4000000 in
theorem runs_addOnce {src dst : Fin 20} (h : src ≠ dst) {c v : ℕ} (σ : Fin 20 → WTape)
    {L R : List (List Bool)} (hs : σ src = ⟨L, R⟩) (hLR : L.reverse ++ R = [ones c]) (hd : σ dst = endv v) :
    Runs (addOnce src dst h) σ (· = Function.update (Function.update σ src (reg (ones c))) dst (endv (v + c)))
      (4 * c + 20 + clen L) := by
  apply Runs.of_wp
  simp only [addOnce, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h, h.symm, ↓reduceIte, hLR, endv, reg, WTape.next_mk,
    WTape.cur_mk, List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [TwistDescriptors.ones_append, WTape.put, endv]
  · simp [time_copy, clen]; omega

/-! ### The constants -/

/-- Phase one: `q` and `b` as ticks, and `D` ticks. -/
noncomputable def consts1 : Cmd 0 20 :=
  .seq (toTicks kX kFuel (by decide)) <| .seq divLoop <| .seq (rewind kQt) <|
  .seq (toTicks kX kBt (by decide)) (toTicks kD kDt (by decide))

/-- Phase two: the products `DK`, `qDK` and `bD`. -/
noncomputable def consts2 : Cmd 0 20 :=
  .seq (emit [[]] kDK) <| .seq (addLoop kK kDK kDt (by decide) (by decide)) <| .seq (rewind kDt) <|
  .seq (rewind kDK) <|
  .seq (emit [[]] kDqK) <| .seq (addLoop kDK kDqK kQt (by decide) (by decide)) <| .seq (rewind kQt) <|
  .seq (emit [[]] kDb) <| .seq (addLoop kD kDb kBt (by decide) (by decide)) (rewind kBt)

/-- Phase three: the number of long axes. -/
noncomputable def consts3 : Cmd 0 20 := .seq (emit [[]] kLc) <| .seq countLoop (rewind kF)

/-- Phase four: the starts `A₀`, `B₀` and `T₀`. -/
noncomputable def consts4 : Cmd 0 20 :=
  .seq (copyTo kDqK kA0 (by decide)) <| .seq (addOnce kD kA0 (by decide)) <|
  .seq (subC kA0 kOne (by decide) (by decide) (by decide) (by decide)) <|
  .seq (copyTo kDK kB0 (by decide)) <| .seq (subC kB0 kK (by decide) (by decide) (by decide) (by decide)) <|
  .seq (copyTo kDqK kT0 (by decide)) <| .seq (addOnce kDb kT0 (by decide)) <|
  .seq (addOnce kLc kT0 (by decide)) (subC kT0 kOne (by decide) (by decide) (by decide) (by decide))

/-- All constants of the tables. -/
noncomputable def consts : Cmd 0 20 := .seq consts1 <| .seq consts2 <| .seq consts3 consts4

set_option maxHeartbeats 16000000 in
theorem runs_consts1 {x K D : ℕ} (hK0 : 0 < K) (σ : Fin 20 → WTape) (hX : σ kX = reg (ones x))
    (hK : σ kK = reg (ones K)) (hD : σ kD = reg (ones D)) (hFuel : σ kFuel = emp) (hQ : σ kQt = emp)
    (hB : σ kBt = emp) (hDt : σ kDt = emp) (hG : σ kG = emp) (hS : σ kS = emp) (hJ : σ kJ = emp) :
    Runs consts1 σ (· = Function.update (Function.update (Function.update (Function.update (Function.update σ
        kFuel ⟨List.replicate x [], []⟩) kX (reg (ones (x % K)))) kQt (ticks (x / K))) kBt (ticks (x % K)))
        kDt (ticks D)) (4 * x + 20 + x * (16 * x + 10 * K + 110) + x + 3 + 4 * (x % K) + 4 * D + 60) := by
  have s1 := runs_toTicks (show kX ≠ kFuel by decide) σ hX hFuel
  set σ₁ := Function.update σ kFuel (ticks x) with hσ₁
  have s2 := runs_divLoop hK0 x x σ₁ [] [] (by tsimp [hσ₁, ticks]) (by tsimp [hσ₁, hK]) (by tsimp [hσ₁, hX])
    (by tsimp [hσ₁, hG]) (by tsimp [hσ₁, hS]) (by tsimp [hσ₁, hJ]) (by tsimp [hσ₁, hQ, emp])
  have hmin : min x (x / K) = x / K := Nat.min_eq_right (Nat.div_le_self _ _)
  have hres : divRes K x x = x % K := divRes_full (Nat.div_le_self _ _)
  rw [hmin, hres] at s2
  set σ₂ := Function.update (Function.update (Function.update σ₁ kX (reg (ones (x % K))))
    kQt ⟨List.replicate (x / K) [] ++ [], []⟩) kFuel ⟨List.replicate x [] ++ [], []⟩ with hσ₂
  have s3 := runs_rewind (a := 0) kQt σ₂
  set σ₃ := Function.update σ₂ kQt ⟨[], (σ₂ kQt).left.reverse ++ (σ₂ kQt).right⟩ with hσ₃
  have s4 := runs_toTicks (x := x % K) (show kX ≠ kBt by decide) σ₃ (by tsimp [hσ₃, hσ₂])
    (by tsimp [hσ₃, hσ₂, hσ₁, hB])
  set σ₄ := Function.update σ₃ kBt (ticks (x % K)) with hσ₄
  have s5 := runs_toTicks (x := D) (show kD ≠ kDt by decide) σ₄ (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hD])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hDt])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₄, hσ₃, hσ₂, hσ₁, ticks]
  · tsimp [hσ₂, clen]; omega

set_option maxHeartbeats 16000000 in
theorem runs_consts2 {K D q b : ℕ} (σ : Fin 20 → WTape) (hK : σ kK = reg (ones K)) (hD : σ kD = reg (ones D))
    (hDt : σ kDt = ticks D) (hQ : σ kQt = ticks q) (hB : σ kBt = ticks b) (hDK : σ kDK = emp)
    (hDqK : σ kDqK = emp) (hDb : σ kDb = emp) (hJ : σ kJ = emp) :
    Runs consts2 σ (· = Function.update (Function.update (Function.update σ kDK (reg (ones (D * K))))
        kDqK (endv (q * (D * K)))) kDb (endv (b * D)))
      (D * (2 * K + 22) + q * (2 * (D * K) + 22) + b * (2 * D + 22) + 3 * D + 3 * q + 3 * b +
        2 * (D * K) + 60) := by
  have s1 := runs_emit (a := 0) [[]] kDK σ (by rw [hDK]; rfl)
  set σ₁ := Function.update σ kDK ⟨[[]].reverse ++ (σ kDK).left, []⟩ with hσ₁
  have s2 := runs_addLoop (c := K) (show kK ≠ kDK by decide) (show kDt ≠ kJ by decide) (by decide) (by decide)
    (by decide) (by decide) D 0 σ₁ [] (by tsimp [hσ₁, hDt, ticks]) (by tsimp [hσ₁, hK])
    (by tsimp [hσ₁, hDK, emp, endv, ones]) (by tsimp [hσ₁, hJ])
  set σ₂ := Function.update (Function.update σ₁ kDK (endv (0 + D * K))) kDt ⟨List.replicate D [] ++ [], []⟩
    with hσ₂
  have s3 := runs_rewind (a := 0) kDt σ₂
  set σ₃ := Function.update σ₂ kDt ⟨[], (σ₂ kDt).left.reverse ++ (σ₂ kDt).right⟩ with hσ₃
  have s4 := runs_rewind (a := 0) kDK σ₃
  set σ₄ := Function.update σ₃ kDK ⟨[], (σ₃ kDK).left.reverse ++ (σ₃ kDK).right⟩ with hσ₄
  have s5 := runs_emit (a := 0) [[]] kDqK σ₄ (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hDqK, emp])
  set σ₅ := Function.update σ₄ kDqK ⟨[[]].reverse ++ (σ₄ kDqK).left, []⟩ with hσ₅
  have s6 := runs_addLoop (c := D * K) (show kDK ≠ kDqK by decide) (show kQt ≠ kJ by decide) (by decide)
    (by decide) (by decide) (by decide) q 0 σ₅ [] (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hQ, ticks])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, endv]; rfl) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDqK, emp, endv, ones])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hJ])
  set σ₆ := Function.update (Function.update σ₅ kDqK (endv (0 + q * (D * K)))) kQt
    ⟨List.replicate q [] ++ [], []⟩ with hσ₆
  have s7 := runs_rewind (a := 0) kQt σ₆
  set σ₇ := Function.update σ₆ kQt ⟨[], (σ₆ kQt).left.reverse ++ (σ₆ kQt).right⟩ with hσ₇
  have s8 := runs_emit (a := 0) [[]] kDb σ₇ (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDb, emp])
  set σ₈ := Function.update σ₇ kDb ⟨[[]].reverse ++ (σ₇ kDb).left, []⟩ with hσ₈
  have s9 := runs_addLoop (c := D) (show kD ≠ kDb by decide) (show kBt ≠ kJ by decide) (by decide)
    (by decide) (by decide) (by decide) b 0 σ₈ [] (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hB, ticks])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hD])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDb, emp, endv, ones])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hJ])
  set σ₉ := Function.update (Function.update σ₈ kDb (endv (0 + b * D))) kBt ⟨List.replicate b [] ++ [], []⟩
    with hσ₉
  have s10 := runs_rewind (a := 0) kBt σ₉
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 s10))))))))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl |
      (tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDt, hQ, hB, hDK, hDqK, hDb, emp, endv, ticks] <;> rfl)
  · tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDK, hDqK, hDb, emp, endv, clen]
    omega

theorem clen_flags : ∀ flags : List Bool, clen (flags.map fun b => [b]) = 2 * flags.length
  | [] => rfl
  | b :: fl => by rw [List.map_cons, clen_cons, clen_flags fl]; simp; ring

set_option maxHeartbeats 8000000 in
theorem runs_consts3 {flags : List Bool} (σ : Fin 20 → WTape) (hF : σ kF = ⟨[], flags.map fun b => [b]⟩)
    (hOne : σ kOne = reg (ones 1)) (hL : σ kLc = emp) (hJ : σ kJ = emp) :
    Runs consts3 σ (· = Function.update σ kLc (endv (flags.filter id).length))
      (flags.length * 40 + 2 * flags.length + 10) := by
  have s1 := runs_emit (a := 0) [[]] kLc σ (by rw [hL]; rfl)
  set σ₁ := Function.update σ kLc ⟨[[]].reverse ++ (σ kLc).left, []⟩ with hσ₁
  have s2 := runs_countLoop flags 0 σ₁ [] (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hOne])
    (by tsimp [hσ₁, hL, emp, endv, ones]) (by tsimp [hσ₁, hJ])
  set σ₂ := Function.update (Function.update σ₁ kLc (endv (0 + (flags.filter id).length)))
    kF ⟨(flags.map fun b => [b]).reverse ++ [], []⟩ with hσ₂
  have s3 := runs_rewind (a := 0) kF σ₂
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hF]
  · have : clen ((flags.map fun b => [b]).reverse ++ []) = 2 * flags.length := by
      rw [List.append_nil, SigmaTableTape.clen_reverse, clen_flags]
    tsimp [hσ₂, hσ₁, hL, emp] at this ⊢
    omega

set_option maxHeartbeats 16000000 in
theorem runs_consts4 {Q D DK K Bd L : ℕ} (σ : Fin 20 → WTape) (hDqK : σ kDqK = endv Q) (hD : σ kD = reg (ones D))
    (hOne : σ kOne = reg (ones 1)) (hDK : σ kDK = reg (ones DK)) (hK : σ kK = reg (ones K))
    (hDb : σ kDb = endv Bd) (hLc : σ kLc = endv L) (hA0 : σ kA0 = emp) (hB0 : σ kB0 = emp)
    (hT0 : σ kT0 = emp) (hS : σ kS = emp) :
    Runs consts4 σ (· = Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update σ kDK (endv DK)) kDb (reg (ones Bd))) kLc (reg (ones L)))
        kA0 (endv (Q + D - 1))) kB0 (endv (DK - K))) kT0 (endv (Q + Bd + L - 1))) kDqK (endv Q))
      (40 * (Q + D + DK + K + Bd + L) + 400) := by
  have s1 := runs_copyTo (x := Q) (show kDqK ≠ kA0 by decide) σ (L := [ones Q]) (R := []) (by rw [hDqK]; rfl)
    (by simp) hA0
  set σ₁ := Function.update (Function.update σ kDqK (endv Q)) kA0 (endv Q) with hσ₁
  have s2 := runs_addOnce (c := D) (v := Q) (show kD ≠ kA0 by decide) σ₁ (L := []) (R := [ones D])
    (by tsimp [hσ₁, hD, reg]) (by simp) (by tsimp [hσ₁])
  set σ₂ := Function.update (Function.update σ₁ kD (reg (ones D))) kA0 (endv (Q + D)) with hσ₂
  have s3 := runs_subC (x := Q + D) (c := 1) (show kA0 ≠ kOne by decide) (by decide) (by decide) (by decide) σ₂
    (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁, hOne]) (by tsimp [hσ₂, hσ₁, hS])
  set σ₃ := Function.update σ₂ kA0 (endv (Q + D - 1)) with hσ₃
  have s4 := runs_copyTo (x := DK) (show kDK ≠ kB0 by decide) σ₃ (L := []) (R := [ones DK])
    (by tsimp [hσ₃, hσ₂, hσ₁, hDK, reg]) (by simp) (by tsimp [hσ₃, hσ₂, hσ₁, hB0])
  set σ₄ := Function.update (Function.update σ₃ kDK (endv DK)) kB0 (endv DK) with hσ₄
  have s5 := runs_subC (x := DK) (c := K) (show kB0 ≠ kK by decide) (by decide) (by decide) (by decide) σ₄
    (by tsimp [hσ₄]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hK]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hS])
  set σ₅ := Function.update σ₄ kB0 (endv (DK - K)) with hσ₅
  have s6 := runs_copyTo (x := Q) (show kDqK ≠ kT0 by decide) σ₅ (L := [ones Q]) (R := [])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, endv]) (by simp) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hT0])
  set σ₆ := Function.update (Function.update σ₅ kDqK (endv Q)) kT0 (endv Q) with hσ₆
  have s7 := runs_addOnce (c := Bd) (v := Q) (show kDb ≠ kT0 by decide) σ₆ (L := [ones Bd]) (R := [])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDb, endv]) (by simp) (by tsimp [hσ₆])
  set σ₇ := Function.update (Function.update σ₆ kDb (reg (ones Bd))) kT0 (endv (Q + Bd)) with hσ₇
  have s8 := runs_addOnce (c := L) (v := Q + Bd) (show kLc ≠ kT0 by decide) σ₇ (L := [ones L]) (R := [])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hLc, endv]) (by simp) (by tsimp [hσ₇])
  set σ₈ := Function.update (Function.update σ₇ kLc (reg (ones L))) kT0 (endv (Q + Bd + L)) with hσ₈
  have s9 := runs_subC (x := Q + Bd + L) (c := 1) (show kT0 ≠ kOne by decide) (by decide) (by decide)
    (by decide) σ₈ (by tsimp [hσ₈]) (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hOne])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hS])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 s9)))))))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hD]
  · simp only [clen_cons, clen_nil, length_ones]; omega

set_option maxHeartbeats 16000000 in
/-- `runs_consts`: from `x`, `K > 0`, `D` and the long-axis flags, the program leaves `q = x / K` and
`b = x mod K` as ticks, `D` ticks, and the starts `A₀ = qDK + D - 1`, `B₀ = DK - K` and
`T₀ = qDK + bD + L - 1`, `L` the number of long axes. -/
theorem runs_consts {x K D : ℕ} {flags : List Bool} (hK0 : 0 < K) (σ : Fin 20 → WTape)
    (hX : σ kX = reg (ones x)) (hK : σ kK = reg (ones K)) (hD : σ kD = reg (ones D))
    (hF : σ kF = ⟨[], flags.map fun b => [b]⟩) (hOne : σ kOne = reg (ones 1)) (hFuel : σ kFuel = emp)
    (hQ : σ kQt = emp) (hB : σ kBt = emp) (hDt : σ kDt = emp) (hDK : σ kDK = emp) (hDqK : σ kDqK = emp)
    (hDb : σ kDb = emp) (hLc : σ kLc = emp) (hG : σ kG = emp) (hS : σ kS = emp) (hJ : σ kJ = emp)
    (hA0 : σ kA0 = emp) (hB0 : σ kB0 = emp) (hT0 : σ kT0 = emp) :
    Runs consts σ (fun σ' => σ' kQt = ticks (x / K) ∧ σ' kBt = ticks (x % K) ∧ σ' kDt = ticks D ∧
        σ' kA0 = endv (x / K * (D * K) + D - 1) ∧ σ' kB0 = endv (D * K - K) ∧
        σ' kT0 = endv (x / K * (D * K) + x % K * D + (flags.filter id).length - 1) ∧
        σ' kF = ⟨[], flags.map fun b => [b]⟩ ∧ σ' kOne = reg (ones 1) ∧ σ' kS = emp ∧ σ' kJ = emp ∧
        σ' kTop = σ kTop)
      (4 * x + 20 + x * (16 * x + 10 * K + 110) + x + 3 + 4 * (x % K) + 4 * D + 60 + 1 +
        (D * (2 * K + 22) + x / K * (2 * (D * K) + 22) + x % K * (2 * D + 22) + 3 * D + 3 * (x / K) +
          3 * (x % K) + 2 * (D * K) + 60 + 1 +
          (flags.length * 40 + 2 * flags.length + 10 + 1 +
            (40 * (x / K * (D * K) + D + D * K + K + x % K * D + (flags.filter id).length) + 400)))) := by
  have s1 := runs_consts1 hK0 σ hX hK hD hFuel hQ hB hDt hG hS hJ
  set σ₁ := Function.update (Function.update (Function.update (Function.update (Function.update σ
    kFuel ⟨List.replicate x [], []⟩) kX (reg (ones (x % K)))) kQt (ticks (x / K))) kBt (ticks (x % K)))
    kDt (ticks D) with hσ₁
  have s2 := runs_consts2 (K := K) (D := D) (q := x / K) (b := x % K) σ₁ (by tsimp [hσ₁, hK])
    (by tsimp [hσ₁, hD]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hDK])
    (by tsimp [hσ₁, hDqK]) (by tsimp [hσ₁, hDb]) (by tsimp [hσ₁, hJ])
  set σ₂ := Function.update (Function.update (Function.update σ₁ kDK (reg (ones (D * K))))
    kDqK (endv (x / K * (D * K)))) kDb (endv (x % K * D)) with hσ₂
  have s3 := runs_consts3 (flags := flags) σ₂ (by tsimp [hσ₂, hσ₁, hF]) (by tsimp [hσ₂, hσ₁, hOne])
    (by tsimp [hσ₂, hσ₁, hLc]) (by tsimp [hσ₂, hσ₁, hJ])
  set σ₃ := Function.update σ₂ kLc (endv (flags.filter id).length) with hσ₃
  have s4 := runs_consts4 (Q := x / K * (D * K)) (D := D) (DK := D * K) (K := K) (Bd := x % K * D)
    (L := (flags.filter id).length) σ₃ (by tsimp [hσ₃, hσ₂]) (by tsimp [hσ₃, hσ₂, hσ₁, hD])
    (by tsimp [hσ₃, hσ₂, hσ₁, hOne]) (by tsimp [hσ₃, hσ₂]) (by tsimp [hσ₃, hσ₂, hσ₁, hK])
    (by tsimp [hσ₃, hσ₂]) (by tsimp [hσ₃]) (by tsimp [hσ₃, hσ₂, hσ₁, hA0]) (by tsimp [hσ₃, hσ₂, hσ₁, hB0])
    (by tsimp [hσ₃, hσ₂, hσ₁, hT0]) (by tsimp [hσ₃, hσ₂, hσ₁, hS])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ e => ?_) le_rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tsimp [hσ₃, hσ₂, hσ₁, hF, hOne, hS, hJ]

/-! ### The top bits -/

/-- One long axis: write the current top bit and lower it. -/
noncomputable def longTop : Cmd 0 20 :=
  .seq (.seq (rewind kT0) (cpy kT0 kTop (by decide))) (subC kT0 kOne (by decide) (by decide) (by decide) (by decide))

/-- The top bits of the long axes, from `T₀` down. -/
noncomputable def topLoop : Cmd 0 20 :=
  .loop kF (.seq (.cond kF longTop (rewind kJ)) (skp kF kJ (by decide)))

set_option maxHeartbeats 8000000 in
theorem runs_longTop {v : ℕ} (σ : Fin 20 → WTape) (hT0 : σ kT0 = endv v) (hOne : σ kOne = reg (ones 1))
    {O : List (List Bool)} (hTop : σ kTop = ⟨O, []⟩) (hS : σ kS = emp) :
    Runs longTop σ (· = Function.update (Function.update σ kTop ⟨ones v :: O, []⟩) kT0 (endv (v - 1)))
      (12 * v + 80) := by
  have s1 : Runs (.seq (rewind (a := 0) kT0) (cpy kT0 kTop (by decide))) σ
      (· = Function.update σ kTop ⟨ones v :: O, []⟩) (2 * v + 10) := by
    apply Runs.of_wp
    simp only [cpy, WP, wp_op0, wp_rewind]
    tsimp [hT0, hTop, endv, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hT0, hTop, endv]
    · simp [time_copy]; omega
  set σ₁ := Function.update σ kTop ⟨ones v :: O, []⟩ with hσ₁
  have s2 := runs_subC (x := v) (c := 1) (show kT0 ≠ kOne by decide) (by decide) (by decide) (by decide) σ₁
    (by tsimp [hσ₁, hT0]) (by tsimp [hσ₁, hOne]) (by tsimp [hσ₁, hS])
  exact (Runs.then s1 s2).mono (fun τ e => e) (by omega)

set_option maxHeartbeats 8000000 in
/-- `runs_topLoop`: over the flags, the long axes get the top bits `v, v - 1, …`. -/
theorem runs_topLoop : ∀ (flags : List Bool) (v : ℕ) (σ : Fin 20 → WTape) (LF O : List (List Bool)),
    σ kF = ⟨LF, flags.map fun b => [b]⟩ → σ kT0 = endv v → σ kOne = reg (ones 1) → σ kTop = ⟨O, []⟩ →
    σ kS = emp → σ kJ = emp →
    Runs topLoop σ (· = Function.update (Function.update (Function.update σ kTop
        ⟨((List.range (flags.filter id).length).map fun k => ones (v - k)).reverse ++ O, []⟩)
        kT0 (endv (v - (flags.filter id).length))) kF ⟨(flags.map fun b => [b]).reverse ++ LF, []⟩)
      (flags.length * (12 * v + 90))
  | [], v, σ, LF, O, hF, hT0, hOne, hTop, hS, hJ => by
    refine (Runs.loop_done (by simp [hF]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hF, hT0, hTop]
  | b :: flags, v, σ, LF, O, hF, hT0, hOne, hTop, hS, hJ => by
    have sk : ∀ τ : Fin 20 → WTape, τ kF = ⟨LF, [b] :: flags.map fun b => [b]⟩ → τ kJ = emp →
        Runs (skp (a := 0) kF kJ (by decide)) τ (· = Function.update τ kF ⟨[b] :: LF, flags.map fun b => [b]⟩) 6 :=
      fun τ hτ hτJ => (runs_skp (a := 0) (show kF ≠ kJ by decide) τ (by simp [hτ]) (by simp [hτJ, emp])).mono
        (fun τ' e => by rw [e, hτ]; rfl) (by simp [hτ])
    cases b with
    | true =>
      have s1 := runs_longTop σ hT0 hOne hTop hS
      have sc := Runs.cond_true (c := longTop) (d := rewind kJ) (i := kF)
        (by rw [hF]; exact (startsOne_mk _ _ _ _).mpr rfl) s1
      set σ₁ := Function.update (Function.update σ kTop ⟨ones v :: O, []⟩) kT0 (endv (v - 1)) with hσ₁
      have s2 := sk σ₁ (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hJ])
      set σ₂ := Function.update σ₁ kF ⟨[true] :: LF, flags.map fun b => [b]⟩ with hσ₂
      have ih := runs_topLoop flags (v - 1) σ₂ ([true] :: LF) (ones v :: O) (by tsimp [hσ₂])
        (by tsimp [hσ₂, hσ₁]) (by tsimp [hσ₂, hσ₁, hOne]) (by tsimp [hσ₂, hσ₁]) (by tsimp [hσ₂, hσ₁, hS])
        (by tsimp [hσ₂, hσ₁, hJ])
      refine (Runs.loop_step (by simp [hF]) ((Runs.then sc s2).mono (fun τ h => by rw [h]; exact ih)
        le_rfl)).mono (fun τ h => ?_) ?_
      · rw [h]
        have e1 := map_range_succ_rev (fun k => ones (v - k)) (flags.filter id).length O
        simp only [Nat.sub_zero] at e1
        have e2 : (fun k => ones (v - 1 - k)) = fun k => ones (v - (k + 1)) := by
          funext k; congr 1; omega
        have e3 : v - 1 - (flags.filter id).length = v - ((flags.filter id).length + 1) := by omega
        funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, e1, e2, e3]
      · simp only [List.length_cons]
        have : (flags.length) * (12 * (v - 1) + 90) ≤ flags.length * (12 * v + 90) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith
    | false =>
      have sc := Runs.cond_false (c := longTop) (d := rewind kJ) (i := kF)
        (by rw [hF]; intro h; have := (startsOne_mk _ _ _ _).mp h; simp at this)
        (runs_rewind (a := 0) kJ σ)
      set σ₁ := Function.update σ kJ ⟨[], (σ kJ).left.reverse ++ (σ kJ).right⟩ with hσ₁
      have s2 := sk σ₁ (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hJ, emp])
      set σ₂ := Function.update σ₁ kF ⟨[false] :: LF, flags.map fun b => [b]⟩ with hσ₂
      have ih := runs_topLoop flags v σ₂ ([false] :: LF) O (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁, hT0])
        (by tsimp [hσ₂, hσ₁, hOne]) (by tsimp [hσ₂, hσ₁, hTop]) (by tsimp [hσ₂, hσ₁, hS])
        (by tsimp [hσ₂, hσ₁, hJ, emp])
      refine (Runs.loop_step (by simp [hF]) ((Runs.then sc s2).mono (fun τ h => by rw [h]; exact ih)
        le_rfl)).mono (fun τ h => ?_) ?_
      · rw [h]
        funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hJ, emp]
      · tsimp [hJ, emp]; nlinarith

/-! ### The paper's constants -/

theorem longRank_getElem {ts : List ℕ} {ℓ : ℕ} {k : ℕ}
    (hk : k < (longs ts ℓ).length) : longRank ts ℓ (longs ts ℓ)[k] = k := by
  obtain ⟨hil, hel⟩ := longs_lt hk
  obtain ⟨hr, hri⟩ := longs_getElem_longRank hil hel
  exact (longs_nodup ts ℓ).getElem_inj_iff.mp hri

/-- The top bits in closed form: long axis `k` holds `T₀ - k`. -/
theorem topWords_paper (ts : List ℕ) (ℓ K : ℕ) :
    (List.range (longs ts ℓ).length).map (fun k => ones (ts.length * ((ℓ - 1) / K) * K +
        ts.length * ((ℓ - 1) % K) + (longs ts ℓ).length - 1 - k)) =
      (longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1)) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hk : k < (longs ts ℓ).length := by simpa using h1
  congr 1
  unfold paperSigma
  have hb : ¬ ℓ - 1 < (ℓ - 1) % K := Nat.not_lt.mpr (Nat.mod_le _ _)
  have ht : ¬ ℓ - 1 < ℓ - 1 := lt_irrefl _
  simp only [hb, ht, ↓reduceIte, longRank_getElem hk]
  omega

/-- The constants, then the top bits. -/
noncomputable def constsTop : Cmd 0 20 := .seq consts topLoop

/-- The paper's long-axis flags. -/
def paperFlags (ts : List ℕ) (ℓ : ℕ) : List Bool := (List.range ts.length).map fun i => decide (axLen ts i = ℓ)

theorem paperFlags_count (ts : List ℕ) (ℓ : ℕ) : ((paperFlags ts ℓ).filter id).length = (longs ts ℓ).length := by
  simp [paperFlags, longs, List.filter_map]

/-- The step bound of `constsTop` on the paper's parameters. -/
def constsTopCost (x K D F L : ℕ) : ℕ :=
  4 * x + 20 + x * (16 * x + 10 * K + 110) + x + 3 + 4 * (x % K) + 4 * D + 60 + 1 +
    (D * (2 * K + 22) + x / K * (2 * (D * K) + 22) + x % K * (2 * D + 22) + 3 * D + 3 * (x / K) +
      3 * (x % K) + 2 * (D * K) + 60 + 1 +
      (F * 40 + 2 * F + 10 + 1 + (40 * (x / K * (D * K) + D + D * K + K + x % K * D + L) + 400))) + 1 +
    F * (12 * (x / K * (D * K) + x % K * D + L - 1) + 90)

set_option maxHeartbeats 16000000 in
/-- `runs_constsTop_paper`: from `ℓ - 1`, `K`, `D` and the paper's flags, the program leaves the tick
tapes `q`, `b`, `D`, the row starts `DqK + D - 1` and `(D - 1)K`, and the top bits of the long axes in
the paper's layout. -/
theorem runs_constsTop_paper {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (hD1 : 1 ≤ ts.length)
    (σ : Fin 20 → WTape) (hX : σ kX = reg (ones (ℓ - 1))) (hK : σ kK = reg (ones K))
    (hD : σ kD = reg (ones ts.length)) (hF : σ kF = ⟨[], (paperFlags ts ℓ).map fun b => [b]⟩)
    (hOne : σ kOne = reg (ones 1)) (hFuel : σ kFuel = emp)
    (hQ : σ kQt = emp) (hB : σ kBt = emp) (hDt : σ kDt = emp) (hDK : σ kDK = emp) (hDqK : σ kDqK = emp)
    (hDb : σ kDb = emp) (hLc : σ kLc = emp) (hG : σ kG = emp) (hS : σ kS = emp) (hJ : σ kJ = emp)
    (hA0 : σ kA0 = emp) (hB0 : σ kB0 = emp) (hT0 : σ kT0 = emp) (hTop : σ kTop = emp) :
    Runs constsTop σ (fun σ' => σ' kQt = ticks ((ℓ - 1) / K) ∧ σ' kBt = ticks ((ℓ - 1) % K) ∧
        σ' kDt = ticks ts.length ∧ σ' kA0 = endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)) ∧
        σ' kB0 = endv ((ts.length - 1) * K) ∧
        σ' kTop = ⟨((longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))).reverse, []⟩)
      (constsTopCost (ℓ - 1) K ts.length ts.length (longs ts ℓ).length) := by
  have hK0 : 0 < K := hL.2.2.1
  have s1 := runs_consts (x := ℓ - 1) (K := K) (D := ts.length) (flags := paperFlags ts ℓ) hK0 σ hX hK hD hF hOne
    hFuel hQ hB hDt hDK hDqK hDb hLc hG hS hJ hA0 hB0 hT0
  rw [paperFlags_count] at s1
  have hlen : (paperFlags ts ℓ).length = ts.length := by simp [paperFlags]
  set T0v := (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length - 1 with hT0v
  have key : Runs consts σ (fun τ => Runs topLoop τ (fun σ' => σ' kQt = ticks ((ℓ - 1) / K) ∧
        σ' kBt = ticks ((ℓ - 1) % K) ∧
        σ' kDt = ticks ts.length ∧ σ' kA0 = endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)) ∧
        σ' kB0 = endv ((ts.length - 1) * K) ∧
        σ' kTop = ⟨((longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))).reverse, []⟩)
      (ts.length * (12 * T0v + 90)))
      (4 * (ℓ - 1) + 20 + (ℓ - 1) * (16 * (ℓ - 1) + 10 * K + 110) + (ℓ - 1) + 3 + 4 * ((ℓ - 1) % K) +
        4 * ts.length + 60 + 1 +
        (ts.length * (2 * K + 22) + (ℓ - 1) / K * (2 * (ts.length * K) + 22) + (ℓ - 1) % K * (2 * ts.length + 22) +
          3 * ts.length + 3 * ((ℓ - 1) / K) + 3 * ((ℓ - 1) % K) + 2 * (ts.length * K) + 60 + 1 +
          ((paperFlags ts ℓ).length * 40 + 2 * (paperFlags ts ℓ).length + 10 + 1 +
            (40 * ((ℓ - 1) / K * (ts.length * K) + ts.length + ts.length * K + K + (ℓ - 1) % K * ts.length +
              (longs ts ℓ).length) + 400)))) := by
    refine s1.mono (fun τ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ => ?_) le_rfl
    have s2 := runs_topLoop (paperFlags ts ℓ) _ τ [] [] h7 h6 h8 (by rw [h11, hTop]; rfl) h9 h10
    rw [paperFlags_count, hlen] at s2
    refine s2.mono (fun τ' e => ?_) le_rfl
    rw [e]
    have htop := topWords_paper ts ℓ K
    have hT0e : T0v = ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) + (longs ts ℓ).length - 1 := by
      rw [hT0v]; congr 1; ring
    have hA0e : (ℓ - 1) / K * (ts.length * K) + ts.length - 1 = ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) := by
      have : (ℓ - 1) / K * (ts.length * K) = ts.length * ((ℓ - 1) / K) * K := by ring
      omega
    have hB0e : ts.length * K - K = (ts.length - 1) * K := by rw [Nat.sub_mul, one_mul]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · tsimp [h1]
    · tsimp [h2]
    · tsimp [h3]
    · tsimp [h4, hA0e]
    · tsimp [h5, hB0e]
    · tsimp [hT0e, htop]
  refine (Runs.seq key).mono (fun τ h => h) ?_
  unfold constsTopCost
  rw [← hT0v, hlen]

theorem ticks_rev (n : ℕ) (L : List (List Bool)) :
    (⟨[], (List.replicate n [] ++ L).reverse⟩ : WTape) = ⟨[], L.reverse ++ List.replicate n []⟩ := by simp

end SigmaConstsTape

end IntegerMultBounds.Schoenhage
