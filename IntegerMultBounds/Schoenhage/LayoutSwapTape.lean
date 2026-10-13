module

public import IntegerMultBounds.Schoenhage.LayoutSwapScan
public import IntegerMultBounds.Schoenhage.LayoutScriptTape
public import IntegerMultBounds.Schoenhage.SigmaConstsTape

/-! The chunk exchanges of the §6 layout script on tapes. The unsettled suffix of
the arrangement sits on `xA` as unary words, position `k` on `xK`. One step reads
the head `a`: when `a = k` the suffix just loses its head; otherwise one pass over
the rest replaces the word of block `k` by `a`, counting `γ = i K` words before it
and `ρ` after it, and the exchange's forward and undo records are written
(`runs_step`). The steps follow the suffix scan `selS` (`runs_exLoop`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Resampling Script TwistDescriptors LayoutScriptTape LayoutScript

namespace LayoutSwapTape

/-! ### The bank -/

/-- The forward script, accumulated reversed. -/
abbrev xO : Fin 18 := 0
/-- The undo script, each record's words accumulated in reverse. -/
abbrev xU : Fin 18 := 1
/-- The unsettled suffix. -/
abbrev xA : Fin 18 := 2
/-- The rebuilt rest. -/
abbrev xB : Fin 18 := 3
/-- The position `k` of the head. -/
abbrev xK : Fin 18 := 4
/-- `ones K`. -/
abbrev xKK : Fin 18 := 5
/-- `ones (n - 2K)`. -/
abbrev xN : Fin 18 := 6
/-- `bin R`. -/
abbrev xBR : Fin 18 := 7
/-- `bin K`. -/
abbrev xBK : Fin 18 := 8
/-- A test flag. -/
abbrev xF : Fin 18 := 9
/-- The head `a`. -/
abbrev xS : Fin 18 := 10
/-- Whether block `k` was found in the pass. -/
abbrev xFd : Fin 18 := 11
/-- `γ`. -/
abbrev xG : Fin 18 := 12
/-- `ρ`. -/
abbrev xR : Fin 18 := 13
/-- Scratch. -/
abbrev xT : Fin 18 := 14
/-- The junk tape. -/
abbrev xJ : Fin 18 := 15
/-- `ones 1`. -/
abbrev xOne : Fin 18 := 16
/-- The exponent of the record's `P`. -/
abbrev xP : Fin 18 := 17

/-- The bank: the outputs, the suffix tape, the rebuilt rest, `k`, the constants, the flag and
counter tapes. -/
def xbank (R nK K : ℕ) (O U A B : WTape) (k : ℕ) (F S Fd G Rr P : WTape) : Fin 18 → WTape :=
  fun i => match i.val with
  | 0 => O | 1 => U | 2 => A | 3 => B | 4 => endv k | 5 => reg (ones K) | 6 => reg (ones nK)
  | 7 => reg (bin R) | 8 => reg (bin K) | 9 => F | 10 => S | 11 => Fd | 12 => G | 13 => Rr
  | 16 => reg (ones 1) | 17 => P
  | _ => emp

/-! ### The head test -/

/-- Copy the head to `xS` and test `k < a`. -/
noncomputable def headTest : Cmd 0 18 :=
  .seq (cpy xA xS (by decide)) <| .seq (back xS) <| .seq (back xK) <|
  .seq (op1 geq false xS xK xF (by decide) (by decide) (by decide)) (rewind xF)

theorem output_geq_ones' (a k : ℕ) :
    output geq (ones a) (fun _ => ones k) = syms [[decide (k < a)]] := by
  rw [output_geq]; simp

set_option maxHeartbeats 8000000 in
theorem runs_headTest {R nK K : ℕ} {O U B Fd G Rr P : WTape} {k a : ℕ} {rest : List (List Bool)} :
    Runs headTest (xbank R nK K O U ⟨[], ones a :: rest⟩ B k emp emp Fd G Rr P)
      (· = xbank R nK K O U ⟨[ones a], rest⟩ B k (reg [decide (k < a)]) ⟨[ones a], []⟩ Fd G Rr P)
      (4 * a + 2 * k + 60) := by
  have t1 : time geq (ones a) (fun _ => ones k) ≤ a + k + 7 :=
    (time_le geq (ones a) (fun _ => ones k) k (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [headTest, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_back]
  tsimp [xbank, endv, emp, reg, Rules.output_copy, output_geq_ones']
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · simp [time_copy] at t1 ⊢; omega

/-! ### One word of the pass -/

/-- A word other than block `k`: copy it and count it before or after the found word. -/
noncomputable def keepWord : Cmd 0 18 :=
  .seq (cpy xA xB (by decide)) (.cond xFd (addTo' xKK xR (by decide)) (addTo' xKK xG (by decide)))
where
  /-- Add the constant on `s` to the value on `d`. -/
  addTo' (s d : Fin 18) (h : s ≠ d) : Cmd 0 18 := .seq (op0 Rules.copy true s d h) (rewind s)

/-- Block `k`: write `a` instead and mark it found. -/
noncomputable def foundWord : Cmd 0 18 :=
  .seq (skp xA xJ (by decide)) <| .seq (back xS) <| .seq (cpy xS xB (by decide)) <|
  .seq (clear xFd) <| .seq (emit [[true]] xFd) (rewind xFd)

/-- Test the current word against `k`, leaving the head on it. -/
noncomputable def passTest : Cmd 0 18 :=
  .seq (back xK) <| .seq (op1 geq false xA xK xF (by decide) (by decide) (by decide)) <|
  .seq (rewind xF) (back xA)

/-- One word of the pass: test it against `k`, then keep it or replace it. -/
noncomputable def passBody : Cmd 0 18 := .seq passTest <| .seq (.cond xF keepWord foundWord) (clear xF)

set_option maxHeartbeats 4000000 in
theorem runs_addTo' {s d : Fin 18} (h : s ≠ d) {c v : ℕ} (σ : Fin 18 → WTape) (hs : σ s = reg (ones c))
    (hd : σ d = endv v) :
    Runs (keepWord.addTo' s d h) σ (· = Function.update σ d (endv (v + c))) (2 * c + 10) := by
  apply Runs.of_wp
  simp only [keepWord.addTo', WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h, ↓reduceIte, endv, reg, WTape.next_mk,
    WTape.cur_mk, List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [ones_append', WTape.put, reg, endv]
  · simp [time_copy]; omega

set_option maxHeartbeats 8000000 in
theorem runs_passTest {R nK K : ℕ} {O U : WTape} {LB : List (List Bool)} {S Fd G Rr P : WTape} {k w : ℕ}
    {LA Q : List (List Bool)} :
    Runs passTest (xbank R nK K O U ⟨LA, ones w :: Q⟩ ⟨LB, []⟩ k emp S Fd G Rr P)
      (· = xbank R nK K O U ⟨LA, ones w :: Q⟩ ⟨LB, []⟩ k (reg [decide (k < w)]) S Fd G Rr P)
      (4 * w + 2 * k + 60) := by
  have t1 : time geq (ones w) (fun _ => ones k) ≤ w + k + 7 :=
    (time_le geq (ones w) (fun _ => ones k) k (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [passTest, WP, wp_op1, wp_rewind, wp_back]
  tsimp [xbank, endv, emp, reg, output_geq_ones']
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · omega

set_option maxHeartbeats 8000000 in
theorem runs_keepWord {R nK K : ℕ} {O U : WTape} {LB : List (List Bool)} {k w a g ρ : ℕ} (found : Bool)
    {LA Q : List (List Bool)} :
    Runs keepWord (xbank R nK K O U ⟨LA, ones w :: Q⟩ ⟨LB, []⟩ k (reg [true]) ⟨[ones a], []⟩ (reg [found])
        (endv g) (endv ρ) emp)
      (· = xbank R nK K O U ⟨ones w :: LA, Q⟩ ⟨ones w :: LB, []⟩ k (reg [true]) ⟨[ones a], []⟩ (reg [found])
        (endv (if found then g else g + K)) (endv (if found then ρ + K else ρ)) emp)
      (w + 2 * K + 20) := by
  set σ := xbank R nK K O U ⟨LA, ones w :: Q⟩ ⟨LB, []⟩ k (reg [true]) ⟨[ones a], []⟩ (reg [found])
        (endv g) (endv ρ) emp with hσ
  have s1 := runs_cpy (a := 0) (show xA ≠ xB by decide) σ (by tsimp [hσ, xbank]) (by tsimp [hσ, xbank])
  set σ₁ := Function.update (Function.update σ xA (σ xA).next) xB ((σ xB).put false [(σ xA).cur]) with hσ₁
  cases found
  · have s2 := runs_addTo' (c := K) (v := g) (show xKK ≠ xG by decide) σ₁ (by tsimp [hσ₁, hσ, xbank])
      (by tsimp [hσ₁, hσ, xbank])
    refine (Runs.then s1 (Runs.cond_false (by tsimp [hσ₁, hσ, xbank, reg, startsOne_mk]) s2)).mono
      (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> rfl
    · tsimp [hσ, xbank, length_ones]; omega
  · have s2 := runs_addTo' (c := K) (v := ρ) (show xKK ≠ xR by decide) σ₁ (by tsimp [hσ₁, hσ, xbank])
      (by tsimp [hσ₁, hσ, xbank])
    refine (Runs.then s1 (Runs.cond_true (by tsimp [hσ₁, hσ, xbank, reg, startsOne_mk]) s2)).mono
      (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> rfl
    · tsimp [hσ, xbank, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_foundWord {R nK K : ℕ} {O U : WTape} {LB : List (List Bool)} {k w a : ℕ} {found : Bool} {G Rr : WTape}
    {LA Q : List (List Bool)} :
    Runs foundWord (xbank R nK K O U ⟨LA, ones w :: Q⟩ ⟨LB, []⟩ k (reg [false]) ⟨[ones a], []⟩ (reg [found])
        G Rr emp)
      (· = xbank R nK K O U ⟨ones w :: LA, Q⟩ ⟨ones a :: LB, []⟩ k (reg [false]) ⟨[ones a], []⟩ (reg [true])
        G Rr emp)
      (w + 2 * a + 40) := by
  apply Runs.of_wp
  simp only [foundWord, cpy, skp, WP, wp_op0, wp_rewind, wp_back, wp_clear, wp_emit]
  tsimp [xbank, endv, emp, reg, Rules.output_copy, Rules.output_skip]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · simp [time_copy, time_skip, clen, WTape.words, length_ones]
    omega

/-! ### The pass -/

/-- The bank during the pass: `LA` words passed, `Q` to come, the rebuilt words `LB`, the found flag and
the counters. -/
def passBank (R nK K : ℕ) (O U : WTape) (a k : ℕ) (LA : List (List Bool)) (Q : List ℕ)
    (LB : List (List Bool)) (found : Bool) (g ρ : ℕ) : Fin 18 → WTape :=
  xbank R nK K O U ⟨LA, Q.map ones⟩ ⟨LB, []⟩ k emp ⟨[ones a], []⟩ (reg [found]) (endv g) (endv ρ) emp

/-- The pass on words: keep every word but block `k`, which becomes `a`; count the words before and after it. -/
def passRun (k a K : ℕ) : List ℕ → List (List Bool) → Bool → ℕ → ℕ → List (List Bool) × Bool × ℕ × ℕ
  | [], LB, f, g, ρ => (LB, f, g, ρ)
  | w :: Q, LB, f, g, ρ =>
    if k < w then passRun k a K Q (ones w :: LB) f (if f then g else g + K) (if f then ρ + K else ρ)
    else passRun k a K Q (ones a :: LB) true g ρ

/-- The cost of one word of the pass. -/
def passCost (W K : ℕ) : ℕ := 10 * W + 2 * K + 160

set_option maxHeartbeats 8000000 in
theorem runs_passBody {R nK K W : ℕ} {O U : WTape} {a k w : ℕ} (hw : w ≤ W) (hk : k ≤ W) (ha : a ≤ W)
    {LA : List (List Bool)} {Q : List ℕ} {LB : List (List Bool)} {found : Bool} {g ρ : ℕ} :
    Runs passBody (passBank R nK K O U a k LA (w :: Q) LB found g ρ)
      (· = passBank R nK K O U a k (ones w :: LA) Q
        (passRun k a K [w] LB found g ρ).1 (passRun k a K [w] LB found g ρ).2.1
        (passRun k a K [w] LB found g ρ).2.2.1 (passRun k a K [w] LB found g ρ).2.2.2)
      (passCost W K) := by
  have s1 := runs_passTest (R := R) (nK := nK) (K := K) (O := O) (U := U) (LB := LB) (S := ⟨[ones a], []⟩)
    (Fd := reg [found]) (G := endv g) (Rr := endv ρ) (P := emp) (k := k) (w := w) (LA := LA) (Q := Q.map ones)
  by_cases hkw : k < w
  · have s2 := runs_keepWord (R := R) (nK := nK) (K := K) (O := O) (U := U) (LB := LB) (k := k) (w := w) (a := a)
      (g := g) (ρ := ρ) found (LA := LA) (Q := Q.map ones)
    set σ₂ := xbank R nK K O U ⟨ones w :: LA, Q.map ones⟩ ⟨ones w :: LB, []⟩ k (reg [true]) ⟨[ones a], []⟩
      (reg [found]) (endv (if found then g else g + K)) (endv (if found then ρ + K else ρ)) emp with hσ₂
    have s3 := runs_clear (a := 0) xF σ₂
    simp only [decide_eq_true hkw] at s1
    refine (Runs.then s1 (Runs.then (Runs.cond_true (by simp [xbank, reg, startsOne_mk]) s2) s3)).mono
      (fun τ e => ?_) ?_
    · rw [e]; simp only [passRun, hkw, ↓reduceIte, passBank]; funext i; fin_cases i <;> rfl
    · simp [hσ₂, xbank, reg, clen, WTape.words, passCost]; omega
  · have s2 := runs_foundWord (R := R) (nK := nK) (K := K) (O := O) (U := U) (LB := LB) (k := k) (w := w) (a := a)
      (found := found) (G := endv g) (Rr := endv ρ) (LA := LA) (Q := Q.map ones)
    set σ₂ := xbank R nK K O U ⟨ones w :: LA, Q.map ones⟩ ⟨ones a :: LB, []⟩ k (reg [false]) ⟨[ones a], []⟩
      (reg [true]) (endv g) (endv ρ) emp with hσ₂
    have s3 := runs_clear (a := 0) xF σ₂
    simp only [decide_eq_false hkw] at s1
    refine (Runs.then s1 (Runs.then (Runs.cond_false (by simp [xbank, reg, startsOne_mk]) s2) s3)).mono
      (fun τ e => ?_) ?_
    · rw [e]; simp only [passRun, hkw, ↓reduceIte, passBank]; funext i; fin_cases i <;> rfl
    · simp [hσ₂, xbank, reg, clen, WTape.words, passCost]; omega

set_option maxHeartbeats 8000000 in
/-- `runs_pass`: the pass over the rest of the suffix. -/
theorem runs_pass {R nK K W : ℕ} {O U : WTape} {a k : ℕ} (hk : k ≤ W) (ha : a ≤ W) :
    ∀ (Q : List ℕ) (LA LB : List (List Bool)) (found : Bool) (g ρ : ℕ), (∀ w ∈ Q, w ≤ W) →
      Runs (.loop xA passBody) (passBank R nK K O U a k LA Q LB found g ρ)
        (· = passBank R nK K O U a k ((Q.map ones).reverse ++ LA) []
          (passRun k a K Q LB found g ρ).1 (passRun k a K Q LB found g ρ).2.1
          (passRun k a K Q LB found g ρ).2.2.1 (passRun k a K Q LB found g ρ).2.2.2)
        (Q.length * (passCost W K + 2))
  | [], LA, LB, found, g, ρ, _ => by
    refine (Runs.loop_done (by simp [passBank, xbank]) rfl).mono (fun τ e => ?_) (by simp)
    rw [← e]; rfl
  | w :: Q, LA, LB, found, g, ρ, hW => by
    have s1 := runs_passBody (R := R) (nK := nK) (K := K) (O := O) (U := U) (a := a) (k := k) (w := w)
      (hW w (by simp)) hk ha (LA := LA) (Q := Q) (LB := LB) (found := found) (g := g) (ρ := ρ)
    have ih := runs_pass (R := R) (nK := nK) (K := K) (O := O) (U := U) hk ha Q (ones w :: LA)
      (passRun k a K [w] LB found g ρ).1 (passRun k a K [w] LB found g ρ).2.1
      (passRun k a K [w] LB found g ρ).2.2.1 (passRun k a K [w] LB found g ρ).2.2.2
      (fun v hv => hW v (by simp [hv]))
    refine (Runs.loop_step (by simp [passBank, xbank]) (s1.mono (fun τ e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ e => ?_) ?_
    · rw [e]
      have hrun : passRun k a K (w :: Q) LB found g ρ = passRun k a K Q (passRun k a K [w] LB found g ρ).1
          (passRun k a K [w] LB found g ρ).2.1 (passRun k a K [w] LB found g ρ).2.2.1
          (passRun k a K [w] LB found g ρ).2.2.2 := by
        by_cases hkw : k < w <;> simp [passRun, hkw]
      rw [hrun]
      simp [List.map_cons, List.reverse_cons, List.append_assoc]
    · simp only [List.length_cons]; rw [Nat.succ_mul]; omega

theorem set_append_single_of_ne {P : List ℕ} {i c : ℕ} (hc : P.length = c) (hic : i ≠ c) (w a : ℕ) :
    (P ++ [w]).set i a = P.set i a ++ [w] := by
  rcases Nat.lt_or_gt_of_ne hic with h | h
  · rw [List.set_append_left _ _ (by omega)]
  · rw [List.set_append_right _ _ (by omega), List.set_eq_of_length_le (by simp; omega),
      List.set_eq_of_length_le (l := P) (by omega)]

/-- `passRun_split`: the pass from a processed prefix `P` of `rest`. -/
theorem passRun_split {k a K : ℕ} {rest : List ℕ} (hge : ∀ x ∈ rest, k ≤ x) (hnd : rest.Nodup) :
    ∀ (Q P : List ℕ), P ++ Q = rest →
      passRun k a K Q (((P.set (rest.idxOf k) a).map ones).reverse) (decide (rest.idxOf k < P.length))
        (min P.length (rest.idxOf k) * K) ((P.length - rest.idxOf k - 1) * K) =
      (((rest.set (rest.idxOf k) a).map ones).reverse, decide (rest.idxOf k < rest.length),
        min rest.length (rest.idxOf k) * K, (rest.length - rest.idxOf k - 1) * K)
  | [], P, hP => by simp only [List.append_nil] at hP; subst hP; rfl
  | w :: Q, P, hP => by
    set i := rest.idxOf k with hi
    have hwm : w ∈ rest := by rw [← hP]; simp
    have hkw' := hge w hwm
    have hstep := passRun_split (a := a) (K := K) hge hnd Q (P ++ [w]) (by rw [← hP]; simp)
    rw [← hstep]
    simp only [passRun]
    by_cases hkw : k < w
    · have hic : i ≠ P.length := by
        rw [hi, ← hP]
        by_cases hkP : k ∈ P
        · rw [List.idxOf_append_of_mem hkP]; exact (List.idxOf_lt_length_of_mem hkP).ne
        · rw [List.idxOf_append_of_notMem hkP, List.idxOf_cons_ne _ (by omega)]; omega
      simp only [hkw, ↓reduceIte]
      rw [set_append_single_of_ne rfl hic]
      simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons, List.map_nil,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      by_cases hil : i < P.length
      · have e1 : decide (i < P.length) = true := decide_eq_true hil
        have e2 : decide (i < P.length + 1) = true := decide_eq_true (by omega)
        rw [e1, e2]
        simp only [↓reduceIte]
        congr 2
        · rw [min_eq_right (by omega), min_eq_right (by omega)]
        · rw [show P.length + 1 - i - 1 = P.length - i - 1 + 1 by omega, Nat.add_mul, one_mul]
      · have e1 : decide (i < P.length) = false := decide_eq_false hil
        have e2 : decide (i < P.length + 1) = false := decide_eq_false (by omega)
        rw [e1, e2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        congr 2
        · rw [min_eq_left (by omega), min_eq_left (by omega), Nat.add_mul, one_mul]
        · rw [show P.length - i - 1 = 0 by omega, show P.length + 1 - i - 1 = 0 by omega]
    · have hwk : w = k := by omega
      subst hwk
      have hik : i = P.length := by
        rw [hi, ← hP, List.idxOf_append_of_notMem, List.idxOf_cons_self, add_zero]
        intro hmem
        rw [← hP] at hnd
        exact (List.nodup_append.mp hnd).2.2 _ hmem _ (by simp) rfl
      have hset : (P ++ [w]).set P.length a = P ++ [a] := by
        rw [List.set_append_right _ _ (le_refl _), Nat.sub_self]; simp
      simp only [hkw, ↓reduceIte]
      rw [← hi, hik, hset, List.set_eq_of_length_le (le_refl _)]
      simp

/-- `passRun_eq`: the pass over the rest of the suffix replaces block `k` by `a` and counts `i K` words
before it and `(|rest| - 1 - i) K` after it, `i` its index. -/
theorem passRun_eq {k a K : ℕ} {rest : List ℕ} (hge : ∀ x ∈ rest, k ≤ x) (hnd : rest.Nodup) :
    passRun k a K rest [] false 0 0 =
      (((rest.set (rest.idxOf k) a).map ones).reverse, decide (rest.idxOf k < rest.length),
        min rest.length (rest.idxOf k) * K, (rest.length - rest.idxOf k - 1) * K) := by
  have := passRun_split (a := a) (K := K) hge hnd rest [] rfl
  simpa using this

/-! ### The records -/

/-- Subtract the counter on `X` from `xP`. -/
noncomputable def subX (X : Fin 18) (h1 : xP ≠ X) (h2 : X ≠ xT) : Cmd 0 18 :=
  .seq (rewind X) <| .seq (rewind xP) <| .seq (op1 Rules.drop false xP X xT h1 (by decide) h2) <|
  .seq (clear xP) <| .seq (rewind xT) <| .seq (cpy xT xP (by decide)) (clear xT)

/-- `P = (n - 2K) - γ - ρ` into `xP`. -/
noncomputable def pCalcX : Cmd 0 18 :=
  .seq (cpy xN xP (by decide)) <| .seq (rewind xN) <| .seq (subX xG (by decide) (by decide))
    (subX xR (by decide) (by decide))

/-- The exchange's forward words onto `xO`. -/
noncomputable def emitFwdX : Cmd 0 18 :=
  .seq (emit [[false]] xO) <|
  .seq (rewind xP) <| .seq (op0 fillOne false xP xO (by decide)) <|
  .seq (rewind xG) <| .seq (op0 fillOne false xG xO (by decide)) <|
  .seq (rewind xR) <| .seq (op0 (Rules.fill false) false xR xO (by decide)) <|
  .seq (op0 Rules.copy true xBR xO (by decide)) <| .seq (rewind xBR) <|
  .seq (cpy xBK xO (by decide)) <| .seq (rewind xBK) <|
  .seq (cpy xBK xO (by decide)) (rewind xBK)

/-- The undo record's words onto `xU`, last word first. -/
noncomputable def emitUndoX : Cmd 0 18 :=
  .seq (cpy xBK xU (by decide)) <| .seq (rewind xBK) <|
  .seq (cpy xBK xU (by decide)) <| .seq (rewind xBK) <|
  .seq (rewind xR) <| .seq (op0 (Rules.fill false) false xR xU (by decide)) <|
  .seq (op0 Rules.copy true xBR xU (by decide)) <| .seq (rewind xBR) <|
  .seq (rewind xG) <| .seq (op0 fillOne false xG xU (by decide)) <|
  .seq (rewind xP) <| .seq (op0 fillOne false xP xU (by decide)) (emit [[false]] xU)

/-- Reset the counters and the found flag. -/
noncomputable def resetX : Cmd 0 18 :=
  .seq (clear xG) <| .seq (emit [[]] xG) <| .seq (clear xR) <| .seq (emit [[]] xR) <| .seq (clear xP) <|
  .seq (clear xFd) <| .seq (emit [[false]] xFd) (rewind xFd)

set_option maxHeartbeats 8000000 in
theorem runs_pCalcX {R nK K : ℕ} {O U A B F S Fd : WTape} {k g ρ : ℕ} :
    Runs pCalcX (xbank R nK K O U A B k F S Fd (endv g) (endv ρ) emp)
      (· = xbank R nK K O U A B k F S Fd (endv g) (endv ρ) (endv (nK - g - ρ)))
      (30 * nK + 8 * g + 8 * ρ + 300) := by
  have t1 : time Rules.drop (List.replicate nK true) (fun _ => List.replicate g true) ≤ nK + g + 6 :=
    (time_le Rules.drop (ones nK) (fun _ => ones g) g (fun _ => by simp)).trans (by simp)
  have t2 : time Rules.drop (List.replicate (nK - g) true) (fun _ => List.replicate ρ true) ≤ nK - g + ρ + 6 :=
    (time_le Rules.drop (ones (nK - g)) (fun _ => ones ρ) ρ (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [pCalcX, subX, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [xbank, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 8000000 in
theorem runs_emitFwdX {R nK K : ℕ} (hR0 : 0 < R) {O : List (List Bool)} {U A B F S Fd : WTape} {k g ρ P : ℕ} :
    Runs emitFwdX (xbank R nK K ⟨O, []⟩ U A B k F S Fd (endv g) (endv ρ) (endv P))
      (· = xbank R nK K ⟨(swapWords R P g ρ K K).reverse ++ O, []⟩ U A B k F S Fd (endv g) (endv ρ) (endv P))
      (4 * (P + g + ρ + (bin R).length + (bin K).length) + 160) := by
  have hbR : bin R ≠ [] := by
    intro h; have := value_bin R; rw [h] at this; simp [Counter.value] at this; omega
  have hpm : ∀ x, bin (2 ^ x * R) = List.replicate x false ++ bin R := fun x => bin_two_pow_mul x R hR0
  apply Runs.of_wp
  simp only [emitFwdX, cpy, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [xbank, endv, reg, Rules.output_copy, output_fillOne, Rules.output_fill, hbR]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, reg, swapWords, bin_two_pow, hpm, WTape.put]
  · simp [time_copy, time_fillOne, time_fill, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_emitUndoX {R nK K : ℕ} (hR0 : 0 < R) {U : List (List Bool)} {O A B F S Fd : WTape} {k g ρ P : ℕ} :
    Runs emitUndoX (xbank R nK K O ⟨U, []⟩ A B k F S Fd (endv g) (endv ρ) (endv P))
      (· = xbank R nK K O ⟨swapWords R P g ρ K K ++ U, []⟩ A B k F S Fd (endv g) (endv ρ) (endv P))
      (4 * (P + g + ρ + (bin R).length + (bin K).length) + 160) := by
  have hbR : bin R ≠ [] := by
    intro h; have := value_bin R; rw [h] at this; simp [Counter.value] at this; omega
  have hpm : ∀ x, bin (2 ^ x * R) = List.replicate x false ++ bin R := fun x => bin_two_pow_mul x R hR0
  apply Runs.of_wp
  simp only [emitUndoX, cpy, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [xbank, endv, reg, Rules.output_copy, output_fillOne, Rules.output_fill, hbR]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, reg, swapWords, bin_two_pow, hpm, WTape.put]
  · simp [time_copy, time_fillOne, time_fill, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_resetX {R nK K : ℕ} {O U A B F S : WTape} {k g ρ P : ℕ} {f : Bool} :
    Runs resetX (xbank R nK K O U A B k F S (reg [f]) (endv g) (endv ρ) (endv P))
      (· = xbank R nK K O U A B k F S (reg [false]) (endv 0) (endv 0) emp)
      (2 * g + 2 * ρ + 2 * P + 40) := by
  apply Runs.of_wp
  simp only [resetX, WP, wp_rewind, wp_clear, wp_emit]
  tsimp [xbank, endv, reg, emp]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · simp [clen, WTape.words, length_ones]; omega

/-! ### One step -/

/-- No exchange: pass the rest over unchanged. -/
noncomputable def skipBody : Cmd 0 18 := .seq (clear xF) (appendAll xA xB (by decide))

/-- An exchange: the pass, then the record's words. -/
noncomputable def exchBody : Cmd 0 18 :=
  .seq (clear xF) <| .seq (.loop xA passBody) <| .seq pCalcX <| .seq emitFwdX <| .seq emitUndoX resetX

/-- Put the rebuilt rest back on the suffix tape. -/
noncomputable def rebuild : Cmd 0 18 :=
  .seq (clear xA) <| .seq (rewind xB) <| .seq (appendAll xB xA (by decide)) <| .seq (rewind xA) (clear xB)

/-- One step of the scan. -/
noncomputable def step : Cmd 0 18 :=
  .seq headTest <| .seq (.cond xF exchBody skipBody) <| .seq rebuild <| .seq (clear xS)
    (keepWord.addTo' xOne xK (by decide))

theorem clen_ones_le {W : ℕ} : ∀ (L : List ℕ), (∀ x ∈ L, x ≤ W) → clen (L.map ones) ≤ L.length * (W + 1)
  | [], _ => by simp
  | x :: L, h => by
    have := clen_ones_le L (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [clen, List.map_cons, List.map_map, List.sum_cons, List.length_cons] at this ⊢
    simp only [Function.comp_def, length_ones] at this ⊢
    nlinarith

theorem clen_reverse (L : List (List Bool)) : clen L.reverse = clen L := by
  simp [clen, List.map_reverse, List.sum_reverse]

theorem clen_append (L M : List (List Bool)) : clen (L ++ M) = clen L + clen M := by
  simp [clen, List.map_append, List.sum_append]

set_option maxHeartbeats 8000000 in
theorem runs_rebuild {R nK K W : ℕ} {O U F S Fd G Rr P : WTape} {k : ℕ} {LA : List (List Bool)} {LB : List ℕ}
    (hW : ∀ x ∈ LB, x ≤ W) :
    Runs rebuild (xbank R nK K O U ⟨LA, []⟩ ⟨(LB.map ones).reverse, []⟩ k F S Fd G Rr P)
      (· = xbank R nK K O U ⟨[], LB.map ones⟩ emp k F S Fd G Rr P)
      (2 * clen LA + LB.length * (5 * W + 13) + 20) := by
  set σ := xbank R nK K O U ⟨LA, []⟩ ⟨(LB.map ones).reverse, []⟩ k F S Fd G Rr P with hσ
  have s1 := runs_clear (a := 0) xA σ
  set σ₁ := Function.update σ xA ⟨[], []⟩ with hσ₁
  have s2 := runs_rewind (a := 0) xB σ₁
  set σ₂ := Function.update σ₁ xB ⟨[], (σ₁ xB).left.reverse ++ (σ₁ xB).right⟩ with hσ₂
  have hB2 : σ₂ xB = ⟨[], LB.map ones⟩ := by tsimp [hσ₂, hσ₁, hσ, xbank]
  have s3 := runs_appendAll (a := 0) (show xB ≠ xA by decide) W (LB.map ones) σ₂ [] [] hB2
    (by tsimp [hσ₂, hσ₁, hσ, xbank]) (by
      intro w hw; simp only [List.mem_map] at hw; obtain ⟨x, hx, rfl⟩ := hw; simpa using hW x hx)
  set σ₃ := Function.update (Function.update σ₂ xB ⟨(LB.map ones).reverse ++ [], []⟩) xA
    ⟨(LB.map ones).reverse ++ [], []⟩ with hσ₃
  have s4 := runs_rewind (a := 0) xA σ₃
  set σ₄ := Function.update σ₃ xA ⟨[], (σ₃ xA).left.reverse ++ (σ₃ xA).right⟩ with hσ₄
  have s5 := runs_clear (a := 0) xB σ₄
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, xbank, emp]
  · have hc := clen_ones_le LB hW
    have e1 : clen (σ xA).words = clen LA := by tsimp [hσ, xbank, WTape.words, clen_reverse]
    have e2 : clen (σ₁ xB).left = clen (LB.map ones) := by
      tsimp [hσ₁, hσ, xbank, clen_reverse]
    have e3 : clen (σ₃ xA).left = clen (LB.map ones) := by
      tsimp [hσ₃, clen_reverse]
    have e4 : clen (σ₄ xB).words = clen (LB.map ones) := by
      tsimp [hσ₄, hσ₃, WTape.words, clen_reverse]
    rw [e1, e2, e3, e4, List.length_map]
    nlinarith

set_option maxHeartbeats 8000000 in
theorem runs_skipBody {R nK K W : ℕ} {O U S Fd G Rr P : WTape} {k : ℕ} {LA : List (List Bool)} {rest : List ℕ}
    (hW : ∀ x ∈ rest, x ≤ W) :
    Runs skipBody (xbank R nK K O U ⟨LA, rest.map ones⟩ emp k (reg [false]) S Fd G Rr P)
      (· = xbank R nK K O U ⟨(rest.map ones).reverse ++ LA, []⟩ ⟨(rest.map ones).reverse, []⟩ k emp S Fd G Rr P)
      (rest.length * (W + 8) + 10) := by
  set σ := xbank R nK K O U ⟨LA, rest.map ones⟩ emp k (reg [false]) S Fd G Rr P with hσ
  have s1 := runs_clear (a := 0) xF σ
  set σ₁ := Function.update σ xF ⟨[], []⟩ with hσ₁
  have s2 := runs_appendAll (a := 0) (show xA ≠ xB by decide) W (rest.map ones) σ₁ LA []
    (by tsimp [hσ₁, hσ, xbank]) (by tsimp [hσ₁, hσ, xbank, emp])
    (by intro w hw; simp only [List.mem_map] at hw; obtain ⟨x, hx, rfl⟩ := hw; simpa using hW x hx)
  refine (Runs.then s1 s2).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hσ, xbank, emp]
  · tsimp [hσ, xbank, reg, clen, WTape.words]; omega

theorem passRun_le (k a K : ℕ) : ∀ (Q : List ℕ) (LB : List (List Bool)) (f : Bool) (g ρ : ℕ),
    (passRun k a K Q LB f g ρ).2.2.1 ≤ g + Q.length * K ∧ (passRun k a K Q LB f g ρ).2.2.2 ≤ ρ + Q.length * K
  | [], _, _, _, _ => by simp [passRun]
  | w :: Q, LB, f, g, ρ => by
    simp only [passRun]
    split_ifs
    · have := passRun_le k a K Q (ones w :: LB) f g (ρ + K); simp only [List.length_cons]; constructor <;> nlinarith
    · have := passRun_le k a K Q (ones w :: LB) f (g + K) ρ; simp only [List.length_cons]; constructor <;> nlinarith
    · have := passRun_le k a K Q (ones a :: LB) true g ρ; simp only [List.length_cons]; constructor <;> nlinarith

/-- The cost of an exchange. -/
def exchCost (W K nK R : ℕ) : ℕ :=
  W * (passCost W K + 2) + 50 * nK + 60 * (W * K) + 8 * ((bin R).length + (bin K).length) + 1000

set_option maxHeartbeats 8000000 in
theorem runs_exchBody {R nK K W : ℕ} (hR0 : 0 < R) {O U : List (List Bool)} {a k : ℕ} {rest : List ℕ}
    (hk : k ≤ W) (ha : a ≤ W) (hW : ∀ x ∈ rest, x ≤ W) (hlen : rest.length ≤ W) :
    Runs exchBody (xbank R nK K ⟨O, []⟩ ⟨U, []⟩ ⟨[ones a], rest.map ones⟩ emp k (reg [true]) ⟨[ones a], []⟩
        (reg [false]) (endv 0) (endv 0) emp)
      (· = xbank R nK K
        ⟨(swapWords R (nK - (passRun k a K rest [] false 0 0).2.2.1 - (passRun k a K rest [] false 0 0).2.2.2)
          (passRun k a K rest [] false 0 0).2.2.1 (passRun k a K rest [] false 0 0).2.2.2 K K).reverse ++ O, []⟩
        ⟨swapWords R (nK - (passRun k a K rest [] false 0 0).2.2.1 - (passRun k a K rest [] false 0 0).2.2.2)
          (passRun k a K rest [] false 0 0).2.2.1 (passRun k a K rest [] false 0 0).2.2.2 K K ++ U, []⟩
        ⟨(rest.map ones).reverse ++ [ones a], []⟩ ⟨(passRun k a K rest [] false 0 0).1, []⟩ k emp
        ⟨[ones a], []⟩ (reg [false]) (endv 0) (endv 0) emp)
      (exchCost W K nK R) := by
  set pr := passRun k a K rest [] false 0 0 with hpr
  obtain ⟨hg, hρ⟩ := passRun_le k a K rest [] false 0 0
  rw [← hpr] at hg hρ
  set σ := xbank R nK K ⟨O, []⟩ ⟨U, []⟩ ⟨[ones a], rest.map ones⟩ emp k (reg [true]) ⟨[ones a], []⟩
        (reg [false]) (endv 0) (endv 0) emp with hσ
  have s1 := runs_clear (a := 0) xF σ
  have s2 := runs_pass (R := R) (nK := nK) (K := K) (W := W) (O := ⟨O, []⟩) (U := ⟨U, []⟩) (a := a) (k := k) hk ha
    rest [ones a] [] false 0 0 hW
  rw [← hpr] at s2
  have s3 := runs_pCalcX (R := R) (nK := nK) (K := K) (O := ⟨O, []⟩) (U := ⟨U, []⟩)
    (A := ⟨(rest.map ones).reverse ++ [ones a], []⟩) (B := ⟨pr.1, []⟩) (F := emp) (S := ⟨[ones a], []⟩)
    (Fd := reg [pr.2.1]) (k := k) (g := pr.2.2.1) (ρ := pr.2.2.2)
  have s4 := runs_emitFwdX (R := R) (nK := nK) (K := K) hR0 (O := O) (U := ⟨U, []⟩)
    (A := ⟨(rest.map ones).reverse ++ [ones a], []⟩) (B := ⟨pr.1, []⟩) (F := emp) (S := ⟨[ones a], []⟩)
    (Fd := reg [pr.2.1]) (k := k) (g := pr.2.2.1) (ρ := pr.2.2.2) (P := nK - pr.2.2.1 - pr.2.2.2)
  have s5 := runs_emitUndoX (R := R) (nK := nK) (K := K) hR0 (U := U)
    (O := ⟨(swapWords R (nK - pr.2.2.1 - pr.2.2.2) pr.2.2.1 pr.2.2.2 K K).reverse ++ O, []⟩)
    (A := ⟨(rest.map ones).reverse ++ [ones a], []⟩) (B := ⟨pr.1, []⟩) (F := emp) (S := ⟨[ones a], []⟩)
    (Fd := reg [pr.2.1]) (k := k) (g := pr.2.2.1) (ρ := pr.2.2.2) (P := nK - pr.2.2.1 - pr.2.2.2)
  have s6 := runs_resetX (R := R) (nK := nK) (K := K)
    (O := ⟨(swapWords R (nK - pr.2.2.1 - pr.2.2.2) pr.2.2.1 pr.2.2.2 K K).reverse ++ O, []⟩)
    (U := ⟨swapWords R (nK - pr.2.2.1 - pr.2.2.2) pr.2.2.1 pr.2.2.2 K K ++ U, []⟩)
    (A := ⟨(rest.map ones).reverse ++ [ones a], []⟩) (B := ⟨pr.1, []⟩) (F := emp) (S := ⟨[ones a], []⟩)
    (k := k) (g := pr.2.2.1) (ρ := pr.2.2.2) (P := nK - pr.2.2.1 - pr.2.2.2) (f := pr.2.1)
  have e1 : Function.update σ xF ⟨[], []⟩ = passBank R nK K ⟨O, []⟩ ⟨U, []⟩ a k [ones a] rest [] false 0 0 := by
    funext i; fin_cases i <;> rfl
  rw [e1] at s1
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun τ e => by rw [e]) ?_
  have hp1 : rest.length * (passCost W K + 2) ≤ W * (passCost W K + 2) := Nat.mul_le_mul_right _ hlen
  have hgK : pr.2.2.1 ≤ W * K := by
    have : rest.length * K ≤ W * K := Nat.mul_le_mul_right _ hlen
    simp at hg; omega
  have hρK : pr.2.2.2 ≤ W * K := by
    have : rest.length * K ≤ W * K := Nat.mul_le_mul_right _ hlen
    simp at hρ; omega
  have hPn : nK - pr.2.2.1 - pr.2.2.2 ≤ nK := by omega
  simp only [hσ, xbank, reg, clen, WTape.words, exchCost]
  simp
  omega

/-! ### The step -/

/-- The bank between steps: outputs `O`, `U`, the suffix `S`, the position `k`. -/
def stBank (R nK K : ℕ) (O U : List (List Bool)) (S : List ℕ) (k : ℕ) : Fin 18 → WTape :=
  xbank R nK K ⟨O, []⟩ ⟨U, []⟩ ⟨[], S.map ones⟩ emp k emp emp (reg [false]) (endv 0) (endv 0) emp

/-- One step of the scan on the outputs and the suffix. -/
def exStep (R nK K : ℕ) (O U : List (List Bool)) (a k : ℕ) (rest : List ℕ) :
    List (List Bool) × List (List Bool) × List ℕ :=
  if a = k then (O, U, rest) else
    ((swapWords R (nK - rest.idxOf k * K - (rest.length - rest.idxOf k - 1) * K) (rest.idxOf k * K)
        ((rest.length - rest.idxOf k - 1) * K) K K).reverse ++ O,
      swapWords R (nK - rest.idxOf k * K - (rest.length - rest.idxOf k - 1) * K) (rest.idxOf k * K)
        ((rest.length - rest.idxOf k - 1) * K) K K ++ U,
      rest.set (rest.idxOf k) a)

/-- The cost of one step. -/
def stepCost (W K nK R : ℕ) : ℕ := exchCost W K nK R + 8 * (W + 1) * (W + 13) + 100

set_option maxHeartbeats 8000000 in
theorem runs_step {R nK K W : ℕ} (hR0 : 0 < R) {O U : List (List Bool)} {a k : ℕ} {rest : List ℕ}
    (hka : k ≤ a) (hge : ∀ x ∈ rest, k ≤ x) (hnd : (a :: rest).Nodup) (hk : k ≤ W) (ha : a ≤ W)
    (hW : ∀ x ∈ rest, x ≤ W) (hlen : rest.length ≤ W) :
    Runs step (stBank R nK K O U (a :: rest) k)
      (· = stBank R nK K (exStep R nK K O U a k rest).1 (exStep R nK K O U a k rest).2.1
        (exStep R nK K O U a k rest).2.2 (k + 1))
      (stepCost W K nK R) := by
  have s1 := runs_headTest (R := R) (nK := nK) (K := K) (O := ⟨O, []⟩) (U := ⟨U, []⟩) (B := emp)
    (Fd := reg [false]) (G := endv 0) (Rr := endv 0) (P := emp) (k := k) (a := a) (rest := rest.map ones)
  have hcl : clen ((rest.map ones).reverse ++ [ones a]) ≤ (W + 1) * (W + 1) := by
    have h1 := clen_ones_le rest hW
    have h2 : clen [ones a] = a + 1 := by simp [clen, length_ones]
    rw [clen_append, clen_reverse, h2]
    nlinarith
  by_cases hak : a = k
  · subst hak
    have hd : decide (a < a) = false := decide_eq_false (lt_irrefl a)
    rw [hd] at s1
    have s2 := runs_skipBody (R := R) (nK := nK) (K := K) (W := W) (O := ⟨O, []⟩) (U := ⟨U, []⟩)
      (S := ⟨[ones a], []⟩) (Fd := reg [false]) (G := endv 0) (Rr := endv 0) (P := emp) (k := a) (LA := [ones a])
      (rest := rest) hW
    have s3 := runs_rebuild (R := R) (nK := nK) (K := K) (W := W) (O := ⟨O, []⟩) (U := ⟨U, []⟩) (F := emp)
      (S := ⟨[ones a], []⟩) (Fd := reg [false]) (G := endv 0) (Rr := endv 0) (P := emp) (k := a)
      (LA := (rest.map ones).reverse ++ [ones a]) (LB := rest) hW
    set σ₃ := xbank R nK K ⟨O, []⟩ ⟨U, []⟩ ⟨[], rest.map ones⟩ emp a emp ⟨[ones a], []⟩ (reg [false]) (endv 0)
      (endv 0) emp with hσ₃
    have s4 := runs_clear (a := 0) xS σ₃
    set σ₄ := Function.update σ₃ xS ⟨[], []⟩ with hσ₄
    have s5 := runs_addTo' (c := 1) (v := a) (show xOne ≠ xK by decide) σ₄ (by tsimp [hσ₄, hσ₃, xbank])
      (by tsimp [hσ₄, hσ₃, xbank])
    refine (Runs.then s1 (Runs.then (Runs.cond_false (by simp [xbank, reg, startsOne_mk]) s2)
      (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ e => ?_) ?_
    · rw [e]; simp only [exStep, ↓reduceIte, stBank]; funext i; fin_cases i <;> rfl
    · have hcs : clen (σ₃ xS).words = a + 1 := by tsimp [hσ₃, xbank, WTape.words, clen, length_ones]
      rw [hcs]
      have h1 : rest.length * (W + 8) ≤ W * (W + 8) := Nat.mul_le_mul_right _ hlen
      have h2 : rest.length * (5 * W + 13) ≤ W * (5 * W + 13) := Nat.mul_le_mul_right _ hlen
      simp only [stepCost, exchCost]
      nlinarith
  · have hka' : k < a := lt_of_le_of_ne hka (Ne.symm hak)
    have hd : decide (k < a) = true := decide_eq_true hka'
    rw [hd] at s1
    have hrest_nd : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hpe := passRun_eq (a := a) (K := K) hge hrest_nd
    have hidx : rest.idxOf k ≤ rest.length := List.idxOf_le_length
    have s2 := runs_exchBody (R := R) (nK := nK) (K := K) (W := W) hR0 (O := O) (U := U) (a := a) (k := k)
      (rest := rest) hk ha hW hlen
    rw [hpe, min_eq_right hidx] at s2
    simp only at s2
    have hWset : ∀ x ∈ rest.set (rest.idxOf k) a, x ≤ W := by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hW x hx
      · exact ha
    have s3 := runs_rebuild (R := R) (nK := nK) (K := K) (W := W)
      (O := ⟨(swapWords R (nK - rest.idxOf k * K - (rest.length - rest.idxOf k - 1) * K) (rest.idxOf k * K)
        ((rest.length - rest.idxOf k - 1) * K) K K).reverse ++ O, []⟩)
      (U := ⟨swapWords R (nK - rest.idxOf k * K - (rest.length - rest.idxOf k - 1) * K) (rest.idxOf k * K)
        ((rest.length - rest.idxOf k - 1) * K) K K ++ U, []⟩) (F := emp)
      (S := ⟨[ones a], []⟩) (Fd := reg [false]) (G := endv 0) (Rr := endv 0) (P := emp) (k := k)
      (LA := (rest.map ones).reverse ++ [ones a]) (LB := rest.set (rest.idxOf k) a) hWset
    set σ₃ := xbank R nK K
      ⟨(swapWords R (nK - rest.idxOf k * K - (rest.length - rest.idxOf k - 1) * K) (rest.idxOf k * K)
        ((rest.length - rest.idxOf k - 1) * K) K K).reverse ++ O, []⟩
      ⟨swapWords R (nK - rest.idxOf k * K - (rest.length - rest.idxOf k - 1) * K) (rest.idxOf k * K)
        ((rest.length - rest.idxOf k - 1) * K) K K ++ U, []⟩
      ⟨[], (rest.set (rest.idxOf k) a).map ones⟩ emp k emp ⟨[ones a], []⟩ (reg [false]) (endv 0) (endv 0) emp
      with hσ₃
    have s4 := runs_clear (a := 0) xS σ₃
    set σ₄ := Function.update σ₃ xS ⟨[], []⟩ with hσ₄
    have s5 := runs_addTo' (c := 1) (v := k) (show xOne ≠ xK by decide) σ₄ (by tsimp [hσ₄, hσ₃, xbank])
      (by tsimp [hσ₄, hσ₃, xbank])
    refine (Runs.then s1 (Runs.then (Runs.cond_true (by simp [xbank, reg, startsOne_mk]) s2)
      (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ e => ?_) ?_
    · rw [e]; simp only [exStep, hak, ↓reduceIte, stBank]; funext i; fin_cases i <;> rfl
    · have hcs : clen (σ₃ xS).words = a + 1 := by tsimp [hσ₃, xbank, WTape.words, clen, length_ones]
      rw [hcs]
      have h2 : (rest.set (rest.idxOf k) a).length * (5 * W + 13) ≤ W * (5 * W + 13) := by
        rw [List.length_set]; exact Nat.mul_le_mul_right _ hlen
      simp only [stepCost]
      nlinarith

/-! ### The scan -/

theorem length_exStep (R nK K : ℕ) (O U : List (List Bool)) (a k : ℕ) (rest : List ℕ) :
    (exStep R nK K O U a k rest).2.2.length = rest.length := by
  unfold exStep; split_ifs <;> simp

/-- The outputs of the whole scan. -/
def exRun (R nK K : ℕ) : List ℕ → ℕ → List (List Bool) → List (List Bool) → List (List Bool) × List (List Bool)
  | [], _, O, U => (O, U)
  | a :: rest, k, O, U => exRun R nK K (exStep R nK K O U a k rest).2.2 (k + 1) (exStep R nK K O U a k rest).1
      (exStep R nK K O U a k rest).2.1
termination_by S => S.length
decreasing_by all_goals (rw [length_exStep]; simp)

/-- The scan's invariant: every unsettled block is at least `k` and at most `W`, no block twice, and
`k + |S| ≤ W`. -/
def Good (W k : ℕ) (S : List ℕ) : Prop := (∀ x ∈ S, k ≤ x ∧ x ≤ W) ∧ S.Nodup ∧ k + S.length ≤ W

theorem not_mem_set_idxOf {rest : List ℕ} {k a : ℕ} (hnd : rest.Nodup) (hak : a ≠ k) :
    k ∉ rest.set (rest.idxOf k) a := by
  intro hmem
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hmem
  have hjl : j < rest.length := by simpa using hj
  rw [List.getElem_set] at hget
  split_ifs at hget with hji
  · exact hak hget
  · have hmem' : k ∈ rest := hget ▸ List.getElem_mem hjl
    have hi := List.idxOf_lt_length_of_mem hmem'
    have h2 := List.getElem_idxOf hi
    exact hji ((hnd.getElem_inj_iff).mp (h2.trans hget.symm))

theorem good_exStep {W k a : ℕ} {rest : List ℕ} (R nK K : ℕ) (O U : List (List Bool)) (h : Good W k (a :: rest)) :
    Good W (k + 1) (exStep R nK K O U a k rest).2.2 := by
  obtain ⟨hb, hnd, hlen⟩ := h
  have hnd' := (List.nodup_cons.mp hnd)
  unfold exStep
  split_ifs with hak
  · subst hak
    dsimp only
    refine ⟨fun x hx => ?_, hnd'.2, by simp at hlen; omega⟩
    have := hb x (by simp [hx])
    have hne : x ≠ a := fun e => hnd'.1 (e ▸ hx)
    omega
  · dsimp only
    refine ⟨fun x hx => ?_, hnd'.2.set hnd'.1, by simp at hlen ⊢; omega⟩
    have hka : k ≤ a := (hb a (by simp)).1
    have hkx : x ≠ k := fun e => not_mem_set_idxOf hnd'.2 hak (e ▸ hx)
    rcases List.mem_or_eq_of_mem_set hx with hx' | rfl
    · have := hb x (by simp [hx']); omega
    · have := hb x (by simp); omega

set_option maxHeartbeats 8000000 in
/-- `runs_exLoop`: the scan over the whole suffix. -/
theorem runs_exLoop {R nK K W : ℕ} (hR0 : 0 < R) :
    ∀ (n : ℕ) (S : List ℕ) (k : ℕ) (O U : List (List Bool)), S.length = n → Good W k S →
      Runs (.loop xA step) (stBank R nK K O U S k)
        (· = stBank R nK K (exRun R nK K S k O U).1 (exRun R nK K S k O U).2 [] (k + n))
        (n * (stepCost W K nK R + 2))
  | 0, S, k, O, U, hn, _ => by
    rw [List.length_eq_zero_iff.mp hn]
    refine (Runs.loop_done (by simp [stBank, xbank]) rfl).mono (fun τ e => ?_) (by simp)
    rw [← e, exRun]; rfl
  | n + 1, a :: rest, k, O, U, hn, hg => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
    obtain ⟨hb, hnd, hlen⟩ := hg
    have s1 := runs_step (R := R) (nK := nK) (K := K) (W := W) hR0 (O := O) (U := U) (a := a) (k := k)
      (rest := rest) (hb a (by simp)).1 (fun x hx => (hb x (by simp [hx])).1) hnd
      (by simp at hlen; omega) (hb a (by simp)).2 (fun x hx => (hb x (by simp [hx])).2) (by simp at hlen; omega)
    have ih := runs_exLoop (R := R) (nK := nK) (K := K) (W := W) hR0 n (exStep R nK K O U a k rest).2.2 (k + 1) (exStep R nK K O U a k rest).1
      (exStep R nK K O U a k rest).2.1 (by rw [length_exStep, hn]) (good_exStep R nK K O U ⟨hb, hnd, hlen⟩)
    refine (Runs.loop_step (by simp [stBank, xbank]) (s1.mono (fun τ e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ e => ?_) ?_
    · rw [e, exRun, show k + 1 + n = k + (n + 1) by omega]
    · rw [Nat.succ_mul]; omega

/-! ### The scan's words -/

theorem words_ex (n R K g ρ : ℕ) :
    AxisDriver.Rec.words (LayoutMachines.opRec n R (K, g, K, ρ)) = swapWords R (n - 2 * K - g - ρ) g ρ K K := by
  simp only [LayoutMachines.opRec, LayoutMachines.opHdrs, LayoutMachines.opP, swapHdrsG, AxisDriver.Rec.words,
    swapWords]
  rw [show n - K - g - K - ρ = n - 2 * K - g - ρ by omega]

theorem exRun_split (R nK K : ℕ) (a k : ℕ) (rest : List ℕ) (O U : List (List Bool)) :
    exRun R nK K (a :: rest) k O U = exRun R nK K (exStep R nK K O U a k rest).2.2 (k + 1)
      (exStep R nK K O U a k rest).1 (exStep R nK K O U a k rest).2.1 := by
  rw [exRun]

/-- `exRun_words`: the scan writes the words of the paper's chunk exchanges, forward (reversed on `xO`)
and undone in reverse order (on `xU`). -/
theorem exRun_words {nA R K m : ℕ} :
    ∀ (e : ℕ) (S : List ℕ) (k : ℕ) (O U : List (List Bool)), S.length = e → k + e = m →
      exRun R (nA - 2 * K) K S k O U =
        ((wordsOf nA R (LayoutMachines.exOps ((selS S k).map (exParamsN m K)))).reverse ++ O,
          wordsOf nA R (LayoutMachines.exOps ((selS S k).map (exParamsN m K)).reverse) ++ U)
  | 0, S, k, O, U, he, _ => by
    rw [List.length_eq_zero_iff.mp he]; simp [exRun, selS, wordsOf, LayoutMachines.exOps]
  | e + 1, a :: rest, k, O, U, he, hm => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at he
    rw [exRun_split]
    by_cases hak : a = k
    · subst hak
      have ih := exRun_words (nA := nA) (R := R) (K := K) (m := m) e rest (a + 1) O U he (by omega)
      simp only [exStep, ↓reduceIte]
      rw [ih, selS_cons_eq]
    · set i := rest.idxOf k with hi
      have ih := exRun_words (nA := nA) (R := R) (K := K) (m := m) e (rest.set i a) (k + 1)
        ((swapWords R (nA - 2 * K - i * K - (rest.length - i - 1) * K) (i * K) ((rest.length - i - 1) * K) K K).reverse ++ O)
        (swapWords R (nA - 2 * K - i * K - (rest.length - i - 1) * K) (i * K) ((rest.length - i - 1) * K) K K ++ U)
        (by simp [he]) (by omega)
      simp only [exStep, hak, ↓reduceIte]
      rw [← hi, ih, selS_cons_ne rest hak, ← hi]
      have hex : exParamsN m K (k, k + 1 + i) = (K, i * K, (rest.length - i - 1) * K) := by
        rw [exParamsN_lt (by omega)]
        congr 2
        · rw [show k + 1 + i - k - 1 = i by omega]
        · rw [show m - 1 - (k + 1 + i) = rest.length - i - 1 by omega]
      have hw : wordsOf nA R (LayoutMachines.exOps [exParamsN m K (k, k + 1 + i)]) =
          swapWords R (nA - 2 * K - i * K - (rest.length - i - 1) * K) (i * K) ((rest.length - i - 1) * K) K K := by
        rw [hex]; simp [wordsOf, LayoutMachines.exOps, words_ex]
      refine Prod.ext ?_ ?_ <;> dsimp only
      · rw [List.map_cons, show ∀ (q : ℕ × ℕ × ℕ) (qs : List (ℕ × ℕ × ℕ)),
          LayoutMachines.exOps (q :: qs) = LayoutMachines.exOps [q] ++ LayoutMachines.exOps qs from
            fun q qs => rfl, wordsOf_append, hw]
        simp
      · rw [List.map_cons, List.reverse_cons, show ∀ (qs : List (ℕ × ℕ × ℕ)) (q : ℕ × ℕ × ℕ),
          LayoutMachines.exOps (qs ++ [q]) = LayoutMachines.exOps qs ++ LayoutMachines.exOps [q] from
            fun qs q => by simp [LayoutMachines.exOps], wordsOf_append, hw]
        simp

/-- The axis-major arrangement is a list of distinct blocks below `q D`. -/
theorem good_axisArr {q D W : ℕ} (hW : q * D ≤ W) : Good W 0 (axisArr q D) := by
  refine ⟨fun x hx => ?_, ?_, by simp [axisArr]; omega⟩
  · simp only [axisArr, List.mem_map, List.mem_range] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hq : 0 < q := by rcases Nat.eq_zero_or_pos q with h | h <;> simp_all
    have hD : y / q < D := by rw [Nat.div_lt_iff_lt_mul hq]; linarith [mul_comm q D]
    have hm : y % q < q := Nat.mod_lt _ hq
    refine ⟨Nat.zero_le _, ?_⟩
    have : y % q * D + y / q < q * D := by nlinarith
    omega
  · apply List.Nodup.map_on _ List.nodup_range
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    have hq : 0 < q := by rcases Nat.eq_zero_or_pos q with h | h <;> simp_all
    have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h | h <;> simp_all
    have hxD : x / q < D := by rw [Nat.div_lt_iff_lt_mul hq]; linarith [mul_comm q D]
    have hyD : y / q < D := by rw [Nat.div_lt_iff_lt_mul hq]; linarith [mul_comm q D]
    have h1 : x / q = y / q := by
      have := congrArg (· % D) hxy
      simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hxD,
        Nat.mod_eq_of_lt hyD] at this
      exact this
    have h2 : x % q = y % q := by
      have := congrArg (· / D) hxy
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hxD, zero_add,
        Nat.add_comm (y % q * D), Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hyD, zero_add] at this
      exact this
    rw [← Nat.div_add_mod x q, ← Nat.div_add_mod y q, h1, h2]

/-- `runs_exScan`: from the axis-major arrangement of `q D` blocks the scan writes the forward words of
its exchanges (reversed, on `xO`) and the undo words of their reversal (on `xU`, last record first). -/
theorem runs_exScan {R nA K W q D : ℕ} (hR0 : 0 < R) (hW : q * D ≤ W) (O U : List (List Bool)) :
    Runs (.loop xA step) (stBank R (nA - 2 * K) K O U (axisArr q D) 0)
      (· = stBank R (nA - 2 * K) K
        ((wordsOf nA R (LayoutMachines.exOps ((selS (axisArr q D) 0).map (exParamsN (q * D) K)))).reverse ++ O)
        (wordsOf nA R (LayoutMachines.exOps ((selS (axisArr q D) 0).map (exParamsN (q * D) K)).reverse) ++ U)
        [] (q * D))
      (q * D * (stepCost W K (nA - 2 * K) R + 2)) := by
  have hl : (axisArr q D).length = q * D := by simp [axisArr]
  have s := runs_exLoop (R := R) (nK := nA - 2 * K) (K := K) (W := W) hR0 (q * D) (axisArr q D) 0 O U hl
    (good_axisArr hW)
  rw [exRun_words (nA := nA) (m := q * D) (q * D) (axisArr q D) 0 O U hl (by omega), zero_add] at s
  exact s

/-- `runs_exScan_paper`: the same for the paper's layout, whose chunk exchanges are `layoutSwaps`. -/
theorem runs_exScan_paper {R nA K W : ℕ} {ts : List ℕ} {ℓ : ℕ} (hR0 : 0 < R)
    (hW : (ℓ - 1) / K * ts.length ≤ W) (O U : List (List Bool)) :
    Runs (.loop xA step) (stBank R (nA - 2 * K) K O U (axisArr ((ℓ - 1) / K) ts.length) 0)
      (· = stBank R (nA - 2 * K) K
        ((wordsOf nA R (LayoutMachines.exOps (LayoutMachines.layoutSwaps ts ℓ K))).reverse ++ O)
        (wordsOf nA R (LayoutMachines.exOps (LayoutMachines.layoutSwaps ts ℓ K).reverse) ++ U)
        [] ((ℓ - 1) / K * ts.length))
      ((ℓ - 1) / K * ts.length * (stepCost W K (nA - 2 * K) R + 2)) := by
  rw [layoutSwaps_selS]
  exact runs_exScan hR0 hW O U

end LayoutSwapTape

end IntegerMultBounds.Schoenhage
