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
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, emp, reg]
  · simp [time_copy, clen] at t1 ⊢; omega

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
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, emp, reg]
  · first | omega | (simp [clen, length_ones] at t1 ⊢; omega)

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
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hσ, xbank, WTape.put, WTape.next]
    · tsimp [hσ, xbank, length_ones]; omega
  · have s2 := runs_addTo' (c := K) (v := ρ) (show xKK ≠ xR by decide) σ₁ (by tsimp [hσ₁, hσ, xbank])
      (by tsimp [hσ₁, hσ, xbank])
    refine (Runs.then s1 (Runs.cond_true (by tsimp [hσ₁, hσ, xbank, reg, startsOne_mk]) s2)).mono
      (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hσ, xbank, WTape.put, WTape.next]
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
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, emp, reg, WTape.put]
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
      rw [if_pos hkw, set_append_single_of_ne rfl hic]
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
      rw [if_neg hkw, ← hi, hik, hset, List.set_eq_of_length_le (le_refl _)]
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
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, emp, reg, ones, Nat.sub_sub]
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
  · funext i; fin_cases i <;> first | rfl | tsimp [xbank, endv, reg, emp, ones]
  · simp [clen, WTape.words, length_ones]; omega

end LayoutSwapTape

end IntegerMultBounds.Schoenhage
