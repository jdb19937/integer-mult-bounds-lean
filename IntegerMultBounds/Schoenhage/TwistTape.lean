import IntegerMultBounds.Schoenhage.Twist
import IntegerMultBounds.Schoenhage.Reverse
import IntegerMultBounds.Schoenhage.RingConst

/-! The recordwise monomial on word tapes. An eleven-tape word program moves
a record's component words to a buffer with their bits reversed, skips the
head words, then emits the tail words and the head words to the output,
each turned back to most-significant-first order and negated in two's
complement when its flag says so (`runs_twist`: the output is `twWords`). -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm

namespace Rules

/-- Two's complement negation, least significant bit first. -/
abbrev neg : Rule 0 where
  Q := Bool
  q0 := false
  step q b _ := (q || b, some (some (if q then !b else b)), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_neg : ∀ (q : Bool) (w : List Bool) (ws : Fin 0 → List Bool),
    (go neg q w ws).2.1 = (if q then w.map (!·) else negL w).map some
  | q, [], ws => by cases q <;> simp [go, negL]
  | q, b :: w, ws => by
    cases q <;> cases b <;> simp [go, negL, go_neg _ w]

theorem output_neg (w : List Bool) (ws : Fin 0 → List Bool) : output neg w ws = syms [negL w] := by
  simp [output, syms_cons, go_neg]

theorem time_neg (w : List Bool) (ws : Fin 0 → List Bool) : time neg w ws = w.length + 6 := by
  simp [time, rest]

end Rules

namespace TwistTape

/-- The record's words, most significant bit first (consumed). -/
abbrev wX : Fin 11 := 0
/-- The output words. -/
abbrev wO : Fin 11 := 1
/-- The buffer of reversed words. -/
abbrev wA : Fin 11 := 2
/-- Unary register: the number of words. -/
abbrev wC : Fin 11 := 3
/-- Unary register: the number of head words. -/
abbrev wH : Fin 11 := 4
/-- Unary register: the number of tail words. -/
abbrev wT : Fin 11 := 5
/-- Flag: negate the tail words. -/
abbrev fT : Fin 11 := 6
/-- Flag: negate the head words. -/
abbrev fH : Fin 11 := 7
/-- Loop ticks. -/
abbrev wQ : Fin 11 := 8
/-- Junk output of skips. -/
abbrev wJ : Fin 11 := 9
/-- One word in transit. -/
abbrev wW : Fin 11 := 10

/-- Ticks from a unary register onto `wQ`. -/
noncomputable def tk (src : Fin 11) (h : src ≠ wQ) : Cmd 0 11 :=
  .seq (op0 Rules.ticks false src wQ h) <| .seq (rewind src) (rewind wQ)

theorem runs_tk {src : Fin 11} (h : src ≠ wQ) {b : ℕ} (τ : Fin 11 → WTape) (hs : τ src = reg (ones b))
    (hT : τ wQ = emp) :
    Runs (tk src h) τ (· = Function.update τ wQ ⟨[], List.replicate b []⟩) (3 * b + 20) := by
  apply Runs.of_wp
  simp only [tk, WP, wp_op0, wp_rewind]
  have e1 : (τ src).cur = ones b := by rw [hs]; rfl
  have e2 : (τ src).right = [ones b] := by rw [hs]; rfl
  have e3 : (τ wQ).right = [] := by rw [hT]; rfl
  have e4 : (τ wQ).left = [] := by rw [hT]; rfl
  simp only [e1, e2, e3, Rules.output_ticks, length_ones, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
    parse_syms, Bool.false_eq_true, false_implies, and_true, Function.update_self,
    Function.update_of_ne h.symm, Function.update_of_ne h]
  refine ⟨?_, ?_⟩
  · funext x
    by_cases a1 : x = wQ
    · subst a1; simp [e4, hT, emp]
    · by_cases a2 : x = src
      · subst a2; simp [a1, hs, reg]
      · simp [a1, a2]
  · have t1 := time_le Rules.ticks (ones b) (fun j => j.elim0) 0 (fun j => j.elim0)
    have hb : Rules.ticks.B = 0 := rfl
    rw [length_ones, hb] at t1
    generalize time Rules.ticks (ones b) (fun j => j.elim0) = T at t1 ⊢
    simp [e4, hs, hT, emp, reg, clen_replicate_nil, WTape.words]
    linarith

/-- Negate (flag set) or copy the buffer's current word into `wW`. -/
noncomputable def pick (F : Fin 11) : Cmd 0 11 :=
  .cond F (op0 Rules.neg false wA wW (by decide)) (op0 Rules.copy false wA wW (by decide))

theorem runs_pick (F : Fin 11) (b : Bool) (σ : Fin 11 → WTape) {x : List Bool} {L R : List (List Bool)}
    (hF : σ F = reg [b]) (hA : σ wA = ⟨L, x :: R⟩) (hW : σ wW = emp) :
    Runs (pick F) σ (· = Function.update (Function.update σ wA ⟨x :: L, R⟩) wW
      ⟨[if b then negL x else x], []⟩) (x.length + 7) := by
  have hd : (σ wA).right ≠ [] := by rw [hA]; simp
  have ho : (σ wW).right = [] := by rw [hW]; rfl
  have hn : (σ wA).next = ⟨x :: L, R⟩ := by rw [hA]; rfl
  have hp : ∀ v : List Bool, (σ wW).put false [v] = ⟨[v], []⟩ := fun v => by rw [hW]; rfl
  have hc : (σ wA).cur = x := by rw [hA]; rfl
  cases b
  · refine Runs.cond_false (by rw [hF]; simp [reg, startsOne_mk]) ?_
    refine (runs_op0 Rules.copy false _ σ hd ho [x] (by rw [hc, Rules.output_copy]) (by simp)).mono
      (fun τ h => ?_) ?_
    · rw [h, hn, hp]; simp
    · rw [hc, time_copy]
  · refine Runs.cond_true (by rw [hF]; simp [reg, startsOne_mk]) ?_
    refine (runs_op0 Rules.neg false _ σ hd ho [negL x] (by rw [hc, Rules.output_neg]) (by simp)).mono
      (fun τ h => ?_) ?_
    · rw [h, hn, hp]; simp
    · rw [hc, Rules.time_neg]

/-- Emit the buffer's current word to the output, back in most-significant-first order, negated when
the flag `F` is set; consume one tick. -/
noncomputable def emitW (F : Fin 11) : Cmd 0 11 :=
  .seq (pick F) <| .seq (rewind wW) <| .seq (revw wW wO (by decide)) <| .seq (clear wW)
    (skp wQ wJ (by decide))

set_option maxHeartbeats 4000000 in
theorem runs_emitW (F : Fin 11) (b : Bool) (σ : Fin 11 → WTape) {x : List Bool}
    {L R Tl D : List (List Bool)} {n : ℕ}
    (hF : σ F = reg [b]) (hA : σ wA = ⟨L, x :: R⟩) (hW : σ wW = emp) (hO : σ wO = ⟨D, []⟩)
    (hQ : σ wQ = ⟨Tl, List.replicate (n + 1) []⟩) (hJ : σ wJ = emp) :
    Runs (emitW F) σ (· = Function.update (Function.update (Function.update σ wA ⟨x :: L, R⟩)
      wO ⟨(if b then negL x else x).reverse :: D, []⟩) wQ ⟨[] :: Tl, List.replicate n []⟩)
      (7 * x.length + 40) := by
  set y := if b then negL x else x
  have hy : y.length = x.length := by simp only [y]; split_ifs <;> simp
  have s1 := runs_pick F b σ hF hA hW
  set σ₁ := Function.update (Function.update σ wA ⟨x :: L, R⟩) wW ⟨[y], []⟩
  have s2 := runs_rewind (a := 0) wW σ₁
  set σ₂ := Function.update σ₁ wW ⟨[], [y]⟩
  have e2 : Function.update σ₁ wW ⟨[], (σ₁ wW).left.reverse ++ (σ₁ wW).right⟩ = σ₂ := by
    simp [σ₂, σ₁]
  rw [e2] at s2
  have s3 := runs_revw (a := 0) (show wW ≠ wO by decide) σ₂ (L := []) (R := []) (w := y)
    (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, hO])
  set σ₃ := Function.update (Function.update σ₂ wW ⟨[y], []⟩) wO ⟨y.reverse :: (σ₂ wO).left, []⟩
  have s4 := runs_clear (a := 0) wW σ₃
  set σ₄ := Function.update σ₃ wW ⟨[], []⟩
  have s5 := runs_skp (a := 0) (show wQ ≠ wJ by decide) σ₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, hQ, List.replicate_succ])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, hJ, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ h => ?_) ?_
  · rw [h]; funext z
    by_cases hm : z ∈ [wA, wO, wQ, wW]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;>
        tsimp [σ₄, σ₃, σ₂, σ₁, hO, hQ, hW, emp, List.replicate_succ]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4⟩ := hm
      simp only [σ₄, σ₃, σ₂, σ₁, Function.update_apply, n1, n2, n3, n4, if_false]
  · tsimp [σ₄, σ₃, σ₂, σ₁, hQ, hO, WTape.words, hy, List.replicate_succ]
    omega

/-- Move one word per tick from `wX` to `wA`, reversed. -/
noncomputable def moveLoop : Cmd 0 11 :=
  .loop wQ (.seq (revw wX wA (by decide)) (skp wQ wJ (by decide)))

theorem runs_moveLoop {W : ℕ} :
    ∀ (ws : List (List Bool)) (τ : Fin 11 → WTape) (Ls R D Tl : List (List Bool)),
      (∀ x ∈ ws, x.length ≤ W) → τ wX = ⟨Ls, ws ++ R⟩ → τ wA = ⟨D, []⟩ →
      τ wQ = ⟨Tl, List.replicate ws.length []⟩ → τ wJ = emp →
      Runs moveLoop τ (· = Function.update (Function.update (Function.update τ
        wX ⟨ws.reverse ++ Ls, R⟩) wA ⟨(ws.map List.reverse).reverse ++ D, []⟩)
        wQ ⟨List.replicate ws.length [] ++ Tl, []⟩) (ws.length * (3 * W + 20))
  | [], τ, Ls, R, D, Tl, _, hs, hd, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hs, hd, hT]) <;> tsimp at *
  | x :: ws, τ, Ls, R, D, Tl, hW, hs, hd, hT, hJ => by
    have hx := hW x (by simp)
    have s1 := runs_revw (a := 0) (show wX ≠ wA by decide) τ (L := Ls) (R := ws ++ R) (w := x)
      (by simpa using hs) (by simp [hd])
    set τ₁ := Function.update (Function.update τ wX ⟨x :: Ls, ws ++ R⟩) wA ⟨x.reverse :: (τ wA).left, []⟩
    have s2 := runs_skp (a := 0) (show wQ ≠ wJ by decide) τ₁
      (by tsimp [τ₁, hT, List.replicate_succ]) (by tsimp [τ₁, hJ, emp])
    set τ₂ := Function.update τ₁ wQ (τ₁ wQ).next
    have ih := runs_moveLoop ws τ₂ (x :: Ls) R (x.reverse :: D) ([] :: Tl)
      (fun y hy => hW y (by simp [hy])) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, hd])
      (by tsimp [τ₂, τ₁, hT, List.replicate_succ]) (by tsimp [τ₂, τ₁, hJ])
    refine (Runs.loop_step (by simp [hT]) ((Runs.then s1 s2).mono (fun τ' e => by rw [e]; exact ih)
      le_rfl)).mono (fun τ' e => ?_) ?_
    · rw [e]; funext y
      simp only [τ₂, τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hd, hT, replicate_nil_append, List.replicate_succ]) <;>
        tsimp at *
    · have hc : (τ₁ wQ).cur.length = 0 := by tsimp [τ₁, hT, List.replicate_succ]
      rw [hc]; simp only [List.length_cons]; nlinarith

/-- Skip one buffered word per tick. -/
noncomputable def skipLoop : Cmd 0 11 :=
  .loop wQ (.seq (skp wA wJ (by decide)) (skp wQ wJ (by decide)))

theorem runs_skipLoop {W : ℕ} :
    ∀ (hs : List (List Bool)) (τ : Fin 11 → WTape) (L R Tl : List (List Bool)),
      (∀ x ∈ hs, x.length ≤ W) → τ wA = ⟨L, hs ++ R⟩ →
      τ wQ = ⟨Tl, List.replicate hs.length []⟩ → τ wJ = emp →
      Runs skipLoop τ (· = Function.update (Function.update τ wA ⟨hs.reverse ++ L, R⟩)
        wQ ⟨List.replicate hs.length [] ++ Tl, []⟩) (hs.length * (W + 20))
  | [], τ, L, R, Tl, _, hs, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hs, hT]) <;> tsimp at *
  | x :: xs, τ, L, R, Tl, hW, hs, hT, hJ => by
    have hx := hW x (by simp)
    have s1 := runs_skp (a := 0) (show wA ≠ wJ by decide) τ (by simp [hs]) (by tsimp [hJ, emp])
    set τ₁ := Function.update τ wA (τ wA).next
    have s2 := runs_skp (a := 0) (show wQ ≠ wJ by decide) τ₁
      (by tsimp [τ₁, hT, List.replicate_succ]) (by tsimp [τ₁, hJ, emp])
    set τ₂ := Function.update τ₁ wQ (τ₁ wQ).next
    have ih := runs_skipLoop xs τ₂ (x :: L) R ([] :: Tl)
      (fun y hy => hW y (by simp [hy])) (by tsimp [τ₂, τ₁, hs])
      (by tsimp [τ₂, τ₁, hT, List.replicate_succ]) (by tsimp [τ₂, τ₁, hJ])
    refine (Runs.loop_step (by simp [hT]) ((Runs.then s1 s2).mono (fun τ' e => by rw [e]; exact ih)
      le_rfl)).mono (fun τ' e => ?_) ?_
    · rw [e]; funext y
      simp only [τ₂, τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hs, hT, replicate_nil_append, List.replicate_succ]) <;>
        tsimp at *
    · have hc : (τ₁ wQ).cur.length = 0 := by tsimp [τ₁, hT, List.replicate_succ]
      have ha : (τ wA).cur = x := by rw [hs]; rfl
      rw [hc, ha]; simp only [List.length_cons]; nlinarith

/-- The word a buffered (reversed) word becomes on the output. -/
def outW (b : Bool) (x : List Bool) : List Bool := (if b then negL x else x).reverse

/-- Emit one buffered word per tick. -/
noncomputable def emitLoop (F : Fin 11) : Cmd 0 11 := .loop wQ (emitW F)

theorem runs_emitLoop (F : Fin 11) (h1 : F ≠ wA) (h2 : F ≠ wO) (h3 : F ≠ wQ) (b : Bool) {W : ℕ} :
    ∀ (xs : List (List Bool)) (τ : Fin 11 → WTape) (L R D Tl : List (List Bool)),
      (∀ x ∈ xs, x.length ≤ W) → τ F = reg [b] → τ wA = ⟨L, xs ++ R⟩ → τ wW = emp →
      τ wO = ⟨D, []⟩ → τ wQ = ⟨Tl, List.replicate xs.length []⟩ → τ wJ = emp →
      Runs (emitLoop F) τ (· = Function.update (Function.update (Function.update τ wA ⟨xs.reverse ++ L, R⟩)
        wO ⟨(xs.map (outW b)).reverse ++ D, []⟩) wQ ⟨List.replicate xs.length [] ++ Tl, []⟩)
        (xs.length * (7 * W + 42))
  | [], τ, L, R, D, Tl, _, _, hs, _, hO, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hs, hO, hT]) <;> tsimp at *
  | x :: xs, τ, L, R, D, Tl, hW, hF, hs, hw, hO, hT, hJ => by
    have hx := hW x (by simp)
    have s1 := runs_emitW F b τ (x := x) (L := L) (R := xs ++ R) (Tl := Tl) (D := D) (n := xs.length)
      hF (by simpa using hs) hw hO (by simpa using hT) hJ
    set τ₁ := Function.update (Function.update (Function.update τ wA ⟨x :: L, xs ++ R⟩)
      wO ⟨outW b x :: D, []⟩) wQ ⟨[] :: Tl, List.replicate xs.length []⟩
    have ih := runs_emitLoop F h1 h2 h3 b xs τ₁ (x :: L) R (outW b x :: D) ([] :: Tl)
      (fun y hy => hW y (by simp [hy]))
      (by simp only [τ₁, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, hF])
      (by tsimp [τ₁]) (by tsimp [τ₁, hw]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁, hJ])
    refine (Runs.loop_step (by simp [hT]) (s1.mono (fun τ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ' e => ?_) ?_
    · rw [e]; funext y
      simp only [τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;>
        (try tsimp [hs, hO, hT, replicate_nil_append, List.replicate_succ]) <;> tsimp at *
    · simp only [List.length_cons]; nlinarith

/-! ### The whole monomial -/

/-- Move all words to the buffer, reversed, and rewind it. -/
noncomputable def moveAll : Cmd 0 11 :=
  .seq (tk wC (by decide)) <| .seq moveLoop <| .seq (clear wQ) (rewind wA)

set_option maxHeartbeats 4000000 in
theorem runs_moveAll {W : ℕ} (ws : List (List Bool)) (hW : ∀ x ∈ ws, x.length ≤ W) (τ : Fin 11 → WTape)
    (hX : τ wX = ⟨[], ws⟩) (hA : τ wA = emp) (hC : τ wC = reg (ones ws.length)) (hQ : τ wQ = emp)
    (hJ : τ wJ = emp) :
    Runs moveAll τ (· = Function.update (Function.update τ wX ⟨ws.reverse, []⟩) wA ⟨[], ws.map List.reverse⟩)
      (ws.length * (4 * W + 30) + 30) := by
  have s1 := runs_tk (show wC ≠ wQ by decide) τ hC hQ
  set τ₁ := Function.update τ wQ ⟨[], List.replicate ws.length []⟩
  have s2 := runs_moveLoop (W := W) ws τ₁ [] [] [] [] hW (by tsimp [τ₁, hX]) (by tsimp [τ₁, hA, emp])
    (by tsimp [τ₁]) (by tsimp [τ₁, hJ])
  set τ₂ := Function.update (Function.update (Function.update τ₁ wX ⟨ws.reverse ++ [], []⟩)
    wA ⟨(ws.map List.reverse).reverse ++ [], []⟩) wQ ⟨List.replicate ws.length [] ++ [], []⟩
  have s3 := runs_clear (a := 0) wQ τ₂
  set τ₃ := Function.update τ₂ wQ ⟨[], []⟩
  have s4 := runs_rewind (a := 0) wA τ₃
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ' h => ?_) ?_
  · rw [h]; funext y
    simp only [τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hQ, emp]) <;> tsimp at *
  · have c1 : clen (ws.map List.reverse) ≤ ws.length * (W + 1) := by
      have := clen_le (L := ws.map List.reverse) (W := W)
        (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; simpa using hW y hy)
      simpa using this
    tsimp [τ₃, τ₂, WTape.words, clen_replicate_nil, clen_reverse]
    nlinarith

/-- Skip the head words. -/
noncomputable def skipHead : Cmd 0 11 := .seq (tk wH (by decide)) <| .seq skipLoop (clear wQ)

theorem runs_skipHead {W n : ℕ} (rv : List (List Bool)) (hn : n ≤ rv.length) (hW : ∀ x ∈ rv, x.length ≤ W)
    (τ : Fin 11 → WTape) (hA : τ wA = ⟨[], rv⟩) (hH : τ wH = reg (ones n)) (hQ : τ wQ = emp)
    (hJ : τ wJ = emp) :
    Runs skipHead τ (· = Function.update τ wA ⟨(rv.take n).reverse, rv.drop n⟩) (n * (W + 25) + 30) := by
  have s1 := runs_tk (show wH ≠ wQ by decide) τ hH hQ
  set τ₁ := Function.update τ wQ ⟨[], List.replicate n []⟩
  have s2 := runs_skipLoop (W := W) (rv.take n) τ₁ [] (rv.drop n) []
    (fun x hx => hW x (List.mem_of_mem_take hx)) (by tsimp [τ₁, hA])
    (by tsimp [τ₁]; omega) (by tsimp [τ₁, hJ])
  have hl : (rv.take n).length = n := by simp; omega
  rw [hl] at s2
  set τ₂ := Function.update (Function.update τ₁ wA ⟨(rv.take n).reverse ++ [], rv.drop n⟩)
    wQ ⟨List.replicate n [] ++ [], []⟩
  have s3 := runs_clear (a := 0) wQ τ₂
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ' h => ?_) ?_
  · rw [h]; funext y
    simp only [τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hQ, emp]) <;> tsimp at *
  · tsimp [τ₂, WTape.words, clen_replicate_nil]
    nlinarith

/-- Emit the tail words. -/
noncomputable def emitTail : Cmd 0 11 := .seq (tk wT (by decide)) <| .seq (emitLoop fT) (clear wQ)

theorem runs_emitTail {W : ℕ} (b : Bool) (xs L D : List (List Bool)) (hW : ∀ x ∈ xs, x.length ≤ W)
    (τ : Fin 11 → WTape) (hA : τ wA = ⟨L, xs⟩) (hT : τ wT = reg (ones xs.length)) (hF : τ fT = reg [b])
    (hw : τ wW = emp) (hO : τ wO = ⟨D, []⟩) (hQ : τ wQ = emp) (hJ : τ wJ = emp) :
    Runs emitTail τ (· = Function.update (Function.update τ wA ⟨xs.reverse ++ L, []⟩)
      wO ⟨(xs.map (outW b)).reverse ++ D, []⟩) (xs.length * (7 * W + 50) + 30) := by
  have s1 := runs_tk (show wT ≠ wQ by decide) τ hT hQ
  set τ₁ := Function.update τ wQ ⟨[], List.replicate xs.length []⟩
  have s2 := runs_emitLoop fT (by decide) (by decide) (by decide) b (W := W) xs τ₁ L [] D [] hW
    (by tsimp [τ₁, hF]) (by tsimp [τ₁, hA]) (by tsimp [τ₁, hw]) (by tsimp [τ₁, hO]) (by tsimp [τ₁])
    (by tsimp [τ₁, hJ])
  set τ₂ := Function.update (Function.update (Function.update τ₁ wA ⟨xs.reverse ++ L, []⟩)
    wO ⟨(xs.map (outW b)).reverse ++ D, []⟩) wQ ⟨List.replicate xs.length [] ++ [], []⟩
  have s3 := runs_clear (a := 0) wQ τ₂
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ' h => ?_) ?_
  · rw [h]; funext y
    simp only [τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hQ, emp]) <;> tsimp at *
  · tsimp [τ₂, WTape.words, clen_replicate_nil]
    nlinarith

/-- Rewind the buffer, emit the head words, and clean up. -/
noncomputable def emitHead : Cmd 0 11 :=
  .seq (rewind wA) <| .seq (tk wH (by decide)) <| .seq (emitLoop fH) <| .seq (clear wQ) <|
    .seq (clear wA) (clear wX)

set_option maxHeartbeats 4000000 in
theorem runs_emitHead {W : ℕ} (b : Bool) (hs tl D Xs : List (List Bool)) (hW : ∀ x ∈ hs ++ tl, x.length ≤ W)
    (hX : ∀ x ∈ Xs, x.length ≤ W)
    (τ : Fin 11 → WTape) (hA : τ wA = ⟨tl.reverse ++ hs.reverse, []⟩) (hH : τ wH = reg (ones hs.length))
    (hF : τ fH = reg [b]) (hw : τ wW = emp) (hO : τ wO = ⟨D, []⟩) (hQ : τ wQ = emp) (hJ : τ wJ = emp)
    (hXt : τ wX = ⟨Xs, []⟩) :
    Runs emitHead τ (· = Function.update (Function.update (Function.update τ wA emp)
      wO ⟨(hs.map (outW b)).reverse ++ D, []⟩) wX emp)
      ((hs.length + tl.length + Xs.length) * (10 * W + 60) + 60) := by
  have s0 := runs_rewind (a := 0) wA τ
  set τ₀ := Function.update τ wA ⟨[], hs ++ tl⟩
  have e0 : Function.update τ wA ⟨[], (τ wA).left.reverse ++ (τ wA).right⟩ = τ₀ := by simp [τ₀, hA]
  rw [e0] at s0
  have s1 := runs_tk (show wH ≠ wQ by decide) (b := hs.length) τ₀ (by tsimp [τ₀, hH]) (by tsimp [τ₀, hQ])
  set τ₁ := Function.update τ₀ wQ ⟨[], List.replicate hs.length []⟩
  have s2 := runs_emitLoop fH (by decide) (by decide) (by decide) b (W := W) hs τ₁ [] tl D []
    (fun x hx => hW x (by simp [hx]))
    (by tsimp [τ₁, τ₀, hF]) (by tsimp [τ₁, τ₀]) (by tsimp [τ₁, τ₀, hw]) (by tsimp [τ₁, τ₀, hO]) (by tsimp [τ₁])
    (by tsimp [τ₁, τ₀, hJ])
  set τ₂ := Function.update (Function.update (Function.update τ₁ wA ⟨hs.reverse ++ [], tl⟩)
    wO ⟨(hs.map (outW b)).reverse ++ D, []⟩) wQ ⟨List.replicate hs.length [] ++ [], []⟩
  have s3 := runs_clear (a := 0) wQ τ₂
  set τ₃ := Function.update τ₂ wQ ⟨[], []⟩
  have s4 := runs_clear (a := 0) wA τ₃
  set τ₄ := Function.update τ₃ wA ⟨[], []⟩
  have s5 := runs_clear (a := 0) wX τ₄
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5))))).mono
    (fun τ' h => ?_) ?_
  · rw [h]; funext y
    simp only [τ₄, τ₃, τ₂, τ₁, τ₀, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hQ, emp]) <;> tsimp at *
  · have c1 : clen (hs ++ tl) ≤ (hs ++ tl).length * (W + 1) := clen_le hW
    have c2 : clen Xs ≤ Xs.length * (W + 1) := clen_le hX
    have c3 : clen (tl.reverse ++ hs.reverse) = clen (hs ++ tl) := by
      rw [← List.reverse_append, clen_reverse]
    tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hA, hXt, WTape.words, clen_replicate_nil, clen_reverse, clen_append] at c1 c3 ⊢
    nlinarith

/-- The monomial on word tapes: move, skip the head, emit the tail, emit the head. -/
noncomputable def twistCmd : Cmd 0 11 := .seq moveAll <| .seq skipHead <| .seq emitTail emitHead

theorem outW_reverse (e : Bool) (x : List Bool) : outW (!e) x.reverse = if e then x else negW x := by
  cases e <;> simp [outW, negW]

theorem outW_reverse' (e : Bool) (x : List Bool) : outW e x.reverse = if e then negW x else x := by
  cases e <;> simp [outW, negW]

theorem twWords_out (n : ℕ) (e : Bool) (ws : List (List Bool)) :
    ((ws.map List.reverse).drop n).map (outW (!e)) ++ ((ws.map List.reverse).take n).map (outW e) =
      twWords n e ws := by
  simp only [twWords, ← List.map_drop, ← List.map_take, List.map_map]
  congr 1
  · congr 1; funext x; simp [outW_reverse]
  · congr 1; funext x; simp [outW_reverse']

/-- `runs_twist`: from the record's words on `wX`, unary `N`, `n`, `N - n` and the two flags, the
output tape gains `twWords n e ws`; the input words are consumed and every work tape is left empty. -/
theorem runs_twist {W n : ℕ} (e : Bool) (ws D : List (List Bool)) (hn : n ≤ ws.length)
    (hW : ∀ x ∈ ws, x.length ≤ W) (τ : Fin 11 → WTape)
    (hX : τ wX = ⟨[], ws⟩) (hO : τ wO = ⟨D, []⟩) (hA : τ wA = emp)
    (hC : τ wC = reg (ones ws.length)) (hH : τ wH = reg (ones n)) (hT : τ wT = reg (ones (ws.length - n)))
    (hFT : τ fT = reg [!e]) (hFH : τ fH = reg [e]) (hQ : τ wQ = emp) (hJ : τ wJ = emp) (hw : τ wW = emp) :
    Runs twistCmd τ (· = Function.update (Function.update τ wX emp) wO ⟨(twWords n e ws).reverse ++ D, []⟩)
      (ws.length * (35 * W + 250) + 200) := by
  set rv := ws.map List.reverse
  have hrv : ∀ x ∈ rv, x.length ≤ W := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; simpa using hW y hy
  have hlr : rv.length = ws.length := by simp [rv]
  have s1 := runs_moveAll ws hW τ hX hA hC hQ hJ
  set τ₁ := Function.update (Function.update τ wX ⟨ws.reverse, []⟩) wA ⟨[], rv⟩
  have s2 := runs_skipHead (n := n) rv (by omega) hrv τ₁ (by tsimp [τ₁]) (by tsimp [τ₁, hH]) (by tsimp [τ₁, hQ])
    (by tsimp [τ₁, hJ])
  set τ₂ := Function.update τ₁ wA ⟨(rv.take n).reverse, rv.drop n⟩
  have hdl : (rv.drop n).length = ws.length - n := by simp [hlr]
  have s3 := runs_emitTail (!e) (rv.drop n) (rv.take n).reverse D (fun x hx => hrv x (List.mem_of_mem_drop hx))
    τ₂ (by tsimp [τ₂]) (by tsimp [τ₂, τ₁, hT, hdl]) (by tsimp [τ₂, τ₁, hFT]) (by tsimp [τ₂, τ₁, hw])
    (by tsimp [τ₂, τ₁, hO]) (by tsimp [τ₂, τ₁, hQ]) (by tsimp [τ₂, τ₁, hJ])
  set τ₃ := Function.update (Function.update τ₂ wA ⟨(rv.drop n).reverse ++ (rv.take n).reverse, []⟩)
    wO ⟨((rv.drop n).map (outW (!e))).reverse ++ D, []⟩
  have htl : (rv.take n).length = n := by simp [hlr]; omega
  have s4 := runs_emitHead (W := W) e (rv.take n) (rv.drop n) (((rv.drop n).map (outW (!e))).reverse ++ D)
    ws.reverse
    (fun x hx => hrv x (by rw [List.take_append_drop] at hx; exact hx))
    (fun x hx => hW x (List.mem_reverse.mp hx))
    τ₃ (by tsimp [τ₃]) (by tsimp [τ₃, τ₂, τ₁, hH, htl]) (by tsimp [τ₃, τ₂, τ₁, hFH]) (by tsimp [τ₃, τ₂, τ₁, hw])
    (by tsimp [τ₃]) (by tsimp [τ₃, τ₂, τ₁, hQ]) (by tsimp [τ₃, τ₂, τ₁, hJ]) (by tsimp [τ₃, τ₂, τ₁])
  have tw : (rv.drop n).map (outW (!e)) ++ (rv.take n).map (outW e) = twWords n e ws := twWords_out n e ws
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ' h => ?_) ?_
  · rw [h, ← tw]; funext y
    simp only [τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hA, emp]) <;> tsimp at *
  · have l1 : (rv.take n).length + (rv.drop n).length = ws.length := by
      rw [← List.length_append, List.take_append_drop, hlr]
    have a1 : n * (W + 25) ≤ ws.length * (W + 25) := Nat.mul_le_mul_right _ hn
    have a2 : (ws.length - n) * (7 * W + 50) ≤ ws.length * (7 * W + 50) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have a3 : (n + (ws.length - n) + ws.length) * (10 * W + 60) = 2 * ws.length * (10 * W + 60) := by
      rw [show n + (ws.length - n) = ws.length by omega]; ring
    simp only [htl, hdl, List.length_reverse]
    nlinarith

theorem recordWords_lengths {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) : ∀ x ∈ recordWords w re im, x.length ≤ w := by
  intro x hx
  simp only [recordWords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨j, -, rfl | rfl⟩ := hx <;> simp

/-- The monomial on a record: from its component words, the output tape gains the component words
of `y^E` times the record (`twistRec`, exact on the grid by `gridPoly_twistRec`). -/
theorem runs_twist_record {r : ℕ} [NeZero r] (w E : ℕ) (f : Spec.SignedRingProduct.Rec r)
    (D : List (List Bool)) (τ : Fin 11 → WTape)
    (hX : τ wX = ⟨[], recordWords w f.1 f.2⟩) (hO : τ wO = ⟨D, []⟩) (hA : τ wA = emp)
    (hC : τ wC = reg (ones (2 * r))) (hH : τ wH = reg (ones (2 * (r - E % r))))
    (hT : τ wT = reg (ones (2 * (E % r))))
    (hFT : τ fT = reg [!decide (E / r % 2 = 1)]) (hFH : τ fH = reg [decide (E / r % 2 = 1)])
    (hQ : τ wQ = emp) (hJ : τ wJ = emp) (hw : τ wW = emp) :
    Runs twistCmd τ (· = Function.update (Function.update τ wX emp) wO
      ⟨(recordWords w (twistRec E f).1 (twistRec E f).2).reverse ++ D, []⟩)
      (2 * r * (35 * w + 250) + 200) := by
  have hs : E % r < r := Nat.mod_lt _ (NeZero.pos r)
  have h := runs_twist (W := w) (n := 2 * (r - E % r)) (decide (E / r % 2 = 1)) (recordWords w f.1 f.2) D
    (by simp) (recordWords_lengths w f.1 f.2) τ hX hO hA (by rw [hC, length_recordWords])
    hH (by rw [hT, length_recordWords]; congr 2; omega) hFT hFH hQ hJ hw
  rw [twWords_recordWords, length_recordWords] at h
  exact h

end TwistTape

end IntegerMultBounds.Schoenhage
