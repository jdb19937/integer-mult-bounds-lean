module

public import IntegerMultBounds.Schoenhage.RingConst
public import IntegerMultBounds.Schoenhage.Reverse
public import IntegerMultBounds.Schoenhage.RingProgram

/-! Moving words between tapes, reversed, once per tick: the operand words of
one record go from the chunk lists to the multiplier's input tapes, and its
output words come back, in each case with the bit order turned
(`runs_moveRev`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- Move one word per tick of `qT` from `src` to `dst`, reversed. -/
noncomputable def moveRev (src dst : Fin 𝕌) (h : src ≠ dst) : Cmd 0 𝕌 :=
  .loop (ι qT) (.seq (revw src dst h) (skp (ι qT) (ι tJ) (by decide)))

theorem runs_moveRev {src dst : Fin 𝕌} (h : src ≠ dst) (h1 : src ≠ ι qT) (h2 : dst ≠ ι qT) (h3 : src ≠ ι tJ)
    (h4 : dst ≠ ι tJ) {W : ℕ} :
    ∀ (ws : List (List Bool)) (τ : Fin 𝕌 → WTape) (Ls R D Tl : List (List Bool)),
      (∀ x ∈ ws, x.length ≤ W) → τ src = ⟨Ls, ws ++ R⟩ → τ dst = ⟨D, []⟩ →
      τ (ι qT) = ⟨Tl, List.replicate ws.length []⟩ → τ (ι tJ) = emp →
      Runs (moveRev src dst h) τ (· = Function.update (Function.update (Function.update τ
        src ⟨ws.reverse ++ Ls, R⟩) dst ⟨(ws.map List.reverse).reverse ++ D, []⟩)
        (ι qT) ⟨List.replicate ws.length [] ++ Tl, []⟩) (ws.length * (3 * W + 20))
  | [], τ, Ls, R, D, Tl, _, hs, hd, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    by_cases a1 : y = src <;> by_cases a2 : y = dst <;> by_cases a3 : y = ι qT <;>
      simp_all [Function.update_apply]
  | x :: ws, τ, Ls, R, D, Tl, hW, hs, hd, hT, hJ => by
    have hx := hW x (by simp)
    have s1 := runs_revw (a := 0) h τ (L := Ls) (R := ws ++ R) (w := x) (by simpa using hs) (by simp [hd])
    set τ₁ := Function.update (Function.update τ src ⟨x :: Ls, ws ++ R⟩) dst ⟨x.reverse :: (τ dst).left, []⟩
    have s2 := runs_skp (a := 0) (show ι qT ≠ ι tJ by decide) τ₁
      (by simp [τ₁, h1.symm, h2.symm, hT, List.replicate_succ]) (by simp [τ₁, h3.symm, h4.symm, hJ])
    set τ₂ := Function.update τ₁ (ι qT) (τ₁ (ι qT)).next
    have ih := runs_moveRev h h1 h2 h3 h4 ws τ₂ (x :: Ls) R (x.reverse :: D) ([] :: Tl)
      (fun y hy => hW y (by simp [hy])) (by simp [τ₂, τ₁, h1, h]) (by simp [τ₂, τ₁, h2, hd])
      (by simp [τ₂, τ₁, h1.symm, h2.symm, hT, List.replicate_succ])
      (by simp [τ₂, τ₁, (show ι tJ ≠ ι qT by decide), h3.symm, h4.symm, hJ])
    refine (Runs.loop_step (by simp [hT]) ((Runs.then s1 s2).mono (fun τ' e => by rw [e]; exact ih)
      le_rfl)).mono (fun τ' e => ?_) ?_
    · rw [e]; funext y
      by_cases a1 : y = src <;> by_cases a2 : y = dst <;> by_cases a3 : y = ι qT <;>
        simp_all [τ₂, τ₁, Function.update_apply, List.replicate_succ, replicate_nil_append]
    · have hc : (τ₁ (ι qT)).cur.length = 0 := by simp [τ₁, h1.symm, h2.symm, hT, List.replicate_succ]
      rw [hc]; simp only [List.length_cons]; nlinarith

/-- Append one output word, reversed, to the output string per tick of `qT`. -/
noncomputable def gatherTail : Cmd 0 𝕌 :=
  .seq (rewind (ι tU)) <| .seq (op0 Rules.copy true (ι tU) zO (by decide)) <|
  .seq (clear (ι tU)) (skp (ι qT) (ι tJ) (by decide))

noncomputable def gatherBody : Cmd 0 𝕌 := .seq (revw rO (ι tU) (by decide)) gatherTail

noncomputable def gatherLoop : Cmd 0 𝕌 := .loop (ι qT) gatherBody

theorem runs_gatherBody (τ : Fin 𝕌 → WTape) {o acc : List Bool} {Lo Ro Tl : List (List Bool)} {n : ℕ}
    (hO : τ rO = ⟨Lo, o :: Ro⟩) (hU : τ (ι tU) = emp) (hZ : τ zO = ⟨[acc], []⟩)
    (hT : τ (ι qT) = ⟨Tl, List.replicate (n + 1) []⟩) (hJ : τ (ι tJ) = emp) :
    Runs gatherBody τ (· = Function.update (Function.update (Function.update τ rO ⟨o :: Lo, Ro⟩)
      zO ⟨[acc ++ o.reverse], []⟩) (ι qT) ⟨[] :: Tl, List.replicate n []⟩) (8 * o.length + 40) := by
  have s1 := runs_revw (a := 0) (show rO ≠ ι tU by decide) τ hO (by rw [hU]; rfl)
  set τ₁ := Function.update (Function.update τ rO ⟨o :: Lo, Ro⟩) (ι tU) ⟨o.reverse :: (τ (ι tU)).left, []⟩
  have s2 : Runs gatherTail τ₁
      (· = Function.update (Function.update (Function.update τ rO ⟨o :: Lo, Ro⟩)
        zO ⟨[acc ++ o.reverse], []⟩) (ι qT) ⟨[] :: Tl, List.replicate n []⟩) (5 * o.length + 29) := by
    apply Runs.of_wp
    simp only [gatherTail, skp, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [τ₁, hU, hZ, hT, hJ, emp, Rules.output_copy, Rules.output_skip, List.replicate_succ]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hU, hZ, hT, hJ, emp, List.replicate_succ]) <;> tsimp at *
    · simp [time_copy, time_skip, clen, WTape.words]; omega
  exact (Runs.then s1 s2).mono (fun τ' h => h) (by omega)

theorem runs_gatherLoop {W : ℕ} : ∀ (os : List (List Bool)) (τ : Fin 𝕌 → WTape) (acc : List Bool)
    (Lo Ro Tl : List (List Bool)), (∀ x ∈ os, x.length ≤ W) →
    τ rO = ⟨Lo, os ++ Ro⟩ → τ (ι tU) = emp → τ zO = ⟨[acc], []⟩ →
    τ (ι qT) = ⟨Tl, List.replicate os.length []⟩ → τ (ι tJ) = emp →
    Runs gatherLoop τ (· = Function.update (Function.update (Function.update τ rO ⟨os.reverse ++ Lo, Ro⟩)
      zO ⟨[acc ++ (os.map List.reverse).flatten], []⟩) (ι qT) ⟨List.replicate os.length [] ++ Tl, []⟩)
      (os.length * (8 * W + 42))
  | [], τ, acc, Lo, Ro, Tl, _, hO, _, hZ, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hO, hZ, hT]) <;> tsimp at *
  | o :: os, τ, acc, Lo, Ro, Tl, hW, hO, hU, hZ, hT, hJ => by
    have s1 := runs_gatherBody τ (o := o) (acc := acc) (Lo := Lo) (Ro := os ++ Ro) (Tl := Tl) (n := os.length)
      (by simpa using hO) hU hZ (by simpa using hT) hJ
    set τ₁ := Function.update (Function.update (Function.update τ rO ⟨o :: Lo, os ++ Ro⟩)
      zO ⟨[acc ++ o.reverse], []⟩) (ι qT) ⟨[] :: Tl, List.replicate os.length []⟩
    have ih := runs_gatherLoop os τ₁ (acc ++ o.reverse) (o :: Lo) Ro ([] :: Tl) (fun y hy => hW y (by simp [hy]))
      (by tsimp [τ₁]) (by tsimp [τ₁, hU]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁, hJ])
    refine (Runs.loop_step (by simp [hT]) (s1.mono (fun τ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ' e => ?_) ?_
    · rw [e]; funext y
      simp only [τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [replicate_nil_append, List.replicate_succ]) <;> tsimp at *
    · have := hW o (by simp); simp only [List.length_cons]; nlinarith

/-! ### Ready for a record -/

/-- Everything the ring product needs except its operands. -/
def RecReady (Wd r w s N : ℕ) (τ : Fin 𝕌 → WTape) : Prop :=
  τ rF = emp ∧ τ rG = emp ∧ ∀ fs gs : List (List Bool × List Bool), fs.length = r → gs.length = r →
    (∀ p ∈ fs, p.1.length = w ∧ p.2.length = w) → (∀ p ∈ gs, p.1.length = w ∧ p.2.length = w) →
    RingSetup Wd r w s N fs gs (Function.update (Function.update τ rF ⟨[], flat fs⟩) rG ⟨[], flat gs⟩)

/-- Tapes the ring product never reads. -/
def Free (x : Fin 𝕌) : Prop := x = iP ∨ x = iL ∨ x = iW ∨ x = zH ∨ x = zF ∨ x = zG ∨ x = zO

theorem Free.own {x : Fin 𝕌} (h : Free x) : Own x := by
  unfold Own; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 4000000 in
theorem RingSetup.update_free {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} {τ : Fin 𝕌 → WTape}
    (h : RingSetup Wd r w s N fs gs τ) {x : Fin 𝕌} (hx : Free x) (v : WTape) :
    RingSetup Wd r w s N fs gs (Function.update τ x v) := by
  have n : ∀ y ∈ [rF, rG, rO, kW, kN, kR, kI, kO, kS, kH, kC, kw, xA, xB, xC, xE, xP, xQ, lR, lI], y ≠ x := by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have e : ∀ y ∈ [rF, rG, rO, kW, kN, kR, kI, kO, kS, kH, kC, kw, xA, xB, xC, xE, xP, xQ, lR, lI],
      Function.update τ x v y = τ y := fun y hy => Function.update_of_ne (n y hy) _ _
  exact ⟨h.hr, h.hw, h.hWd, h.hws, h.hN, h.hk, h.lf, h.lg, h.wf, h.wg, h.clean.update hx.own v,
    by rw [e _ (by simp)]; exact h.F, by rw [e _ (by simp)]; exact h.G, by rw [e _ (by simp)]; exact h.O,
    by rw [e _ (by simp)]; exact h.KW, by rw [e _ (by simp)]; exact h.KN, by rw [e _ (by simp)]; exact h.KR,
    by rw [e _ (by simp)]; exact h.KI, by rw [e _ (by simp)]; exact h.KO, by rw [e _ (by simp)]; exact h.KS,
    by rw [e _ (by simp)]; exact h.KH, by rw [e _ (by simp)]; exact h.KC, by rw [e _ (by simp)]; exact h.Kw,
    by rw [e _ (by simp)]; exact h.A, by rw [e _ (by simp)]; exact h.B, by rw [e _ (by simp)]; exact h.C,
    by rw [e _ (by simp)]; exact h.E, by rw [e _ (by simp)]; exact h.P, by rw [e _ (by simp)]; exact h.Q,
    by rw [e _ (by simp)]; exact h.R, by rw [e _ (by simp)]; exact h.I⟩

theorem RecReady.update_free {Wd r w s N : ℕ} {τ : Fin 𝕌 → WTape} (h : RecReady Wd r w s N τ) {x : Fin 𝕌}
    (hx : Free x) (v : WTape) : RecReady Wd r w s N (Function.update τ x v) := by
  obtain ⟨hF, hG, hS⟩ := h
  have nF : rF ≠ x := by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have nG : rG ≠ x := by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨by rw [Function.update_of_ne nF, hF], by rw [Function.update_of_ne nG, hG], fun fs gs h1 h2 h3 h4 => ?_⟩
  have e : Function.update (Function.update (Function.update τ x v) rF ⟨[], flat fs⟩) rG ⟨[], flat gs⟩ =
      Function.update (Function.update (Function.update τ rF ⟨[], flat fs⟩) rG ⟨[], flat gs⟩) x v := by
    rw [Function.update_comm nF.symm, Function.update_comm nG.symm]
  rw [e]; exact (hS fs gs h1 h2 h3 h4).update_free hx v

/-! ### One record -/

/-- Load one record of each operand (reversing its words), multiply, append the reversed output words. -/
noncomputable def recIn : Cmd 0 𝕌 :=
  .seq (ticksFrom iW (by decide)) <| .seq (moveRev iP rF (by decide)) <| .seq (clear (ι qT)) <|
  .seq (rewind rF) <|
  .seq (ticksFrom iW (by decide)) <| .seq (moveRev iL rG (by decide)) <| .seq (clear (ι qT)) (rewind rG)

noncomputable def recOut : Cmd 0 𝕌 :=
  .seq (ticksFrom iW (by decide)) <| .seq gatherLoop <| .seq (clear (ι qT)) <|
  .seq (clear rF) <| .seq (clear rG) (clear rO)

noncomputable def recStep : Cmd 0 𝕌 := .seq recIn <| .seq ringProd recOut

/-- The multiplier's output words for one record pair. -/
def ringWords (Wd r w s N : ℕ) (fs gs : List (List Bool × List Bool)) : List (List Bool) :=
  flat (List.zip (outs Wd r s w N (reRes Wd r w N fs gs)) (outs Wd r s w N (imRes Wd r w N fs gs)))

theorem length_flat (ps : List (List Bool × List Bool)) : (flat ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]; ring

theorem flat_reverse_reverse (ps : List (List Bool × List Bool)) :
    ((flat ps).map List.reverse).map List.reverse = flat ps := by simp [List.map_map]

theorem flat_lengths {w : ℕ} {ps : List (List Bool × List Bool)} (h : ∀ p ∈ ps, p.1.length = w ∧ p.2.length = w) :
    ∀ x ∈ (flat ps).map List.reverse, x.length ≤ w := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  induction ps with
  | nil => simp at hy
  | cons p ps ih =>
    simp only [flat_cons, List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · simp [(h p (by simp)).1]
    · simp [(h p (by simp)).2]
    · exact ih (fun q hq => h q (by simp [hq])) hy

set_option maxHeartbeats 16000000 in
theorem runs_recIn {Wd r w s N : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hW : τ iW = reg (ones (2 * r)))
    (hF : τ rF = emp) (hG : τ rG = emp) {fs gs : List (List Bool × List Bool)} (hlf : fs.length = r)
    (hlg : gs.length = r) (hwf : ∀ p ∈ fs, p.1.length = w ∧ p.2.length = w)
    (hwg : ∀ p ∈ gs, p.1.length = w ∧ p.2.length = w) {Lf Rf Lg Rg : List (List Bool)}
    (hP : τ iP = ⟨Lf, (flat fs).map List.reverse ++ Rf⟩) (hL : τ iL = ⟨Lg, (flat gs).map List.reverse ++ Rg⟩) :
    Runs recIn τ (· = Function.update (Function.update (Function.update (Function.update τ
      iP ⟨((flat fs).map List.reverse).reverse ++ Lf, Rf⟩) iL ⟨((flat gs).map List.reverse).reverse ++ Lg, Rg⟩)
      rF ⟨[], flat fs⟩) rG ⟨[], flat gs⟩) (r * (24 * w + 200) + 100) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have lF : ((flat fs).map List.reverse).length = 2 * r := by simp [length_flat, hlf]
  have lG : ((flat gs).map List.reverse).length = 2 * r := by simp [length_flat, hlg]
  set A := (flat fs).map List.reverse
  set B := (flat gs).map List.reverse
  have s1 := runs_ticksFrom (show iW ≠ ι qT by decide) τ (b := 2 * r) hW (hz qT)
  set τ₁ := Function.update τ (ι qT) ⟨[], List.replicate (2 * r) []⟩
  have s2 := runs_moveRev (show iP ≠ rF by decide) (by decide) (by decide) (by decide) (by decide) (W := w)
    A τ₁ Lf Rf [] [] (flat_lengths hwf) (by tsimp [τ₁, hP]) (by tsimp [τ₁, hF, emp]) (by tsimp [τ₁, lF])
    (by tsimp [τ₁, hz])
  rw [lF] at s2
  set τ₂ := Function.update (Function.update (Function.update τ₁ iP ⟨A.reverse ++ Lf, Rf⟩)
    rF ⟨(A.map List.reverse).reverse ++ [], []⟩) (ι qT) ⟨List.replicate (2 * r) [] ++ [], []⟩
  have s3 := runs_clear (a := 0) (ι qT) τ₂
  have s4 := runs_rewind (a := 0) rF (Function.update τ₂ (ι qT) ⟨[], []⟩)
  set τ₄ := Function.update (Function.update τ₂ (ι qT) ⟨[], []⟩) rF ⟨[], flat fs⟩
  have e₄ : Function.update (Function.update τ₂ (ι qT) ⟨[], []⟩) rF
      ⟨[], (Function.update τ₂ (ι qT) ⟨[], []⟩ rF).left.reverse ++ (Function.update τ₂ (ι qT) ⟨[], []⟩ rF).right⟩
      = τ₄ := by simp only [τ₄]; tsimp [τ₂, A, flat_reverse_reverse]
  have s5 := runs_ticksFrom (show iW ≠ ι qT by decide) τ₄ (b := 2 * r) (by tsimp [τ₄, τ₂, τ₁, hW])
    (by tsimp [τ₄, emp])
  set τ₅ := Function.update τ₄ (ι qT) ⟨[], List.replicate (2 * r) []⟩
  have s6 := runs_moveRev (show iL ≠ rG by decide) (by decide) (by decide) (by decide) (by decide) (W := w)
    B τ₅ Lg Rg [] [] (flat_lengths hwg) (by tsimp [τ₅, τ₄, τ₂, τ₁, hL]) (by tsimp [τ₅, τ₄, τ₂, τ₁, hG, emp])
    (by tsimp [τ₅, lG]) (by tsimp [τ₅, τ₄, τ₂, τ₁, hz])
  rw [lG] at s6
  set τ₆ := Function.update (Function.update (Function.update τ₅ iL ⟨B.reverse ++ Lg, Rg⟩)
    rG ⟨(B.map List.reverse).reverse ++ [], []⟩) (ι qT) ⟨List.replicate (2 * r) [] ++ [], []⟩
  have s7 := runs_clear (a := 0) (ι qT) τ₆
  have s8 := runs_rewind (a := 0) rG (Function.update τ₆ (ι qT) ⟨[], []⟩)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then (s4.mono (fun _ h => h.trans e₄) le_rfl)
    (Runs.then s5 (Runs.then s6 (Runs.then s7 s8))))))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5 s6 s7 s8 e₄
    rw [h]; funext y
    by_cases hm : y ∈ [iP, iL, rF, rG, ι qT]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₆, τ₅, τ₄, τ₂, τ₁] <;> tsimp [hz, emp, B, flat_reverse_reverse]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5⟩ := hm
      simp only [τ₆, τ₅, τ₄, τ₂, τ₁, Function.update_apply, n1, n2, n3, n4, n5, if_false]
  · clear s1 s2 s3 s4 s5 s6 s7 s8 e₄
    tsimp [τ₆, τ₅, τ₄, τ₂, τ₁, hz, hF, hG, emp, reg, WTape.words, clen_cons, clen_nil, length_ones,
      clen_replicate_nil, clen_reverse]
    have cA : clen (List.map List.reverse A) = r * 2 * (w + 1) := by
      simp only [A, flat_reverse_reverse]; rw [clen_flat fs hwf, hlf]
    have cB : clen (List.map List.reverse B) = r * 2 * (w + 1) := by
      simp only [B, flat_reverse_reverse]; rw [clen_flat gs hwg, hlg]
    rw [cA, cB]; nlinarith

theorem ringWords_length (Wd r w s N : ℕ) (fs gs : List (List Bool × List Bool)) :
    (ringWords Wd r w s N fs gs).length = 2 * r := by
  simp [ringWords, length_flat, length_outs]

theorem ringWords_le {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} :
    ∀ x ∈ ringWords Wd r w s N fs gs, x.length ≤ w := by
  intro x hx
  have key : ∀ ps : List (List Bool × List Bool), (∀ p ∈ ps, p.1.length ≤ w ∧ p.2.length ≤ w) →
      ∀ x ∈ flat ps, x.length ≤ w := by
    intro ps; induction ps with
    | nil => simp
    | cons p ps ih =>
      intro h x hx
      simp only [flat_cons, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact (h p (by simp)).1
      · exact (h p (by simp)).2
      · exact ih (fun q hq => h q (by simp [hq])) x hx
  refine key _ (fun p hp => ?_) x hx
  have := List.of_mem_zip hp
  exact ⟨outs_length_le _ this.1, outs_length_le _ this.2⟩

set_option maxHeartbeats 16000000 in
theorem runs_recOut {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hW : τ iW = reg (ones (2 * r))) {acc : List Bool} (hZ : τ zO = ⟨[acc], []⟩)
    (hO : τ rO = ⟨[], ringWords Wd r w s N fs gs⟩) (hF : τ rF = ⟨[], flat fs⟩) (hG : τ rG = ⟨[], flat gs⟩)
    (hlf : fs.length = r) (hlg : gs.length = r) (hwf : ∀ p ∈ fs, p.1.length = w ∧ p.2.length = w)
    (hwg : ∀ p ∈ gs, p.1.length = w ∧ p.2.length = w) :
    Runs recOut τ (· = Function.update (Function.update (Function.update (Function.update τ
      zO ⟨[acc ++ ((ringWords Wd r w s N fs gs).map List.reverse).flatten], []⟩) rF emp) rG emp) rO emp)
      (r * (32 * w + 200) + 100) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set Os := ringWords Wd r w s N fs gs
  have lO : Os.length = 2 * r := ringWords_length Wd r w s N fs gs
  have s1 := runs_ticksFrom (show iW ≠ ι qT by decide) τ (b := 2 * r) hW (hz qT)
  set τ₁ := Function.update τ (ι qT) ⟨[], List.replicate (2 * r) []⟩
  have s2 := runs_gatherLoop (W := w) Os τ₁ acc [] [] [] ringWords_le (by tsimp [τ₁, hO]) (by tsimp [τ₁, hz])
    (by tsimp [τ₁, hZ]) (by tsimp [τ₁, lO]) (by tsimp [τ₁, hz])
  rw [lO] at s2
  set τ₂ := Function.update (Function.update (Function.update τ₁ rO ⟨Os.reverse ++ [], []⟩)
    zO ⟨[acc ++ (Os.map List.reverse).flatten], []⟩) (ι qT) ⟨List.replicate (2 * r) [] ++ [], []⟩
  have s3 := runs_clear (a := 0) (ι qT) τ₂
  have s4 := runs_clear (a := 0) rF (Function.update τ₂ (ι qT) ⟨[], []⟩)
  have s5 := runs_clear (a := 0) rG (Function.update (Function.update τ₂ (ι qT) ⟨[], []⟩) rF ⟨[], []⟩)
  have s6 := runs_clear (a := 0) rO (Function.update (Function.update (Function.update τ₂ (ι qT) ⟨[], []⟩)
    rF ⟨[], []⟩) rG ⟨[], []⟩)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5 s6
    rw [h]; funext y
    by_cases hm : y ∈ [zO, rF, rG, rO, ι qT]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp only [τ₂, τ₁] <;> tsimp [hz, emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5⟩ := hm
      simp only [τ₂, τ₁, Function.update_apply, n1, n2, n3, n4, n5, if_false]
  · clear s1 s2 s3 s4 s5 s6
    have cO : clen Os ≤ 2 * r * (w + 1) := by
      have := clen_le (W := w) (L := Os) ringWords_le; rwa [lO] at this
    tsimp [τ₂, τ₁, hz, hF, hG, emp, reg, WTape.words, clen_cons, clen_nil, clen_replicate_nil, clen_reverse,
      clen_append, clen_flat fs hwf, clen_flat gs hwg, hlf, hlg]
    nlinarith

set_option maxHeartbeats 8000000 in
theorem runs_recStep {Wd r w s N : ℕ} (τ : Fin 𝕌 → WTape) (hR : RecReady Wd r w s N τ)
    (hW : τ iW = reg (ones (2 * r))) {fs gs : List (List Bool × List Bool)} (hlf : fs.length = r)
    (hlg : gs.length = r) (hwf : ∀ p ∈ fs, p.1.length = w ∧ p.2.length = w)
    (hwg : ∀ p ∈ gs, p.1.length = w ∧ p.2.length = w) {Lf Rf Lg Rg : List (List Bool)} {acc : List Bool}
    (hP : τ iP = ⟨Lf, (flat fs).map List.reverse ++ Rf⟩) (hL : τ iL = ⟨Lg, (flat gs).map List.reverse ++ Rg⟩)
    (hZ : τ zO = ⟨[acc], []⟩) :
    Runs recStep τ (· = Function.update (Function.update (Function.update τ
      iP ⟨((flat fs).map List.reverse).reverse ++ Lf, Rf⟩) iL ⟨((flat gs).map List.reverse).reverse ++ Lg, Rg⟩)
      zO ⟨[acc ++ ((ringWords Wd r w s N fs gs).map List.reverse).flatten], []⟩)
      (r * (56 * w + 400) + ringCost Wd r w s N + 202) := by
  set τP := Function.update (Function.update τ iP ⟨((flat fs).map List.reverse).reverse ++ Lf, Rf⟩)
    iL ⟨((flat gs).map List.reverse).reverse ++ Lg, Rg⟩
  have hR' : RecReady Wd r w s N τP := (hR.update_free (Or.inl rfl) _).update_free (Or.inr (Or.inl rfl)) _
  have hS := hR'.2.2 fs gs hlf hlg hwf hwg
  have hc : Clean τ := by
    have := hS.clean
    unfold Clean at this ⊢
    rwa [comp_ι_update_own (show Own rG by unfold Own; decide), comp_ι_update_own (show Own rF by unfold Own; decide),
      comp_ι_update_own (show Own iL by unfold Own; decide), comp_ι_update_own (show Own iP by unfold Own; decide)]
      at this
  have s1 := runs_recIn (Wd := Wd) (s := s) (N := N) τ hc hW hR.1 hR.2.1 hlf hlg hwf hwg hP hL
  have s2 := runs_ringProd hS
  set τ₁ := Function.update (Function.update τP rF ⟨[], flat fs⟩) rG ⟨[], flat gs⟩
  have s3 := runs_recOut (Wd := Wd) (r := r) (w := w) (s := s) (N := N) (fs := fs) (gs := gs) (acc := acc)
    (Function.update τ₁ rO ⟨[], ringWords Wd r w s N fs gs⟩)
    (hS.clean.update (show Own rO by unfold Own; decide) _) (by tsimp [τ₁, τP, hW]) (by tsimp [τ₁, τP, hZ])
    (by tsimp [ringWords]) (by tsimp [τ₁]) (by tsimp [τ₁]) hlf hlg hwf hwg
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ₉ h => ?_) (by nlinarith)
  rw [h]; funext y
  have hO : τ rO = emp := by have := hS.O; tsimp [τ₁, τP] at this; exact this
  by_cases hm : y ∈ [iP, iL, zO, rF, rG, rO]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [τ₁, τP] <;> tsimp [hR.1, hR.2.1, hO, emp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hm
    simp only [τ₁, τP, Function.update_apply, n1, n2, n3, n4, n5, n6, if_false]

/-! ### Every record -/

/-- One record per pass while operand words remain. -/
noncomputable def recLoop : Cmd 0 𝕌 := .loop iP recStep

/-- The operand words of a list of records, as stored (most significant bit first). -/
def opWords (qs : List (List (List Bool × List Bool))) : List (List Bool) :=
  (qs.map fun q => (flat q).map List.reverse).flatten

set_option maxHeartbeats 8000000 in
theorem runs_recLoop {Wd r w s N : ℕ} (hr : 1 ≤ r) :
    ∀ (ps : List (List (List Bool × List Bool) × List (List Bool × List Bool))) (τ : Fin 𝕌 → WTape)
      (Lf Lg : List (List Bool)) (acc : List Bool),
      (∀ q ∈ ps, q.1.length = r ∧ q.2.length = r ∧ (∀ p ∈ q.1, p.1.length = w ∧ p.2.length = w) ∧
        (∀ p ∈ q.2, p.1.length = w ∧ p.2.length = w)) →
      RecReady Wd r w s N τ → τ iW = reg (ones (2 * r)) →
      τ iP = ⟨Lf, opWords (ps.map Prod.fst)⟩ → τ iL = ⟨Lg, opWords (ps.map Prod.snd)⟩ →
      τ zO = ⟨[acc], []⟩ →
      Runs recLoop τ (· = Function.update (Function.update (Function.update τ
        iP ⟨(opWords (ps.map Prod.fst)).reverse ++ Lf, []⟩) iL ⟨(opWords (ps.map Prod.snd)).reverse ++ Lg, []⟩)
        zO ⟨[acc ++ (ps.map fun q => ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten).flatten], []⟩)
        (ps.length * (r * (56 * w + 400) + ringCost Wd r w s N + 204))
  | [], τ, Lf, Lg, acc, _, _, _, hP, hL, hZ => by
    refine (Runs.loop_done (by simp [hP, opWords]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hP, hL, hZ, opWords]) <;> tsimp at *
  | q :: ps, τ, Lf, Lg, acc, hq, hR, hW, hP, hL, hZ => by
    obtain ⟨h1, h2, h3, h4⟩ := hq q (by simp)
    have s1 := runs_recStep (Wd := Wd) (s := s) (N := N) τ hR hW h1 h2 h3 h4 (Lf := Lf) (Lg := Lg)
      (Rf := opWords (ps.map Prod.fst)) (Rg := opWords (ps.map Prod.snd)) (acc := acc)
      (by rw [hP]; simp [opWords]) (by rw [hL]; simp [opWords]) hZ
    set τ₁ := Function.update (Function.update (Function.update τ
      iP ⟨((flat q.1).map List.reverse).reverse ++ Lf, opWords (ps.map Prod.fst)⟩)
      iL ⟨((flat q.2).map List.reverse).reverse ++ Lg, opWords (ps.map Prod.snd)⟩)
      zO ⟨[acc ++ ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten], []⟩
    have hR₁ : RecReady Wd r w s N τ₁ :=
      ((hR.update_free (Or.inl rfl) _).update_free (Or.inr (Or.inl rfl)) _).update_free
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) _
    have ih := runs_recLoop hr ps τ₁ (((flat q.1).map List.reverse).reverse ++ Lf)
      (((flat q.2).map List.reverse).reverse ++ Lg) (acc ++ ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten)
      (fun x hx => hq x (by simp [hx])) hR₁ (by tsimp [τ₁, hW]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁])
    have hne : (τ iP).right ≠ [] := by
      have hl : ((flat q.1).map List.reverse).length = 2 * r := by simp [length_flat, h1]
      have h0 : (flat q.1).map List.reverse ≠ [] := by
        intro e; rw [e] at hl; simp at hl; omega
      rw [hP]
      show opWords ((q :: ps).map Prod.fst) ≠ []
      simp only [opWords, List.map_cons, List.flatten_cons]
      exact List.append_ne_nil_of_left_ne_nil h0 _
    refine (Runs.loop_step hne (s1.mono (fun τ' e => by rw [e]; exact ih) le_rfl)).mono (fun τ' e => ?_) ?_
    · rw [e]; funext y
      simp only [τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [opWords, List.append_assoc]) <;> tsimp [opWords] at *
    · simp only [List.length_cons]; nlinarith

end IntegerMultBounds.Schoenhage
