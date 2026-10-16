module

public import IntegerMultBounds.Schoenhage.DriverCalls

/-! One twist step of the transform drivers (§6 task 6): the round's table moves
from the round script to the twist block's table tape, the array word is cut
into component words, the twist program runs on its block, and the twisted
component words are joined back into the array word (`runs_twistStep`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct

variable {A t : ℕ}

/-- Ticks from a unary register `s` onto the empty tape `d`. -/
noncomputable def tickN (s d : Fin t) (h : s ≠ d) : Cmd A t :=
  .seq (op0 Rules.ticks false s d h) <| .seq (rewind s) (rewind d)

theorem runs_tickN {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {n : ℕ} (hs : σ s = reg (ones n))
    (hd : σ d = emp) :
    Runs (a := A) (tickN s d h) σ (· = Function.update σ d ⟨[], List.replicate n []⟩) (4 * n + 20) := by
  apply Runs.of_wp
  simp only [tickN, WP, wp_op0, wp_rewind]
  have e1 : (σ s).cur = ones n := by rw [hs]; rfl
  have e2 : (σ s).right = [ones n] := by rw [hs]; rfl
  have e3 : (σ d).right = [] := by rw [hd]; rfl
  have e4 : (σ d).left = [] := by rw [hd]; rfl
  simp only [e1, e2, e3, Rules.output_ticks, length_ones, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
    parse_syms, Bool.false_eq_true, false_implies, and_true, Function.update_self,
    Function.update_of_ne h.symm, Function.update_of_ne h]
  refine ⟨?_, ?_⟩
  · funext x
    by_cases a1 : x = d
    · subst a1; simp [hd, emp, WTape.put]
    · by_cases a2 : x = s
      · subst a2; simp [a1, hs, reg, WTape.next]
      · simp [a1, a2]
  · have t1 := time_le Rules.ticks (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
    have hb : Rules.ticks.B = 0 := rfl
    rw [length_ones, hb] at t1
    generalize time Rules.ticks (ones n) (fun j => j.elim0) = T at t1 ⊢
    simp [hs, hd, emp, reg, clen_replicate_nil, WTape.put, WTape.next]
    omega

/-! ### The twist step -/

variable {tL nL : ℕ}

theorem nm_ne {i j : Fin 13} (h : i ≠ j) : nm tL nL i ≠ nm tL nL j := fun e => h (nm_inj e)

/-- The twist step: load the round's table, cut, twist on the twist block, join. -/
noncomputable def twistStep (A tL nL : ℕ) (c : Cmd 0 29) : Cmd A (DB tL nL) :=
  .seq (regIn (nm tL nL 6) (nm tL nL 8) (nm_ne (by decide))) <|
  .seq (tickN (nm tL nL 8) (nm tL nL 9) (nm_ne (by decide))) <|
  .seq (moveN (nm tL nL 9) (nm tL nL 6) (twT tL nL 16) (nm tL nL 12) (nm_ne_twT _ _) (nm_ne (by decide))) <|
  .seq (clear (nm tL nL 9)) <| .seq (clear (nm tL nL 8)) <| .seq (rewind (twT tL nL 16)) <|
  .seq (chunkw (nm tL nL 0) (nm tL nL 2) (twT tL nL 0) (nm_ne (by decide)) (nm_ne_twT _ _) (nm_ne_twT _ _)) <|
  .seq (rewind (twT tL nL 0)) <|
  .seq (.prim (Prim.liftE (Nat.zero_le A) (Prim.ofHoare (compile (a := 0) (by decide) c).2 (by decide)))
    (twT tL nL) twT_injective) <|
  .seq (clear (nm tL nL 0)) <| .seq (rewind (twT tL nL 1)) <|
  .seq (joinAll (twT tL nL 1) (nm tL nL 0) (fun e => nm_ne_twT _ _ e.symm)) <| .seq (rewind (nm tL nL 0)) <|
  .seq (clear (twT tL nL 0)) <| .seq (clear (twT tL nL 1)) (clear (twT tL nL 16))

theorem clen_cut_array {r w : ℕ} (hw : 1 ≤ w) (fs : List (Rec r)) :
    clen (cut w (array w fs)) ≤ 2 * (array w fs).length := by
  have hd : w ∣ (array w fs).length := by rw [length_array]; exact Dvd.intro (2 * r * fs.length) (by ring)
  rw [clen_uniform _ w (cut_lengths hw _ hd), length_cut hw _ hd]
  have := Nat.div_mul_le_self (array w fs).length w
  nlinarith [Nat.div_le_self (array w fs).length w]

theorem clen_le_of {L : List (List Bool)} {W : ℕ} (h : ∀ x ∈ L, x.length ≤ W) : clen L ≤ L.length * (W + 1) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [clen_cons, List.length_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    nlinarith

set_option maxHeartbeats 8000000 in
theorem runs_twistStep {r : ℕ} (c : Cmd 0 29) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    {Lr R tab : List (List Bool)} {nT Wt w : ℕ} {fs gs : List (Rec r)} {B : ℕ} (hw : 1 ≤ w)
    (hR : v 6 = ⟨Lr, ones nT :: (tab ++ R)⟩) (htl : tab.length = nT) (htw : ∀ x ∈ tab, x.length ≤ Wt)
    (h0 : v 0 = reg (array w fs)) (h2 : v 2 = reg (ones w)) (h8 : v 8 = emp) (h9 : v 9 = emp) (h12 : v 12 = emp)
    (t0 : tw 0 = emp) (t1 : tw 1 = emp) (t16 : tw 16 = emp)
    (hc : Runs c (Function.update (Function.update tw 0 ⟨[], cut w (array w fs)⟩) 16 ⟨[], tab⟩)
      (· = Function.update (Function.update (Function.update (Function.update tw 0 ⟨[], cut w (array w fs)⟩)
        16 ⟨[], tab⟩) 0 ⟨(cut w (array w fs)).reverse, []⟩) 1 ⟨(cut w (array w gs)).reverse, []⟩) B) :
    Runs (twistStep A tL nL c) (dstate tL nL v tw)
      (· = dstate tL nL (Function.update (Function.update v 0 (reg (array w gs))) 6
        ⟨tab.reverse ++ ones nT :: Lr, R⟩) tw)
      (B + nT * (5 * Wt + 40) + 40 * (array w fs).length + 40 * (array w gs).length + 400) := by
  set x := array w fs
  set y := array w gs
  -- 1. the table count
  have s1 := runs_regIn (a := A) (nm_ne (tL := tL) (nL := nL) (show (6 : Fin 13) ≠ 8 by decide)) (dstate tL nL v tw)
    (L := Lr) (R := tab ++ R) (w := ones nT) (by rw [dstate_nm, hR]) (by rw [dstate_nm, h8])
  rw [update_nm, update_nm] at s1
  set v1 := Function.update (Function.update v 6 ⟨ones nT :: Lr, tab ++ R⟩) 8 (reg (ones nT))
  -- 2. ticks
  have s2 := runs_tickN (A := A) (nm_ne (tL := tL) (nL := nL) (show (8 : Fin 13) ≠ 9 by decide)) (dstate tL nL v1 tw)
    (n := nT) (by rw [dstate_nm]; simp [v1]) (by rw [dstate_nm]; simp [v1, h9])
  rw [update_nm] at s2
  set v2 := Function.update v1 9 ⟨[], List.replicate nT []⟩
  -- 3. the table
  have s3 := runs_moveN (a := A) (k := nm tL nL 9) (s := nm tL nL 6) (d := twT tL nL 16) (j := nm tL nL 12)
    (nm_ne_twT _ _) (nm_ne (by decide)) (nm_ne (by decide)) (nm_ne_twT _ _) (nm_ne (by decide))
    (fun e => nm_ne_twT _ _ e.symm) Wt (List.replicate nT []) (dstate tL nL v2 tw) [] (ones nT :: Lr) tab R []
    (by rw [dstate_nm]; simp [v2]) (by rw [dstate_nm]; simp [v2, v1]) (by simp [htl])
    (by rw [dstate_twT, t16]; rfl) (by rw [dstate_nm]; simp [v2, v1, h12, emp]) htw
    (fun z hz => by rw [List.eq_of_mem_replicate hz]; simp)
  rw [update_nm, update_nm, update_tw] at s3
  set v3 := Function.update (Function.update v2 9 ⟨(List.replicate nT []).reverse ++ [], []⟩) 6
    ⟨tab.reverse ++ ones nT :: Lr, R⟩
  set tw3 := Function.update tw 16 ⟨tab.reverse ++ [], []⟩
  -- 4–6. clear the counters, rewind the table
  have s4 := runs_clear (a := A) (nm tL nL 9) (dstate tL nL v3 tw3)
  rw [update_nm] at s4
  have s5 := runs_clear (a := A) (nm tL nL 8) (dstate tL nL (Function.update v3 9 ⟨[], []⟩) tw3)
  rw [update_nm] at s5
  set v5 := Function.update (Function.update v3 9 ⟨[], []⟩) 8 ⟨[], []⟩
  have s6 := runs_rewind (a := A) (twT tL nL 16) (dstate tL nL v5 tw3)
  rw [update_tw] at s6
  set tw6 := Function.update tw3 16 ⟨[], (dstate tL nL v5 tw3 (twT tL nL 16)).left.reverse ++
    (dstate tL nL v5 tw3 (twT tL nL 16)).right⟩
  have htw6 : tw6 = Function.update tw 16 ⟨[], tab⟩ := by
    simp only [tw6, tw3, dstate_twT]; simp
  rw [htw6] at s6
  -- 7–8. cut the array into component words
  have s7 := runs_chunkw (a := A) (nm_ne (tL := tL) (nL := nL) (show (0 : Fin 13) ≠ 2 by decide)) (nm_ne_twT _ _)
    (nm_ne_twT _ _) (dstate tL nL v5 (Function.update tw 16 ⟨[], tab⟩)) (L := []) (R := []) (x := x) (w := w)
    (by rw [dstate_nm]; simp [v5, v3, v2, v1, h0, reg]) (by rw [dstate_nm]; simp [v5, v3, v2, v1, h2]) hw
    (by rw [dstate_twT, Function.update_of_ne (show (0 : Fin 29) ≠ 16 by decide), t0]; rfl)
  rw [update_nm, update_tw] at s7
  set v7 := Function.update v5 0 ⟨[x], []⟩
  have htw7 : Function.update (Function.update tw 16 ⟨[], tab⟩) 0
      ⟨(cut w x).reverse ++ (dstate tL nL v5 (Function.update tw 16 ⟨[], tab⟩) (twT tL nL 0)).left, []⟩ =
      Function.update (Function.update tw 16 ⟨[], tab⟩) 0 ⟨(cut w x).reverse, []⟩ := by
    rw [dstate_twT, Function.update_of_ne (show (0 : Fin 29) ≠ 16 by decide), t0]; simp [emp]
  rw [htw7] at s7
  have s8 := runs_rewind (a := A) (twT tL nL 0)
    (dstate tL nL v7 (Function.update (Function.update tw 16 ⟨[], tab⟩) 0 ⟨(cut w x).reverse, []⟩))
  rw [update_tw, dstate_twT] at s8
  set tw8 := Function.update (Function.update tw 16 ⟨[], tab⟩) 0 ⟨[], cut w x⟩
  have htw8 : Function.update (Function.update (Function.update tw 16 ⟨[], tab⟩) 0 ⟨(cut w x).reverse, []⟩) 0
      ⟨[], (Function.update (Function.update tw 16 ⟨[], tab⟩) 0 ⟨(cut w x).reverse, []⟩ 0).left.reverse ++
        (Function.update (Function.update tw 16 ⟨[], tab⟩) 0 ⟨(cut w x).reverse, []⟩ 0).right⟩ = tw8 := by
    simp [tw8]
  rw [htw8] at s8
  -- 9. the twist
  have hc' : Runs c tw8 (· = Function.update (Function.update tw8 0 ⟨(cut w x).reverse, []⟩) 1
      ⟨(cut w y).reverse, []⟩) B := by
    have e : Function.update (Function.update tw 0 ⟨[], cut w x⟩) 16 ⟨[], tab⟩ = tw8 :=
      Function.update_comm (show (0 : Fin 29) ≠ 16 by decide) _ _ _
    rw [e] at hc
    exact hc
  obtain ⟨τc, kc, hxc, hqc, hkc⟩ := hc'
  subst hqc
  have hT : HoareTo (compile (a := 0) (by decide) c).2 (dstate tL nL v7 tw8 ∘ twT tL nL)
      (Function.update (Function.update tw8 0 ⟨(cut w x).reverse, []⟩) 1 ⟨(cut w y).reverse, []⟩) B := by
    rw [dstate_comp_twT]
    exact (compile_correct (by decide) hxc).consequence (fun _ h => h) (fun _ h => h) hkc
  have s9 := runs_ofHoare_liftE (Nat.zero_le A) _ (by decide) twT_injective hT
  rw [upd_dstate_twT] at s9
  set tw9 := Function.update (Function.update tw8 0 ⟨(cut w x).reverse, []⟩) 1 ⟨(cut w y).reverse, []⟩
  -- 10–13. join the twisted words into the array word
  have s10 := runs_clear (a := A) (nm tL nL 0) (dstate tL nL v7 tw9)
  rw [update_nm] at s10
  set v10 := Function.update v7 0 ⟨[], []⟩
  have s11 := runs_rewind (a := A) (twT tL nL 1) (dstate tL nL v10 tw9)
  rw [update_tw, dstate_twT] at s11
  set tw11 := Function.update tw9 1 ⟨[], (tw9 1).left.reverse ++ (tw9 1).right⟩
  have h11 : tw11 1 = ⟨[], cut w y⟩ := by simp [tw11, tw9]
  have s12 := runs_joinAll (a := A) (fun e => nm_ne_twT (tL := tL) (nL := nL) 0 1 e.symm) (cut w y)
    (dstate tL nL v10 tw11) [] [] (by rw [dstate_twT, h11]) (by rw [dstate_nm]; simp [v10])
  rw [update_tw, update_nm] at s12
  set tw12 := Function.update tw11 1 ⟨(cut w y).reverse ++ [], []⟩
  set v12 := Function.update v10 0 ⟨[(cut w y).flatten], []⟩
  have s13 := runs_rewind (a := A) (nm tL nL 0) (dstate tL nL v12 tw12)
  rw [update_nm, dstate_nm] at s13
  -- 14–16. clear the twist block's data tapes
  set v13 := Function.update v12 0 ⟨[], (v12 0).left.reverse ++ (v12 0).right⟩
  have s14 := runs_clear (a := A) (twT tL nL 0) (dstate tL nL v13 tw12)
  rw [update_tw] at s14
  have s15 := runs_clear (a := A) (twT tL nL 1) (dstate tL nL v13 (Function.update tw12 0 ⟨[], []⟩))
  rw [update_tw] at s15
  have s16 := runs_clear (a := A) (twT tL nL 16)
    (dstate tL nL v13 (Function.update (Function.update tw12 0 ⟨[], []⟩) 1 ⟨[], []⟩))
  rw [update_tw] at s16
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13
    (Runs.then s14 (Runs.then s15 s16))))))))))))))).mono (fun τ h => ?_) ?_
  · rw [h]
    congr 1
    · funext i
      simp only [v13, v12, v10, v7, v5, v3, v2, v1, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> simp_all [cut_flatten, reg, emp]
    · funext j
      simp only [tw12, tw11, tw9, tw8, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> simp_all [emp]
  · have cx := clen_cut_array hw fs
    have cy := clen_cut_array hw gs
    have ct := clen_le_of htw
    have hlx : (cut w y).length ≤ y.length := by
      have hd : w ∣ y.length := by simp only [y]; rw [length_array]; exact Dvd.intro (2 * r * gs.length) (by ring)
      rw [length_cut hw _ hd]; exact Nat.div_le_self _ _
    simp (config := {decide := true}) only [dstate_nm, dstate_twT, v13, v12, v10, v7, v5, v3, v2, v1, tw12, tw11,
      tw9, tw8, tw3, Function.update_apply, WTape.words, clen_reverse, List.reverse_nil, List.nil_append,
      List.append_nil, List.reverse_reverse, clen_cons, clen_nil, length_ones, List.length_replicate,
      clen_replicate_nil, h0, h8, h9, reg, emp, ite_true, ite_false, cut_flatten] at *
    rw [htl] at ct
    simp only [x, y] at *
    nlinarith

end IntegerMultBounds.Schoenhage
