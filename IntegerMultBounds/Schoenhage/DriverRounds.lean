module

public import IntegerMultBounds.Schoenhage.DriverTwist

/-! The Hadamard part of a transform round on the drivers' bank (§6 task 6):
a prefix or top round runs the prefix-round machine on the array with the
round's block ruler and pass count from the round script (`runs_bflyStep`); a
chunk-group round runs the layer program with the round's layer header
(`runs_chunkStep`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

variable {A tL nL : ℕ}

/-- The prefix-round machine as a primitive of the drivers. -/
noncomputable def prefixPrim (A : ℕ) : Prim A :=
  Prim.liftE (Nat.zero_le A) (Prim.ofHoare (compile (a := 0) (by decide) prefixHad).2 (by decide))

/-- A prefix or top round's Hadamard part: drop the kind word, load the ruler and the pass count,
run the prefix-round machine, move its output into the array tape. -/
noncomputable def bflyStep (A tL nL : ℕ) : Cmd A (DB tL nL) :=
  .seq (skp (nm tL nL 6) (nm tL nL 12) (nm_ne (by decide))) <|
  .seq (regIn (nm tL nL 6) (nm tL nL 4) (nm_ne (by decide))) <|
  .seq (regIn (nm tL nL 6) (nm tL nL 3) (nm_ne (by decide))) <|
  .seq (.prim (prefixPrim A) (pslot tL nL) pslot_injective) <|
  .seq (clear (nm tL nL 0)) <| .seq (regMove (nm tL nL 1) (nm tL nL 0) (nm_ne (by decide)))
    (clear (nm tL nL 3))

set_option maxHeartbeats 8000000 in
theorem runs_bflyStep {r w D s c : ℕ} (hr : 1 ≤ r) (hw : 2 ≤ w) (hc : 1 ≤ c) (fs : List (Rec r))
    (hlen : fs.length = 2 ^ (s + D) * c) (hb : Bounded (2 ^ (w - 1) - 1) fs)
    (v : Fin 13 → WTape) (tw : Fin 29 → WTape) {Lr R : List (List Bool)} {kind : List Bool}
    (hR : v 6 = ⟨Lr, kind :: ones (2 * r * 2 ^ s) :: ones D :: R⟩)
    (h0 : v 0 = reg (array w fs)) (h1 : v 1 = emp) (h2 : v 2 = reg (ones w)) (h3 : v 3 = emp) (h4 : v 4 = emp)
    (h12 : v 12 = emp) :
    Runs (bflyStep A tL nL) (dstate tL nL v tw)
      (· = dstate tL nL (Function.update (Function.update v 0
        (reg (array w ((bflysRecs ((List.range D).map (s + ·)) fs).map (truncRec D)))))
        6 ⟨ones D :: ones (2 * r * 2 ^ s) :: kind :: Lr, R⟩) tw)
      (prefixCost w D (2 * r * fs.length) + 8 * (array w fs).length + 2 * kind.length +
        8 * (2 * r * 2 ^ s) + 8 * D + 200) := by
  set B0 := 2 * r * 2 ^ s
  set out := (bflysRecs ((List.range D).map (s + ·)) fs).map (truncRec D)
  -- 1–3. the kind word, the ruler, the pass count
  have s1 := runs_skp (a := A) (nm_ne (tL := tL) (nL := nL) (show (6 : Fin 13) ≠ 12 by decide)) (dstate tL nL v tw)
    (by rw [dstate_nm, hR]; simp) (by rw [dstate_nm, h12]; rfl)
  rw [update_nm, dstate_nm, hR] at s1
  set v1 := Function.update v 6 (WTape.next ⟨Lr, kind :: ones B0 :: ones D :: R⟩)
  have s2 := runs_regIn (a := A) (nm_ne (tL := tL) (nL := nL) (show (6 : Fin 13) ≠ 4 by decide)) (dstate tL nL v1 tw)
    (L := kind :: Lr) (R := ones D :: R) (w := ones B0) (by rw [dstate_nm]; simp [v1, WTape.next, WTape.cur])
    (by rw [dstate_nm]; simp [v1, h4])
  rw [update_nm, update_nm] at s2
  set v2 := Function.update (Function.update v1 6 ⟨ones B0 :: kind :: Lr, ones D :: R⟩) 4 (reg (ones B0))
  have s3 := runs_regIn (a := A) (nm_ne (tL := tL) (nL := nL) (show (6 : Fin 13) ≠ 3 by decide)) (dstate tL nL v2 tw)
    (L := ones B0 :: kind :: Lr) (R := R) (w := ones D) (by rw [dstate_nm]; simp [v2])
    (by rw [dstate_nm]; simp [v2, v1, h3])
  rw [update_nm, update_nm] at s3
  set v3 := Function.update (Function.update v2 6 ⟨ones D :: ones B0 :: kind :: Lr, R⟩) 3 (reg (ones D))
  -- 4. the prefix-round machine
  have hcl : Clean (pview v3) := by
    funext i
    have hi := i.isLt
    change i.val < 64 at hi
    have ne : ∀ x : Fin 𝕌, 64 ≤ x.val → ι i ≠ x := fun x hx e => by
      have := congrArg Fin.val e; simp at this; omega
    simp only [Function.comp_apply, pview]
    rw [ite_eq_right (ne zF (by decide)), ite_eq_right (ne zO (by decide)), ite_eq_right (ne kw (by decide)),
      ite_eq_right (ne kS (by decide)), ite_eq_right (ne xP (by decide))]
  obtain ⟨τp, kp, hxp, hqp, hkp⟩ := runs_prefixHad hr hw hc fs hlen hb (pview v3) hcl
    (by simp (config := {decide := true}) [pview, v3, v2, v1, h0])
    (by simp (config := {decide := true}) [pview, v3, v2, v1, h2])
    (by simp (config := {decide := true}) [pview, v3, v2, v1])
    (by simp (config := {decide := true}) [pview, v3, v2, v1]; rfl)
    (by simp (config := {decide := true}) [pview])
    (by simp (config := {decide := true}) [pview]) (by simp (config := {decide := true}) [pview])
    (by simp (config := {decide := true}) [pview]) (by simp (config := {decide := true}) [pview])
    (by simp (config := {decide := true}) [pview]) (by simp (config := {decide := true}) [pview])
    (by simp (config := {decide := true}) [pview]) (by simp (config := {decide := true}) [pview])
    (by simp (config := {decide := true}) [pview]) (by simp (config := {decide := true}) [pview])
    (by simp (config := {decide := true}) [pview, v3, v2, v1, h1])
  subst hqp
  have hT : HoareTo (compile (a := 0) (by decide) prefixHad).2 (dstate tL nL v3 tw ∘ pslot tL nL)
      (Function.update (Function.update (pview v3) zO (reg (array w out))) xP emp) kp := by
    rw [dstate_comp_pslot]
    exact (compile_correct (by decide) hxp).consequence (fun _ h => h) (fun _ h => h) le_rfl
  have s4 := runs_ofHoare_liftE (Nat.zero_le A) _ (by decide) pslot_injective hT
  rw [upd_dstate_pslot _ _ _ (fun x h1 h2 h3 h4 h5 => by
    simp [h2, h5, pview, h1, h3, h4])] at s4
  set v4 := pnew v3 (Function.update (Function.update (pview v3) zO (reg (array w out))) xP emp)
  -- 5–7. the output into the array tape, the pass count cleared
  have s5 := runs_clear (a := A) (nm tL nL 0) (dstate tL nL v4 tw)
  rw [update_nm] at s5
  set v5 := Function.update v4 0 ⟨[], []⟩
  have s6 := runs_regMove (a := A) (nm_ne (tL := tL) (nL := nL) (show (1 : Fin 13) ≠ 0 by decide))
    (dstate tL nL v5 tw) (w := array w out) (by rw [dstate_nm]; simp (config := {decide := true}) [v5, v4, pnew])
    (by rw [dstate_nm]; simp [v5, emp])
  rw [update_nm, update_nm] at s6
  set v6 := Function.update (Function.update v5 1 emp) 0 (reg (array w out))
  have s7 := runs_clear (a := A) (nm tL nL 3) (dstate tL nL v6 tw)
  rw [update_nm] at s7
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    s7)))))).mono (fun τ h => ?_) ?_
  · rw [h]
    congr 1
    funext i
    fin_cases i <;> simp (config := {decide := true}) [v6, v5, v4, v3, v2, v1, pnew, pview,
      h1, h2, h3, h4, emp]
  · have hlo : (array w out).length = (array w fs).length := by simp [length_array, out]
    simp (config := {decide := true}) only [dstate_nm, v6, v5, v4, v3, v2, v1, pnew, pview, Function.update_apply,
      WTape.words, WTape.cur, h0, reg, emp, ite_true, ite_false, List.reverse_nil, List.nil_append, clen_cons,
      clen_nil, length_ones, List.headD] at *
    omega

/-- The layer program as a primitive of the drivers. -/
noncomputable def layerPrim {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Prim A :=
  Prim.liftE haA (Prim.ofHoare (prog1 M ht) (by omega))

/-- A chunk-group round's Hadamard part: drop the kind word, load the layer header, run the layer
program on header and array, clear the header. -/
noncomputable def chunkStep {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Cmd A (DB tL nL) :=
  .seq (skp (nm tL nL 6) (nm tL nL 12) (nm_ne (by decide))) <|
  .seq (regIn (nm tL nL 6) (nm tL nL 5) (nm_ne (by decide))) <|
  .seq (.prim (layerPrim M ht haA) (lslot tL nL) lslot_injective) (clear (nm tL nL 5))

theorem runs_chunkStep {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    (v : Fin 13 → WTape) (tw : Fin 29 → WTape) {Lr R : List (List Bool)} {kind hdr X X' : List Bool} {k : ℕ}
    (hR : v 6 = ⟨Lr, kind :: hdr :: R⟩) (h0 : v 0 = reg X) (h5 : v 5 = emp) (h12 : v 12 = emp)
    (hM : HoareTo (prog1 M ht) (start1 tL hdr X) (start1 tL hdr X') k) :
    Runs (chunkStep (nL := nL) M ht haA) (dstate tL nL v tw)
      (· = dstate tL nL (Function.update (Function.update v 0 (reg X')) 6 ⟨hdr :: kind :: Lr, R⟩) tw)
      (k + kind.length + 4 * hdr.length + 40) := by
  have s1 := runs_skp (a := A) (nm_ne (tL := tL) (nL := nL) (show (6 : Fin 13) ≠ 12 by decide)) (dstate tL nL v tw)
    (by rw [dstate_nm, hR]; simp) (by rw [dstate_nm, h12]; rfl)
  rw [update_nm, dstate_nm, hR] at s1
  set v1 := Function.update v 6 (WTape.next ⟨Lr, kind :: hdr :: R⟩)
  have s2 := runs_regIn (a := A) (nm_ne (tL := tL) (nL := nL) (show (6 : Fin 13) ≠ 5 by decide)) (dstate tL nL v1 tw)
    (L := kind :: Lr) (R := R) (w := hdr) (by rw [dstate_nm]; simp [v1, WTape.next, WTape.cur])
    (by rw [dstate_nm]; simp [v1, h5])
  rw [update_nm, update_nm] at s2
  set v2 := Function.update (Function.update v1 6 ⟨hdr :: kind :: Lr, R⟩) 5 (reg hdr)
  have hL : HoareTo (prog1 M ht) (dstate tL nL v2 tw ∘ lslot tL nL) (start1 tL hdr X') k := by
    rw [dstate_comp_lslot ht v2 tw (hdr := hdr) (A := X) (by simp [v2]) (by simp [v2, v1, h0])]
    exact hM
  have s3 := runs_ofHoare_liftE haA _ (by omega) lslot_injective hL
  rw [upd_dstate_lslot ht] at s3
  set v3 := Function.update (Function.update v2 5 (reg hdr)) 0 (reg X')
  have s4 := runs_clear (a := A) (nm tL nL 5) (dstate tL nL v3 tw)
  rw [update_nm] at s4
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ h => ?_) ?_
  · rw [h]
    congr 1
    funext i
    fin_cases i <;> simp (config := {decide := true}) [v3, v2, v1, h5, emp]
  · simp (config := {decide := true}) only [dstate_nm, v3, v2, v1, Function.update_apply, WTape.words,
      WTape.cur, reg, ite_true, ite_false, List.reverse_nil, List.nil_append, clen_cons, clen_nil, List.headD] at *
    omega

end IntegerMultBounds.Schoenhage
