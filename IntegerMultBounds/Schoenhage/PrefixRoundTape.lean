module

public import IntegerMultBounds.Schoenhage.BlockPass
public import IntegerMultBounds.Schoenhage.ConvScaleRun

/-! §6 task 5 on the ring product's word tapes: one prefix-round pass in
blocks of `B` words (`runs_passLoop`, output `blockPass B`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Rules

/-! ### Blocks -/

theorem blockPass_cons {B : ℕ} (xs ys R : List (List Bool)) (hx : xs.length = B) (hy : ys.length = B) :
    blockPass B (xs ++ ys ++ R) =
      List.zipWith (addW false) xs ys ++ List.zipWith (fun x y => addW true x (cmpl y)) xs ys ++ blockPass B R := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    rw [List.length_eq_zero_iff] at hx hy; subst hx; subst hy; simp
  apply List.ext_getElem
  · simp [blockPass, hx, hy]
  intro k h1 h2
  have hl : (xs ++ ys ++ R).length = 2 * B + R.length := by simp [hx, hy]; ring
  have hb1 : (blockPass B (xs ++ ys ++ R)).length = 2 * B + R.length := by simp [blockPass, hx, hy]; ring
  have hb2 : (List.zipWith (addW false) xs ys ++ List.zipWith (fun x y => addW true x (cmpl y)) xs ys ++
      blockPass B R).length = 2 * B + R.length := by simp [blockPass, hx, hy]; ring
  simp only [blockPass, List.getElem_ofFn]
  by_cases k1 : k < B
  · have hkB : k / B % 2 = 0 := by rw [Nat.div_eq_of_lt k1]
    rw [ite_eq_left hkB]
    rw [List.getElem_append_left (by simp [hx, hy]; omega), List.getElem_append_left (by simp [hx, hy]; omega)]
    simp only [List.getElem_zipWith]
    rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by rw [hl]; omega)]
    rw [List.getElem_append_left (by simp [hx, hy]; omega), List.getElem_append_left (by simp [hx]; omega),
      List.getElem_append_left (by simp [hx, hy]; omega), List.getElem_append_right (by simp [hx])]
    congr 2; (try simp [hx])
  · by_cases k2 : k < 2 * B
    · have hkB : k / B % 2 = 1 := by
        rw [show k / B = 1 by rw [Nat.div_eq_iff (by omega)]; omega]
      rw [ite_eq_right (by omega)]
      rw [List.getElem_append_left (by simp [hx, hy]; omega), List.getElem_append_right (by simp [hx, hy]; omega)]
      simp only [List.getElem_zipWith, List.length_zipWith, hx, hy, min_self]
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by rw [hl]; omega)]
      rw [List.getElem_append_left (by simp [hx, hy]; omega), List.getElem_append_left (by simp [hx]; omega),
        List.getElem_append_left (by simp [hx, hy]; omega), List.getElem_append_right (by simp [hx]; omega)]
      congr 2; (try simp [hx])
    · rw [List.getElem_append_right (by simp [hx, hy]; omega)]
      simp only [List.length_append, List.length_zipWith, hx, hy, min_self, List.getElem_ofFn]
      have hkB : k / B % 2 = (k - (B + B)) / B % 2 := by
        have : k = (k - (B + B)) + B * 2 := by omega
        conv_lhs => rw [this]
        rw [Nat.add_mul_div_left _ _ hB, Nat.add_mod_right]
      rw [hkB]
      have hR : R.length = (xs ++ ys ++ R).length - 2 * B := by rw [hl]; omega
      split_ifs with hpar
      · congr 1
        · rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by omega),
            List.getElem_append_right (by simp [hx, hy]; omega)]
          congr 1; (try simp [hx, hy])
        · by_cases hk' : k + B < (xs ++ ys ++ R).length
          · rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ (by omega),
              List.getElem_append_right (by simp [hx, hy]; omega)]
            congr 1; (try simp [hx, hy]); (try omega)
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · have hge : B ≤ k - (B + B) := by
          by_contra hh
          exact hpar (by rw [Nat.div_eq_of_lt (by omega)])
        congr 1
        · rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by omega),
            List.getElem_append_right (by simp [hx, hy]; omega)]
          congr 1; (try simp [hx, hy]); (try omega)
        · rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by omega),
            List.getElem_append_right (by simp [hx, hy]; omega)]
          congr 2; (try simp [hx, hy])

/-! ### One block pair -/

/-- Ticks of the ruler `xP` onto `qS`, ready to count. -/
noncomputable def tickB : Cmd 0 𝕌 :=
  .seq (op0 Rules.ticks false xP (ι qS) (by decide)) <| .seq (rewind xP) (rewind (ι qS))

/-- Sums and complement sums of the next two blocks of `xB`, appended to `xC`. -/
noncomputable def bsMid : Cmd 0 𝕌 := .seq (clear (ι qS)) <| .seq (rewind rF) (rewind rG)

noncomputable def bsMid2 : Cmd 0 𝕌 := .seq (clear rF) <| .seq (clear rG) <| .seq (rewind rO) (rewind kW)

noncomputable def bsEnd : Cmd 0 𝕌 := .seq (clear rO) (clear kW)

noncomputable def blockStep : Cmd 0 𝕌 :=
  .seq tickB <| .seq (moveN (ι qS) xB rF (ι tJ) (by decide) (by decide)) <| .seq (clear (ι qS)) <|
  .seq tickB <| .seq (moveN (ι qS) xB rG (ι tJ) (by decide) (by decide)) <| .seq bsMid <|
  .seq (zipAddSub rF rG rO kW (by decide) (by decide) (by decide) (by decide) (by decide)) <| .seq bsMid2 <|
  .seq (appendAll rO xC (by decide)) <| .seq (appendAll kW xC (by decide)) bsEnd

theorem runs_tickB {B : ℕ} (σ : Fin 𝕌 → WTape) (hP : σ xP = reg (ones B)) (hT : σ (ι qS) = emp) :
    Runs tickB σ (· = Function.update σ (ι qS) ⟨[], List.replicate B []⟩) (4 * B + 20) := by
  apply Runs.of_wp
  simp only [tickB, WP, wp_op0, wp_rewind]
  tsimp [hP, hT, emp, reg, Rules.output_ticks, WTape.put, WTape.next, WTape.cur]
  have t1 := time_le Rules.ticks (ones B) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hP, hT, reg, emp] at *
  · have hb : Rules.ticks.B = 0 := rfl
    rw [hb] at t1
    simp [clen] at t1 ⊢; omega

theorem clen_uniform (L : List (List Bool)) (W : ℕ) (h : ∀ x ∈ L, x.length = W) : clen L = L.length * (W + 1) := by
  induction L with
  | nil => simp
  | cons x L ih => rw [clen_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]; simp; ring

set_option maxHeartbeats 16000000 in
theorem runs_blockStep {B W : ℕ} (σ : Fin 𝕌 → WTape) {Ls M xs ys R : List (List Bool)}
    (hB : σ xB = ⟨Ls, xs ++ ys ++ R⟩) (hP : σ xP = reg (ones B)) (hC : σ xC = ⟨M, []⟩)
    (hT : σ (ι qS) = emp) (hJ : σ (ι tJ) = emp) (hF : σ rF = emp) (hG : σ rG = emp) (hO : σ rO = emp)
    (hK : σ kW = emp) (hxl : xs.length = B) (hyl : ys.length = B)
    (hxw : ∀ x ∈ xs, x.length = W) (hyw : ∀ y ∈ ys, y.length = W) :
    Runs blockStep σ (· = Function.update (Function.update σ xB ⟨ys.reverse ++ xs.reverse ++ Ls, R⟩) xC
      ⟨(List.zipWith (fun x y => addW true x (cmpl y)) xs ys).reverse ++
        (List.zipWith (addW false) xs ys).reverse ++ M, []⟩) (60 * B * (W + 3) + 200) := by
  have s1 := runs_tickB σ hP hT
  set σ₁ := Function.update σ (ι qS) ⟨[], List.replicate B []⟩
  have s2 := runs_moveN (a := 0) (k := ι qS) (s := xB) (d := rF) (j := ι tJ) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) W (List.replicate B []) σ₁ [] Ls xs (ys ++ R) []
    (by tsimp [σ₁]) (by tsimp [σ₁, hB]) (by simp [hxl]) (by tsimp [σ₁, hF, emp]) (by tsimp [σ₁, hJ, emp])
    (fun x hx => (hxw x hx).le) (fun x hx => by rw [List.eq_of_mem_replicate hx]; simp)
  set σ₂ := Function.update (Function.update (Function.update σ₁ (ι qS) ⟨(List.replicate B []).reverse ++ [], []⟩)
    xB ⟨xs.reverse ++ Ls, ys ++ R⟩) rF ⟨xs.reverse ++ [], []⟩
  have s3 := runs_clear (a := 0) (ι qS) σ₂
  set σ₃ := Function.update σ₂ (ι qS) ⟨[], []⟩
  have s4 := runs_tickB (B := B) σ₃ (by tsimp [σ₃, σ₂, σ₁, hP]) (by tsimp [σ₃, emp])
  set σ₄ := Function.update σ₃ (ι qS) ⟨[], List.replicate B []⟩
  have s5 := runs_moveN (a := 0) (k := ι qS) (s := xB) (d := rG) (j := ι tJ) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) W (List.replicate B []) σ₄ [] (xs.reverse ++ Ls) ys R []
    (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, σ₂]) (by simp [hyl]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hG, emp])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, hJ, emp])
    (fun x hx => (hyw x hx).le) (fun x hx => by rw [List.eq_of_mem_replicate hx]; simp)
  set σ₅ := Function.update (Function.update (Function.update σ₄ (ι qS) ⟨(List.replicate B []).reverse ++ [], []⟩)
    xB ⟨ys.reverse ++ (xs.reverse ++ Ls), R⟩) rG ⟨ys.reverse ++ [], []⟩
  have s6 : Runs bsMid σ₅
      (· = Function.update (Function.update (Function.update σ₅ (ι qS) emp) rF ⟨[], xs⟩) rG ⟨[], ys⟩)
      (2 * B + 2 * (B * (W + 1)) + 20) := by
    apply Runs.of_wp
    simp only [bsMid, WP, wp_clear, wp_rewind]
    tsimp [σ₅, σ₄, σ₃, σ₂, σ₁]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [emp] at *
    · have hx := clen_uniform xs.reverse W (by simpa using hxw)
      have hy := clen_uniform ys.reverse W (by simpa using hyw)
      simp [WTape.words, clen_replicate_nil] at hx hy ⊢
      rw [hx, hy, hxl, hyl]; omega
  set σ₆ := Function.update (Function.update (Function.update σ₅ (ι qS) emp) rF ⟨[], xs⟩) rG ⟨[], ys⟩
  have s7 := runs_zipAddSub (a := 0) (X := rF) (Y := rG) (S1 := rO) (S2 := kW) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) W xs ys σ₆ [] [] [] []
    (by tsimp [σ₆]) (by tsimp [σ₆]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hO, emp])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hK, emp]) (by rw [hxl, hyl])
    (fun i hi => ⟨hxw _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _),
      hyw _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)⟩)
  set Za := List.zipWith (addW false) xs ys
  set Zn := List.zipWith (fun x y => addW true x (cmpl y)) xs ys
  set σ₇ := Function.update (Function.update (Function.update (Function.update σ₆ rF ⟨xs.reverse ++ [], []⟩)
    rG ⟨ys.reverse ++ [], []⟩) rO ⟨Za.reverse ++ [], []⟩) kW ⟨Zn.reverse ++ [], []⟩
  have hZa : ∀ z ∈ Za, z.length = W + 1 := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    simp only [Za, List.getElem_zipWith, length_addW]
    rw [hxw _ (List.getElem_mem _)]
  have hZn : ∀ z ∈ Zn, z.length = W + 1 := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    simp only [Zn, List.getElem_zipWith, length_addW]
    rw [hxw _ (List.getElem_mem _)]
  have hZal : Za.length = B := by simp [Za, hxl, hyl]
  have hZnl : Zn.length = B := by simp [Zn, hxl, hyl]
  have s8 : Runs bsMid2 σ₇ (· = Function.update (Function.update (Function.update (Function.update σ₇ rF emp)
      rG emp) rO ⟨[], Za⟩) kW ⟨[], Zn⟩) (6 * (B * (W + 2)) + 20) := by
    apply Runs.of_wp
    simp only [bsMid2, WP, wp_clear, wp_rewind]
    tsimp [σ₇]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [emp] at *
    · have h1 := clen_uniform xs W hxw
      have h2 := clen_uniform ys W hyw
      have h3 := clen_uniform Za (W + 1) hZa
      have h4 := clen_uniform Zn (W + 1) hZn
      simp only [WTape.words, clen_reverse, List.append_nil, 
        List.reverse_reverse, h1, h2, h3, h4, hxl, hyl, hZal, hZnl]
      nlinarith
  set σ₈ := Function.update (Function.update (Function.update (Function.update σ₇ rF emp)
      rG emp) rO ⟨[], Za⟩) kW ⟨[], Zn⟩
  have s9 := runs_appendAll (a := 0) (s := rO) (d := xC) (by decide) (W + 1) Za σ₈ [] M
    (by tsimp [σ₈]) (by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hC]) (fun z hz => (hZa z hz).le)
  set σ₉ := Function.update (Function.update σ₈ rO ⟨Za.reverse ++ [], []⟩) xC ⟨Za.reverse ++ M, []⟩
  have s10 := runs_appendAll (a := 0) (s := kW) (d := xC) (by decide) (W + 1) Zn σ₉ [] (Za.reverse ++ M)
    (by tsimp [σ₉, σ₈]) (by tsimp [σ₉]) (fun z hz => (hZn z hz).le)
  set σ₁₀ := Function.update (Function.update σ₉ kW ⟨Zn.reverse ++ [], []⟩) xC ⟨Zn.reverse ++ (Za.reverse ++ M), []⟩
  have s11 : Runs bsEnd σ₁₀ (· = Function.update (Function.update σ xB ⟨ys.reverse ++ xs.reverse ++ Ls, R⟩) xC
      ⟨Zn.reverse ++ Za.reverse ++ M, []⟩) (4 * (B * (W + 2)) + 10) := by
    apply Runs.of_wp
    simp only [bsEnd, WP, wp_clear]
    tsimp [σ₁₀, σ₉]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;>
        tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hT, hJ, hF, hG, hO, hK, emp] <;>
        first | rfl | exact hG.symm | exact hF.symm | exact hT.symm | exact hO.symm | exact hK.symm |
          (split_ifs <;> (try subst_vars) <;>
            first | rfl | exact hG.symm | exact hF.symm | exact hT.symm) |
          simp_all (config := {decide := true})
    · have h3 := clen_uniform Za (W + 1) hZa
      have h4 := clen_uniform Zn (W + 1) hZn
      simp only [WTape.words, List.append_nil, 
        List.reverse_reverse, h3, h4, hZal, hZnl]
      nlinarith
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 (Runs.then s10 s11)))))))))).mono (fun τ h => h) ?_
  tsimp [σ₂, σ₁, WTape.words, clen_replicate_nil]
  nlinarith

/-! ### A whole pass -/

/-- One pass: every block pair of `xB`, onto `xC`. -/
noncomputable def passLoop : Cmd 0 𝕌 := .loop xB blockStep

set_option maxHeartbeats 4000000 in
theorem runs_passLoop {B W : ℕ} (hB : 1 ≤ B) : ∀ (m : ℕ) (σ : Fin 𝕌 → WTape) (Ls M L : List (List Bool)),
    σ xB = ⟨Ls, L⟩ → σ xP = reg (ones B) → σ xC = ⟨M, []⟩ →
    σ (ι qS) = emp → σ (ι tJ) = emp → σ rF = emp → σ rG = emp → σ rO = emp → σ kW = emp →
    L.length = 2 * B * m → (∀ x ∈ L, x.length = W) →
    Runs passLoop σ (· = Function.update (Function.update σ xB ⟨L.reverse ++ Ls, []⟩) xC
      ⟨(blockPass B L).reverse ++ M, []⟩) (m * (60 * B * (W + 3) + 202))
  | 0, σ, Ls, M, L, hX, _, hC, _, _, _, _, _, _, hl, _ => by
    have hL : L = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hL
    refine (Runs.loop_done (by simp [hX]) rfl).mono (fun τ h => ?_) (by simp)
    subst h
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> simp_all [blockPass]
  | m + 1, σ, Ls, M, L, hX, hP, hC, hT, hJ, hF, hG, hO, hK, hl, hw => by
    set xs := L.take B
    set ys := (L.drop B).take B
    set R := L.drop (2 * B)
    have h2B : 2 * B ≤ L.length := by rw [hl]; nlinarith
    have hsplit : L = xs ++ ys ++ R := by
      simp only [xs, ys, R]
      conv_lhs => rw [← List.take_append_drop B L, ← List.take_append_drop B (L.drop B)]
      rw [List.drop_drop, two_mul, List.append_assoc]
    have hxl : xs.length = B := by simp [xs]; omega
    have hyl : ys.length = B := by simp [ys]; omega
    have hRl : R.length = 2 * B * m := by simp [R, hl]; ring_nf; omega
    have hw' : ∀ x ∈ xs ++ ys ++ R, x.length = W := by rw [← hsplit]; exact hw
    have s1 := runs_blockStep (W := W) σ (Ls := Ls) (M := M) (xs := xs) (ys := ys) (R := R)
      (by rw [hX, ← hsplit]) hP hC hT hJ hF hG hO hK hxl hyl
      (fun x hx => hw' x (by simp [hx])) (fun x hx => hw' x (by simp [hx]))
    set σ₁ := Function.update (Function.update σ xB ⟨ys.reverse ++ xs.reverse ++ Ls, R⟩) xC
      ⟨(List.zipWith (fun x y => addW true x (cmpl y)) xs ys).reverse ++
        (List.zipWith (addW false) xs ys).reverse ++ M, []⟩
    have ih := runs_passLoop hB m σ₁ (ys.reverse ++ xs.reverse ++ Ls)
      ((List.zipWith (fun x y => addW true x (cmpl y)) xs ys).reverse ++
        (List.zipWith (addW false) xs ys).reverse ++ M) R (by tsimp [σ₁]) (by tsimp [σ₁, hP])
      (by tsimp [σ₁]) (by tsimp [σ₁, hT]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁, hF]) (by tsimp [σ₁, hG])
      (by tsimp [σ₁, hO]) (by tsimp [σ₁, hK]) hRl (fun x hx => hw' x (by simp [hx]))
    refine (Runs.loop_step (by simp only [hX, ne_eq]; intro hL; rw [hL] at h2B; simp at h2B; omega) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) (by nlinarith)
    rw [h]
    funext y
    simp only [Function.update_apply, σ₁]
    rw [hsplit, blockPass_cons xs ys R hxl hyl]
    split_ifs <;> simp

theorem length_blockPass_words {B W : ℕ} (L : List (List Bool)) (hw : ∀ x ∈ L, x.length = W) :
    ∀ x ∈ blockPass B L, x.length = W + 1 := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  simp only [blockPass, List.length_ofFn] at hk
  simp only [blockPass, List.getElem_ofFn]
  split_ifs
  · rw [length_addW, List.getD_eq_getElem _ _ hk, hw _ (List.getElem_mem _)]
  · rw [length_addW, List.getD_eq_getElem _ _ (by omega), hw _ (List.getElem_mem _)]

noncomputable def ptA : Cmd 0 𝕌 := .seq (clear xB) (rewind xC)

noncomputable def ptB : Cmd 0 𝕌 :=
  .seq (clear xC) <| .seq (rewind xB) <| .seq (op0 Rules.copy false xP xQ (by decide)) <| .seq (rewind xP) <|
  .seq (op0 Rules.copy true xP xQ (by decide)) <| .seq (clear xP) <| .seq (rewind xQ) <|
  .seq (regMove xQ xP (by decide)) (skp (ι qT) (ι tJ) (by decide))

/-- Move a pass's output back to `xB`, double the ruler, and use one tick. -/
noncomputable def passTail : Cmd 0 𝕌 := .seq ptA <| .seq (appendAll xC xB (by decide)) ptB

/-- `D` passes, one per tick of `qT`. -/
noncomputable def passesLoop : Cmd 0 𝕌 := .loop (ι qT) (.seq passLoop passTail)

set_option maxHeartbeats 8000000 in
theorem runs_passTail {B W : ℕ} (σ : Fin 𝕌 → WTape) {Lb P Tl Tr : List (List Bool)}
    (hX : σ xB = ⟨Lb, []⟩) (hC : σ xC = ⟨P.reverse, []⟩) (hP : σ xP = reg (ones B)) (hQ : σ xQ = emp)
    (hT : σ (ι qT) = ⟨Tl, [] :: Tr⟩) (hJ : σ (ι tJ) = emp) (hPw : ∀ x ∈ P, x.length = W) :
    Runs passTail σ (· = Function.update (Function.update (Function.update (Function.update σ xB ⟨[], P⟩) xC emp)
      xP (reg (ones (2 * B)))) (ι qT) ⟨[] :: Tl, Tr⟩)
      (2 * clen Lb + P.length * (W + 8) + 4 * clen P + 40 * B + 100) := by
  have s1 : Runs ptA σ (· = Function.update (Function.update σ xB emp) xC ⟨[], P⟩) (2 * clen Lb + clen P + 6) := by
    apply Runs.of_wp
    simp only [ptA, WP, wp_rewind, wp_clear]
    tsimp [hX, hC]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]; split_ifs <;> (try subst_vars) <;> tsimp [emp] at *
    · simp [WTape.words, clen_reverse]; omega
  set σ₁ := Function.update (Function.update σ xB emp) xC ⟨[], P⟩
  have s2 := runs_appendAll (a := 0) (s := xC) (d := xB) (by decide) W P σ₁ [] []
    (by tsimp [σ₁]) (by tsimp [σ₁, emp]) (fun x hx => (hPw x hx).le)
  set σ₂ := Function.update (Function.update σ₁ xC ⟨P.reverse ++ [], []⟩) xB ⟨P.reverse ++ [], []⟩
  have s3 : Runs ptB σ₂ (· = Function.update (Function.update (Function.update (Function.update σ xB ⟨[], P⟩)
      xC emp) xP (reg (ones (2 * B)))) (ι qT) ⟨[] :: Tl, Tr⟩) (3 * clen P + 40 * B + 80) := by
    apply Runs.of_wp
    simp only [ptB, regMove, regIn, cpy, skp, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [σ₂, σ₁, hP, hQ, hT, hJ, emp, reg, Rules.output_copy, Rules.output_skip, WTape.put, WTape.next,
      WTape.cur]
    have t3 := time_le Rules.skip [] (fun j => j.elim0) 0 (fun j => j.elim0)
    have hones : ones B ++ ones B = ones (2 * B) := by simp [ones, two_mul]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hX, hC, hP, hQ, hT, hJ, emp, reg, hones] at *
    · simp [WTape.words, clen, time_copy] at t3 ⊢; omega
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ h => h) ?_
  omega

theorem clen_le_uniform (L : List (List Bool)) (W : ℕ) (h : ∀ x ∈ L, x.length = W) :
    clen L = L.length * (W + 1) := clen_uniform L W h

set_option maxHeartbeats 8000000 in
theorem runs_passesLoop : ∀ (D B W c : ℕ) (σ : Fin 𝕌 → WTape) (L Tl : List (List Bool)), 1 ≤ B → 1 ≤ c →
    σ xB = ⟨[], L⟩ → σ xP = reg (ones B) → σ xC = emp → σ xQ = emp →
    σ (ι qT) = ⟨Tl, List.replicate D []⟩ → σ (ι qS) = emp → σ (ι tJ) = emp → σ rF = emp → σ rG = emp →
    σ rO = emp → σ kW = emp → L.length = B * 2 ^ D * c → (∀ x ∈ L, x.length = W) →
    Runs passesLoop σ (· = Function.update (Function.update (Function.update σ xB ⟨[], passes B D L⟩)
      xP (reg (ones (2 ^ D * B)))) (ι qT) ⟨List.replicate D [] ++ Tl, []⟩)
      (D * (L.length * (40 * (W + D) + 400) + 200))
  | 0, B, W, c, σ, L, Tl, _, _, hX, hP, _, _, hT, _, _, _, _, _, _, _, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ h => ?_) (by simp)
    subst h
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> simp_all [passes]
  | D + 1, B, W, c, σ, L, Tl, hB, hc, hX, hP, hC, hQ, hT, hS, hJ, hF, hG, hO, hK, hl, hw => by
    have hm : L.length = 2 * B * (2 ^ D * c) := by rw [hl, pow_succ]; ring
    have s1 := runs_passLoop (W := W) hB (2 ^ D * c) σ [] [] L hX hP (by rw [hC]; rfl) hS hJ hF hG hO hK hm hw
    set P := blockPass B L
    have hPw := length_blockPass_words (B := B) L hw
    have hPl : P.length = L.length := by simp [P, blockPass]
    set σ₁ := Function.update (Function.update σ xB ⟨L.reverse ++ [], []⟩) xC ⟨P.reverse ++ [], []⟩
    have s2 := runs_passTail (B := B) (W := W + 1) σ₁ (Lb := L.reverse) (P := P) (Tl := Tl)
      (Tr := List.replicate D []) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁, hP]) (by tsimp [σ₁, hQ])
      (by tsimp [σ₁, hT, List.replicate_succ]) (by tsimp [σ₁, hJ]) hPw
    set σ₂ := Function.update (Function.update (Function.update (Function.update σ₁ xB ⟨[], P⟩) xC emp)
      xP (reg (ones (2 * B)))) (ι qT) ⟨[] :: Tl, List.replicate D []⟩
    have ih := runs_passesLoop D (2 * B) (W + 1) c σ₂ P ([] :: Tl) (by omega) hc (by tsimp [σ₂]) (by tsimp [σ₂])
      (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, hQ]) (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, hS]) (by tsimp [σ₂, σ₁, hJ])
      (by tsimp [σ₂, σ₁, hF]) (by tsimp [σ₂, σ₁, hG]) (by tsimp [σ₂, σ₁, hO]) (by tsimp [σ₂, σ₁, hK])
      (by rw [hPl, hl, pow_succ]; ring) hPw
    refine (Runs.loop_step (by simp [hT, List.replicate_succ])
      (Runs.then s1 (s2.mono (fun τ h => by rw [h]; exact ih) le_rfl))).mono (fun τ h => ?_) ?_
    · rw [h]
      funext y
      simp only [Function.update_apply, σ₂, σ₁]
      split_ifs <;> (try subst_vars) <;>
        simp_all [passes, P, pow_succ, List.replicate_succ, replicate_append_cons, mul_comm, mul_left_comm,
          mul_assoc]
    · have h1 := clen_uniform L.reverse W (by simpa using hw)
      have h2 := clen_uniform P W.succ hPw
      simp only [List.length_reverse] at h1
      rw [hPl] at h2
      rw [h1, h2, hPl]
      have hc1 : 1 ≤ 2 ^ D * c := Nat.one_le_iff_ne_zero.mpr (by positivity)
      generalize 2 ^ D * c = M' at hm hc1 ⊢
      have e1 : M' * (60 * B * (W + 3) + 202) = 30 * L.length * (W + 3) + 202 * M' := by rw [hm]; ring
      rw [e1]
      have hBn : 2 * B ≤ L.length := by rw [hm]; nlinarith
      have hMn : 2 * M' ≤ L.length := by rw [hm]; nlinarith
      generalize L.length = n at *
      nlinarith

/-! ### From records to offset words -/

open Spec.SignedRingProduct in
theorem flipLast_tw {w : ℕ} {a : ℤ} (hw : 1 ≤ w) (h1 : -2 ^ (w - 1) ≤ a) (h2 : a < 2 ^ (w - 1)) :
    flipLast (tw w a) = offWord w a := by
  have hne : tw w a ≠ [] := by intro e; have := congrArg List.length e; simp [tw] at this; omega
  apply offWord_of_bval (by rw [length_flipLast hne]; simp [tw])
  rw [bval_flipLast hne, sv_tw hw h1 h2]
  simp [tw]

open Spec.SignedRingProduct in
theorem cut_array_off {r w : ℕ} (hw : 1 ≤ w) (fs : List (Rec r))
    (hb : ∀ f ∈ fs, ∀ j, -2 ^ (w - 1) ≤ f.1 j ∧ f.1 j < 2 ^ (w - 1) ∧ -2 ^ (w - 1) ≤ f.2 j ∧ f.2 j < 2 ^ (w - 1)) :
    (cut w (array w fs)).map (fun x => flipLast x.reverse) = arrOff w fs := by
  rw [array_words, cut_flatten_words hw]
  · simp only [arrOff, List.flatMap, List.map_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro f hf
    simp only [Function.comp_apply, recordWords, recOff, List.flatMap, List.map_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    obtain ⟨a1, a2, a3, a4⟩ := hb f hf j
    simp [compWord_reverse, flipLast_tw hw a1 a2, flipLast_tw hw a3 a4]
  · intro c hc
    simp only [List.mem_flatten, List.mem_map] at hc
    obtain ⟨l, ⟨f, -, rfl⟩, hl⟩ := hc
    exact recordWords_lengths w f.1 f.2 c hl

/-- Reverse a word of `xA` and flip its last bit onto `xB`. -/
noncomputable def offBody : Cmd 0 𝕌 :=
  .seq (revw xA (ι tX) (by decide)) <| .seq (rewind (ι tX)) <|
  .seq (op0 Rules.flip false (ι tX) xB (by decide)) (clear (ι tX))

noncomputable def offLoop : Cmd 0 𝕌 := .loop xA offBody

theorem runs_offLoop : ∀ (ps : List (List Bool)) (σ : Fin 𝕌 → WTape) (La Lb : List (List Bool)),
    σ xA = ⟨La, ps⟩ → σ xB = ⟨Lb, []⟩ → σ (ι tX) = emp → (∀ x ∈ ps, x ≠ []) →
    Runs offLoop σ (· = Function.update (Function.update σ xA ⟨ps.reverse ++ La, []⟩) xB
      ⟨(ps.map fun x => flipLast x.reverse).reverse ++ Lb, []⟩) (ps.length * 40 + 10 * clen ps)
  | [], σ, La, Lb, hA, hB, _, _ => by
    refine (Runs.loop_done (by simp [hA]) rfl).mono (fun τ h => ?_) (by simp)
    subst h
    funext y; simp only [Function.update_apply]; split_ifs <;> (try subst_vars) <;> simp_all
  | x :: ps, σ, La, Lb, hA, hB, hX, hne => by
    have hx : x ≠ [] := hne x (by simp)
    have s1 : Runs offBody σ (· = Function.update (Function.update σ xA ⟨x :: La, ps⟩) xB
        ⟨flipLast x.reverse :: Lb, []⟩) (10 * x.length + 30) := by
      have r1 := runs_revw (a := 0) (show xA ≠ ι tX by decide) σ (L := La) (R := ps) (w := x) hA
        (by rw [hX]; rfl)
      set σ₁ := Function.update (Function.update σ xA ⟨x :: La, ps⟩) (ι tX) ⟨x.reverse :: (σ (ι tX)).left, []⟩
      have r2 := runs_rewind (a := 0) (ι tX) σ₁
      set σ₂ := Function.update σ₁ (ι tX) ⟨[], (σ₁ (ι tX)).left.reverse ++ (σ₁ (ι tX)).right⟩
      have hxr : x.reverse ≠ [] := by simpa using hx
      have r3 := runs_op0 (a := 0) Rules.flip false (show ι tX ≠ xB by decide) σ₂
        (by tsimp [σ₂, σ₁, hX, emp]) (by tsimp [σ₂, σ₁, hB]) [flipLast x.reverse]
        (by tsimp [σ₂, σ₁, hX, emp, WTape.cur]; exact Rules.output_flip _ _ hxr) (by simp)
      set σ₃ := Function.update (Function.update σ₂ (ι tX) (σ₂ (ι tX)).next) xB ((σ₂ xB).put false [flipLast x.reverse])
      have r4 := runs_clear (a := 0) (ι tX) σ₃
      have t1 := time_le Rules.flip x.reverse (fun j => j.elim0) 0 (fun j => j.elim0)
      refine (Runs.then r1 (Runs.then r2 (Runs.then r3 r4))).mono (fun τ h => ?_) ?_
      · rw [h]; funext y; simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> tsimp [σ₃, σ₂, σ₁, hX, hA, hB, emp, WTape.put, WTape.next,
          WTape.cur] <;> simp_all (config := {decide := true})
      · have hb : Rules.flip.B = 2 := rfl
        rw [hb] at t1
        tsimp [σ₃, σ₂, σ₁, hX, emp, WTape.put, WTape.next, WTape.cur, WTape.words, clen] at t1 ⊢
        omega
    set σ₁ := Function.update (Function.update σ xA ⟨x :: La, ps⟩) xB ⟨flipLast x.reverse :: Lb, []⟩
    have ih := runs_offLoop ps σ₁ (x :: La) (flipLast x.reverse :: Lb) (by tsimp [σ₁]) (by tsimp [σ₁])
      (by tsimp [σ₁, hX]) (fun y hy => hne y (by simp [hy]))
    refine (Runs.loop_step (by simp [hA]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]; funext y; simp only [Function.update_apply, σ₁]; split_ifs <;> simp
    · simp [clen_cons]; omega

/-! ### Words to digits and back -/

/-- Append a zero bit to every word of `xB`, onto `tD`. -/
noncomputable def zextLoop : Cmd 0 𝕌 := .loop xB (op0 Rules.zext false xB (ι tD) (by decide))

theorem runs_zextLoop : ∀ (ps : List (List Bool)) (σ : Fin 𝕌 → WTape) (Lb Ld : List (List Bool)),
    σ xB = ⟨Lb, ps⟩ → σ (ι tD) = ⟨Ld, []⟩ →
    Runs zextLoop σ (· = Function.update (Function.update σ xB ⟨ps.reverse ++ Lb, []⟩) (ι tD)
      ⟨(ps.map (· ++ [false])).reverse ++ Ld, []⟩) (ps.length * 12 + clen ps)
  | [], σ, Lb, Ld, hB, hD => by
    refine (Runs.loop_done (by simp [hB]) rfl).mono (fun τ h => ?_) (by simp)
    subst h
    funext y; simp only [Function.update_apply]; split_ifs <;> (try subst_vars) <;> simp_all
  | x :: ps, σ, Lb, Ld, hB, hD => by
    have s1 := runs_op0 (a := 0) Rules.zext false (show xB ≠ ι tD by decide) σ (by simp [hB]) (by simp [hD])
      [x ++ [false]] (by simp [hB, WTape.cur, Rules.output_zext]) (by simp)
    set σ₁ := Function.update (Function.update σ xB (σ xB).next) (ι tD) ((σ (ι tD)).put false [x ++ [false]])
    have ih := runs_zextLoop ps σ₁ (x :: Lb) ((x ++ [false]) :: Ld) (by tsimp [σ₁, hB, WTape.next, WTape.cur])
      (by tsimp [σ₁, hD, WTape.put])
    have t1 := time_le Rules.zext x (fun j => j.elim0) 0 (fun j => j.elim0)
    refine (Runs.loop_step (by simp [hB]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]; funext y; simp only [Function.update_apply, σ₁]; split_ifs <;> simp
    · have hb : Rules.zext.B = 2 := rfl
      rw [hb] at t1
      simp [hB, WTape.cur, clen_cons] at t1 ⊢; omega

/-- Reverse every word of `xE` and append it to `zO`'s word. -/
noncomputable def prJoinBody : Cmd 0 𝕌 :=
  .seq (revw xE (ι tX) (by decide)) <| .seq (rewind (ι tX)) <|
  .seq (op0 Rules.copy true (ι tX) zO (by decide)) (clear (ι tX))

noncomputable def prJoinLoop : Cmd 0 𝕌 := .loop xE prJoinBody

theorem runs_prJoinLoop : ∀ (ps : List (List Bool)) (σ : Fin 𝕌 → WTape) (Le : List (List Bool)) (acc : List Bool),
    σ xE = ⟨Le, ps⟩ → σ zO = ⟨[acc], []⟩ → σ (ι tX) = emp →
    Runs prJoinLoop σ (· = Function.update (Function.update σ xE ⟨ps.reverse ++ Le, []⟩) zO
      ⟨[acc ++ (ps.map List.reverse).flatten], []⟩) (ps.length * 40 + 10 * clen ps)
  | [], σ, Le, acc, hE, hO, _ => by
    refine (Runs.loop_done (by simp [hE]) rfl).mono (fun τ h => ?_) (by simp)
    subst h
    funext y; simp only [Function.update_apply]; split_ifs <;> (try subst_vars) <;> simp_all
  | x :: ps, σ, Le, acc, hE, hO, hX => by
    have s1 : Runs prJoinBody σ (· = Function.update (Function.update σ xE ⟨x :: Le, ps⟩) zO
        ⟨[acc ++ x.reverse], []⟩) (10 * x.length + 30) := by
      have r1 := runs_revw (a := 0) (show xE ≠ ι tX by decide) σ (L := Le) (R := ps) (w := x) hE
        (by rw [hX]; rfl)
      set σ₁ := Function.update (Function.update σ xE ⟨x :: Le, ps⟩) (ι tX) ⟨x.reverse :: (σ (ι tX)).left, []⟩
      have r2 := runs_rewind (a := 0) (ι tX) σ₁
      set σ₂ := Function.update σ₁ (ι tX) ⟨[], (σ₁ (ι tX)).left.reverse ++ (σ₁ (ι tX)).right⟩
      have r3 := runs_op0 (a := 0) Rules.copy true (show ι tX ≠ zO by decide) σ₂
        (by tsimp [σ₂, σ₁, hX, emp]) (by tsimp [σ₂, σ₁, hO]) [x.reverse]
        (by tsimp [σ₂, σ₁, hX, emp, WTape.cur, Rules.output_copy]) (by tsimp [σ₂, σ₁, hO])
      set σ₃ := Function.update (Function.update σ₂ (ι tX) (σ₂ (ι tX)).next) zO ((σ₂ zO).put true [x.reverse])
      have r4 := runs_clear (a := 0) (ι tX) σ₃
      refine (Runs.then r1 (Runs.then r2 (Runs.then r3 r4))).mono (fun τ h => ?_) ?_
      · rw [h]; funext y; simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> tsimp [σ₃, σ₂, σ₁, hX, hE, hO, emp, WTape.put, WTape.next,
          WTape.cur] <;> simp_all (config := {decide := true})
      · tsimp [σ₃, σ₂, σ₁, hX, emp, WTape.put, WTape.next, WTape.cur, WTape.words, clen, time_copy]
        omega
    set σ₁ := Function.update (Function.update σ xE ⟨x :: Le, ps⟩) zO ⟨[acc ++ x.reverse], []⟩
    have ih := runs_prJoinLoop ps σ₁ (x :: Le) (acc ++ x.reverse) (by tsimp [σ₁]) (by tsimp [σ₁])
      (by tsimp [σ₁, hX])
    refine (Runs.loop_step (by simp [hE]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]; funext y; simp only [Function.update_apply, σ₁]; split_ifs <;> simp
    · simp [clen_cons]; omega

/-! ### The digit constants -/

namespace Rules

/-- Zeros for all driver bits after the first, then `1, 0`. -/
abbrev hmark : Rule 0 where
  Q := Bool
  q0 := false
  step q _ _ := (true, if q then some (some false) else none, fun _ => false)
  flush _ := [some true, some false, none]
  B := 3
  hB _ := le_rfl

theorem go_hmark_true (w : List Bool) (ws : Fin 0 → List Bool) :
    (go hmark true w ws).2.1 = (List.replicate w.length false).map some := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih, List.replicate_succ]

theorem output_hmark (w : List Bool) (ws : Fin 0 → List Bool) (h : w ≠ []) :
    output hmark w ws = syms [List.replicate (w.length - 1) false ++ [true, false]] := by
  cases w with
  | nil => exact absurd rfl h
  | cons b w => simp [output, go, go_hmark_true, syms_cons]

/-- One zero per driver bit and one more. -/
abbrev fill1 : Rule 0 where
  Q := Unit
  q0 := ()
  step _ _ _ := ((), some (some false), fun _ => false)
  flush _ := [some false, none]
  B := 2
  hB _ := le_rfl

theorem go_fill1 (w : List Bool) (ws : Fin 0 → List Bool) :
    (go fill1 () w ws).2.1 = (List.replicate w.length false).map some := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih, List.replicate_succ]

theorem output_fill1 (w : List Bool) (ws : Fin 0 → List Bool) :
    output fill1 w ws = syms [List.replicate (w.length + 1) false] := by
  simp [output, go_fill1, syms_cons, List.replicate_succ']

end Rules

theorem bits_half {Wd : ℕ} (hW : 1 ≤ Wd) :
    bits (Wd + 1) (2 ^ (Wd - 1)) = List.replicate (Wd - 1) false ++ [true, false] := by
  have h := bits_bval (List.replicate (Wd - 1) false ++ [true, false])
  have hl : (List.replicate (Wd - 1) false ++ [true, false]).length = Wd + 1 := by simp; omega
  rw [hl, bval_append, bval_replicate_false] at h
  simpa using h

theorem bits_lowOnes {Wd D : ℕ} (hD : D ≤ Wd + 1) :
    bits (Wd + 1) (2 ^ D - 1) = List.replicate D true ++ List.replicate (Wd + 1 - D) false := by
  have hones : ∀ n, bval (List.replicate n true) = 2 ^ n - 1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih, pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  have h := bits_bval (List.replicate D true ++ List.replicate (Wd + 1 - D) false)
  have hl : (List.replicate D true ++ List.replicate (Wd + 1 - D) false).length = Wd + 1 := by simp; omega
  rw [hl, bval_append, bval_replicate_false, hones] at h
  simpa using h

/-- `kH`, `kC` for width `w + D` and shift `D`, from `kw = ones w` and `kS = ones D`. -/
noncomputable def constK : Cmd 0 𝕌 :=
  .seq (op0 Rules.copy false kw (ι qR) (by decide)) <| .seq (rewind kw) <|
  .seq (op0 Rules.copy true kS (ι qR) (by decide)) <| .seq (rewind kS) <| .seq (rewind (ι qR)) <|
  .seq (op0 Rules.hmark false (ι qR) kH (by decide)) <| .seq (rewind (ι qR)) <| .seq (rewind kH) <|
  .seq (op0 Rules.copy false kS kC (by decide)) <| .seq (rewind kS) <|
  .seq (op0 Rules.fill1 true kw kC (by decide)) <| .seq (rewind kw) <| .seq (rewind kC) (clear (ι qR))

set_option maxHeartbeats 8000000 in
theorem runs_constK {w D : ℕ} (hw : 1 ≤ w) (σ : Fin 𝕌 → WTape) (hW : σ kw = reg (ones w)) (hS : σ kS = reg (ones D))
    (hR : σ (ι qR) = emp) (hH : σ kH = emp) (hC : σ kC = emp) :
    Runs constK σ (· = Function.update (Function.update σ kH (reg (bits (w + D + 1) (2 ^ (w + D - 1)))))
      kC (reg (bits (w + D + 1) (2 ^ D - 1)))) (20 * (w + D) + 100) := by
  apply Runs.of_wp
  simp only [constK, WP, wp_op0, wp_rewind, wp_clear]
  have hne : ones w ++ ones D ≠ [] := by simp [ones]; omega
  tsimp [hW, hS, hR, hH, hC, emp, reg, Rules.output_copy, Rules.output_hmark _ _ hne, Rules.output_fill1,
    WTape.put, WTape.next, WTape.cur]
  have t1 := time_le Rules.hmark (ones w ++ ones D) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.fill1 (ones w) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;>
      tsimp [hW, hS, hR, hH, hC, emp, reg, bits_half (show 1 ≤ w + D by omega), bits_lowOnes (show D ≤ w + D + 1 by omega),
        ones] at *
    all_goals omega
  · have hb1 : Rules.hmark.B = 3 := rfl
    have hb2 : Rules.fill1.B = 2 := rfl
    rw [hb1] at t1; rw [hb2] at t2
    simp [time_copy, clen, WTape.words] at t1 t2 ⊢; omega

/-! ### The output words -/

open Spec.SignedRingProduct NLogN in
theorem outWord_offWord {Wd D w : ℕ} {a : ℤ} (hw : 1 ≤ w) (hws : w + D ≤ Wd + 1) (hW : 1 ≤ Wd)
    (h1 : -2 ^ (Wd - 1) ≤ a) (h2 : a < 2 ^ (Wd - 1)) :
    (outWord Wd D w (bval (offWord Wd a))).reverse = compWord w (rho0 ((a : ℝ) / 2 ^ D)) := by
  have hv := bval_offWord hW h1 h2
  have he : bval (offWord Wd a) < 2 ^ Wd := by have := bval_lt (offWord Wd a); simpa using this
  rw [outWord_eq hW he hw hws, rho0_div, tw_reverse]
  congr 2
  rw [hv]; ring

open Spec.SignedRingProduct in
/-- Bounds of components hold for every record of the array. -/
theorem comp_bound_of {r : ℕ} {A : ℤ} {G : List (Rec r)} (hb : Bounded A G) {f : Rec r} (hf : f ∈ G) (j : Fin r) :
    |f.1 j| ≤ A ∧ |f.2 j| ≤ A := by
  obtain ⟨y, hy, rfl⟩ := List.getElem_of_mem hf
  have h1 := hb y (2 * j.val)
  have h2 := hb y (2 * j.val + 1)
  rw [List.getD_eq_getElem _ _ hy] at h1 h2
  unfold comp at h1 h2
  have e1 : 2 * j.val / 2 = j.val := by omega
  have e2 : (2 * j.val + 1) / 2 = j.val := by omega
  simp only [e1, e2, j.isLt, ↓reduceDIte, show 2 * j.val % 2 = 0 by omega, show (2 * j.val + 1) % 2 = 1 by omega,
    ↓reduceIte, one_ne_zero] at h1 h2
  exact ⟨h1, h2⟩

open Spec.SignedRingProduct NLogN in
theorem join_outWords {r Wd D w : ℕ} (hw : 1 ≤ w) (hws : w + D ≤ Wd + 1) (hW : 1 ≤ Wd) (G : List (Rec r))
    (hb : Bounded (2 ^ (Wd - 1) - 1) G) :
    (((arrOff Wd G).map fun x => outWord Wd D w (bval x)).map List.reverse).flatten =
      array w (G.map (truncRec D)) := by
  rw [array_words]
  simp only [arrOff, List.flatMap, List.map_flatten, List.map_map, List.flatten_flatten]
  congr 1
  apply List.map_congr_left
  intro f hf
  simp only [Function.comp_apply, recOff, recordWords, truncRec, List.flatMap, List.map_flatten, List.map_map]
  congr 2
  apply List.map_congr_left
  intro j _
  obtain ⟨b1, b2⟩ := comp_bound_of hb hf j
  rw [abs_le] at b1 b2
  simp only [Function.comp_apply, List.map_cons, List.map_nil]
  rw [outWord_offWord hw hws hW (by linarith) (by linarith), outWord_offWord hw hws hW (by linarith) (by linarith)]

theorem zext_digits {Wd : ℕ} (L : List (List Bool)) (h : ∀ x ∈ L, x.length = Wd) :
    L.map (· ++ [false]) = (L.map bval).map (bits (Wd + 1)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply]
  rw [← bits_succ_zext _ _ (by have := bval_lt x; rwa [h x hx] at this), ← h x hx, bits_bval]

open Spec.SignedRingProduct in
theorem bounded_bflysRecs {r : ℕ} {A : ℤ} : ∀ (Ps : List ℕ) (fs : List (Rec r)), Bounded A fs →
    Bounded (2 ^ Ps.length * A) (bflysRecs Ps fs)
  | [], fs, h => by simpa [bflysRecs] using h
  | P :: Ps, fs, h => by
    have := bounded_bflysRecs Ps _ (bounded_bflyRecs P h)
    simp only [List.length_cons, pow_succ]
    rw [bflysRecs]
    convert this using 1; ring

end IntegerMultBounds.Schoenhage
