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
    rw [if_pos hkB]
    rw [List.getElem_append_left (by simp [hx, hy] <;> omega), List.getElem_append_left (by simp [hx, hy] <;> omega)]
    simp only [List.getElem_zipWith]
    rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by rw [hl]; omega)]
    rw [List.getElem_append_left (by simp [hx, hy] <;> omega), List.getElem_append_left (by simp [hx, hy] <;> omega),
      List.getElem_append_left (by simp [hx, hy] <;> omega), List.getElem_append_right (by simp [hx, hy] <;> omega)]
    congr 2 <;> (try simp [hx])
  · by_cases k2 : k < 2 * B
    · have hkB : k / B % 2 = 1 := by
        rw [show k / B = 1 by rw [Nat.div_eq_iff (by omega)]; omega]
      rw [if_neg (by omega)]
      rw [List.getElem_append_left (by simp [hx, hy] <;> omega), List.getElem_append_right (by simp [hx, hy] <;> omega)]
      simp only [List.getElem_zipWith, List.length_zipWith, hx, hy, min_self]
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by rw [hl]; omega)]
      rw [List.getElem_append_left (by simp [hx, hy] <;> omega), List.getElem_append_left (by simp [hx, hy] <;> omega),
        List.getElem_append_left (by simp [hx, hy] <;> omega), List.getElem_append_right (by simp [hx, hy] <;> omega)]
      congr 2 <;> (try simp [hx]) <;> (try omega)
    · rw [List.getElem_append_right (by simp [hx, hy] <;> omega)]
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
            List.getElem_append_right (by simp [hx, hy] <;> omega)]
          congr 1; (try simp [hx, hy]); (try omega)
        · by_cases hk' : k + B < (xs ++ ys ++ R).length
          · rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ (by omega),
              List.getElem_append_right (by simp [hx, hy] <;> omega)]
            congr 1; (try simp [hx, hy]); (try omega)
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · have hge : B ≤ k - (B + B) := by
          by_contra hh
          exact hpar (by rw [Nat.div_eq_of_lt (by omega)])
        congr 1
        · rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by omega),
            List.getElem_append_right (by simp [hx, hy] <;> omega)]
          congr 1; (try simp [hx, hy]); (try omega)
        · rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getD_eq_getElem _ _ (by omega),
            List.getElem_append_right (by simp [hx, hy] <;> omega)]
          congr 2; (try simp [hx, hy]); (try omega)

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
    simp [WTape.words, clen, clen_replicate_nil] at t1 ⊢; omega

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
      simp only [WTape.words, clen_reverse, List.reverse_nil, List.append_nil, List.nil_append,
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
            first | rfl | exact hG.symm | exact hF.symm | exact hT.symm | exact hO.symm | exact hK.symm) |
          simp_all (config := {decide := true})
    · have h3 := clen_uniform Za (W + 1) hZa
      have h4 := clen_uniform Zn (W + 1) hZn
      simp only [WTape.words, clen_reverse, List.reverse_nil, List.append_nil, List.nil_append,
        List.reverse_reverse, clen_append, h3, h4, hZal, hZnl]
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

end IntegerMultBounds.Schoenhage
