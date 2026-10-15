module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateTraversalLayout

/-! # Complete runtime descriptor producer -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Setup, target-counter copy, complete traversal, and binary workspace release. -/
def crtControlProducer (rg : TblR 10 → Fin T) (u : Fin 5 → Fin T)
    (e : Fin 14 → Fin T) : Pr P T Q A U :=
  .seq (crtControlGenerateSetup rg u) <|
  .seq (ucopy (u 0) (e 7) (e 13)) <|
  .seq (crtControlGenerateLoop rg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
    (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) (e 12) (e 13))
    (crtControlWorkspaceClear rg)

def crtControlProducerCost (W w target ai a0 pre widthsLen moduliLen widthSum N axisBudget : ℕ) : ℕ :=
  crtControlGenerateSetupCost W w target ai a0 pre + (4 * target + 4) +
    (N * (axisBudget + 2) + 2 + (2 * widthsLen + 2) + (2 * moduliLen + 2) +
      (2 * widthSum + 2) + 4) + (10 * (2 * W + 2) + 1)

/-- A uniform budget for all original-axis iterations. -/
def crtControlProducerAxisBudget {d : ℕ} (W w : ℕ) (a s : Fin (d + 1) → ℕ) : ℕ :=
  Finset.univ.sup fun j => crtControlGenerateAxisCost W w (a j) (s j) (crtPre a j.val) (4 * W)

/-- The producer restores its unary inputs and every workspace register, leaving
only the exact exposed-layout descriptor tape prepended to the destination. -/
theorem crtControlProducer_runs {d B w : ℕ} {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (u : Fin 5 → Fin T) (hu : Function.Injective u)
    (e : Fin 14 → Fin T) (he : Function.Injective e)
    (hrgu : ∀ r j, rg r ≠ u j) (hrge : ∀ r j, rg r ≠ e j)
    (hue : ∀ j k, u j ≠ e k)
    (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1))
    (hs : ∀ j, s j ≤ 2 ^ a j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w)
    (hw : w ≤ 3 * B + 1) (R : Regs T A)
    (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hindex : (R (u 0)).length = i.val) (htarget : (R (u 1)).length = a i)
    (hzero : (R (u 2)).length = a 0) (hlow : (R (u 3)).length = crtPre a i.val)
    (hsaved : R (u 4) = [])
    (hwidths : R (e 0) = crtEnts (List.ofFn a))
    (hmoduli : R (e 1) = crtEnts (List.ofFn s))
    (hempty : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 11 → R (e j) = []) :
    crtRuns body (crtControlProducer rg u e) R
      (Function.update R (e 11)
        (crtControlTape (3 * B + 1) (crtControlFields a s i.val (crtExposePrefix i)) ++ R (e 11)))
      (crtControlProducerCost (3 * B + 1) w i.val (a i) (a 0) (crtPre a i.val)
        (crtEnts (A := A) (List.ofFn a)).length (crtEnts (A := A) (List.ofFn s)).length
        (List.ofFn a).sum (d + 1) (crtControlProducerAxisBudget (3 * B + 1) w a s)) := by
  let W := 3 * B + 1
  let st := crtControlGenerateSetupState i.val (a i) (a 0) (crtPre a i.val) (R (rg .acc))
  let R₁ := crtBankOverlay rg R (tblRho W wl nl st)
  let R₂ := Function.update R₁ (e 7) (List.replicate i.val tick)
  let Ψ := crtControlTraversalRegs rg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
    (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) W wl nl st R₂ (List.ofFn a) (List.ofFn s)
  have hR₁e : ∀ j, R₁ (e j) = R (e j) := fun j => crtBankOverlay_off _ _ _ _ (fun r => hrge r j)
  have hR₁u : ∀ j, R₁ (u j) = R (u j) := fun j => crtBankOverlay_off _ _ _ _ (fun r => hrgu r j)
  have hR₂e : ∀ j, R₂ (e j) = if j = 7 then List.replicate i.val tick else R (e j) := by
    intro j; simp [R₂, Function.update_apply, he.eq_iff, hR₁e]
  have hreg : [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10, e 11, e 12, e 13].Nodup := by
    simp [List.nodup_cons, he.eq_iff]
  have hdisj : ∀ r, ∀ x ∈ [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10, e 11, e 12, e 13], rg r ≠ x := by
    intro r x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hrge r _
  have hiB : i.val < B := i.isLt.trans_le hd
  have haB : ∀ j, a j ≤ B := fun j =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hB
  have hpB : crtPre a i.val ≤ B := (crtControl_pre_le_sum a i.val).trans hB
  have hsetup := crtControlGenerateSetup_runs (body := body) hrg u hu hrgu
    (show 0 < W by dsimp [W]; omega)
    (show i.val < 2 ^ W from hiB.trans (lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)))
    (show a i < W by dsimp [W]; have := haB i; omega)
    (show a 0 < W by dsimp [W]; have := haB 0; omega)
    (show crtPre a i.val < W by dsimp [W]; omega)
    wl nl hwl hnl hw R hwr hwn hv hz hindex htarget hzero hlow hsaved
  have hcopy := crtUcopy_runs (body := body) (hue 0 7) (hue 0 13) (he.ne (by decide : (7 : Fin 14) ≠ 13))
    R₁ (by rw [hR₁e]; exact hempty 13 (by decide) (by decide) (by decide))
  have hcopy' : crtRuns body (ucopy (u 0) (e 7) (e 13)) R₁ R₂ (4 * i.val + 4) := by
    simpa only [hR₁u, hindex, hR₁e, hempty 7 (by decide) (by decide) (by decide), List.append_nil] using hcopy
  have hinit : CrtControlTraversalInvariant rg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
      (e 6) (e 7) (e 9) (e 12) (e 13) W wl nl st (List.ofFn a) (List.ofFn s) i.val 0 R₂ := by
    constructor
    · intro r; simp [R₂, hrge r 7, R₁, crtBankOverlay_on hrg]
    all_goals simp [hR₂e, hwidths, hmoduli, hempty]
  have hI₀ : CrtControlLayoutInvariant W a s i (e 10) (e 11) (e 8) (R (e 11)) 0 R₂ := by
    apply CrtControlLayoutInvariant_zero
    all_goals simp [hR₂e, hempty]
  have hfields := crtControlTraversal_field a s i st
    (by simp [st, crtControlGenerateSetupState, crtControlGenerateInitial])
    (by simp [st, crtControlGenerateSetupState])
    (by simp [st, crtControlGenerateSetupState])
    (by simp [st, crtControlGenerateSetupState])
    (by simp [st, crtControlGenerateSetupState, crtControlGenerateInitial])
    (by simp [st, crtControlGenerateSetupState])
  have hsem := crtControlTraversal_layout hrg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
    (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) (e 12) (e 13) hreg hdisj W wl nl st R₂ a s i
      (R (e 11)) hinit hI₀ hfields
  have hstruct := crtControlTraversal_invariant hrg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
    (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) (e 12) (e 13) hreg hdisj W wl nl st R₂
      (List.ofFn a) (List.ofFn s) i.val (by simp) hinit
  have harith := crtControlTraversal_arithmetic a s i hs hB hd (R (rg .acc))
  have hcost : ∀ j < (List.ofFn a).length,
      crtControlGenerateAxisCost W w ((List.ofFn a).getD j 0) ((List.ofFn s).getD j 0)
        ((List.ofFn a).take j).sum ((Ψ j) (e 10)).length ≤ crtControlProducerAxisBudget W w a s := by
    intro j hj
    have hj' : j < d + 1 := by simpa only [List.length_ofFn] using hj
    have hzlen : ((Ψ j) (e 10)).length ≤ 4 * W := by
      have h := (hsem j hj'.le).2.1
      change Ψ j (e 10) = _ at h
      rw [h]
      unfold crtControlParkedZero
      split_ifs <;> simp [crtControlPacket_length]
    have hga : (List.ofFn a).getD j 0 = a ⟨j, hj'⟩ := by
      rw [List.getD_eq_getElem _ _ hj]; simp only [List.getElem_ofFn]
    have hgs : (List.ofFn s).getD j 0 = s ⟨j, hj'⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj')]; simp only [List.getElem_ofFn]
    rw [hga, hgs, crtControl_ofFn_take_sum a j hj'.le]
    apply le_trans (show _ ≤ crtControlGenerateAxisCost W w (a ⟨j, hj'⟩) (s ⟨j, hj'⟩) (crtPre a j) (4 * W) by
      unfold crtControlGenerateAxisCost; omega)
    exact Finset.le_sup (f := fun k : Fin (d + 1) => crtControlGenerateAxisCost W w (a k) (s k) (crtPre a k.val) (4 * W))
      (Finset.mem_univ (⟨j, hj'⟩ : Fin (d + 1)))
  have hrun := crtControlTraversal_runs (body := body) hrg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
    (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) (e 12) (e 13) hreg hdisj
    (show 0 < W by dsimp [W]; omega) wl nl hwl hnl hw st R₂ (List.ofFn a) (List.ofFn s) i.val
      (crtControlProducerAxisBudget W w a s) (by simp) hinit
      (fun j hj => (harith j (by simpa only [List.length_ofFn] using hj)).1)
      (fun j hj => (harith j (by simpa only [List.length_ofFn] using hj)).2.1)
      (fun j hj => (harith j (by simpa only [List.length_ofFn] using hj)).2.2.1)
      (fun j hj => (harith j (by simpa only [List.length_ofFn] using hj)).2.2.2.1)
      (fun j hj => (harith j (by simpa only [List.length_ofFn] using hj)).2.2.2.2) hcost
  have hfinal := hstruct (d + 1) (by simp)
  have htape := CrtControlLayoutInvariant_full W a s i (e 10) (e 11) (e 8) (R (e 11)) _ (hsem (d + 1) le_rfl)
  change Ψ (d + 1) (e 11) = _ ∧ Ψ (d + 1) (e 10) = [] ∧ Ψ (d + 1) (e 8) = [tick] at htape
  let Sf := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Ψ (d + 1)) (e 2) []) (e 0) (crtEnts (List.ofFn a))) (e 3) [])
      (e 1) (crtEnts (List.ofFn s))) (e 6) []) (e 8) []
  let Rf := Function.update R (e 11)
    (crtControlTape W (crtControlFields a s i.val (crtExposePrefix i)) ++ R (e 11))
  let sf := crtControlTraversalState st (List.ofFn a) (List.ofFn s) (d + 1)
  have hSf : Sf = crtBankOverlay rg Rf (tblRho W wl nl sf) := by
    funext r
    by_cases hb : ∃ k, rg k = r
    · obtain ⟨k, rfl⟩ := hb
      simp only [Sf, Function.update_of_ne (hrge k 8), Function.update_of_ne (hrge k 6),
        Function.update_of_ne (hrge k 1), Function.update_of_ne (hrge k 3),
        Function.update_of_ne (hrge k 0), Function.update_of_ne (hrge k 2), crtBankOverlay_on hrg]
      exact hfinal.bank k
    · have hb' : ∀ k, rg k ≠ r := by simpa using hb
      rw [crtBankOverlay_off _ _ _ _ hb']
      by_cases he' : ∃ j, e j = r
      · obtain ⟨j, rfl⟩ := he'
        have haw := hfinal.axisWidth
        have ham := hfinal.axisModulus
        have hleft := hfinal.left
        have hp := hfinal.packet
        have hpad := hfinal.pad
        have htmp := hfinal.tmp
        change Ψ (d + 1) (e 4) = [] at haw
        change Ψ (d + 1) (e 5) = [] at ham
        change Ψ (d + 1) (e 7) = _ at hleft
        change Ψ (d + 1) (e 9) = [] at hp
        change Ψ (d + 1) (e 12) = [] at hpad
        change Ψ (d + 1) (e 13) = [] at htmp
        fin_cases j <;> simp [Sf, Rf, he.eq_iff, hwidths, hmoduli, hempty,
          haw, ham, hleft, hp, hpad, htmp, htape.1, htape.2.1, show i.val - (d + 1) = 0 by omega]
      · have he'' : ∀ j, r ≠ e j := by intro j h; exact he' ⟨j, h.symm⟩
        have hoff := crtControlTraversalRegs_off rg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
          (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) W wl nl st R₂ (List.ofFn a) (List.ofFn s)
          r hb' (by
            intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals exact he'' _) (d + 1)
        change Ψ (d + 1) r = R₂ r at hoff
        simp [Sf, Rf, he'', hoff, R₂, R₁, crtBankOverlay_off _ _ _ _ hb']
  have hclear := crtControlWorkspace_restore (body := body) hrg W wl nl sf Rf
    (by intro j; simpa [Rf, hrge] using hv j)
    (by intro j; simpa [Rf, hrge] using hz j)
    (by simpa [Rf, hrge] using hwr) (by simpa [Rf, hrge] using hwn)
    (by simp [sf, st, crtControlTraversalState_acc, crtControlGenerateSetupState, Rf, hrge])
  rw [← hSf] at hclear
  dsimp only [Ψ] at htape
  have hrun' : crtRuns body (crtControlGenerateLoop rg (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
      (e 6) (e 7) (e 8) (e 9) (e 10) (e 11) (e 12) (e 13)) R₂ Sf
      ((d + 1) * (crtControlProducerAxisBudget W w a s + 2) + 2 +
        (2 * (crtEnts (A := A) (List.ofFn a)).length + 2) +
        (2 * (crtEnts (A := A) (List.ofFn s)).length + 2) +
        (2 * (List.ofFn a).sum + 2) + 4) := by
    simpa only [List.length_ofFn, htape.2.2, List.length_cons, List.length_nil] using hrun
  apply crtRuns_mono (crtRuns_seq hsetup (crtRuns_seq hcopy' (crtRuns_seq hrun' hclear)))
  dsimp only [crtControlProducerCost, W]
  omega

end IntegerMultBounds.MathlibTM2.Fast
