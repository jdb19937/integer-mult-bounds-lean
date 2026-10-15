module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcP1

/-!
# Phase C of the converter: the parameters of the CRT machines

`dsPC rg g`: `S_0 = P_0 = 1`, the CRT loop (`dsGLoop … dsCC₁ dsCC₂`, `Fast/DistCrt.lean`) pushing
the entries of `μ_j` onto `c .mT`, `logT` ticks onto a spare, the packed bounds and the mask
narrowed to `logT = crtPre a d` bits onto `c .sig`, `c .msk`, the spares and the loop counter
cleared, the loop variables cleared.

`ds_PC`: the contract.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section PC

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- The offset list of the CRT machines. -/
abbrev dsyMT : DsY t₀ := .s (.c .mT)
/-- The packed bounds. -/
abbrev dsySig : DsY t₀ := .s (.c .sig)
/-- The mask. -/
abbrev dsyMsk : DsY t₀ := .s (.c .msk)

/-- Phase C. -/
def dsPC (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg dsCInit) <|
  .seq (dsGLoop rg (g (.o .uD)) (g (.o .tm)) dsCC₁ dsCC₂ (dsLC (g dsyMT))) <|
  .seq (dsUn rg 5 (g (.o .ut))) <|
  .seq (dsNarrow rg 34 (g (.o .ut)) (g (.o .tm)) (g (.o .tb)) (g (.o .tx)) (g dsySig)) <|
  .seq (dsNarrow rg 35 (g (.o .ut)) (g (.o .tm)) (g (.o .tb)) (g (.o .tx)) (g dsyMsk)) <|
  .seq (uclear (g (.o .ut))) <| .seq (uclear (g (.o .uD))) (tblCompile rg dsCEnd)

/-- The step bound of the CRT loop. -/
noncomputable def dsCrtCost (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d n), ((dsCK₁ n + 17) * tblC (pmW n) (pmW n) +
    ((pmW n * (4 * dsMu n i + 11) + 2 * dsMu n i + 8) + 1) + 3) + 2 * d n + 4

/-- The step bound of phase C. -/
noncomputable def dsPCCost (n : ℕ) : ℕ :=
  2 * tblC (pmW n) (pmW n) + dsCrtCost n + (pmW n * (4 * logT n + 11) + 2 * logT n + 6) +
    2 * (14 * pmW n + 14) + (2 * logT n + 2) + (2 * d n + 2) + 5 * tblC (pmW n) (pmW n)

/-- The registers phase C needs empty. -/
def dsPCPre : List (DsY t₀) := [.o .tm, .o .ut, .o .tb, .o .tx, dsyMT, dsySig, dsyMsk]

/-- The registers phase C writes. -/
def dsPCOut : List (DsY t₀) := [.o .uD, dsyMT, dsySig, dsyMsk]

variable (h : DsLay rg g)
include h

set_option maxHeartbeats 1000000 in
/-- **Phase C.** -/
theorem ds_PC (R : Regs T A) {n : ℕ} (hbig : Big n) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4)))
    (hD : (X (.o .uD)).length = d n) (h0 : ∀ y ∈ (dsPCPre : List (DsY t₀)), X y = []) :
    ∃ X' : DsY t₀ → List (Fin (A + 4)),
      (∀ y, y ∉ (dsPCOut : List (DsY t₀)) → X' y = X y) ∧ X' (.o .uD) = [] ∧
      X' dsyMT = crtEnts ((crtRevAx (d n)).map fun j =>
        (crtMu (s n) (Pipeline.s_pairwise n) j : ZMod (s n j)).val) ∧
      X' dsySig = binSyms (crtPre (srcAx n) (d n)) (crtSig (srcAx n) (s n) (d n)) ∧
      X' dsyMsk = binSyms (crtPre (srcAx n) (d n)) (crtMask (srcAx n) (d n)) ∧
      dsRuns body (dsPC rg g) (dsF rg g R X (pmW n) wl (pmVals n))
        (dsF rg g R X' (pmW n) wl (pmVals n)) (dsPCCost n) := by
  have hn := hbig.1
  simp only [dsPCPre, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h0
  obtain ⟨eTm, eUt, eTb, eTx, eMT, eSig, eMsk⟩ := h0
  have ne : ∀ {x y : DsY t₀}, x ≠ y → g x ≠ g y := fun hxy => h.ig.ne hxy
  -- init
  have s1 := dsF_code (body := body) h R wl X (pmVals n) (dsCInit_do (n := n))
    (ds_pmVals_lt hn) hwl
  -- the loop
  have hLC1 : ∀ e ∈ dsLC (g dsyMT), ∀ r, rg r ≠ e.1 := by simp [dsLC, h.disj]
  have hLC2 : ∀ e ∈ dsLC (g dsyMT), e.1 ≠ g (.o .uD) := by
    simp [dsLC]; exact ne (fun e => by cases e)
  have hLC3 : ∀ e ∈ dsLC (g dsyMT), e.1 ≠ g (.o .tm) := by
    simp [dsLC]; exact ne (fun e => by cases e)
  have s2 := ds_crtLoop (body := body) h.irg (fun r => h.disj r (.o .uD))
    (fun r => h.disj r (.o .tm)) (ne (fun e => by cases e)) (fun r => h.disj r dsyMT)
    (ne (fun e => by cases e)) (ne (fun e => by cases e)) hbig wl hwl (dsOv g R X)
    (by rw [dsOv_rg h.ig, hD]) (by rw [dsOv_rg h.ig, eTm])
  set X₁ := fun y => dsGAcc (dsCW n) (dsLC (g dsyMT)) (d n) (g y) ++ X y with hX₁
  have e2 : dsGPsi rg (dsOv g R X) (dsCV n) (dsCW n) (dsLC (g dsyMT)) (pmW n) wl wl (d n) =
      dsF rg g R X₁ (pmW n) wl (dsCV n (d n)) := by
    unfold dsGPsi dsF
    congr 1
    refine dsOv_eq_of h.ig (fun y => by rw [dsOv_rg h.ig]) (fun k hk => ?_)
    rw [dsOv_off _ _ hk, dsGAcc_none _ _ (by simp [dsLC]; exact hk _),
      List.nil_append]
  rw [e2] at s2
  have hoff : ∀ y, y ≠ dsyMT → X₁ y = X y := by
    intro y hy
    simp only [hX₁]
    rw [dsGAcc_none _ _ (by simp [dsLC]; exact ne (Ne.symm hy)), List.nil_append]
  have x1MT : X₁ dsyMT = crtEnts ((crtRevAx (d n)).map fun j =>
      (crtMu (s n) (Pipeline.s_pairwise n) j : ZMod (s n j)).val) := by
    simp only [hX₁, eMT, List.append_nil]
    exact ds_crt_mT (n := n) (d n) le_rfl
  -- `logT` ticks
  have hcv : ∀ j, dsCV n (d n) j < 2 ^ pmW n := dsCV_lt hbig le_rfl
  have s3 := dsF_un (body := body) h R wl X₁ (dsCV n (d n)) 5 (.o .ut) (hcv 5)
    (by rw [hoff _ (fun e => by cases e), eUt])
  have hv5 : dsCV n (d n) 5 = logT n := by simp [dsCV, pmNV, pmVal]
  rw [hv5, List.append_nil] at s3
  set X₂ := Function.update X₁ (.o .ut) (List.replicate (logT n) tick) with hX₂
  have hlogW : logT n ≤ pmW n := by
    have := pm_logT_le hn; have := pmW_ge n; omega
  have s4 := dsF_narrow (body := body) h R wl X₂ (dsCV n (d n)) 34 (.o .ut) (.o .tm) (.o .tb)
    (.o .tx) dsySig (by simp [List.nodup_cons]) (by simp [hX₂, hoff, eTm])
    (by simp [hX₂, hoff, eTb]) (by simp [hX₂, hoff, eTx]) (by simp [hX₂]) hlogW
    (l := []) (by simp [hX₂, hoff, eSig])
  rw [List.append_nil] at s4
  set X₃ := Function.update X₂ dsySig (binSyms (logT n) (dsCV n (d n) 34)) with hX₃
  have s5 := dsF_narrow (body := body) h R wl X₃ (dsCV n (d n)) 35 (.o .ut) (.o .tm) (.o .tb)
    (.o .tx) dsyMsk (by simp [List.nodup_cons]) (by simp [hX₃, hX₂, hoff, eTm])
    (by simp [hX₃, hX₂, hoff, eTb]) (by simp [hX₃, hX₂, hoff, eTx]) (by simp [hX₃, hX₂]) hlogW
    (l := []) (by simp [hX₃, hX₂, hoff, eMsk])
  rw [List.append_nil] at s5
  set X₄ := Function.update X₃ dsyMsk (binSyms (logT n) (dsCV n (d n) 35)) with hX₄
  have s6 := dsF_uclear (body := body) (W := pmW n) h R wl X₄ (dsCV n (d n)) (.o .ut)
    (c := logT n) (by simp [hX₄, hX₃, hX₂])
  set X₅ := Function.update X₄ (.o .ut) [] with hX₅
  have s7 := dsF_uclear (body := body) (W := pmW n) h R wl X₅ (dsCV n (d n)) (.o .uD)
    (c := d n) (by simp [hX₅, hX₄, hX₃, hX₂, hoff, hD])
  set X₆ := Function.update X₅ (.o .uD) [] with hX₆
  have s8 := dsF_code (body := body) h R wl X₆ (dsCV n (d n)) (dsCEnd_do (n := n)) hcv hwl
  have h34 : dsCV n (d n) 34 = crtSig (srcAx n) (s n) (d n) := by
    simp [dsCV, pmNV]; exact (ds_crtSig n (d n) le_rfl).symm
  have h35 : dsCV n (d n) 35 = crtMask (srcAx n) (d n) := by
    simp [dsCV, pmNV]; exact (ds_crtMask hbig (d n) le_rfl).symm
  have hpre : logT n = crtPre (srcAx n) (d n) := (ds_crtPre_d hn).symm
  refine ⟨X₆, fun y hy => ?_, by simp [hX₆], ?_, ?_, ?_, ?_⟩
  · simp only [dsPCOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4⟩ := hy
    by_cases hU : y = .o .ut
    · subst hU; simp [hX₆, hX₅, eUt]
    simp only [hX₆, hX₅, hX₄, hX₃, hX₂, Function.update_apply, hU, h1, h3, h4, if_false]
    exact hoff y h2
  · simp [hX₆, hX₅, hX₄, hX₃, hX₂, x1MT]
  · simp [hX₆, hX₅, hX₄, hX₃, h34, hpre]
  · simp [hX₆, hX₅, hX₄, h35, hpre]
  · refine (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8))))))).mono ?_
    unfold dsPCCost dsCrtCost dsGCost
    simp only [dsPushCost, dsLC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    have e : ∀ i ∈ Finset.range (d n), dsCW n i 38 = dsMu n i := fun i _ => by
      simp [dsCW, pmNV]
    rw [Finset.sum_congr rfl fun i hi => by rw [e i hi]]
    omega

end PC

end IntegerMultBounds.MathlibTM2.Fast.TableVM
