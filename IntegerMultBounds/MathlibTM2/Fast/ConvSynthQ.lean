module

public import IntegerMultBounds.MathlibTM2.Fast.ConvSynth
public import IntegerMultBounds.MathlibTM2.Fast.ConvSpecQ

/-!
# The synthetic convolution with computed rounds

`Fast/ConvSynth` for transforms meeting `SynFwdSpecQ`, `SynOppSpecQ` (`Fast/ConvSpecQ`) with
computed rounds `F`, `O`: the same program `cvSynth` pushes the numerators `cvConvNumQ` of
`convQ a F O` (`Mult/SynthErrQ`) of the grid operands (`cvSynthQ_runs`). Unlike `Q_p`, the
computed rounds keep the grid only on disk grid inputs, so the semantics lemmas take the disk
hypotheses of the operands.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.ConvSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.Spec.SignedRingProduct

noncomputable section

/-! ### Semantics -/

section SemQ

variable {d : ℕ} {τ : ℝ}

/-- The grid records of the forward output are the computed forward rounds in the order `π`. -/
theorem cv_rpGrid_fwdOutQ (p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ)
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (Z : ℕ → Fin (2 ^ l) → GaussianInt) (hZ : SupLe (List.ofFn a).sum (rpGrid p Z) 1) :
    rpGrid p (cvFwdOutQ p l a π F Z) =
      fun n => fwdRoundsQ F (nRounds a) (rpGrid p Z) (π n) := by
  funext n c
  rw [cv_rpGrid_apply]
  exact cst_grid_numer ((fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hZ (cv_gridR_rpGrid p Z)).2
    (π n) c)

/-- The ring products of the two forward outputs are the numerators of the pointwise products,
in the order `π`. -/
theorem cv_rpOut_fwdQ (p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ)
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt)
    (hu : SupLe (List.ofFn a).sum (rpGrid p Zu) 1) (hv : SupLe (List.ofFn a).sum (rpGrid p Zv) 1) :
    rpOut p (cvFwdOutQ p l a π F Zu) (cvFwdOutQ p l a π F Zv) =
      fun n => cvNum p (pwC p (fwdRoundsQ F (nRounds a) (rpGrid p Zu))
        (fwdRoundsQ F (nRounds a) (rpGrid p Zv))) (π n) := by
  funext n c
  have h := rp_pwC_grid p (cvFwdOutQ p l a π F Zu) (cvFwdOutQ p l a π F Zv) n c
  rw [cv_rpGrid_fwdOutQ p l a π F Zu hu, cv_rpGrid_fwdOutQ p l a π F Zv hv, cv_pwC_comp,
    cv_mk_grid] at h
  show _ = numer p _
  rw [h, cst_numer_grid]

/-- The numerators of the computed synthetic convolution `convQ` of two grid arrays. -/
def cvConvNumQ (p : ℕ) {l : ℕ} (a : Fin d → ℕ)
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt) : ℕ → Fin (2 ^ l) → GaussianInt :=
  cvNum p (convQ a F O (rpGrid p Zu) (rpGrid p Zv))

/-- `convQ` is the opposite output of the pointwise products, scaled by `M = 2^{Σ aᵢ}`. -/
theorem cv_convNumQ_eq (p l : ℕ) (a : Fin d → ℕ)
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt)
    (hu : SupLe (List.ofFn a).sum (rpGrid p Zu) 1) (hv : SupLe (List.ofFn a).sum (rpGrid p Zv) 1) :
    cvConvNumQ p a F O Zu Zv = fun n c => 2 ^ (List.ofFn a).sum *
      cvOppOutQ p l a O (cvNum p (pwC p (fwdRoundsQ F (nRounds a) (rpGrid p Zu))
        (fwdRoundsQ F (nRounds a) (rpGrid p Zv)))) n c := by
  funext n c
  have hFu := (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hu (cv_gridR_rpGrid p Zu)).1
  have hFv := (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hv (cv_gridR_rpGrid p Zv)).1
  have hg : GridR p (pwC p (fwdRoundsQ F (nRounds a) (rpGrid p Zu))
      (fwdRoundsQ F (nRounds a) (rpGrid p Zv))) := gridR_rdR p _
  have hO := (oppRoundsQ_dom (List.ofFn a) O (nRounds a) (pwC_supLe p hFu hFv) hg).2
  simp only [cvConvNumQ, cvOppOutQ]
  rw [cv_rpGrid_cvNum hg]
  simp only [cvNum, convQ, Pi.smul_apply, smul_eq_mul]
  rw [tsA_prod]
  push_cast
  exact cst_numer_two_pow_mul (hO n c) _

end SemQ

/-! ### The contract -/

section MainQ

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

variable {d : ℕ} {τ : ℝ}

/-- The forward transform on `io`. -/
theorem cv_fwd_runsQ (hrg : Function.Injective rg) {fwdP : Pr P T Q A U}
    {PreF : Stacks T A → Prop} {w p l cF : ℕ} {a : Fin d → ℕ} {π : ℕ → ℕ}
    {F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ)}
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w p l a π F cF)
    (hPF : ∀ S, Pre S → PreF S) (Z : ℕ → Fin (2 ^ l) → GaussianInt)
    (hZ : SupLe (List.ofFn a).sum (rpGrid p Z) 1) (ρ : CvR → List (Fin (A + 4)))
    (hio : ρ .io = cstream A w (rpStream (cvM a) Z)) :
    CvRuns body rg ι Pre fwdP ρ
      (Function.update ρ .io (cstream A w (rpStream (cvM a) (cvFwdOutQ p l a π F Z)))) cF :=
  cv_runs_of_update hrg _ _ fun v S _ hpre hS =>
    hF Z v S (hPF S hpre) hZ (by rw [hS, hio])

/-- The opposite transform on `io`. -/
theorem cv_opp_runsQ (hrg : Function.Injective rg) {oppP : Pr P T Q A U}
    {PreO : Stacks T A → Prop} {w p l cO : ℕ} {a : Fin d → ℕ} {π : ℕ → ℕ}
    {O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ)}
    (hO : SynOppSpecQ body oppP (rg .io) PreO w p l a π O cO)
    (hPO : ∀ S, Pre S → PreO S) (V : ℕ → Fin (2 ^ l) → GaussianInt)
    (hV : SupLe (List.ofFn a).sum (rpGrid p V) 1) (ρ : CvR → List (Fin (A + 4)))
    (hio : ρ .io = cstream A w (rpStream (cvM a) fun n => V (π n))) :
    CvRuns body rg ι Pre oppP ρ
      (Function.update ρ .io (cstream A w (rpStream (cvM a) (cvOppOutQ p l a O V)))) cO :=
  cv_runs_of_update hrg _ _ fun v S _ hpre hS =>
    hO V v S (hPO S hpre) hV (by rw [hS, hio])

theorem cvSynthQ_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hP : CvFramed rg Pre) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p l cF cO : ℕ}
    {a : Fin d → ℕ} {π : ℕ → ℕ} {τ : ℝ}
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w p l a π F cF)
    (hO : SynOppSpecQ body oppP (rg .io) PreO w p l a π O cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM a, π n < cvM a) (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn a).sum ≤ w)
    (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt)
    (hu : SupLe (List.ofFn a).sum (rpGrid p Zu) 1) (hv : SupLe (List.ofFn a).sum (rpGrid p Zv) 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hio : ρ .io = cstream A w (rpStream (cvM a) Zu))
    (hsy : ρ .sy = cstream A w (rpStream (cvM a) Zv))
    (ht1 : ρ .t1 = []) (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = [])
    (hwn : (ρ (.cm .wn)).length = w) (hsv : ρ (.rr .sv) = []) (hta : ρ (.rr .ta) = [])
    (htb : ρ (.rr .tb) = []) (hacc : ρ (.rr .acc) = []) (htmp : ρ (.rr .tmp) = [])
    (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn a).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn a).sum) (hshT : ρ .shT = [])
    (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvSynth rg hrg hT hQ fwdP oppP) ρ
      (Function.update (Function.update (Function.update ρ .io []) .sy []) .so
        (cstream A w (rpStream (cvM a) (cvConvNumQ p a F O Zu Zv)) ++ ρ .so))
      (cvSynthCost T p l w (List.ofFn a).sum (cvM a) cF cO) := by
  set Fu := fwdRoundsQ F (nRounds a) (rpGrid p Zu) with hFu_def
  set Fv := fwdRoundsQ F (nRounds a) (rpGrid p Zv) with hFv_def
  set Xu := cvFwdOutQ p l a π F Zu with hXu_def
  set Xv := cvFwdOutQ p l a π F Zv with hXv_def
  set V := cvNum p (pwC p Fu Fv) with hV_def
  set Ov := cvOppOutQ p l a O V with hO_def
  have hFu : SupLe (List.ofFn a).sum Fu 1 :=
    (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hu (cv_gridR_rpGrid p Zu)).1
  have hFv : SupLe (List.ofFn a).sum Fv 1 :=
    (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hv (cv_gridR_rpGrid p Zv)).1
  have hVd : SupLe (List.ofFn a).sum (rpGrid p V) 1 := by
    have hg : GridR p (pwC p Fu Fv) := gridR_rdR p _
    rw [hV_def, cv_rpGrid_cvNum hg]
    exact pwC_supLe p hFu hFv
  have hXu : ∀ n < cvM a, DiskGrid p (rpRec Xu n).1 (rpRec Xu n).2 := fun n hn =>
    rp_diskGrid_of_norm p Xu n fun c => by
      rw [hXu_def, cv_rpGrid_fwdOutQ p l a π F Zu hu]; exact hFu (π n) (hπ n hn) c
  have hXv : ∀ n < cvM a, DiskGrid p (rpRec Xv n).1 (rpRec Xv n).2 := fun n hn =>
    rp_diskGrid_of_norm p Xv n fun c => by
      rw [hXv_def, cv_rpGrid_fwdOutQ p l a π F Zv hv]; exact hFv (π n) (hπ n hn) c
  have hW : rpOut p Xu Xv = fun n => V (π n) := cv_rpOut_fwdQ p l a π F Zu Zv hu hv
  have hscale : (rpStream (cvM a) Ov).map (fun N => 2 ^ (List.ofFn a).sum * N) =
      rpStream (cvM a) (cvConvNumQ p a F O Zu Zv) := by
    rw [cv_rpStream_map, cv_convNumQ_eq p l a F O Zu Zv hu hv]
  -- 1. forward transform of `Zu` on `io`
  have s1 := cv_fwd_runsQ (body := body) (ι := ι) (Pre := Pre) hrg hF hPF Zu hu ρ hio
  set ρ1 := Function.update ρ .io (cstream A w (rpStream (cvM a) Xu)) with hρ1
  -- 2. `io → rr.xs`
  have s2 := cv_xfer_runs (body := body) (Pre := Pre) hrg hdisj (a := .io) (b := .rr .xs)
    (by decide) (by decide) (by decide) ρ1 (by simp [ρ1, ht1])
  set ρ2 := Function.update (Function.update ρ1 .io []) (.rr .xs) (ρ1 .io ++ ρ1 (.rr .xs))
    with hρ2
  -- 3. `sy → io`
  have s3 := cv_xfer_runs (body := body) (Pre := Pre) hrg hdisj (a := .sy) (b := .io)
    (by decide) (by decide) (by decide) ρ2 (by simp [ρ2, ρ1, ht1])
  set ρ3 := Function.update (Function.update ρ2 .sy []) .io (ρ2 .sy ++ ρ2 .io) with hρ3
  -- 4. forward transform of `Zv` on `io`
  have s4 := cv_fwd_runsQ (body := body) (ι := ι) (Pre := Pre) hrg hF hPF Zv hv ρ3
    (by simp [ρ3, ρ2, ρ1, hsy])
  set ρ4 := Function.update ρ3 .io (cstream A w (rpStream (cvM a) Xv)) with hρ4
  -- 5. ring products onto `rr.out`
  have s5 := cv_rp_runs (body := body) (ι := ι) (Pre := Pre) hrg hT hQ hA hp hw Xu Xv hXu hXv ρ4
    (by simp [ρ4, ρ3, ρ2, ρ1, hxs]) (by simp [ρ4]) (by simp [ρ4, ρ3, ρ2, ρ1, hwn])
    (by simp [ρ4, ρ3, ρ2, ρ1, hsv]) (by simp [ρ4, ρ3, ρ2, ρ1, hta])
    (by simp [ρ4, ρ3, ρ2, ρ1, htb]) (by simp [ρ4, ρ3, ρ2, ρ1, hacc])
    (by simp [ρ4, ρ3, ρ2, ρ1, htmp]) (by simp [ρ4, ρ3, ρ2, ρ1, hd0])
    (fun j hj => by simp [ρ4, ρ3, ρ2, ρ1, hpriv j hj])
  set ρ5 := Function.update ρ4 (.rr .out)
    (cstream A w (rpStream (cvM a) (rpOut p Xu Xv)) ++ ρ4 (.rr .out)) with hρ5
  -- 6, 7. clear the operands
  have s6 := CvRuns.of_rsa (Pre := Pre) (rsa_uclear (body := body) (ι := ι) hrg (.rr .xs) ρ5)
  set ρ6 := Function.update ρ5 (.rr .xs) [] with hρ6
  have s7 := CvRuns.of_rsa (Pre := Pre) (rsa_uclear (body := body) (ι := ι) hrg .io ρ6)
  set ρ7 := Function.update ρ6 .io [] with hρ7
  -- 8. `rr.out → io`
  have s8 := cv_xfer_runs (body := body) (Pre := Pre) hrg hdisj (a := .rr .out) (b := .io)
    (by decide) (by decide) (by decide) ρ7 (by simp [ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, ht1])
  set ρ8 := Function.update (Function.update ρ7 (.rr .out) []) .io (ρ7 (.rr .out) ++ ρ7 .io)
    with hρ8
  -- 9. the opposite transform on `io`
  have s9 := cv_opp_runsQ (body := body) (ι := ι) (Pre := Pre) hrg hO hPO V hVd ρ8
    (by simp [ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hout, hW])
  set ρ9 := Function.update ρ8 .io (cstream A w (rpStream (cvM a) Ov)) with hρ9
  -- 10. the shift by `Σ aᵢ` bits onto `so`
  have s10 := CvRuns.of_rsa (Pre := Pre) (cst_scale_runs (body := body) (ι := ι) hrg
    (src := CvR.io) (dst := .shD) (out := .so) (cS := .shS) (cR := .shR) (tS := .shT)
    (tR := .shU) (by decide) (by decide) (by omega) hSw ρ9 (rpStream (cvM a) Ov) (by simp [ρ9])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshS])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshR])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshT])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshU])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshD]))
  have H := s1.seq hdisj hP (s2.seq hdisj hP (s3.seq hdisj hP (s4.seq hdisj hP
    (s5.seq hdisj hP (s6.seq hdisj hP (s7.seq hdisj hP (s8.seq hdisj hP
      (s9.seq hdisj hP s10))))))))
  refine (H.congr ?_).mono ?_
  · rw [hscale]
    funext k
    simp only [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have hL : ∀ X : ℕ → Fin (2 ^ l) → GaussianInt,
        (cstream A w (rpStream (cvM a) X)).length = cvM a * 2 ^ l * w := fun X => by
      rw [length_cstream, length_rpStream]
    have e1 : (ρ1 .io).length = cvM a * 2 ^ l * w := by simp only [ρ1, Function.update_self, hL]
    have e2 : (ρ2 .sy).length = cvM a * 2 ^ l * w := by simp [ρ2, ρ1, hsy, hL]
    have e3 : (ρ5 (.rr .xs)).length = cvM a * 2 ^ l * w := by simp [ρ5, ρ4, ρ3, ρ2, ρ1, hxs, hL]
    have e4 : (ρ6 .io).length = cvM a * 2 ^ l * w := by simp [ρ6, ρ5, ρ4, hL]
    have e5 : (ρ7 (.rr .out)).length = cvM a * 2 ^ l * w := by
      simp [ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hout, hL]
    rw [e1, e2, e3, e4, e5, length_rpStream]
    unfold cvSynthCost
    omega

end MainQ

end

end IntegerMultBounds.MathlibTM2.Fast.ConvSt
