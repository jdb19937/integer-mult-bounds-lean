module

public import IntegerMultBounds.MathlibTM2.Fast.ConvBox
public import IntegerMultBounds.MathlibTM2.Fast.ConvSynthQ

/-!
# The complex convolution stage with computed rounds

`Fast/ConvBox` for transforms meeting `SynFwdSpecQ`, `SynOppSpecQ` with computed rounds `F`,
`O`: the same program `cvBox` pushes the box stream of
`cconvApproxVia (boxSplit t h) p θ⁺ θ⁻ (synthMrQ a N F O) f g` (`cvBoxQ_runs`), given
`eSynthQ a N τ < 2^p` (`Mult/SynthErrQ`), which bounds the computed convolution below modulus
`2` (`cv_norm_convQ_lt`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.ConvSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Mult.ComplexConv
open IntegerMultBounds.Spec.SignedRingProduct

noncomputable section

/-! ### Semantics -/

section StageSemQ

variable {D r : ℕ} [NeZero r] (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)]
  (h : t (Fin.last D) = r) (a : Fin D → ℕ) {p : ℕ} {τ : ℝ}
  (F : RoundOp (List.ofFn a).sum p (fwdRound (r := r) (List.ofFn a)) (etaQ p τ))
  (O : RoundOp (List.ofFn a).sum p (oppRound (r := r) (List.ofFn a)) (etaQ p τ))

/-- On the first `M` records the computed convolution of the twisted records is `M̃_r` of the
ring operands at the record's box point. -/
theorem cv_convQ_eq_synthMrQ (θ : Fin r → ℂ) (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ)
    {n : ℕ} (hn : n < (List.ofFn (cvN t)).prod) :
    convQ a F O (cvTw t h p θ f) (cvTw t h p θ g) n =
      synthMrQ a (cvN t) F O (cvU t h p θ f) (cvU t h p θ g) (dec (cvN t) n) := by
  simp only [synthMrQ, enc_dec (cvN t) hn]
  rfl

/-- The computed convolution has modulus below `2` when `eSynthQ < 2^p`. -/
theorem cv_norm_convQ_lt (ha : ∀ i, t i.castSucc = 2 ^ a i) (hdvd : ∀ i, 2 ^ a i ∣ 2 * r)
    (hE : eSynthQ a (cvN t) τ < 2 ^ p) (θ : Fin r → ℂ) (hθ : ∀ k, ‖θ k‖ ≤ 1)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1)
    {n : ℕ} (hn : n < (List.ofFn (cvN t)).prod) (k : Fin r) :
    ‖convQ a F O (cvTw t h p θ f) (cvTw t h p θ g) n k‖ < 2 := by
  rw [cv_convQ_eq_synthMrQ t h a F O θ f g hn]
  have hU := cv_diskGrid_U t h (p := p) θ hθ f hf
  have hV := cv_diskGrid_U t h (p := p) θ hθ g hg
  have hR := synthMrQ_ringApprox a (cvN t) ha hdvd F O _ _ hU hV (dec (cvN t) n) k
  have hC := norm_synthConvNormG_le (fun j k => (hU j k).2) (fun j k => (hV j k).2) zero_le_one
    zero_le_one (dec (cvN t) n) k
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set X := synthMrQ a (cvN t) F O (cvU t h p θ f) (cvU t h p θ g) (dec (cvN t) n) k
  set Y := synthConvNormG (cvU t h p θ f) (cvU t h p θ g) (dec (cvN t) n) k
  have h1 : ‖X‖ ≤ ‖X - Y‖ + ‖Y‖ := by
    calc ‖X‖ = ‖(X - Y) + Y‖ := by rw [sub_add_cancel]
      _ ≤ ‖X - Y‖ + ‖Y‖ := norm_add_le _ _
  have h2 : 2 ^ p * ‖X - Y‖ < 2 ^ p := hR.trans_lt hE
  have h3 : ‖X - Y‖ < 1 := lt_of_mul_lt_mul_left (by rwa [mul_one]) hp.le
  linarith

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
/-- The computed convolution of disk grid records lies on the grid. -/
theorem cv_isFixed_convQ {u v : Recs r} (hu : SupLe (List.ofFn a).sum u 1)
    (hv : SupLe (List.ofFn a).sum v 1) (hug : GridR p u) (hvg : GridR p v) (n : ℕ) (k : Fin r) :
    IsFixed p (convQ a F O u v n k) := by
  have hFu := (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hu hug).1
  have hFv := (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hv hvg).1
  have hg := (oppRoundsQ_dom (List.ofFn a) O (nRounds a) (pwC_supLe p hFu hFv)
    (gridR_rdR p _)).2 n k
  simp only [convQ, Pi.smul_apply, smul_eq_mul]
  rw [tsA_prod]
  push_cast
  rw [← cst_grid_numer hg, cst_two_pow_mul_grid]
  exact cst_isFixed_grid p _

/-- **The untwist.** The table product of the records of `convQ` of the twisted operands with
the table `θ⁻` is the box stream of `cconvApproxVia (boxSplit t h) p θ⁺ θ⁻ (synthMrQ …)`. -/
theorem cv_untwist_eqQ (θp θm : Fin r → ℂ) (hθp : ∀ k, ‖θp k‖ ≤ 1)
    (hθm : ∀ k, IsFixed p (θm k)) (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    tableOut (fun x y => tdivN p (x * y))
        ((List.range (List.ofFn (cvN t)).prod).map fun n =>
          List.ofFn (cvNum p (convQ a F O (cvTw t h p θp f) (cvTw t h p θp g)) n))
        (List.ofFn fun k => numer p (θm k)) =
      cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMrQ a (cvN t) F O) f g) := by
  rw [cv_tableOut_rec, cv_numBox_eq t h]
  refine cv_rpStream_congr fun n hn => ?_
  funext k
  simp only [cvNum]
  have hfix := cv_isFixed_convQ a F O (fun n _ c => cv_tw_norm_le t h θp hθp f hf n c)
    (fun n _ c => cv_tw_norm_le t h θp hθp g hg n c) (cv_gridR_tw t h p θp f)
    (cv_gridR_tw t h p θp g) n k
  rw [cv_numer_twist hfix (hθm k), cv_convQ_eq_synthMrQ t h a F O θp f g hn]
  simp only [cvRecs, cconvApproxVia, Function.comp_apply, AddEquiv.apply_symm_apply]
  rfl

end StageSemQ

/-! ### The contract -/

section MainQ

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

theorem cvBoxQ_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {D l : ℕ} (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] (h : t (Fin.last D) = 2 ^ l)
    (a : Fin D → ℕ) (ha : ∀ i, t i.castSucc = 2 ^ a i)
    (hdvd : ∀ i, 2 ^ a i ∣ 2 * 2 ^ l)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p cF cO : ℕ} {π : ℕ → ℕ} {τ : ℝ}
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) (etaQ p τ))
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w p l a π F cF)
    (hO : SynOppSpecQ body oppP (rg .io) PreO w p l a π O cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM a, π n < cvM a) (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn a).sum ≤ w) (hE : eSynthQ a (cvN t) τ < 2 ^ p)
    (θp θm : Fin (2 ^ l) → ℂ) (hθp : ∀ k, IsFixed p (θp k) ∧ ‖θp k‖ ≤ 1)
    (hθm : ∀ k, IsFixed p (θm k) ∧ ‖θm k‖ ≤ 1)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ∀ x, IsFixed p (f x))
    (hg : ∀ x, IsFixed p (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox p t f)) (hgi : ρ .gi = cstream A w (cstNumBox p t g))
    (htp : ρ .tp = cstream A w (List.ofFn fun k => numer p (θp k)))
    (htm : ρ .tm = cstream A w (List.ofFn fun k => numer p (θm k)))
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w p) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = []) (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn a).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn a).sum) (hshT : ρ .shT = [])
    (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo (cstream A w
        (cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMrQ a (cvN t) F O) f g)) ++
          ρ .fo))
      (cvBoxCost T p l w (List.ofFn a).sum (cvM a) cF cO) := by
  have hMN : (List.ofFn (cvN t)).prod = cvM a := by
    rw [ofFn_eq_tsA a (cvN t) ha, tsA_prod]
  set Tu := cvTw t h p θp f with hTu
  set Tv := cvTw t h p θp g with hTv
  set Zu := cvNum p Tu with hZu
  set Zv := cvNum p Tv with hZv
  have hgu : rpGrid p Zu = Tu := cv_rpGrid_cvNum (cv_gridR_tw t h p θp f)
  have hgv : rpGrid p Zv = Tv := cv_rpGrid_cvNum (cv_gridR_tw t h p θp g)
  have hconv : cvConvNumQ p a F O Zu Zv = cvNum p (convQ a F O Tu Tv) := by
    rw [cvConvNumQ, hgu, hgv]
  have hu : SupLe (List.ofFn a).sum (rpGrid p Zu) 1 := by
    rw [hgu]; intro n _ c; exact cv_tw_norm_le t h θp (fun k => (hθp k).2) f hf1 n c
  have hv : SupLe (List.ofFn a).sum (rpGrid p Zv) 1 := by
    rw [hgv]; intro n _ c; exact cv_tw_norm_le t h θp (fun k => (hθp k).2) g hg1 n c
  -- blocks and tables
  set Θp := List.ofFn fun k => numer p (θp k) with hΘp
  set Θm := List.ofFn fun k => numer p (θm k) with hΘm
  have hL : 1 ≤ Θp.length := by simp [hΘp, Nat.one_le_two_pow]
  have hLm : 1 ≤ Θm.length := by simp [hΘm, Nat.one_le_two_pow]
  have hlen : ∀ (X : ℕ → Fin (2 ^ l) → GaussianInt) (Θ : List GaussianInt),
      Θ.length = 2 ^ l → ∀ b ∈ (List.range (cvM a)).map (fun n => List.ofFn (X n)),
        b.length = Θ.length := by
    intro X Θ hΘ b hb
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 hb
    simp [hΘ]
  have hfitsΘ : ∀ θ : Fin (2 ^ l) → ℂ, (∀ k, IsFixed p (θ k) ∧ ‖θ k‖ ≤ 1) →
      ∀ x ∈ List.ofFn (fun k => numer p (θ k)), Fits w x := by
    intro θ hθ x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact cv_fits_of_norm (lt_of_le_of_lt (hθ k).2 one_lt_two) hw
  have hfitsF : ∀ F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ, ‖F‖ ≤ 1 →
      ∀ x ∈ ((List.range (cvM a)).map fun n => List.ofFn (cvRecs t h p F n)).flatten,
        Fits w x := by
    intro F hF1 x hx
    rw [cv_blocks_flatten] at hx
    obtain ⟨n, _, k, rfl⟩ := cv_mem_rpStream hx
    exact cv_fits_of_norm (lt_of_le_of_lt ((norm_le_pi_norm F _).trans hF1) one_lt_two) hw
  have hfitsS : ∀ x ∈ ((List.range (cvM a)).map fun n =>
      List.ofFn (cvNum p (convQ a F O Tu Tv) n)).flatten, Fits w x := by
    intro x hx
    rw [cv_blocks_flatten] at hx
    obtain ⟨n, hn, k, rfl⟩ := cv_mem_rpStream hx
    exact cv_fits_of_norm (cv_norm_convQ_lt t h a F O ha hdvd hE θp (fun k => (hθp k).2) f g hf1 hg1
      (by rw [hMN]; exact hn) k) hw
  have hBf : cstream A w (cstNumBox p t f) =
      cstream A w ((List.range (cvM a)).map fun n => List.ofFn (cvRecs t h p f n)).flatten := by
    rw [cv_blocks_flatten, cv_numBox_eq t h, hMN]
  have hBg : cstream A w (cstNumBox p t g) =
      cstream A w ((List.range (cvM a)).map fun n => List.ofFn (cvRecs t h p g n)).flatten := by
    rw [cv_blocks_flatten, cv_numBox_eq t h, hMN]
  have tw1 := cv_twist_eq t h θp (fun k => (hθp k).1) f hf (cvM a)
  have tw2 := cv_twist_eq t h θp (fun k => (hθp k).1) g hg (cvM a)
  have tw4 : tableOut (fun x y => tdivN p (x * y))
      ((List.range (cvM a)).map fun n => List.ofFn (cvNum p (convQ a F O Tu Tv) n)) Θm =
      cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMrQ a (cvN t) F O) f g) := by
    rw [← hMN]
    exact cv_untwist_eqQ t h a F O θp θm (fun k => (hθp k).2) (fun k => (hθm k).1) f g hf1 hg1
  -- 1. twist of `f` onto `io`
  have s1 := cv_table_runs (body := body) (Pre := Pre) hrg hdisj hι hT64 hQs hA
    (xs := .fi) (ys := .tp) (out := .io)
    (cvLay_inj (by decide) (by decide) (by decide) (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp)) (w := w) (q := p) (by omega) (by omega) ρ hrd _ Θp hL
    (hlen _ Θp (by simp [hΘp])) (hfitsF f hf1) (hfitsΘ θp hθp) (by rw [hfi, hBf]) htp hxsv hysv
    hacc
  rw [tw1, hio, List.append_nil] at s1
  set ρ1 := Function.update ρ .io (cstream A w (rpStream (cvM a) Zu)) with hρ1
  have hcm1 : (fun x => ρ1 (.cm x)) = fun x => ρ (.cm x) := by funext x; simp [ρ1]
  -- 2. twist of `g` onto `sy`
  have s2 := cv_table_runs (body := body) (Pre := Pre) hrg hdisj hι hT64 hQs hA
    (xs := .gi) (ys := .tp) (out := .sy)
    (cvLay_inj (by decide) (by decide) (by decide) (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp)) (w := w) (q := p) (by omega) (by omega) ρ1 (by rw [hcm1]; exact hrd) _
    Θp hL
    (hlen _ Θp (by simp [hΘp])) (hfitsF g hg1) (hfitsΘ θp hθp)
    (by simp [ρ1, hgi, hBg]) (by simp [ρ1, htp]) (by simp [ρ1, hxsv]) (by simp [ρ1, hysv])
    (by simp [ρ1, hacc])
  rw [tw2] at s2
  set ρ2 := Function.update ρ1 .sy (cstream A w (rpStream (cvM a) Zv) ++ ρ1 .sy) with hρ2
  -- 3. the synthetic convolution onto `so`
  have s3 := cvSynthQ_runs (body := body) (ι := ι) (Pre := Pre) hrg hdisj hP hT hQ (by omega)
    F O hF hO hPF hPO hπ hp hw hSw Zu Zv hu hv ρ2 (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1, hsy])
    (by simp [ρ2, ρ1, ht1]) (by simp [ρ2, ρ1, hxs]) (by simp [ρ2, ρ1, hout])
    (by simp [ρ2, ρ1, hrd.wn]) (by simp [ρ2, ρ1, hsv]) (by simp [ρ2, ρ1, hta])
    (by simp [ρ2, ρ1, htb]) (by simp [ρ2, ρ1, hracc]) (by simp [ρ2, ρ1, htmp])
    (by simp [ρ2, ρ1, hd0]) (fun j hj => by simp [ρ2, ρ1, hpriv j hj]) (by simp [ρ2, ρ1, hshD])
    (by simp [ρ2, ρ1, hshS]) (by simp [ρ2, ρ1, hshR]) (by simp [ρ2, ρ1, hshT])
    (by simp [ρ2, ρ1, hshU])
  rw [hconv] at s3
  set ρ3 := Function.update (Function.update (Function.update ρ2 .io []) .sy []) .so
    (cstream A w (rpStream (cvM a) (cvNum p (convQ a F O Tu Tv))) ++ ρ2 .so) with hρ3
  have hcm3 : (fun x => ρ3 (.cm x)) = fun x => ρ (.cm x) := by funext x; simp [ρ3, ρ2, ρ1]
  -- 4. untwist of `so` onto `fo`
  have s4 := cv_table_runs (body := body) (Pre := Pre) hrg hdisj hι hT64 hQs hA
    (xs := .so) (ys := .tm) (out := .fo)
    (cvLay_inj (by decide) (by decide) (by decide) (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp)) (w := w) (q := p) (by omega) (by omega) ρ3 (by rw [hcm3]; exact hrd) _
    Θm hLm
    (hlen _ Θm (by simp [hΘm])) hfitsS (hfitsΘ θm hθm)
    (by simp [ρ3, ρ2, ρ1, hso, cv_blocks_flatten]) (by simp [ρ3, ρ2, ρ1, htm])
    (by simp [ρ3, ρ2, ρ1, hxsv]) (by simp [ρ3, ρ2, ρ1, hysv]) (by simp [ρ3, ρ2, ρ1, hacc])
  rw [tw4] at s4
  set ρ4 := Function.update ρ3 .fo (cstream A w
    (cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMrQ a (cvN t) F O) f g)) ++
      ρ3 .fo) with hρ4
  -- 5. clear `so`
  have s5 := CvRuns.of_rsa (Pre := Pre) (rsa_uclear (body := body) (ι := ι) hrg .so ρ4)
  have H := s1.seq hdisj hP (s2.seq hdisj hP (s3.seq hdisj hP (s4.seq hdisj hP s5)))
  refine (H.congr ?_).mono ?_
  · funext k
    simp only [ρ4, ρ3, ρ2, ρ1, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have e1 : (ρ4 .so).length = cvM a * 2 ^ l * w := by
      simp [ρ4, ρ3, ρ2, ρ1, hso, length_cstream, length_rpStream]
    rw [e1, cv_blocks_flatten, cv_blocks_flatten, cv_blocks_flatten, length_rpStream,
      length_rpStream, length_rpStream]
    unfold cvBoxCost
    omega

end MainQ

end

end IntegerMultBounds.MathlibTM2.Fast.ConvSt
