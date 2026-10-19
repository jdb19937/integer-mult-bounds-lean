module

public import IntegerMultBounds.MathlibTM2.Fast.SrcDirectStage
public import IntegerMultBounds.MathlibTM2.Fast.ConvBoxQPipeline
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The source transforms for any box stage

`Fast/SrcPhase`, `Fast/SrcStage` and `Fast/SrcDirectStage` for a box stage given as a contract:
`CvBoxRuns` says the box program computes a box convolution `cb`. `cvBox_convBox_runs` and
`cvBoxQ_convBoxQ_runs` are the instances with exact and with computed rounds. With the guarantee
`BoxConvSpec n cb` and grid outputs, the source machines compute `srcMapG n cb` and
`oppMapG n cb` (`srcDirectP_runsG`, `srcDirectOpp_runsG`).
-/

@[expose] public section

noncomputable section

namespace IntegerMultBounds.MathlibTM2.Fast.ConvSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Mult.ComplexConv
open IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Fast.TableVM

section Box

variable {T Q A : ℕ} {U P : Type}

/-- **The box stage computes `cb`.** From `fi`, `gi` holding the box streams of grid functions
of sup norm at most `1`, the twist tables on `tp`, `tm`, the ring header on `rpi 0` and the
other stage registers as `cvBox_convBox` needs them, `box` pushes the box stream of `cb f g`
onto `fo` and leaves every other register as it found it, within `c` steps. -/
def CvBoxRuns (body : P → Pr P T Q A U) (rg : CvR → Fin T) (ι : Fin 64 → Fin T)
    (Pre : Stacks T A → Prop) (box : Pr P T Q A U) (n w : ℕ) (cb : BoxConvOf n) (c : ℕ) : Prop :=
  ∀ (f g : ((i : Fin (Sizes.d n)) → ZMod (Sizes.t n i)) → ℂ),
    (∀ x, IsFixed (Sizes.p n) (f x)) → (∀ x, IsFixed (Sizes.p n) (g x)) → ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
  ∀ (ρ : CvR → List (Fin (A + 4))),
    ρ .fi = cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) f) →
    ρ .gi = cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) g) →
    ρ .tp = tblTwistStream A w (Sizes.p n) (Sizes.r n) false →
    ρ .tm = tblTwistStream A w (Sizes.p n) (Sizes.r n) true →
    ρ .io = [] → ρ .sy = [] → ρ .so = [] → ρ .t1 = [] →
    Ready (fun x => ρ (.cm x)) w (Sizes.p n) → ρ (.cm .xsv) = [] →
    ρ (.cm .ysv) = [] → ρ (.cm .acc) = [] →
    ρ (.rr .xs) = [] → ρ (.rr .out) = [] → ρ (.rr .sv) = [] →
    ρ (.rr .ta) = [] → ρ (.rr .tb) = [] → ρ (.rr .acc) = [] →
    ρ (.rr .tmp) = [] →
    ρ (.rpi 0) = (header (Sizes.p n) (Sizes.r n) w).map bitSymbol →
    (∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = []) →
    ρ .shD = [] → (ρ .shS).length = (List.ofFn (cvAx (Sizes.t n))).sum →
    (ρ .shR).length = w - (List.ofFn (cvAx (Sizes.t n))).sum →
    ρ .shT = [] → ρ .shU = [] →
    CvRuns body rg ι Pre box ρ
      (Function.update ρ .fo
        (cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) (cb f g)) ++ ρ .fo)) c

variable {body : P → Pr P T Q A U} {rg : CvR → Fin T} {ι : Fin 64 → Fin T}
  {Pre : Stacks T A → Prop}

/-- `cvBox` with exact transforms computes `convBox n`. -/
theorem cvBox_convBox_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A) {n : ℕ} (hn : Sizes.Big n)
    (hEs : 9 * (2 : ℝ) ^ Sizes.gamma n * Sizes.T n * Sizes.logT n ≤ 2 ^ Sizes.p n / 100)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (rg .io) PreF w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π cF)
    (hO : SynOppSpec body oppP (rg .io) PreO w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (Sizes.t n)), π m < cvM (cvAx (Sizes.t n)))
    (hw : Sizes.p n + 2 ≤ w) (hSw : (List.ofFn (cvAx (Sizes.t n))).sum ≤ w) :
    CvBoxRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) n w (convBox n)
      (cvBoxCost T (Sizes.p n) (Sizes.ℓ n) w (List.ofFn (cvAx (Sizes.t n))).sum
        (cvM (cvAx (Sizes.t n))) cF cO) :=
  fun f g hf hg hf1 hg1 ρ hfi hgi htp htm hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv hta
    htb hracc htmp hd0 hpriv hshD hshS hshR hshT hshU =>
  cvBox_convBox hrg hdisj hι hP hT64 hQs hT hQ hA hn hEs hF hO hPF hPO hπ hw hSw f g hf hg hf1 hg1
    ρ hfi hgi htp htm hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv hta htb hracc htmp hd0 hpriv
    hshD hshS hshR hshT hshU

/-- `cvBox` with transforms meeting their contracts for computed rounds `F`, `O` computes
`convBoxQ n` of their pair on the box. -/
theorem cvBoxQ_convBoxQ_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A) {n : ℕ} (hn : Sizes.Big n)
    (hEs : 9 * (2 : ℝ) ^ Sizes.gamma n * Sizes.T n * Sizes.logT n ≤ 2 ^ Sizes.p n / 100)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w cF cO : ℕ} {π : ℕ → ℕ}
    {τ : ℝ} (hτ : 0 ≤ τ) (hτ8 : τ ≤ 1 / 8)
    (F : RoundOp (List.ofFn (cvAx (Sizes.t n))).sum (Sizes.p n)
      (fwdRound (r := 2 ^ Sizes.ℓ n) (List.ofFn (cvAx (Sizes.t n)))) (etaQ (Sizes.p n) τ))
    (O : RoundOp (List.ofFn (cvAx (Sizes.t n))).sum (Sizes.p n)
      (oppRound (r := 2 ^ Sizes.ℓ n) (List.ofFn (cvAx (Sizes.t n)))) (etaQ (Sizes.p n) τ))
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π F cF)
    (hO : SynOppSpecQ body oppP (rg .io) PreO w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π O cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (Sizes.t n)), π m < cvM (cvAx (Sizes.t n)))
    (hw : Sizes.p n + 2 ≤ w) (hSw : (List.ofFn (cvAx (Sizes.t n))).sum ≤ w) :
    CvBoxRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) n w
      (convBoxQ n (roundPairsOf (Sizes.p n) τ (Sizes.ℓ n) (Sizes.d n) (Sizes.t n) inferInstance
        (fun i hi => Pipeline.t_of_last hn i hi) F O))
      (cvBoxCost T (Sizes.p n) (Sizes.ℓ n) w (List.ofFn (cvAx (Sizes.t n))).sum
        (cvM (cvAx (Sizes.t n))) cF cO) :=
  fun f g hf hg hf1 hg1 ρ hfi hgi htp htm hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv hta
    htb hracc htmp hd0 hpriv hshD hshS hshR hshT hshU =>
  cvBoxQ_convBoxQ hrg hdisj hι hP hT64 hQs hT hQ hA hn hEs hτ hτ8 F O hF hO hPF hPO hπ hw hSw f g
    hf hg hf1 hg1 ρ hfi hgi htp htm hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv hta htb hracc
    htmp hd0 hpriv hshD hshS hshR hshT hshU

end Box

/-- The outputs of `boxConvQ` lie on the grid. -/
theorem boxConvQ_isFixed (p : ℕ) {τ : ℝ} :
    ∀ (D : ℕ) (t : Fin D → ℕ) (inst : ∀ i, NeZero (t i)) (FO : RoundPairs p τ D t inst)
      (f g : ((i : Fin D) → ZMod (t i)) → ℂ) (x : (i : Fin D) → ZMod (t i)),
      IsFixed p (boxConvQ p D t inst FO f g x)
  | 0, _, _, _, _, _, _ => ⟨0, 0, by apply Complex.ext <;> simp [boxConvQ]⟩
  | _ + 1, _, _, _, _, _, _ => isFixed_rhoC _ _

end IntegerMultBounds.MathlibTM2.Fast.ConvSt


namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Spec.SignedRingProduct (header)
open scoped Function

variable {t₀ T Q : ℕ}

section MarginsG

open IntegerMultBounds.Resampling.WeightTable (tableA tables_ok)

variable {n : ℕ}

theorem src_marginsG (h : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    (cb : BoxConvOf n) (hcb : BoxConvSpec n cb)
    {v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ} (hv : ‖v‖ ≤ 1 / 2) :
    ‖tensorZR (d n) (s n) (t n) (lineA n) v‖ ≤ 6 / 10 ∧
      ‖fun j => rhoC (p n) (starRingEnd ℂ (chirpKernel n j) *
        tensorZR (d n) (s n) (t n) (lineA n) v j)‖ ≤ 6 / 10 ∧
      ‖cb (chirpKernel n) (fun j => rhoC (p n) (starRingEnd ℂ (chirpKernel n j) *
        tensorZR (d n) (s n) (t n) (lineA n) v j))‖ ≤ 701 / 1000 ∧
      ‖bluesteinApproxD (p n) (chirpKernel n) cb
        (tensorZR (d n) (s n) (t n) (lineA n) v)‖ ≤ 701 / 1000 := by
  have hd1 := h.one_le_d
  have hpT : ∏ i, t n i = Sizes.T n := prod_t hd1
  have hα1 : (1 : ℝ) ≤ alpha n := by
    have := two_le_alpha h.1; exact_mod_cast (show 1 ≤ alpha n by omega)
  have hsm : 2 * d n * p n ^ 2 ≤ (∏ i, t n i) * logT n := by rw [hpT]; exact hsmall
  have hEs' : 9 * (2 : ℝ) ^ (d n * (2 * ⌈(alpha n : ℝ) ^ 2⌉₊ + 2)) *
      ((∏ i, t n i : ℕ) : ℝ) * logT n ≤ 2 ^ p n / 100 := by
    rw [hpT]
    refine le_trans ?_ hEs
    have hle : d n * (2 * ⌈(alpha n : ℝ) ^ 2⌉₊ + 2) ≤ gamma n := by
      rw [gamma_eq_ceil]; exact Nat.mul_le_mul_left _ (by omega)
    have : (2 : ℝ) ^ (d n * (2 * ⌈(alpha n : ℝ) ^ 2⌉₊ + 2)) ≤ 2 ^ gamma n :=
      pow_le_pow_right₀ (by norm_num) hle
    have h0 : (0 : ℝ) ≤ Sizes.T n * logT n := by positivity
    nlinarith
  exact SourceErr.sourceApprox_margins (fun i => opNorm_resampA_le hα1) (src_lineA_approx h)
    (fun i u hu => pre_lineA_ball h i u hu)
    (fun j => (Chirp.chirpProd_ha'_explicit (t n) (s n) (p n) j).2)
    (fun f g hf hg => (hcb f g hf hg).2) hsm hEs' hv

end MarginsG

section PhaseVG

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

set_option maxHeartbeats 1000000 in
/-- **Phase: the complex convolution.** `k .kr` holds the kernel box of `a'`, `m .out` the box
of `x₀` (grid functions at scale `2^p` of modulus at most `1`); the unary `p`, `ℓ`, `w` are on
`k (.x .pU)`, `x .lU`, `k (.x .wU)`. Afterwards `v .fo` holds the box of `cb a' x₀`,
`m .out` is empty and every other register ends as it started. -/
theorem srcV_runsG (M : SrcMach t₀ T Q) {n : ℕ}
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre : Stacks T (prime + K) → Prop}
    {w cF cO : ℕ} (cb : BoxConvOf n)
    (hBox : CvBoxRuns body M.rv M.ι Pre (cvBox M.rv M.ι M.hrv M.hι M.hT M.hQ M.hT91 M.hQrp fwdP oppP) n w cb
      (cvBoxCost T (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) cF cO))
    (hP : SrcFramed M.rg Pre)
    (a' x₀ : ((i : Fin (d n)) → ZMod (t n i)) → ℂ) (ha : ∀ y, IsFixed (p n) (a' y))
    (hx : ∀ y, IsFixed (p n) (x₀ y)) (ha1 : ‖a'‖ ≤ 1) (hx1 : ‖x₀‖ ≤ 1)
    (E : SrcF t₀ (prime + K)) (hv : SrcConvBase E.v n w)
    (hK : E.k .kr = cstream (prime + K) w (cstNumBox (p n) (t n) a'))
    (hX : E.m .out = cstream (prime + K) w (cstNumBox (p n) (t n) x₀))
    (hpU : (E.k (.x .pU)).length = p n) (hlU : (E.x .lU).length = ℓ n)
    (hwU : (E.k (.x .wU)).length = w) (htr : E.x .tr = []) (hc1 : E.x .c1 = [])
    (hc2 : E.x .c2 = []) :
    SrcRuns body M.rg M.ι Pre (srcPV M fwdP oppP) E.get
      { E with m := Function.update E.m .out [],
               v := (Function.update E.v .fo
                 (cstream (prime + K) w (cstNumBox (p n) (t n) (cb a' x₀)))) }.get
      (srcCostV T n w cF cO) := by
  have hdisj := M.hdisj
  -- the kernel copy
  have s1 := rsa_bcopy (body := body) (ι := M.ι) M.hrg (a := .k .kr) (c := .v .fi)
    (t₁ := .x .c1) (t₂ := .x .c2) (by simp) E.get hc1 hc2
  rw [SrcF.get_k, SrcF.get_v, hv.fi, List.append_nil, SrcF.upd_v] at s1
  set E₁ : SrcF t₀ (prime + K) := { E with v := Function.update E.v .fi (E.k .kr) } with hE₁
  -- the operand transfer
  have s2 := src_mv_runs (body := body) M.hrg hdisj (a := .m .out) (b := .v .gi) (sp := .x .tr)
    (by simp) (by simp) (by simp) E₁.get htr
  rw [SrcF.get_m, SrcF.get_v, SrcF.upd_m, SrcF.upd_v] at s2
  set E₂ : SrcF t₀ (prime + K) :=
    { E with m := Function.update E.m .out [],
             v := (Function.update (Function.update E.v .fi (E.k .kr)) .gi (E.m .out)) }
    with hE₂
  have hv₂ : ∀ y, y ≠ .fi → y ≠ .gi → E₂.v y = E.v y := fun y h1 h2 => by
    simp only [hE₂, Function.update_of_ne h1, Function.update_of_ne h2]
  have e₂ : ({ { E₁ with m := Function.update E₁.m .out [] } with
      v := Function.update { E₁ with m := Function.update E₁.m .out [] }.v .gi
        (E₁.m .out ++ { E₁ with m := Function.update E₁.m .out [] }.v .gi) } : SrcF t₀ _) = E₂ := by
    simp only [hE₁, hE₂, Function.update_of_ne (show CvR.gi ≠ .fi by decide), hv.gi,
      List.append_nil]
  rw [e₂] at s2
  -- the ring header
  have s3 := src_header_runs (body := body) (ι := M.ι) M.hrg (pR := .k (.x .pU)) (lR := .x .lU)
    (wR := .k (.x .wU)) (d0 := .v (.rpi 0)) (a := .v (.rr .ta)) (h := .v (.rr .tb))
    (par := .v (.rr .acc)) (cnt := .v (.rr .sv)) (t := .v (.rr .tmp)) (by simp) E₂.get
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rta])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rtb])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.racc])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rsv])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rtmp])
  simp only [SrcF.get_k, SrcF.get_x, SrcF.get_v] at s3
  rw [hv₂ _ (by decide) (by decide), hv.rpi, List.append_nil, SrcF.upd_v] at s3
  have hk₂ : E₂.k = E.k := rfl
  have hx₂ : E₂.x = E.x := rfl
  rw [hk₂, hx₂, hpU, hlU, hwU] at s3
  set H : List (Fin (prime + K + 4)) := (header (p n) (2 ^ ℓ n) w).map bitSymbol with hH
  set E₃ : SrcF t₀ (prime + K) := { E₂ with v := Function.update E₂.v (.rpi 0) H } with hE₃
  have hv₃ : ∀ y, y ≠ .fi → y ≠ .gi → y ≠ .rpi 0 → E₃.v y = E.v y := fun y h1 h2 h3 => by
    simp only [hE₃, Function.update_of_ne h3]; exact hv₂ y h1 h2
  -- the convolution stage
  have hcv := hBox a' x₀ ha hx ha1 hx1 E₃.v
    (by simp [hE₃, hE₂, hK]) (by simp [hE₃, hE₂, hX])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.tp])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.tm])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.io])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.sy])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.so])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.t1])
    (cst_ready_of_eq hv.ready fun y _ _ _ _ _ _ => hv₃ _ (by simp) (by simp) (by simp))
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.cmxsv])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.cmysv])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.cmacc])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rxs])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rout])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rsv])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rta])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rtb])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.racc])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rtmp])
    (by simp only [hE₃, Function.update_self]; rfl)
    (fun j hj => by
      rw [hv₃ _ (by simp) (by simp) (by simpa using hj), hv.rpi])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shD])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shS])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shR])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shT])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shU])
  have s4 := SrcRuns.lift M.hrg SrcR.v_inj hcv E₃.get (fun _ => rfl)
  rw [SrcF.ext_v, hv₃ _ (by decide) (by decide) (by decide), hv.fo, List.append_nil] at s4
  set Y := cstream (prime + K) w (cstNumBox (p n) (t n) (cb a' x₀)) with hY
  set E₄ : SrcF t₀ (prime + K) := { E₃ with v := Function.update E₃.v .fo Y } with hE₄
  -- the clears
  have s5 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v .fi) E₄.get
  rw [SrcF.upd_v] at s5
  have s6 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v .gi)
    { E₄ with v := Function.update E₄.v .fi [] }.get
  rw [SrcF.upd_v] at s6
  have s7 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v (.rpi 0))
    { { E₄ with v := Function.update E₄.v .fi [] } with
      v := Function.update { E₄ with v := Function.update E₄.v .fi [] }.v .gi [] }.get
  rw [SrcF.upd_v] at s7
  refine (((SrcRuns.of_rsa s1).seq hdisj hP ((SrcRuns.of_rsa s2).seq hdisj hP
    ((SrcRuns.of_rsa s3).seq hdisj hP (s4.seq hdisj hP ((SrcRuns.of_rsa s5).seq hdisj hP
    ((SrcRuns.of_rsa s6).seq hdisj hP (SrcRuns.of_rsa s7))))))).congr ?_).mono (le_of_eq ?_)
  · congr 1
    simp only [hE₄, hE₃, hE₂]
    congr 1
    funext y
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hv.fi, hv.gi, hv.fo, hv.rpi]
  · simp only [srcCostV, SrcF.get_v, hK, hE₄, hE₃, hE₂, hE₁, hX, hY, hH,
      length_cstream, cst_length_numBox, Function.update_self, List.length_map,
      Function.update_of_ne (show CvR.fi ≠ .fo by decide),
      Function.update_of_ne (show CvR.gi ≠ .fo by decide),
      Function.update_of_ne (show CvR.gi ≠ .fi by decide),
      Function.update_of_ne (show CvR.fi ≠ .gi by decide),
      Function.update_of_ne (show CvR.rpi 0 ≠ .fo by decide),
      Function.update_of_ne (show CvR.rpi 0 ≠ .fi by decide),
      Function.update_of_ne (show CvR.rpi 0 ≠ .gi by decide),
      Function.update_of_ne (show CvR.fi ≠ .rpi 0 by decide),
      Function.update_of_ne (show CvR.gi ≠ .rpi 0 by decide)]
    ring

end PhaseVG

section CoreG

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

theorem srcCore_runsG (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} (cb : BoxConvOf n) (hcb : BoxConvSpec n cb)
    (hfix : ∀ f g x, IsFixed (p n) (cb f g x))
    (hBox : CvBoxRuns body M.rv M.ι Pre (cvBox M.rv M.ι M.hrv M.hι M.hT M.hQ M.hT91 M.hQrp fwdP oppP) n w cb
      (cvBoxCost T (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) cF cO))
    (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
(hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hv : ‖v‖ ≤ 1 / 2)
    (hvf : ∀ x, IsFixed (p n) (v x))
    (hln : E.a .ln = cstream (prime + K) w (srcPad (p n) (s n) (t n) v)) :
    SrcRuns body M.rg M.ι Pre (srcCore M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               x := (Function.update E.x .sb (cstream (prime + K) w (srcPad (p n) (s n) (t n)
                 (SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
                   (chirpKernel n) cb v)) ++ E.x .sb)) }.get
      (srcCoreCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  have hd0 := srcHd0 hbig
  have hp13 := hbig.thirteen_le_p
  obtain ⟨m1, m2, m3, m4⟩ := src_marginsG hbig hsmall hEs cb hcb hv
  set a' := chirpKernel n with ha'
  set x₁ := tensorZR (d n) (s n) (t n) (lineA n) v with hx₁
  set x₀ := cstChirpProd (t n) (p n) a' x₁ with hx₀
  set y₀ := cb a' x₀ with hy₀
  set c₁ := cstChirpProd (t n) (p n) a' y₀ with hc₁
  have hc₁' : c₁ = bluesteinApproxD (p n) a' cb x₁ := rfl
  have ha1 : ‖a'‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => (src_kernel_ok n j).2
  have hfit_a : ∀ k, Fits w (numer (p n) (a' (cstCast (t n) k))) := fun k =>
    cst_fits_numer (k := 1) (by
      have := (src_kernel_ok n (cstCast (t n) k)).2; rw [pow_one]; linarith) (by omega)
  have hb := hE.k
  have hvv := hE.v
  have hm := hE.m
  have hx := hE.x
  -- phase `Ã`
  obtain ⟨hfix₁, sA⟩ := srcA_runs (body := body) M hA hbig hd0 (by omega) hwW.le hWA V₀ hE.aBase
    restA hE.aOut axsA hE.aAx v (fun x => (norm_le_pi_norm v x).trans (by linarith)) hvf E
    (by rw [hE.a_eq, hln])
  set X₁ := cstream (prime + K) w (cstNumBox (p n + 1) (t n) x₁) with hX₁
  set E₁ : SrcF t₀ (prime + K) :=
    { E with a := (rsaWith (preCfgA V₀ M.hd n w W hd0 restA (d n - 1)) X₁ axsA []).get } with hE₁
  -- the kernel
  have sK := srcK_runs (body := body) M hA n hbig.one_le_d (by omega) hwW hWs hWk E₁ hb.base hb.ax
    hb.tS hb.sS hb.tU hb.sU hb.pU hb.gU hb.wU hb.wr hb.wn hb.tbl hx.tSp hx.sSp hx.c1 hx.c2
  set KER := cstream (prime + K) w (cstNumBox (p n) (t n) a') with hKER
  rw [show E₁.k .kr = [] from hb.kr, List.append_nil] at sK
  set E₂ : SrcF t₀ (prime + K) := { E₁ with k := Function.update E₁.k .kr KER } with hE₂
  -- the first chirp product
  have sC1 := srcC1_runs (body := body) M hA (by omega) (by omega) (t n) a' x₁
    (fun k => (src_kernel_ok n _).1) hfix₁ hfit_a
    (fun k => cst_fits_numer (k := 0) (by
      have := (norm_le_pi_norm x₁ (cstCast (t n) k)).trans m1; rw [pow_zero]; linarith)
      (by omega))
    E₂ rfl (by simp [hE₂, hKER]) hm.ready hm.xs hm.ys hm.xsv hm.ysv hm.acc hm.out hx.tr hx.cA hx.cB
    hx.c1 hx.c2
  set X₀ := cstream (prime + K) w (cstNumBox (p n) (t n) x₀) with hX₀
  set E₃ : SrcF t₀ (prime + K) :=
    { E₂ with a := Function.update E₂.a .ln [], m := Function.update E₂.m .out X₀ } with hE₃
  -- the convolution
  have sV := srcV_runsG (body := body) M cb hBox hP a' x₀ (fun y => (src_kernel_ok n y).1)
    (fun y => isFixed_rhoC _ _) ha1 (m2.trans (by norm_num)) E₃ hvv (by simp [hE₃, hE₂, hKER])
    (by simp [hE₃, hX₀]) hb.pU hx.lU hb.wU hx.tr hx.c1 hx.c2
  set Y₀ := cstream (prime + K) w (cstNumBox (p n) (t n) y₀) with hY₀
  set E₄ : SrcF t₀ (prime + K) :=
    { E₃ with m := Function.update E₃.m .out [], v := Function.update E₃.v .fo Y₀ } with hE₄
  -- the second chirp product
  have sC2 := srcC2_runs (body := body) M hA (by omega) (by omega) (t n) a' y₀
    (fun k => (src_kernel_ok n _).1) (fun k => hfix _ _ _) hfit_a
    (fun k => cst_fits_numer (k := 0) (by
      have := (norm_le_pi_norm y₀ (cstCast (t n) k)).trans m3; rw [pow_zero]; linarith)
      (by omega))
    E₄ (by simp [hE₄, hY₀]) (by simp [hE₄, hE₃, hE₂, hKER]) (cst_ready_of_eq hvv.ready fun y h1 h2 h3 h4 h5 h6 =>
      by simp [hE₄, hE₃, hE₂, hE₁])
    (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmxs]) (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmys])
    (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmxsv]) (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmysv])
    (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmacc]) (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmout])
    hx.tr hx.cA hx.cB hx.c1 hx.c2
  set C₁ := cstream (prime + K) w (cstNumBox (p n) (t n) c₁) with hC₁
  set E₅ : SrcF t₀ (prime + K) :=
    { E₄ with k := Function.update E₄.k .kr [],
              v := (Function.update (Function.update E₄.v .fo []) (.cm .out) C₁) } with hE₅
  -- `B̃₀`
  obtain ⟨hfixz, sB⟩ := srcB_runs (body := body) M hA hbig hd0 hWB.1 hwW.le hWB.2 σ₀ hE.bBase
    restB hE.bOut axsB hE.bAx c₁ (fun y => isFixed_rhoC _ _)
    (fun y => (norm_le_pi_norm c₁ y).trans (m4.trans (by norm_num))) E₅ (by simp [hE₅, hE₄,
      hE₃, hE₂, hE₁, hE.b]) (by simp [hE₅, hC₁]) hx.tr
  set z := tensorZR (d n) (t n) (s n) (lineB n) c₁ with hz
  set Z := cstream (prime + K) w (srcPad (p n) (s n) (t n) z) with hZ
  set E₆ : SrcF t₀ (prime + K) :=
    { E₅ with v := Function.update E₅.v (.cm .out) [],
              b := rsbWith (bandCfgB σ₀ M.hd n w W hd0 restB (d n - 1)) Z axsB [] } with hE₆
  -- the scale
  have sG := srcG_runs (body := body) M (q := p n) (γ := gamma n) (w := w) (s n) (t n)
    (by omega) ((src_gamma_le hbig).trans (by omega)) z hfixz E₆
    (by simp only [hE₆, src_rsbWith_get_src, hZ])
    (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gS]) (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gR])
    (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gT]) (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gU])
    (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gD])
  refine ((SrcRuns.of_rsa sA).seq hdisj hP ((SrcRuns.of_rsa sK).seq hdisj hP
    ((SrcRuns.of_rsa sC1).seq hdisj hP (sV.seq hdisj hP ((SrcRuns.of_rsa sC2).seq hdisj hP
    ((SrcRuns.of_rsa sB).seq hdisj hP (SrcRuns.of_rsa sG))))))).congr ?_ |>.mono (le_of_eq ?_)
  swap
  · simp only [srcCoreCost]
    ring
  congr 1
  refine SrcF.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, RsaV.upd_ln, src_rsaWith_ln]
  · simp only [hE₆, hZ, src_rsbWith_src]
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, Function.update_idem]
    exact Function.update_eq_self_iff.2 hb.kr.symm
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, Function.update_idem]
    have e1 : Function.update E.v .fo [] = E.v := Function.update_eq_self_iff.2 hvv.fo.symm
    rw [e1]
    exact Function.update_eq_self_iff.2 hvv.cmout.symm
  · rfl
  · rfl
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, Function.update_idem]
    exact Function.update_eq_self_iff.2 hm.out.symm
  · rfl

end CoreG

section TransformsG

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

end TransformsG

section DirectG

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- **The computed source transform `F'` as a machine.** From the register file between runs
(`SrcBase`, `SrcCrtBase`) with the coefficient stream of `u` (grid values at scale `2^p`,
`‖u‖ ≤ 1/2`) on `c .str` and the box register `a .ln` empty, `srcDirectP` pushes the padded stream of
`Pipeline.srcMapG n cb u` on the source box onto `x .sb`, empties `c .str`, configures the resampling
families for axis `0` (consuming one set of records), and leaves every other register as it
began, within `srcDirectPCost` steps. -/
theorem srcDirectP_runsG (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} (cb : BoxConvOf n) (hcb : BoxConvSpec n cb)
    (hfix : ∀ f g x, IsFixed (p n) (cb f g x))
    (hBox : CvBoxRuns body M.rv M.ι Pre (cvBox M.rv M.ι M.hrv M.hι M.hT M.hQ M.hT91 M.hQrp fwdP oppP) n w cb
      (cvBoxCost T (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) cF cO))
    (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = [])
    (u : ZMod (∏ i, s n i) → ℂ) (hu : ‖u‖ ≤ 1 / 2) (huf : ∀ k, IsFixed (p n) (u k))
    (hstr : E.c .str = cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) u)) :
    SrcRuns body M.rg M.ι Pre (srcDirectP M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := Function.update E.c .str [],
               x := (Function.update E.x .sb
                 (cstream (prime + K) w (srcPad (p n) (s n) (t n) (srcMapG n cb u)) ++ E.x .sb)) }.get
      (srcDirectPCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  set v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ :=
    fun x => u ((crtPhi (s n) (s_pairwise n)).symm x) with hvdef
  have s1 := srcDirectCrtF_runs (body := body) M hA hbig (by omega) E hC u hstr
  set BOX := cstream (prime + K) w (srcPad (p n) (s n) (t n) v) with hBOX
  set E₁ : SrcF t₀ (prime + K) := { E with c := Function.update E.c .str BOX } with hE₁
  have s2 := src_mv_runs (body := body) M.hrg hdisj (a := .c .str) (b := .a .ln) (sp := .x .tr)
    (by simp) (by simp) (by simp) E₁.get (by simp [hE₁, hE.x.tr])
  rw [SrcF.get_c, SrcF.get_a, SrcF.upd_c, SrcF.upd_a] at s2
  set E₂ : SrcF t₀ (prime + K) :=
    { E with c := Function.update E.c .str [], a := Function.update E.a .ln BOX } with hE₂
  have e₂ : ({ { E₁ with c := Function.update E₁.c .str [] } with
      a := Function.update { E₁ with c := Function.update E₁.c .str [] }.a .ln
        (E₁.c .str ++ { E₁ with c := Function.update E₁.c .str [] }.a .ln) } :
      SrcF t₀ _) = E₂ := by
    simp only [hE₁, hE₂, Function.update_idem, Function.update_self, hln, List.append_nil]
  rw [e₂] at s2
  have hE₂b : SrcBase M E₂ n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB :=
    hE.of_eq (fun r hr => by simp [hE₂, Function.update_of_ne hr]) rfl rfl rfl rfl
      (fun _ _ => rfl)
  have s3 := srcCore_runsG (body := body) M hA hbig hsmall hEs cb hcb hfix hBox hP hw hwW hWA hWB
    hWs hWk E₂ hE₂b v
    ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun x => (norm_le_pi_norm u _).trans hu)
    (fun x => huf _) (by simp [hE₂, hBOX])
  refine ((SrcRuns.of_rsa s1).seq hdisj hP ((SrcRuns.of_rsa s2).seq hdisj hP s3)).congr ?_
    |>.mono (le_of_eq ?_)
  · congr 1
  · simp only [srcDirectPCost, hE₁, Function.update_self, hBOX, length_cstream, src_length_pad]
    ring

/-- **The computed opposite transform `G'` as a machine.** From the register file between runs
(`SrcBase`, `SrcCrtBase`) with the padded stream of `y` (grid values at scale `2^p`,
`‖y‖ ≤ 1/2`) on `x .sb`, the box register `a .ln` and `c .str` empty, `oppDirectP` leaves the
coefficient stream of `Pipeline.oppMapG n cb y` on `c .str`, empties `x .sb`, configures the
resampling families for axis `0`, and leaves every other register as it began, within
`oppDirectPCost` steps. -/
theorem srcDirectOpp_runsG (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} (cb : BoxConvOf n) (hcb : BoxConvSpec n cb)
    (hfix : ∀ f g x, IsFixed (p n) (cb f g x))
    (hBox : CvBoxRuns body M.rv M.ι Pre (cvBox M.rv M.ι M.hrv M.hι M.hT M.hQ M.hT91 M.hQrp fwdP oppP) n w cb
      (cvBoxCost T (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) cF cO))
    (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = []) (hstr : E.c .str = [])
    (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hy : ‖y‖ ≤ 1 / 2)
    (hyf : ∀ k, IsFixed (p n) (y k))
    (hsb : E.x .sb = cstream (prime + K) w (srcPad (p n) (s n) (t n) y)) :
    SrcRuns body M.rg M.ι Pre (oppDirectP M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := (Function.update E.c .str
                 (cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) (oppMapG n cb y)))),
               x := Function.update E.x .sb [] }.get
      (oppDirectPCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  set yc : ((i : Fin (d n)) → ZMod (s n i)) → ℂ := fun k => starRingEnd ℂ (y k) with hyc
  set SA := SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
    (chirpKernel n) cb yc with hSA
  -- the first conjugation
  have s1 := src_conj_runs (body := body) M hA (w := w) (by omega) (src := .x .sb)
    (dst := .a .ln) (by simp) (by simp) (by simp) E.get _ hsb (by simp [hE.x.cB]) hE.m.ready.wn hE.m.ready.tmp
  rw [src_pad_conj, SrcF.get_a, hln, List.append_nil, SrcF.upd_x, SrcF.upd_a, src_length_pad]
    at s1
  set E₁ : SrcF t₀ (prime + K) :=
    { E with x := Function.update E.x .sb [],
             a := Function.update E.a .ln (cstream (prime + K) w (srcPad (p n) (s n) (t n) yc)) }
    with hE₁
  have hE₁b : SrcBase M E₁ n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB :=
    hE.of_eq (fun r hr => by simp [hE₁, Function.update_of_ne hr]) rfl rfl rfl rfl
      (fun j hj => by simp [hE₁, Function.update_of_ne hj])
  -- the source transform
  have s2 := srcCore_runsG (body := body) M hA hbig hsmall hEs cb hcb hfix hBox hP hw hwW hWA hWB
    hWs hWk E₁ hE₁b yc (by rw [hyc, SourceErr.norm_conj_fun]; exact hy)
    (fun x => cst_isFixed_conj (hyf x)) (by simp [hE₁])
  set E₂ : SrcF t₀ (prime + K) :=
    { E₁ with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
              b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
              x := (Function.update E₁.x .sb (cstream (prime + K) w
                (srcPad (p n) (s n) (t n) SA) ++ E₁.x .sb)) } with hE₂
  -- the second conjugation
  have s3 := src_conj_runs (body := body) M hA (w := w) (by omega) (src := .x .sb)
    (dst := .c .str) (by simp) (by simp) (by simp) E₂.get (srcPad (p n) (s n) (t n) SA)
    (by simp [hE₂, hE₁]) (by simp [hE₂, hE₁, hE.x.cB])
    (by simpa [hE₂, hE₁] using hE.m.ready.wn) (by simpa [hE₂, hE₁] using hE.m.ready.tmp)
  rw [src_pad_conj, SrcF.get_c, SrcF.upd_x, SrcF.upd_c, src_length_pad] at s3
  set E₃ : SrcF t₀ (prime + K) :=
    { E₂ with x := Function.update E₂.x .sb [],
              c := (Function.update E.c .str (cstream (prime + K) w
                (srcPad (p n) (s n) (t n) fun k => starRingEnd ℂ (SA k)))) } with hE₃
  replace s3 := s3.congr (ρ'' := E₃.get) (by
    congr 1
    simp only [hE₃, hE₂, hE₁, hstr, List.append_nil])
  -- the inverse layout
  have s4 := srcDirectCrtI_runs (body := body) M hA hbig (w := w) (by omega) E₃ (hC.upd_str _)
    (fun k => starRingEnd ℂ (SA k)) (by simp [hE₃])
  refine ((SrcRuns.of_rsa s1).seq hdisj hP (s2.seq hdisj hP ((SrcRuns.of_rsa s3).seq hdisj hP
    (SrcRuns.of_rsa s4)))).congr ?_ |>.mono (le_of_eq ?_)
  · congr 1
    refine SrcF.ext rfl rfl rfl rfl ?_ rfl rfl ?_
    · simp only [hE₃, Function.update_idem]
      rfl
    · simp only [hE₃, hE₂, hE₁, Function.update_idem]
  · simp only [oppDirectPCost, srcConjCost]
    ring

end DirectG

end IntegerMultBounds.MathlibTM2.Fast.Src
