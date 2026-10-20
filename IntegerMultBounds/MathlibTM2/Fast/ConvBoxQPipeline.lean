module

public import IntegerMultBounds.MathlibTM2.Fast.ConvBoxQ
public import IntegerMultBounds.MathlibTM2.Mult.PipelineQ
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The complex convolution stage with computed rounds at the pipeline sizes

`cvBoxQ_boxConvSuccQ`, `cvBoxQ_boxConvQ`: `cvBox` computes `Pipeline.boxConvSuccQ`, `boxConvQ`
with the twist tables of the table machine, for transforms meeting `SynFwdSpecQ`, `SynOppSpecQ`
on records of length `2^l`. `roundPairsOf` moves the transforms' rounds onto the last axis of
the box. `cvBoxQ_convBoxQ`: the instance `convBoxQ n` at the pipeline sizes, from the margin
`hEs` (`cv_eSynthQ_lt`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.ConvSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Mult.ComplexConv
open IntegerMultBounds.Spec.SignedRingProduct


noncomputable section

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Pipeline
  IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The forward and opposite rounds of the transforms, on the last axis of the box. -/
def roundPairsOf (p : ℕ) (τ : ℝ) (l : ℕ) : (D' : ℕ) → (t : Fin D' → ℕ) → (inst : ∀ i, NeZero (t i)) →
    (∀ i : Fin D', (i : ℕ) + 1 = D' → t i = 2 ^ l) →
    RoundOp (List.ofFn (cvAx t)).sum p (fwdRound (r := 2 ^ l) (List.ofFn (cvAx t))) (etaQ p τ) →
    RoundOp (List.ofFn (cvAx t)).sum p (oppRound (r := 2 ^ l) (List.ofFn (cvAx t))) (etaQ p τ) →
    RoundPairs p τ D' t inst
  | 0, _, _, _, _, _ => ()
  | D + 1, t, inst, hlast, F, O =>
    haveI : NeZero (t (Fin.last D)) := inst _
    (castFwdOp (hlast (Fin.last D) rfl).symm F, castOppOp (hlast (Fin.last D) rfl).symm O)

section PipelineQ

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

theorem cvBoxQ_boxConvSuccQ (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {D l : ℕ} (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] (hrl : t (Fin.last D) = 2 ^ l)
    (hpow : ∀ i, t i = 2 ^ Nat.log 2 (t i)) (hdvd : ∀ i, t i ∣ 2 * t (Fin.last D))
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p cF cO : ℕ} {π : ℕ → ℕ} {τ : ℝ} (FO : RoundPairs p τ (D + 1) t inferInstance)
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w p l (boxAx t) π (castFwdOp hrl FO.1) cF)
    (hO : SynOppSpecQ body oppP (rg .io) PreO w p l (boxAx t) π (castOppOp hrl FO.2) cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM (fun i : Fin D => Nat.log 2 (t i.castSucc)),
      π n < cvM (fun i : Fin D => Nat.log 2 (t i.castSucc)))
    (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum ≤ w)
    (hE : eSynthQ (boxAx t) (cvN t) τ < 2 ^ p)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ∀ x, IsFixed p (f x))
    (hg : ∀ x, IsFixed p (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox p t f)) (hgi : ρ .gi = cstream A w (cstNumBox p t g))
    (htp : ρ .tp = tblTwistStream A w p (t (Fin.last D)) false)
    (htm : ρ .tm = tblTwistStream A w p (t (Fin.last D)) true)
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w p) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = []) (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = [])
    (hshS : (ρ .shS).length = (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum)
    (hshT : ρ .shT = []) (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo (cstream A w (cstNumBox p t (boxConvSuccQ p D t FO f g)) ++ ρ .fo))
      (cvBoxCost p l w (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum
        (cvM fun i : Fin D => Nat.log 2 (t i.castSucc)) cF cO) :=
  cvBoxQ_runs hrg hdisj hι hP hT64 hQs hT hQ hA t rfl hrl (boxAx t)
    (fun i => hpow i.castSucc) (fun i => by show 2 ^ Nat.log 2 (t i.castSucc) ∣ _; rw [← hpow i.castSucc]; exact hdvd i.castSucc) FO.1 FO.2 hF hO
    hPF hPO hπ hp hw hSw hE (twistPlus p _) (twistMinus p _) (cv_twistPlus_ok p _)
    (cv_twistMinus_ok p _) f g hf hg hf1 hg1 ρ hfi hgi (htp.trans (cv_twistPlus_stream A w p _))
    (htm.trans (cv_twistMinus_stream A w p _)) hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv
    hta htb hracc htmp hd0 hpriv hshD hshS hshR hshT hshU

theorem cvBoxQ_boxConvQ (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {D' l : ℕ} (t : Fin D' → ℕ) [inst : ∀ i, NeZero (t i)] (hD : 0 < D')
    (hlast : ∀ i : Fin D', (i : ℕ) + 1 = D' → t i = 2 ^ l)
    (hpow : ∀ i, t i = 2 ^ Nat.log 2 (t i)) (hdvd : ∀ i, t i ∣ 2 * 2 ^ l)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p cF cO : ℕ} {π : ℕ → ℕ} {τ : ℝ}
    (F : RoundOp (List.ofFn (cvAx t)).sum p (fwdRound (r := 2 ^ l) (List.ofFn (cvAx t))) (etaQ p τ))
    (O : RoundOp (List.ofFn (cvAx t)).sum p (oppRound (r := 2 ^ l) (List.ofFn (cvAx t))) (etaQ p τ))
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w p l (cvAx t) π F cF)
    (hO : SynOppSpecQ body oppP (rg .io) PreO w p l (cvAx t) π O cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM (cvAx t), π n < cvM (cvAx t)) (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn (cvAx t)).sum ≤ w) (hE : eSynthQ (cvAx t) (cvNx t) τ < 2 ^ p)
    (f g : ((i : Fin D') → ZMod (t i)) → ℂ) (hf : ∀ x, IsFixed p (f x))
    (hg : ∀ x, IsFixed p (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox p t f)) (hgi : ρ .gi = cstream A w (cstNumBox p t g))
    (htp : ρ .tp = tblTwistStream A w p (2 ^ l) false)
    (htm : ρ .tm = tblTwistStream A w p (2 ^ l) true)
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w p) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = []) (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn (cvAx t)).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn (cvAx t)).sum)
    (hshT : ρ .shT = []) (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo (cstream A w (cstNumBox p t (boxConvQ p D' t inst (roundPairsOf p τ l D' t inst hlast F O) f g)) ++ ρ .fo))
      (cvBoxCost p l w (List.ofFn (cvAx t)).sum (cvM (cvAx t)) cF cO) := by
  obtain ⟨D, rfl⟩ : ∃ D, D' = D + 1 := ⟨D' - 1, by omega⟩
  have hl : t (Fin.last D) = 2 ^ l := hlast _ rfl
  exact cvBoxQ_boxConvSuccQ hrg hdisj hι hP hT64 hQs hT hQ hA t hl hpow
    (fun i => by rw [hl]; exact hdvd i) (roundPairsOf p τ l (D + 1) t inst hlast F O)
    (by show SynFwdSpecQ _ _ _ _ _ _ _ _ _ (castFwdOp hl (castFwdOp hl.symm F)) _
        rw [castFwdOp_symm]; exact hF)
    (by show SynOppSpecQ _ _ _ _ _ _ _ _ _ (castOppOp hl (castOppOp hl.symm O)) _
        rw [castOppOp_symm]; exact hO) hPF hPO hπ hp hw hSw hE f g hf hg hf1 hg1 ρ hfi hgi
    (by rw [hl]; exact htp) (by rw [hl]; exact htm) hio hsy hso ht1 hrd hxsv hysv hacc hxs hout
    hsv hta htb hracc htmp hd0 hpriv hshD hshS hshR hshT hshU

end PipelineQ

section ConvBoxNQ

open Sizes

/-- `eSynthQ < 2^p` at the pipeline sizes, from the margin `hEs` of `convBox_spec`. -/
theorem cv_eSynthQ_lt {n : ℕ} (h : Sizes.Big n) {τ : ℝ} (hτ : 0 ≤ τ) (hτ8 : τ ≤ 1 / 8)
    (hEs : 9 * (2 : ℝ) ^ Sizes.gamma n * Sizes.T n * Sizes.logT n ≤ 2 ^ Sizes.p n / 100) :
    eSynthQ (cvAx (Sizes.t n)) (cvNx (Sizes.t n)) τ < 2 ^ Sizes.p n := by
  have hA : nRounds (cvAx (Sizes.t n)) ≤ Sizes.ℓ n :=
    Finset.sup_le fun i _ => log_t_le n _
  have hlt := eSynthQ_lt (r := Sizes.r n) (cvAx (Sizes.t n)) (cvNx (Sizes.t n)) (two_le_r h) hA
    (by have := h.two_le_ℓ; omega) (ℓ_le_logT h) hτ hτ8
  have hd := h.one_le_d
  have hT : Sizes.r n * ∏ i, cvNx (Sizes.t n) i = Sizes.T n := by
    rw [← Sizes.prod_t hd, cv_prod_last (Sizes.t n) (by omega),
      t_of_last h ⟨Sizes.d n - 1, by omega⟩ (by show Sizes.d n - 1 + 1 = Sizes.d n; omega),
      mul_comm]
  rw [hT] at hlt
  have hg4 : (16 : ℝ) ≤ 2 ^ Sizes.gamma n :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ Sizes.gamma n := pow_le_pow_right₀ (by norm_num) (four_le_gamma h)
  have hX : (0 : ℝ) ≤ (Sizes.T n : ℝ) * Sizes.logT n := by positivity
  have hp : (0 : ℝ) < 2 ^ Sizes.p n := by positivity
  nlinarith

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

theorem cvBoxQ_convBoxQ (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A) {n : ℕ} (hn : Sizes.Big n)
    (hEs : 9 * (2 : ℝ) ^ Sizes.gamma n * Sizes.T n * Sizes.logT n ≤ 2 ^ Sizes.p n / 100)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w cF cO : ℕ} {π : ℕ → ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (hτ8 : τ ≤ 1 / 8)
    (F : RoundOp (List.ofFn (cvAx (Sizes.t n))).sum (Sizes.p n)
      (fwdRound (r := 2 ^ Sizes.ℓ n) (List.ofFn (cvAx (Sizes.t n)))) (etaQ (Sizes.p n) τ))
    (O : RoundOp (List.ofFn (cvAx (Sizes.t n))).sum (Sizes.p n)
      (oppRound (r := 2 ^ Sizes.ℓ n) (List.ofFn (cvAx (Sizes.t n)))) (etaQ (Sizes.p n) τ))
    (hF : SynFwdSpecQ body fwdP (rg .io) PreF w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π F cF)
    (hO : SynOppSpecQ body oppP (rg .io) PreO w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π O cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (Sizes.t n)), π m < cvM (cvAx (Sizes.t n)))
    (hw : Sizes.p n + 2 ≤ w) (hSw : (List.ofFn (cvAx (Sizes.t n))).sum ≤ w)
    (f g : ((i : Fin (Sizes.d n)) → ZMod (Sizes.t n i)) → ℂ) (hf : ∀ x, IsFixed (Sizes.p n) (f x))
    (hg : ∀ x, IsFixed (Sizes.p n) (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) f))
    (hgi : ρ .gi = cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) g))
    (htp : ρ .tp = tblTwistStream A w (Sizes.p n) (Sizes.r n) false)
    (htm : ρ .tm = tblTwistStream A w (Sizes.p n) (Sizes.r n) true)
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w (Sizes.p n)) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = [])
    (hd0 : ρ (.rpi 0) = (header (Sizes.p n) (Sizes.r n) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn (cvAx (Sizes.t n))).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn (cvAx (Sizes.t n))).sum)
    (hshT : ρ .shT = []) (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo
        (cstream A w (cstNumBox (Sizes.p n) (Sizes.t n)
          (convBoxQ n (roundPairsOf (Sizes.p n) τ (Sizes.ℓ n) (Sizes.d n) (Sizes.t n) inferInstance
            (fun i hi => t_of_last hn i hi) F O) f g)) ++ ρ .fo))
      (cvBoxCost (Sizes.p n) (Sizes.ℓ n) w (List.ofFn (cvAx (Sizes.t n))).sum
        (cvM (cvAx (Sizes.t n))) cF cO) :=
  cvBoxQ_boxConvQ hrg hdisj hι hP hT64 hQs hT hQ hA (Sizes.t n) (by have := hn.one_le_d; omega)
    (fun i hi => t_of_last hn i hi) (t_pow_log n) (t_dvd_two_r n) F O hF hO hPF hPO hπ
    (by have := hn.thirteen_le_p; omega) hw hSw (cv_eSynthQ_lt hn hτ hτ8 hEs) f g hf hg hf1 hg1 ρ hfi hgi
    htp htm hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv hta htb hracc htmp hd0 hpriv hshD
    hshS hshR hshT hshU

end ConvBoxNQ

end

end IntegerMultBounds.MathlibTM2.Fast.ConvSt
