module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLayerNormalized
public import IntegerMultBounds.MathlibTM2.Layer.Recurrence
public import IntegerMultBounds.MathlibTM2.Cost.BranchingMoment
public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Closed bounds for the actual compact layer with its current level-zero
stopping regime. The width factor is guard^tau; the leaf contribution remains
explicit. Every exposed cost coefficient is a fixed power of two. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationShape (Shape)
noncomputable section

theorem compactLayerExistsDyadic (x : ℝ) : ∃ e : ℕ,x≤(2:ℝ)^e := by
  obtain ⟨e,_,he⟩ := exists_nat_pow_near (show (1:ℝ)≤|x|+1 by linarith only [abs_nonneg x])
    (show (1:ℝ)<2 by norm_num)
  exact ⟨e+1,(le_abs_self x).trans (by linarith only [he.le])⟩

def compactLayerDyadicExponent (x : ℝ) : ℕ := Classical.choose (compactLayerExistsDyadic x)
def compactLayerDyadic (x : ℝ) : ℝ := 2^compactLayerDyadicExponent x

theorem compactLayerDyadic_le (x : ℝ) : x≤compactLayerDyadic x :=
  Classical.choose_spec (compactLayerExistsDyadic x)

theorem compactLayerDyadic_pos (x : ℝ) : 0<compactLayerDyadic x := by
  unfold compactLayerDyadic
  positivity

def compactLayerStepConst (T D : ℕ) (ds : ComplexFramedExecution.Directions) : ℝ :=
  compactLayerDyadic (6*((lcBas ds:ℝ)/NW)*compactBasisConst T D+
    2*((lcBas ds:ℝ)/NW)+2*(lcLin ds:ℝ))

private theorem step_absorption {q q' a a' b L C E X inv ratio S : ℝ}
    (ha' : 0≤a') (hL : 0≤L) (hC : 0≤C) (hX : 0≤X)
    (hq : q'=a*q+2*a'*b+L*(1+ratio))
    (hb : b≤3*C*E+inv) (hE : E≤X) (hi : inv≤1) (hr : ratio≤1)
    (hS : 6*a'*C+2*a'+2*L≤S) : q'≤a*q+S*(X+1) := by
  have hb' := mul_le_mul_of_nonneg_left hb (show 0≤2*a' by positivity)
  have he := mul_le_mul_of_nonneg_left hE (show 0≤6*a'*C by positivity)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤2*a' by positivity)
  have hr' := mul_le_mul_of_nonneg_left hr hL
  have hs := mul_le_mul_of_nonneg_right hS (show 0≤X+1 by positivity)
  have hx := mul_nonneg (show 0≤2*a'+2*L by positivity) hX
  have hac : 0≤6*a'*C := by positivity
  nlinarith only [hq,hb',he,hi',hr',hs,hx,hac]

/-- The full normalized recurrence has guard times selected width, with all
setup, control, rounding-up, and address-ratio costs absorbed. -/
theorem compactLayerNormalized_step (ds : ComplexFramedExecution.Directions)
    (T D : ℕ) (s : Shape) (u R₀ n o r w : ℕ)
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w) (j : ℕ) :
    compactLayerNormalized ds u R₀ (o+n) r w (compactLayerBasisBound T D s u R₀ n) (j+1) ≤
      ((factorCount (program ds):ℝ)/NW)*
        compactLayerNormalized ds u R₀ (o+n) r w (compactLayerBasisBound T D s u R₀ n) j+
      compactLayerStepConst T D ds*(((s.guard:ℝ)*(m:ℝ)^j*u)^Parameters.tau+1) := by
  have hV : 1≤rowsAt R₀ j*2^(o+n)*(r*w) :=
    Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j) (pow_pos (by decide) _)) (Nat.mul_pos hr hw)
  have hVR : (0:ℝ)<((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by exact_mod_cast hV
  have hVR1 : (1:ℝ)≤((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by exact_mod_cast hV
  have hinv : 1/((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ)≤1 :=
    (div_le_one hVR).mpr hVR1
  have hp : (0:ℝ)<((r*w:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hr hw
  have hratio : (o+n:ℕ)/((r*w:ℕ):ℝ)≤1 :=
    (div_le_one hp).mpr (by exact_mod_cast hN)
  have hwidth : max 1 ((bits u j-1)*s.guard)≤s.guard*bits u j := by
    apply max_le
    · exact Nat.mul_pos hG (bits_pos hu j)
    · have h := Nat.mul_le_mul_right s.guard (Nat.sub_le (bits u j) 1)
      simpa only [Nat.mul_comm] using h
  have hwidthR : ((max 1 ((bits u j-1)*s.guard):ℕ):ℝ)≤(s.guard:ℝ)*(m:ℝ)^j*u := by
    have h : ((max 1 ((bits u j-1)*s.guard):ℕ):ℝ)≤((s.guard*bits u j:ℕ):ℝ) := by exact_mod_cast hwidth
    simpa only [lc_bits_eq,Nat.cast_mul,Nat.cast_pow,mul_assoc] using h
  have hE := Real.rpow_le_rpow (Nat.cast_nonneg _) hwidthR
    (show 0≤Parameters.tau by norm_num [Parameters.tau])
  exact step_absorption
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    (by unfold compactBasisConst; positivity) (Real.rpow_nonneg (by positivity) _)
    (by simpa only [mul_div_assoc] using (compactLayerNormalized_succ ds u R₀ (o+n) r w
      (compactLayerBasisBound T D s u R₀ n) j hR₀ hr hw))
    (compactLayerBasisBound_ratio T D s u R₀ n o r w j hbits hpayload hR₀ hr hw)
    hE hinv hratio (compactLayerDyadic_le _)

def compactLayerClosedConst (T D : ℕ) (ds : ComplexFramedExecution.Directions) (lam : ℝ) : ℝ :=
  compactLayerDyadic (Recurrence.recConst ((factorCount (program ds):ℝ)/NW) m lam 512
    (compactLayerStepConst T D ds))

/-- Closed no-stopping bound. The internal term uses guard^tau, while the
existing level-zero leaf contributes the separate branching-power term. -/
theorem compactLayerNormalized_closed (ds : ComplexFramedExecution.Directions)
    (T D : ℕ) (s : Shape) (u R₀ n o r w : ℕ) {lam : ℝ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hτl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam) (j : ℕ) :
    compactLayerNormalized ds u R₀ (o+n) r w (compactLayerBasisBound T D s u R₀ n) j ≤
      compactLayerClosedConst T D ds lam*((m:ℝ)^j*u)^lam*(s.guard:ℝ)^Parameters.tau+
      compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^j*u := by
  have ha : (0:ℝ)≤(factorCount (program ds):ℝ)/NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hm : (1:ℝ)<m := by norm_num [m]
  have hτ : 0≤Parameters.tau := by norm_num [Parameters.tau]
  have hg : (1:ℝ)≤s.guard := by exact_mod_cast hG
  have huR : (1:ℝ)≤u := by exact_mod_cast hu
  have hC : 0≤compactLayerStepConst T D ds := (compactLayerDyadic_pos _).le
  have hzero : compactLayerNormalized ds u R₀ (o+n) r w
      (compactLayerBasisBound T D s u R₀ n) 0≤512*(u:ℝ) := by
    rw [compactLayerNormalized_zero ds u R₀ (o+n) r w _ hR₀ hr hw]
    have hp : (0:ℝ)<((r*w:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hr hw
    have hratio : (o+n:ℕ)/((r*w:ℕ):ℝ)≤1 :=
      (div_le_one hp).mpr (by exact_mod_cast hN)
    have hh := mul_le_mul_of_nonneg_left hratio (show (0:ℝ)≤200*(u:ℝ) by positivity)
    nlinarith only [hh,huR]
  have hclosed := Recurrence.recurrence_closed ha hm hτ hτl hal hg (by norm_num : (0:ℝ)≤512)
    hC huR hzero (compactLayerNormalized_step ds T D s u R₀ n o r w hu hR₀ hr hw hG hbits hpayload hN) j
  have hc := compactLayerDyadic_le (Recurrence.recConst ((factorCount (program ds):ℝ)/NW) m lam 512
    (compactLayerStepConst T D ds))
  have hi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (show (0:ℝ)≤(m:ℝ)^j*u by positivity) lam))
    (Real.rpow_nonneg (Nat.cast_nonneg s.guard) Parameters.tau)
  have hl := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (pow_nonneg ha j)) (Nat.cast_nonneg u)
  exact hclosed.trans (add_le_add hi hl)

/-- Closed bound on the actual recursive program's numerical cost with the
canonical concrete basis budget. No recursion execution assumption is supplied. -/
theorem compactLayerCost_closed (ds : ComplexFramedExecution.Directions)
    (D : ℕ) (s : Shape) (u R₀ n o r w : ℕ) {ρ : ℕ} {lam : ℝ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hτl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (j : ℕ) (hTw : ∀ i<j,expZ u ds i≤w) (a : ℕ)
    (hfit : (o+a)+s.chunk*bits u j≤o+n) :
    (compactLayerCost ds u s.chunk ρ R₀ n o r w
      (compactLayerBasisBudget (nT CompactBReg) D s u R₀ n) j a:ℝ) ≤
      ((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst (nT CompactBReg) D ds lam*((m:ℝ)^j*u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst (nT CompactBReg) D ds lam*((factorCount (program ds):ℝ)/NW)^j*u) := by
  have hM := compactLayerCost_compact_majorant ds D hu hr hw hR₀ hρ j hTw a hfit
  have hclosed := compactLayerNormalized_closed ds (nT CompactBReg) D s u R₀ n o r w
    hu hR₀ hr hw hG hbits hpayload hN hτl hal j
  have hV : (0:ℝ)<((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j)
      (pow_pos (by decide : 0<2) _)) (Nat.mul_pos hr hw)
  have hh := (div_le_iff₀ hV).mp hclosed
  exact (Nat.cast_le.mpr hM).trans (by simpa only [mul_comm] using hh)

/-- Closed bound from an occurrence-moment hypothesis on the layer node in place of
`log_m (F/NW) < λ`. -/
theorem compactLayerCost_closed_moment (ds : ComplexFramedExecution.Directions)
    (D : ℕ) (s : Shape) (u R₀ n o r w : ℕ) {ρ : ℕ} {lam : ℝ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hτl : Parameters.tau≤lam) (hmom : layerMoment ds lam<1)
    (j : ℕ) (hTw : ∀ i<j,expZ u ds i≤w) (a : ℕ)
    (hfit : (o+a)+s.chunk*bits u j≤o+n) :
    (compactLayerCost ds u s.chunk ρ R₀ n o r w
      (compactLayerBasisBudget (nT CompactBReg) D s u R₀ n) j a:ℝ) ≤
      ((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst (nT CompactBReg) D ds lam*((m:ℝ)^j*u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst (nT CompactBReg) D ds lam*((factorCount (program ds):ℝ)/NW)^j*u) :=
  compactLayerCost_closed ds D s u R₀ n o r w hu hR₀ hr hw hρ hG hbits hpayload hN hτl
    (logb_lt_of_layerMoment ds
      (lt_of_lt_of_le (by norm_num [Parameters.tau]) hτl) hmom) j hTw a hfit

/-- The checked branching network permits the manuscript's sigma/tau gap, through the h=25
instance of the layer occurrence moment. -/
theorem compactLayer_br_logb :
    Real.logb (m:ℝ) ((factorCount (program brDirs):ℝ)/NW)<CompactInterim.lam :=
  br_logb_lt_999.trans (by norm_num [CompactInterim.lam])

end
end IntegerMultBounds.MathlibTM2.Cost
