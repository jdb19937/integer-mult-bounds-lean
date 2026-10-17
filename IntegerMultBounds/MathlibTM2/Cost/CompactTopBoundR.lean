module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopActualBoundR
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlPower
import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopRowControlBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The control work of the rounded top: the exact top's stages plus the guard, the cut, `k`
shrinks by one and the final shift by `2^(s - s')`. Each new stage is linear in the padded
working volume, so the controls cost a fixed coefficient times the volume and the record count
(`compactTopControlCostR_volume`), and any positive dimension power (`_power`). With the rounded
pieces (`compactTopCallCostR_reserved_sum`) and the kernel this gives `compactTopCostR_complete`,
the bound of `compactTopCost_complete`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

/-! ### The new stages -/

theorem compactTopGuardSCost_linear (cfg : List ℕ) (R N r w' g : ℕ) (hw' : 1 ≤ w') (hg : g ≤ w') :
    compactTopGuardSCost cfg R N r w' g ≤ topGetCost cfg + 24*(R*2^N*(r*w')) + 12*w' + 18 := by
  have hcoeff : R*2^N*r ≤ R*2^N*r*w' := Nat.le_mul_of_pos_right _ hw'
  have hgv := Nat.mul_le_mul_left (R*2^N*r) hg
  have he : R*2^N*(r*w') = R*2^N*r*w' := by ring
  have hsub : w' - g ≤ w' := Nat.sub_le _ _
  unfold compactTopGuardSCost
  nlinarith only [hcoeff, hgv, he, hsub, hg, Nat.zero_le (R*2^N*r*w')]

theorem compactTopCutSCost_linear (cfg : List ℕ) (R N r w' s' : ℕ) (hw' : 1 ≤ w') (hs : s' ≤ w') :
    compactTopCutSCost cfg R N r w' s' ≤ topGetCost cfg + 64*(R*2^N*(r*w')) + 32*w' + 40 := by
  have hc := compactTopShiftWordCost_linear w' s' (w'-s') (by omega)
  have hcoeff : R*2^N*r ≤ R*2^N*r*w' := Nat.le_mul_of_pos_right _ hw'
  have hmul := Nat.mul_le_mul_left (R*2^N*r) hc
  have hsub : w' - s' ≤ w' := Nat.sub_le _ _
  have hvol := Nat.mul_le_mul_left (R*2^N*r) hsub
  have hsv := Nat.mul_le_mul_left (R*2^N*r) hs
  have he : R*2^N*(r*w') = R*2^N*r*w' := by ring
  have hz' : w' - (w' - s') = s' := by omega
  unfold compactTopCutSCost topShiftCost topWidenCost
  rw [hz']
  nlinarith only [hmul, hcoeff, hvol, hsv, he, hsub, hs, Nat.zero_le (R*2^N*r*w')]

theorem compactTopShrinkSCost_linear (cfg : List ℕ) (R N r w' k : ℕ) (hw' : 1 ≤ w') :
    compactTopShrinkSCost cfg R N r w' k ≤ topGetCost cfg + 64*k*(R*2^N*(r*w')) + 14*k + 6 := by
  have hcoeff : R*2^N*r ≤ R*2^N*r*w' := Nat.le_mul_of_pos_right _ hw'
  have he : R*2^N*(r*w') = R*2^N*r*w' := by ring
  have hsh : shrinkCost R N r w' + 3 ≤ 64 * (R*2^N*(r*w')) + 10 := by
    unfold shrinkCost shrWordCost
    nlinarith only [hcoeff, he, Nat.zero_le (R*2^N*r*w')]
  have hk := Nat.mul_le_mul_left k hsh
  unfold compactTopShrinkSCost
  nlinarith only [hk, Nat.zero_le (k*(R*2^N*(r*w')))]

theorem compactTopShiftSRCost_linear (cfg : List ℕ) (R N r w' s s' w : ℕ) (hw' : 1 ≤ w')
    (hsw : (s - s') + w ≤ w') (hs' : s' ≤ w') :
    compactTopShiftSRCost cfg R N r w' s s' w ≤
      3*topGetCost cfg + 64*(R*2^N*(r*w')) + 22*w' + 30 := by
  have hc := compactTopShiftWordCost_linear w' (s-s') w hsw
  have hcoeff : R*2^N*r ≤ R*2^N*r*w' := Nat.le_mul_of_pos_right _ hw'
  have hmul := Nat.mul_le_mul_left (R*2^N*r) hc
  have hw : w ≤ w' := by omega
  have hvol := Nat.mul_le_mul_left (R*2^N*r) hw
  have hsub : w'-(s-s')-w ≤ w' := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  unfold compactTopShiftSRCost compactTopShiftTailCost topShiftCost
  nlinarith only [hmul,hcoeff,hvol,hsw,hsub,hs',Nat.zero_le (R*2^N*r*w')]

/-! ### The piece records with the rounded piece conditions -/

private theorem bits_indices {u : ℕ} (hu : 1≤u) (j : ℕ) : u≤bits u j ∧ j≤bits u j := by
  induction j with
  | zero => simp [bits]
  | succ j ih =>
    have hb := bits_pos hu j
    have hm := Nat.mul_le_mul_right (bits u j) one_lt_m
    simp only [bits]
    constructor <;> nlinarith only [ih.1,ih.2,hb,hm]

theorem compactTopPcR_header_bounds {K n R₂ : ℕ} {pc : TopPc} (hK : 1≤K) (h : pc.OkR K n R₂) :
    pc.j≤n ∧ pc.u≤n ∧ pc.a₀≤n ∧ K*bits pc.u pc.j≤n := by
  have hb : bits pc.u pc.j≤n :=
    (Nat.le_mul_of_pos_left _ hK).trans (by have := h.hfit; omega)
  have hi := bits_indices h.hu pc.j
  exact ⟨hi.2.trans hb,hi.1.trans hb,by have := h.hfit; omega,by have := h.hfit; omega⟩

theorem compactTopPcCostR_control (cfg : List ℕ) {K n R₂ : ℕ} {pc : TopPc}
    (hK : 1≤K) (h : pc.OkR K n R₂) :
    compactTopPcCost cfg K pc 0 ≤ topGetCost cfg+16*n+2*R₂+23 := by
  obtain ⟨hj,hu,ha,hwidth⟩ := compactTopPcR_header_bounds hK h
  have hrow := h.hR
  unfold compactTopPcCost
  omega

theorem compactTopPcsCostR_control (cfg : List ℕ) {K n R₂ : ℕ} (pcs : List TopPc) (hK : 1≤K)
    (h : ∀ pc∈pcs,pc.OkR K n R₂) :
    compactTopPcsCost cfg K (fun _ => 0) pcs ≤
      pcs.length*(topGetCost cfg+16*n+2*R₂+24)+1 := by
  induction pcs with
  | nil => simp [compactTopPcsCost]
  | cons pc pcs ih =>
    have hc := compactTopPcCostR_control cfg hK (h pc (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [compactTopPcsCost,List.length_cons]
    nlinarith only [hc,ht]

theorem compactTopPcRecLenR_control {K n R₂ : ℕ} (pcs : List TopPc) (hK : 1≤K)
    (h : ∀ pc∈pcs,pc.OkR K n R₂) :
    topRecLen (topPcRec K pcs) ≤ pcs.length*(4*n+4) := by
  induction pcs with
  | nil => simp [topPcRec,topRecLen]
  | cons pc pcs ih =>
    obtain ⟨hj,hu,ha,hwidth⟩ := compactTopPcR_header_bounds hK (h pc (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    have he : topRecLen (topPcRec K (pc::pcs)) =
        pc.j+pc.u+pc.a₀+K*bits pc.u pc.j+4+topRecLen (topPcRec K pcs) := by
      simp [topPcRec,topPcFields,topRecLen]
      omega
    rw [he,List.length_cons]
    nlinarith only [hj,hu,ha,hwidth,ht]

theorem compactTopBlockCostR_control (cfg : List ℕ) (K n a r w R R₂ : ℕ) (pcs : List TopPc)
    (hK : 1≤K) (hr : 1≤r) (hw : 1≤w) (hR : 1≤R)
    (hcap : 2^a*R≤R₂) (hpcs : ∀ pc∈pcs,pc.OkR K n R₂) :
    compactTopBlockCost cfg K n a r w R R₂ (fun _ => 0) pcs ≤
      512*(R₂*(2^n*r*w))+8*topGetCost cfg+
        pcs.length*(topGetCost cfg+32*n+2*R₂+32)+4 := by
  have hrw : 1≤r*w := Nat.mul_le_mul hr hw
  have hL : 1≤2^n*r*w := Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow n 2 (by decide)) hr) hw
  have hpow : 2^a≤R₂ := (Nat.le_mul_of_pos_right _ hR).trans hcap
  have hsmall : 2^(n+a)*(r*w)≤R₂*(2^n*r*w) := by
    have hm := Nat.mul_le_mul_right (2^n*(r*w)) hpow
    rw [pow_add]
    nlinarith only [hm]
  have hinput : R*2^a*2^n*r*w≤R₂*(2^n*r*w) := by
    have hm := Nat.mul_le_mul_right (2^n*r*w) hcap
    nlinarith only [hm]
  have hfull : R₂*2^n*r*w≤R₂*(2^n*r*w) := by simp only [Nat.mul_assoc,le_refl]
  have hdown := compactTopDownCost_linear cfg n a r w hrw
  have hup := compactTopUpCost_linear cfg n a r w hrw
  have hpad := compactTopPadCost_linear cfg a R R₂ (2^n*r*w)
    (R*2^a*2^n*r*w) hR hL hcap hinput
  have hunpad := compactTopUnpadCost_linear cfg a R R₂ (2^n*r*w)
    (R₂*2^n*r*w) hR hL hcap hfull
  have hdispatch := compactTopPcsCostR_control cfg pcs hK hpcs
  have hrecord := compactTopPcRecLenR_control pcs hK hpcs
  unfold compactTopBlockCost
  nlinarith only [hdown,hup,hpad,hunpad,hdispatch,hrecord,hsmall,
    Nat.zero_le (R₂*(2^n*r*w)),Nat.zero_le (topGetCost cfg),Nat.zero_le (pcs.length*n)]

/-! ### The controls of the rounded top -/

/-- The rounded top without its recursive calls and its kernel. -/
def compactTopControlCostR (w w' s n a R r K ρ q aT oS D R₂ g s' k : ℕ) (pcs : List TopPc) : ℕ :=
  compactTopCostR w w' s n a R r K ρ q aT oS D R₂ g s' k pcs 0 (fun _ => 0)

theorem compactTopCostR_split (w w' s n a R r K ρ q aT oS D R₂ g s' k kc : ℕ) (pcs : List TopPc)
    (cc : TopPc→ℕ) :
    compactTopCostR w w' s n a R r K ρ q aT oS D R₂ g s' k pcs kc cc =
      compactTopControlCostR w w' s n a R r K ρ q aT oS D R₂ g s' k pcs+kc+(pcs.map cc).sum := by
  unfold compactTopControlCostR compactTopCostR compactTopBlockCost compactTopKerSCost
  rw [compactTopPcsCost_split]
  omega

private theorem cfgRCost_le (w s a R R₂ q aT K o D g s' k V : ℕ)
    (hV : 1≤V) (hw : w≤V) (hs : s≤V) (ha : a≤V) (hR : R≤V) (hR₂ : R₂≤V)
    (hq : q≤V) (haT : aT≤V) (hKq : K*q≤V) (ho : o≤V) (hD : D≤V) (hg : g≤V) (hs' : s'≤V)
    (hk : k≤V) :
    topGetCost (topCfgR w s a R R₂ q aT K o D g s' k) ≤256*V := by
  simp only [topGetCost,topRecLen,topCfgR,topCfg,List.cons_append,List.nil_append,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- **The controls of the rounded top** cost a fixed coefficient times the padded volume and the
record count, plus `k` shrink passes. -/
theorem compactTopControlCostR_volume
    (w w' s n a R r K ρ q aT o D R₂ g s' k : ℕ) (pcs : List TopPc)
    (hR : 1≤R) (hr : 1≤r) (hw' : 1≤w') (hK : 1≤K)
    (hsw : s+w≤w') (hgw : g≤w') (hs'w : s'≤w') (hssw : (s - s')+w≤w') (hk : k≤w')
    (hN : n+a≤r*w') (hρo : ρ+o≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a)
    (hcap : 2^a*R≤R₂) (hpcs : ∀ pc∈pcs,pc.OkR K n R₂) :
    compactTopControlCostR w w' s n a R r K ρ q aT o D R₂ g s' k pcs ≤
      16384*(pcs.length+k+1)*(R₂*(2^n*r*w')) := by
  let V := R₂*(2^n*r*w')
  let cfg := topCfgR w s a R R₂ q aT K o D g s' k
  have hR₂pos : 1≤R₂ := (Nat.mul_le_mul (Nat.one_le_pow a 2 (by decide)) hR).trans hcap
  have hL : 1≤2^n*r*w' := Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow n 2 (by decide)) hr) hw'
  have hV : 1≤V := Nat.mul_le_mul hR₂pos hL
  have hR₂V : R₂≤V := Nat.le_mul_of_pos_right _ hL
  have hRV : R≤V := (Nat.le_mul_of_pos_left _ (Nat.one_le_pow a 2 (by decide))).trans (hcap.trans hR₂V)
  have hrwV : r*w'≤V := by
    have hs : 1≤R₂*2^n := Nat.mul_le_mul hR₂pos (Nat.one_le_pow n 2 (by decide))
    have hh := Nat.le_mul_of_pos_left (r*w') hs
    dsimp only [V]
    nlinarith only [hh]
  have hwV : w'≤V := (Nat.le_mul_of_pos_left w' hr).trans hrwV
  have hNV : n+a≤V := hN.trans hrwV
  have hD : D≤V := ((Nat.le_mul_of_pos_right D hK).trans hDK).trans hNV
  have hq : q≤V := (Nat.le_mul_of_pos_left q hK).trans (by omega)
  have hw'V := hwV
  have hget : topGetCost cfg≤256*V := cfgRCost_le _ _ _ _ _ _ _ _ _ _ _ _ _ V hV
    (((Nat.le_add_left w s).trans hsw).trans hw'V) (((Nat.le_add_right s w).trans hsw).trans hw'V)
    ((Nat.le_add_left a n).trans hNV) hRV hR₂V hq
    ((((Nat.le_add_right aT (K*q)).trans hker)).trans hNV)
    ((((Nat.le_add_left (K*q) aT).trans hker)).trans hNV)
    (((Nat.le_add_left o ρ).trans hρo).trans hNV) hD
    (hgw.trans hw'V) (hs'w.trans hw'V) (hk.trans hw'V)
  -- the stages
  have hL' : 1≤2^(n+a)*r*w' := Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ 2 (by decide)) hr) hw'
  have hsource : R*2^(n+a)*(r*w')≤V := by
    have hm := Nat.mul_le_mul_right (2^n*(r*w')) hcap
    dsimp only [V]
    rw [pow_add]
    nlinarith only [hm]
  have hww : w≤w' := by omega
  have hwiden := compactTopWidenSCost_linear cfg R (n+a) r w w' hw' hww
  have hphase := compactTopPhaseSCost_linear cfg (n+a) R r w' K ρ o D hR
    (Nat.mul_le_mul hr hw') hN hρo hDK ((Nat.le_mul_of_pos_right D hK).trans hDK)
  have hguard := compactTopGuardSCost_linear cfg R (n+a) r w' g hw' hgw
  have hunit := compactTopUnitSCost_linear cfg R (n+a) r w' D hw'
  have hcut := compactTopCutSCost_linear cfg R (n+a) r w' s' hw' hs'w
  have hshrink := compactTopShrinkSCost_linear cfg R (n+a) r w' k hw'
  have hshift := compactTopShiftSRCost_linear cfg R (n+a) r w' s s' w hw' hssw hs'w
  have hblock := compactTopBlockCostR_control cfg K n a r w' R R₂ pcs hK hr hw' hR hcap hpcs
  have hkernel : compactTopKerSCost cfg K R q aT 0 ≤ 4*topGetCost cfg+24*V := by
    unfold compactTopKerSCost
    nlinarith only [hq,hker,hNV,hRV,hV]
  have hheaders : topGetCost cfg+32*n+2*R₂+32≤512*V := by
    have : n ≤ V := (Nat.le_add_right n a).trans hNV
    omega
  have hlist := Nat.mul_le_mul_left pcs.length hheaders
  have hkV : k*(R*2^(n+a)*(r*w'))≤k*V := Nat.mul_le_mul_left _ hsource
  have hdef : compactTopControlCostR w w' s n a R r K ρ q aT o D R₂ g s' k pcs =
      compactTopWidenSCost cfg R (n+a) r w w' + compactTopPhaseSCost cfg (n+a) R r w' K ρ o D +
      compactTopGuardSCost cfg R (n+a) r w' g + compactTopKerSCost cfg K R q aT 0 +
      compactTopBlockCost cfg K n a r w' R R₂ (fun _ => 0) pcs +
      compactTopPhaseSCost cfg (n+a) R r w' K ρ o D + compactTopUnitSCost cfg R (n+a) r w' D +
      compactTopCutSCost cfg R (n+a) r w' s' + compactTopShrinkSCost cfg R (n+a) r w' k +
      compactTopShiftSRCost cfg R (n+a) r w' s s' w := rfl
  rw [hdef]
  have hk' : k ≤ V := hk.trans hwV
  have hD' : D ≤ V := hD
  have hexp : 16384*(pcs.length+k+1)*V = 16384*(pcs.length*V)+16384*(k*V)+16384*V := by ring
  have hlist' : pcs.length*(topGetCost cfg+32*n+2*R₂+32) ≤ 512*(pcs.length*V) := by
    calc _ ≤ pcs.length*(512*V) := hlist
      _ = 512*(pcs.length*V) := by ring
  have hkV' : 64*k*(R*2^(n+a)*(r*w')) ≤ 64*(k*V) := by
    calc 64*k*(R*2^(n+a)*(r*w')) = 64*(k*(R*2^(n+a)*(r*w'))) := by ring
      _ ≤ 64*(k*V) := Nat.mul_le_mul_left _ hkV
  rw [hexp]
  generalize pcs.length*V = LV at *
  generalize k*V = KV at *
  omega

/-- The controls of the rounded top with at most one shrink pass, against any positive dimension
power. -/
theorem compactTopControlCostR_power (d g K D o R₂ w w' s n a R r ρ q aT gb s' k : ℕ)
    (hd : 1≤d) (hD : D≤d) {lam : ℝ} (hlam : 0<lam) (hk1 : k≤1)
    (hR : 1≤R) (hr : 1≤r) (hw' : 1≤w') (hK : 1≤K)
    (hsw : s+w≤w') (hgw : gb≤w') (hs'w : s'≤w') (hssw : (s - s')+w≤w')
    (hN : n+a≤r*w') (hρo : ρ+o≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a) (hcap : 2^a*R≤R₂)
    (hpcs : ∀ pc∈compactTopPcs d g K D o R₂,pc.OkR K n R₂) :
    (compactTopControlCostR w w' s n a R r K ρ q aT o D R₂ gb s' k (compactTopPcs d g K D o R₂):ℝ) ≤
      (32768*compactTopCountConst lam)*((R₂*(2^n*r*w'):ℕ):ℝ)*(d:ℝ)^lam := by
  let pcs := compactTopPcs d g K D o R₂
  let V := R₂*(2^n*r*w')
  have hn := compactTopControlCostR_volume w w' s n a R r K ρ q aT o D R₂ gb s' k pcs
    hR hr hw' hK hsw hgw hs'w hssw (by omega) hN hρo hDK hker hcap hpcs
  have hk2 : pcs.length+k+1 ≤ 2*(pcs.length+1) := by omega
  have hn2 : compactTopControlCostR w w' s n a R r K ρ q aT o D R₂ gb s' k pcs ≤
      32768*(pcs.length+1)*V := by
    have := Nat.mul_le_mul_right V (Nat.mul_le_mul_left 16384 hk2)
    calc _ ≤ 16384*(pcs.length+k+1)*V := hn
      _ ≤ 16384*(2*(pcs.length+1))*V := this
      _ = 32768*(pcs.length+1)*V := by ring
  have hnat : (compactTopControlCostR w w' s n a R r K ρ q aT o D R₂ gb s' k pcs:ℝ) ≤
      32768*((pcs.length+1:ℕ):ℝ)*(V:ℝ) := by exact_mod_cast hn2
  have hcount := compactTopPcs_length_power d g K D o R₂ hd hD hlam
  have hscale := mul_le_mul_of_nonneg_left hcount (show (0:ℝ)≤32768*(V:ℝ) by positivity)
  calc
    (compactTopControlCostR w w' s n a R r K ρ q aT o D R₂ gb s' k pcs:ℝ)
        ≤32768*((pcs.length+1:ℕ):ℝ)*(V:ℝ) := hnat
    _ = (32768*(V:ℝ))*((pcs.length+1:ℕ):ℝ) := by ring
    _ ≤ (32768*(V:ℝ))*(compactTopCountConst lam*(d:ℝ)^lam) := hscale
    _ = (32768*compactTopCountConst lam)*(V:ℝ)*(d:ℝ)^lam := by ring

/-! ### The complete rounded top -/

/-- **The rounded top's cost**: controls, the rounded reserved pieces and the widened kernel,
with the right-hand side of `compactTopCost_complete` (control coefficient doubled). -/
theorem compactTopCostR_complete (ds : ComplexFramedExecution.Directions)
    (shape : CompactGadgetReservationShape.Shape)
    (packD d g K D oS R₂ W w shift n a R r ρ o q aT gb s' k : ℕ)
    {lam : ℝ} (hd : 1≤d) (hD : D≤d) (hactive : compactReservationActive d g K D≠0)
    (hK : K=shape.chunk) (hKpos : 1≤K)
    (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<shape.chunk)
    (hG : 1≤shape.guard) (hn : o≤n) (hoS : o≤oS)
    (hbits : shape.bits≤n-o) (hpayload : shape.payload=2^o*(3*(r*w)))
    (hsw : shift+W≤w) (hgw : gb≤w) (hs'w : s'≤w) (hssw : (shift - s')+W≤w) (hk1 : k≤1)
    (hN : n+a≤r*w) (hρo : ρ+oS≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a) (hqa : o≤aT) (hq : 1≤q)
    (hcap : 2^a*R≤R₂) (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hpcsR : ∀ pc∈compactTopPcs d g K D oS R₂,pc.OkR K n R₂)
    (hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,TopPcOkS ds K n w R₂ pc)
    (hbase : ∀ pc∈compactTopPcs d g K D oS R₂,o≤pc.a₀) :
    (compactTopCostR W w shift n a R r K ρ q aT oS D R₂ gb s' k
      (compactTopPcs d g K D oS R₂)
      (compactTopCallCostR ds shape packD (n+a) o r w ρ ⟨0,q,R,aT⟩)
      (compactTopCallCostR ds shape packD n o r w ρ):ℝ) ≤
    ((R₂*2^n*(r*w):ℕ):ℝ)*
      (32768*compactTopCountConst lam*(d:ℝ)^lam+
       512*(backChunks d g K:ℝ)+512*(q:ℝ)+
       compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) packD ds lam) m lam*
         (compactReservationActive d g K D:ℝ)^lam*(shape.guard:ℝ)^Parameters.tau) := by
  have hc := compactTopControlCostR_power d g K D oS R₂ W w shift n a R r ρ q aT gb s' k
    hd hD hl hk1 hR hr hw hKpos hsw hgw hs'w hssw hN hρo hDK hker hcap hpcsR
  have hpcshape : ∀ pc∈compactTopPcs d g K D oS R₂,TopPcOkS ds shape.chunk n w R₂ pc := by
    simpa only [hK] using hpcs
  have hs := compactTopCallCostR_reserved_sum ds packD K 0
    (compactReservationActive d g K D) oS (oS+K*backChunks d g K) (backChunks d g K)
    (CompactGlobalRowPadding.depth m d) R₂ n o r w ρ shape hactive hr hw hρ hG hn
    (by omega) hbits hpayload (by omega) hl htl hal hpcshape hbase
  have hk := compactTopCallCostR_kernel ds packD shape (n+a) o r w ρ q R aT
    hq hR hr hw hρ (by omega) hqa (by simpa only [hK] using hker) hN
  have hvol : R*2^(n+a)*(r*w)≤R₂*2^n*(r*w) := by
    calc
      R*2^(n+a)*(r*w) = (2^a*R)*(2^n*(r*w)) := by rw [pow_add]; ring
      _ ≤ R₂*(2^n*(r*w)) := Nat.mul_le_mul_right _ hcap
      _ = _ := by ring
  have hk' := hk.trans (Nat.mul_le_mul_left (512*q) hvol)
  have hkR : (compactTopCallCostR ds shape packD (n+a) o r w ρ ⟨0,q,R,aT⟩:ℝ)≤
      512*(q:ℝ)*((R₂*2^n*(r*w):ℕ):ℝ) := by exact_mod_cast hk'
  have hv : R₂*(2^n*r*w)=R₂*2^n*(r*w) := by ring
  rw [hv] at hc
  change (((compactTopPcs d g K D oS R₂).map
    (compactTopCallCostR ds shape packD n o r w ρ)).sum:ℝ)≤_ at hs
  rw [compactTopCostR_split,Nat.cast_add,Nat.cast_add]
  nlinarith only [hc,hs,hkR]

end
end IntegerMultBounds.MathlibTM2.Cost
