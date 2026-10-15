module

public import IntegerMultBounds.MathlibTM2.Cost.CompactPrepared
public import IntegerMultBounds.MathlibTM2.Node.CompactBasis

/-! Full compact basis budgets, including quadratic unary division costs in
runtime descriptor synthesis, native preparation, and both cleanup stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section

private theorem quotient_cost_le {x k B V : ℕ} (hx : x≤B) (hk : k≤m*(B+1))
    (hV : (B+1)^2≤V) : compactDescriptorQuotientCost x k ≤ 200000*V := by
  have hprod := Nat.mul_le_mul hx hk
  have hrem := Nat.mod_le x k
  unfold compactDescriptorQuotientCost synDivModCost
  norm_num [m] at hk hprod
  nlinarith

/-- Every address-linear and address-quadratic descriptor operation is charged;
the row and payload exponentials remain the actual computed values. -/
theorem compactDescriptorBankCost_le {v : Fin 16 → ℕ} {B V : ℕ}
    (hV : (B+1)^2≤V)
    (haddr : ∀ i : Fin 16, i.val ∈ [0,1,2,3,4,5,6,7,11,12] → v i≤B)
    (hrows : v 8≤V) (hr : v 9≤V) (hrw : v 9*v 10≤V)
    (hnative : 2^(v 6-v 3-v 7)*v 8≤V)
    (hpay : 2^(v 3)*(3*(v 9*v 10))≤V) :
    compactDescriptorBankCost v ≤ 2^20*V := by
  have h0 := haddr 0 (by simp); have h1 := haddr 1 (by simp)
  have h2 := haddr 2 (by simp); have h3 := haddr 3 (by simp)
  have h4 := haddr 4 (by simp); have h5 := haddr 5 (by simp)
  have h6 := haddr 6 (by simp); have h7 := haddr 7 (by simp)
  have h11 := haddr 11 (by simp); have h12 := haddr 12 (by simp)
  have hwidth := Nat.div_le_self (v 0) (m*v 1)
  have hright := Nat.div_le_self (v 2-v 3-v 4) (v 1)
  have hsub : v 2-v 3-v 4≤B := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans h2)
  have hsubn : v 6-v 3-v 7≤B := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans h6)
  have hq0 := quotient_cost_le h0 (Nat.mul_le_mul_left m (show v 1≤B+1 by omega)) hV
  have hq1 := quotient_cost_le hsub (show v 1≤m*(B+1) by norm_num [m]; omega) hV
  unfold compactDescriptorBankCost compactDescriptorStageCost compactDescriptorWidthCost
    compactDescriptorRightCost compactDescriptorLeftCost compactDescriptorRowsCost
    compactDescriptorPayloadCost synMulRCost
  norm_num only [m] at *
  nlinarith

/-- A universal exponential budget for the quadratic address work. -/
theorem compactAddressSquare_le (n : ℕ) : (n+1)^2≤8*2^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n hn hn1 =>
      rw [show n+2+1=n+1+2 by omega,show 2^(n+2)=4*2^n by ring]
      have hp : 1≤2^n := Nat.one_le_pow n 2 (by decide)
      nlinarith

/-- Each generated unary output is one of the original native descriptor values. -/
theorem compactComputedValues_le {s : Shape} (d : Inputs s) (input : Fin 16 → ℕ)
    (hin : compactDescriptorBankOriginals input =
      ActivePrefixStageHeadersData.originalValues d.stage d.rows) :
    ∀ i, compactDescriptorBankValues input i≤d.rows*s.recordWidth := by
  intro i
  have h := compactOriginalValues_le d (![7,9,8,4,5,6,11,12] i)
  rw [←hin] at h
  fin_cases i <;> simpa [compactDescriptorBankOriginals] using h

/-- Actual synthesis inputs are bounded by the full live address, while folded
rows and coefficient products are paid by the literal local array volume. -/
theorem compactDescriptorBank_actual_le {s : Shape} {n a₀ k ρ left right o R r w : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hR : 0<R)
    (hrecord : s.bits+1≤s.payload) (hpayload : s.payload=2^o*(3*(r*w))) :
    compactDescriptorBankCost (compactDescriptorBankInputs layout o R r w x y) ≤
      2^23*((2^(n-s.bits)*R)*s.recordWidth) := by
  let d := compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord
  let V := d.rows*s.recordWidth
  have hVp : 0<V := by
    have hp : 0<s.payload := by omega
    dsimp [V,Shape.recordWidth]
    exact Nat.mul_pos d.hr (by positivity)
  have hvol : V=(R*2^(o+n))*(3*(r*w)) := by
    change (2^(n-s.bits)*R)*s.recordWidth=_
    rw [compactSlotComputed_volume layout R,hpayload]
    simp only [pow_add]
    ring
  have hrw : 0<r*w := by
    by_contra h
    have hz : r*w=0 := by omega
    rw [hvol,hz] at hVp
    simp at hVp
  have hw : 0<w := by nlinarith
  have hr : 0<r := by nlinarith
  have hpow : 1≤2^(o+n) := Nat.one_le_pow _ _ (by decide)
  have hstock : 1≤R*2^(o+n) := Nat.mul_pos hR (by positivity)
  have hpowV : 2^(o+n)≤V := by
    rw [hvol]
    have h1 := Nat.le_mul_of_pos_left (2^(o+n)) hR
    exact h1.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hrows : R≤V := by
    rw [hvol]
    exact (Nat.le_mul_of_pos_right _ (by positivity)).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  have hrwV : r*w≤V := by
    rw [hvol]
    exact (show r*w≤3*(r*w) by omega).trans (Nat.le_mul_of_pos_left _ hstock)
  have hrV : r≤V := (Nat.le_mul_of_pos_right _ hw).trans hrwV
  have hsquare : (o+n+1)^2≤8*V :=
    (compactAddressSquare_le (o+n)).trans (Nat.mul_le_mul_left 8 hpowV)
  have ha := layout.live_fit
  have hk := layout.positiveWidth
  have hK : 0<s.chunk := by have := layout.selectedFits; omega
  have hL : s.chunk*(m*k)≤n := by nlinarith only [ha]
  have hchunk : s.chunk≤n := by
    have hh := Nat.le_mul_of_pos_right s.chunk (Nat.mul_pos (by decide : 0<m) hk)
    exact hh.trans hL
  have hm : m≤n := by
    have hh : 1≤s.chunk*k := Nat.mul_pos hK hk
    nlinarith only [ha,hh]
  have hactive : s.active≤n := by
    have hh := Nat.le_mul_of_pos_right s.active hK
    have hbits := layout.totalFits
    unfold Shape.bits at hbits
    omega
  have hb : s.H+s.B≤n := by have := layout.lowReserve; omega
  have haddr : ∀ i : Fin 16,i.val ∈ [0,1,2,3,4,5,6,7,11,12] →
      compactDescriptorBankInputs layout o R r w x y i≤o+n := by
    intro i hi
    have hx := x.isLt; have hy := y.isLt; have hbits := layout.totalFits
    fin_cases i <;> simp_all [compactDescriptorBankInputs] <;> omega
  have horig : compactDescriptorBankOriginals (compactDescriptorBankInputs layout o R r w x y)=
      ActivePrefixStageHeadersData.originalValues d.stage d.rows :=
    compactDescriptorBank_originals layout o R r w x y hxy hpayload
  have hout := compactComputedValues_le d _ horig
  have hnative := hout 3
  have hpay := hout 4
  change 2^((o+n)-o-s.bits)*R≤V at hnative
  change 2^o*(3*(r*w))≤V at hpay
  have hv := compactDescriptorBankCost_le hsquare haddr
    (show R≤8*V by omega) (show r≤8*V by omega) (show r*w≤8*V by omega)
    (show 2^((o+n)-o-s.bits)*R≤8*V from hnative.trans (by omega))
    (show 2^o*(3*(r*w))≤8*V from hpay.trans (by omega))
  change _≤2^23*V
  exact hv.trans_eq (by ring)

def compactBasisSlotConst (T D : ℕ) : ℝ := 2^(compactSlotXorExponent T D+34)

theorem compactBasisSlotConst_le (T D : ℕ) :
    compactPreparedConst T D+2^24≤compactBasisSlotConst T D := by
  have h : (1:ℝ)≤2^compactSlotXorExponent T D := one_le_pow₀ (by norm_num)
  unfold compactPreparedConst compactBasisSlotConst
  rw [pow_add,pow_add]
  norm_num
  nlinarith

/-- The complete slot budget includes seeds, computed descriptors, native
headers, native execution, and both unary and binary cleanup. -/
theorem compactBasisSlotCost_le {s : Shape} {n a₀ k ρ left right o R r w : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hR : 0<R)
    (hrecord : s.bits+1≤s.payload) (hpayload : s.payload=2^o*(3*(r*w)))
    (T K D : ℕ)
    (hp : 1<k → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord) D) :
    (compactBasisSlotCost T K D
      (compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord) hp
      (compactDescriptorBankInputs layout o R r w x y) (s.chunk*k)
      (R*2^(o+n)*r*w) x y : ℝ) ≤
      compactBasisSlotConst T D*((2^(n-s.bits)*R)*s.recordWidth : ℕ)*
        ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  let d := compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord
  let input := compactDescriptorBankInputs layout o R r w x y
  let V := d.rows*s.recordWidth
  have hV : 1≤V := by
    have hpay : 0<s.payload := by omega
    exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
  have hpay : s.payload≤V := by
    exact (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0<2) _)).trans
      (Nat.le_mul_of_pos_left _ d.hr)
  have hmk : m*(s.chunk*k)≤s.bits := by
    have hh := layout.active
    unfold Shape.bits
    nlinarith only [hh]
  have hmkV : m*(s.chunk*k)≤V := hmk.trans ((by omega : s.bits≤s.payload).trans hpay)
  have hK : 0<s.chunk := by have := layout.selectedFits; omega
  have hL : s.chunk*k≤V :=
    (Nat.le_mul_of_pos_left _ (by decide : 0<m)).trans hmkV
  have hm : m≤V :=
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK layout.positiveWidth)).trans hmkV
  have hx : x.val≤V := x.isLt.le.trans hm
  have hy : y.val≤V := y.isLt.le.trans hm
  have hseed : (4*(s.chunk*k)+6)+
      ((2*(m*(s.chunk*k))+2)+(2*x.val+2)+(2*y.val+2)+1)≤23*V := by omega
  have hsynth : compactDescriptorBankCost input≤2^23*V :=
    compactDescriptorBank_actual_le layout x y hxy hG hGK hR hrecord hpayload
  have horig : compactDescriptorBankOriginals input=
      ActivePrefixStageHeadersData.originalValues d.stage d.rows :=
    compactDescriptorBank_originals layout o R r w x y hxy hpayload
  have hout := compactComputedValues_le d input horig
  have hclear : (∑ i : Fin 8,(2*compactDescriptorBankValues input i+2))+1≤33*V := by
    have hh : (∑ i : Fin 8,(2*compactDescriptorBankValues input i+2))≤∑ _i : Fin 8,4*V := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hout i
      omega
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    omega
  have hlength : R*2^(o+n)*r*w≤V := by
    have hv : V=3*(R*2^(o+n)*r*w) := by
      change (2^(n-s.bits)*R)*s.recordWidth=_
      rw [compactSlotComputed_volume layout R,hpayload]
      simp only [pow_add]
      ring
    omega
  have hprepared := compactSlotPreparedCost_le T K D d hp _ hlength
  have hover : (compactBasisSlotCost T K D d hp input (s.chunk*k)
      (R*2^(o+n)*r*w) x y : ℝ) ≤
      (compactSlotPreparedCost T K D d hp (R*2^(o+n)*r*w) : ℝ)+(2:ℝ)^24*V := by
    have hn : compactBasisSlotCost T K D d hp input (s.chunk*k)
        (R*2^(o+n)*r*w) x y ≤
        compactSlotPreparedCost T K D d hp (R*2^(o+n)*r*w)+2^24*V := by
      unfold compactBasisSlotCost compactSlotComputedCost
      omega
    exact_mod_cast hn
  have he : (1:ℝ)≤((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((k-1)*s.guard))
      (by norm_num [Parameters.tau])
  have hm := mul_le_mul_of_nonneg_left he (show (0:ℝ)≤2^24*(V:ℝ) by positivity)
  have hc := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (compactBasisSlotConst_le T D) (Nat.cast_nonneg V))
    (show (0:ℝ)≤((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau by positivity)
  change _≤compactBasisSlotConst T D*(V:ℝ)*_
  change _≤compactPreparedConst T D*(V:ℝ)*
    ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau at hprepared
  nlinarith only [hover,hprepared,hm,hc]

def compactBasisConst (T D : ℕ) : ℝ := 2^(compactSlotXorExponent T D+49)

theorem compactBasisConst_le (T D : ℕ) :
    (m:ℝ)*compactBasisSlotConst T D+1≤compactBasisConst T D := by
  have h : (1:ℝ)≤compactBasisSlotConst T D := one_le_pow₀ (by norm_num)
  have he : compactBasisConst T D=compactBasisSlotConst T D*2^15 := by
    unfold compactBasisConst compactBasisSlotConst
    rw [←pow_add]
  rw [he]
  norm_num [m]
  nlinarith

private theorem list_cost_le {α : Type} (f : α → ℕ) (C : ℝ) (l : List α)
    (h : ∀ y∈l,(f y:ℝ)≤C) : ((l.map f).sum:ℝ)≤l.length*C := by
  induction l with
  | nil => simp
  | cons y l ih =>
      have hy := h y (by simp)
      have hl := ih (fun z hz => h z (by simp [hz]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith

/-- The entire concrete basis target list retains the local compact-width
bound; the final terminating instruction is included in the power-of-two coefficient. -/
theorem compactBasisCost_le {s : Shape} {n a₀ k ρ left right o R r w : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hR : 0<R)
    (hrecord : s.bits+1≤s.payload) (hpayload : s.payload=2^o*(3*(r*w)))
    (T K D : ℕ)
    (hp : ∀ y (hxy : x≠y),1<k → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord) D)
    (vv : BinaryWalsh.Address m) :
    ((((basisTargets vv x).map
      (compactBasisTargetCost layout x hG hGK hR hrecord D hp T K o r w)).sum+1 : ℕ):ℝ) ≤
      compactBasisConst T D*((2^(n-s.bits)*R)*s.recordWidth : ℕ)*
        ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  let V := (2^(n-s.bits)*R)*s.recordWidth
  let E : ℝ := ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau
  have hV : 1≤V := by
    have hpay : 0<s.payload := by omega
    change 0<(2^(n-s.bits)*R)*(2^s.bits*s.payload)
    positivity
  have hE : 1≤E := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 ((k-1)*s.guard)) (by norm_num [Parameters.tau])
  have hslot : 0≤compactBasisSlotConst T D := by unfold compactBasisSlotConst; positivity
  have hs := list_cost_le (compactBasisTargetCost layout x hG hGK hR hrecord D hp T K o r w)
    (compactBasisSlotConst T D*(V:ℝ)*E) (basisTargets vv x) (by
      intro y hy
      have hxy : x≠y := (mem_basisTargets.mp hy).2.symm
      simpa only [compactBasisTargetCost,dite_eq_left hxy] using
        compactBasisSlotCost_le layout x y hxy hG hGK hR hrecord hpayload T K D (hp y hxy))
  have hlen : (basisTargets vv x).length≤m := by
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := m))
  have hlenR : ((basisTargets vv x).length:ℝ)≤m := by exact_mod_cast hlen
  have hs' := hs.trans (mul_le_mul_of_nonneg_right hlenR
    (show 0≤compactBasisSlotConst T D*(V:ℝ)*E by positivity))
  have hVR : (1:ℝ)≤V := by exact_mod_cast hV
  have hone : (1:ℝ)≤(V:ℝ)*E := by nlinarith only [hVR,hE]
  have hc := mul_le_mul_of_nonneg_right (compactBasisConst_le T D)
    (show 0≤(V:ℝ)*E by positivity)
  change _≤compactBasisConst T D*(V:ℝ)*E
  simp only [Nat.cast_add,Nat.cast_one]
  nlinarith only [hs',hone,hc]

end
end IntegerMultBounds.MathlibTM2.Cost
