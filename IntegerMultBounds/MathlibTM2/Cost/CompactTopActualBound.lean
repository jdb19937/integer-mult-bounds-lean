module
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopBound
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section
/-- Canonical actual compact layer cost attached to a piece record. -/
def compactPieceCost (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ : ℕ) (pc : TopPc) : ℕ :=
  compactLayerCost ds pc.u s.chunk ρ pc.R₀ n o r w
    (compactLayerBasisBudget (nT CompactBReg) D s pc.u pc.R₀ n) pc.j pc.a₀

/-- Explicit bridge from the absolute serialized call to the relative cost below. -/
theorem compactTopCallCost_eq_piece (ds : ComplexFramedExecution.Directions)
    (D : ℕ) (s : CompactGadgetReservationShape.Shape) (n o r w ρ : ℕ) (pc : TopPc) :
    compactTopCallCost ds s D n o r w ρ pc =
      compactPieceCost ds D s (n-o) o r w ρ {pc with a₀:=pc.a₀-o} := rfl

private theorem compactList_sum_mono {α : Type} (xs : List α) (f g : α→ℝ)
    (h : ∀ x∈xs,f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem compactList_scale_sum {α : Type} (xs : List α) (f g : α→ℝ)
    (V B : ℝ) (hV : 0≤V) (hp : ∀ x∈xs,f x≤V*g x)
    (hs : (xs.map g).sum≤B) : (xs.map f).sum≤V*B := by
  calc
    _ ≤ (xs.map (fun x => V*g x)).sum := compactList_sum_mono xs f _ hp
    _ = V*(xs.map g).sum := List.sum_map_mul_left xs g V
    _ ≤ V*B := mul_le_mul_of_nonneg_left hs hV

/-- Numerical budget with an abstract host-size coefficient. -/
def compactPieceCostWith (T : ℕ) (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ : ℕ) (pc : TopPc) : ℕ :=
  compactLayerCost ds pc.u s.chunk ρ pc.R₀ n o r w
    (compactLayerBasisBudget T D s pc.u pc.R₀ n) pc.j pc.a₀

theorem compactLayerCost_closed_with (ds : ComplexFramedExecution.Directions)
    (T D : ℕ) (s : CompactGadgetReservationShape.Shape) (u R₀ n o r w : ℕ) {ρ : ℕ} {lam : ℝ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hτl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (j : ℕ) (hTw : ∀ i<j,expZ u ds i≤w) (a : ℕ)
    (hfit : (o+a)+s.chunk*bits u j≤o+n) :
    (compactLayerCost ds u s.chunk ρ R₀ n o r w
      (compactLayerBasisBudget T D s u R₀ n) j a:ℝ) ≤
      ((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst T D ds lam*((m:ℝ)^j*u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^j*u) := by
  have hM := compactLayerCost_majorant ds (compactLayerBasisBudget T D s u R₀ n)
    (compactLayerBasisBound T D s u R₀ n)
    hu hr hw hR₀ hρ (fun _ _ _ _ => le_rfl) j hTw a hfit
  have hclosed := compactLayerNormalized_closed ds T D s u R₀ n o r w
    hu hR₀ hr hw hG hbits hpayload hN hτl hal j
  have hV : (0:ℝ)<((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j)
      (pow_pos (by decide : 0<2) _)) (Nat.mul_pos hr hw)
  have hh := (div_le_iff₀ hV).mp hclosed
  exact (Nat.cast_le.mpr hM).trans (by simpa only [mul_comm] using hh)

/-- Pointwise closed bound with symbolic row metadata. -/
theorem compactPieceCostWith_closed (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D R n o r w ρ : ℕ) (s : CompactGadgetReservationShape.Shape) (pc : TopPc)
    {lam : ℝ} (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hbits : s.bits≤n) (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : pc.Ok ds s.chunk n w R) :
    (compactPieceCostWith T ds D s n o r w ρ pc:ℝ) ≤
      ((R*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst T D ds lam*((m:ℝ)^pc.j*pc.u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^pc.j*pc.u) := by
  have hfit : (o+pc.a₀)+s.chunk*bits pc.u pc.j≤o+n := by
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hok.hfit o
  have hc := compactLayerCost_closed_with ds T D s pc.u pc.R₀ n o r w
    hok.hu hok.hR₀ hr hw hρ hG hbits hpayload hN htl hal pc.j hok.hTw pc.a₀ hfit
  change (compactPieceCostWith T ds D s n o r w ρ pc:ℝ)≤_ at hc
  have heq := congrArg (fun rows : ℕ => ((rows*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst T D ds lam*((m:ℝ)^pc.j*pc.u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^pc.j*pc.u)) hok.hR.symm
  exact hc.trans_eq heq

/-- Sum of the actual canonical recursive costs over the rebased active pieces.
All pieces use the same padded stock; no execution or cost bound is assumed. -/
theorem compactActiveCost_sum_with (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D K X active oS J R n o r w ρ : ℕ) (s : CompactGadgetReservationShape.Shape)
    {lam : ℝ} (hactive : active≠0) (hK : K=s.chunk)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hbits : s.bits≤n) (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : ∀ pc∈(synPcs K X active oS J active).map (compactRebasePc R),
      pc.Ok ds s.chunk n w R) :
    ((((synPcs K X active oS J active).map (compactRebasePc R)).map
      (compactPieceCostWith T ds D s n o r w ρ)).sum:ℝ) ≤
      ((R*2^(o+n)*(r*w):ℕ):ℝ)*
        (compactDigitSumConst (compactLayerClosedConst T D ds lam) m lam*
          (active:ℝ)^lam*(s.guard:ℝ)^Parameters.tau) := by
  let C := compactLayerClosedConst T D ds lam
  let V : ℝ := ((R*2^(o+n)*(r*w):ℕ):ℝ)
  let f := fun pc : TopPc => C*((m:ℝ)^pc.j*pc.u)^lam*(s.guard:ℝ)^Parameters.tau+
    C*((factorCount (program ds):ℝ)/NW)^pc.j*pc.u
  have hper : ∀ pc∈synPcs K X active oS J active,
      (compactPieceCostWith T ds D s n o r w ρ (compactRebasePc R pc):ℝ)≤V*f pc := by
    intro pc hp
    have hokpc := hok _ (List.mem_map.mpr ⟨pc,hp,rfl⟩)
    cases pc with
    | mk j u R₀ a =>
      exact compactPieceCostWith_closed T ds D R n o r w ρ s ⟨j,u,R/NW^j,a⟩
        hr hw hρ hG hbits hpayload hN htl hal hokpc
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def]
  have hp := compactList_sum_mono (synPcs K X active oS J active) _ _ hper
  have hs := compactSynPcs_envelope_sum K X active oS J (a:=((factorCount (program ds):ℝ)/NW)) (lam:=lam)
    (tau:=Parameters.tau) (C:=C) (g:=(s.guard:ℝ)) hactive
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hl
    (by norm_num [Parameters.tau]) hal (compactLayerDyadic_pos _).le
    (by exact_mod_cast hG)
  have hdist : ((synPcs K X active oS J active).map (fun pc => V*f pc)).sum =
      V*((synPcs K X active oS J active).map f).sum :=
    List.sum_map_mul_left (synPcs K X active oS J active) f V
  with_reducible
    have hp2 := hp.trans_eq hdist
    have hV : (0:ℝ)≤V := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hs hV
    exact hp2.trans hh

/-- Back-reservation and top-kernel leaves are linear in their reserved axes. -/
theorem compactPieceCost_leaf_with (T : ℕ) (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ u R a : ℕ)
    (hu : 1≤u) (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hfit : a+s.chunk*u≤n) (hN : o+n≤r*w) :
    compactPieceCostWith T ds D s n o r w ρ ⟨0,u,R,a⟩ ≤
      512*u*(R*2^(o+n)*(r*w)) := by
  have hc := lc_leaf_nat 0 ds (n:=o+n) (a₀:=o+a) hu hr hw hR hρ
    (by simpa only [Nat.add_assoc] using Nat.add_le_add_left hfit o)
  have hn := Nat.mul_le_mul_left (R*2^(o+n)) hN
  change leafCost u s.chunk ρ (o+a) R (o+n) r w+4≤_ at hc ⊢
  nlinarith only [hc,hn,Nat.mul_le_mul_left (200*u) hn]


/-- Actual back leaf plus all active digits, with their different charges explicit. -/
theorem compactReservedCost_sum_with (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D K X active oS activeOffset B J R n o r w ρ : ℕ)
    (s : CompactGadgetReservationShape.Shape) {lam : ℝ}
    (hactive : active≠0) (hK : K=s.chunk)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hbits : s.bits≤n) (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : ∀ pc∈(compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R),
      pc.Ok ds s.chunk n w R) :
    ((((compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R)).map
      (compactPieceCostWith T ds D s n o r w ρ)).sum:ℝ) ≤
      ((R*2^(o+n)*(r*w):ℕ):ℝ)*
        (512*(B:ℝ)+compactDigitSumConst (compactLayerClosedConst T D ds lam) m lam*
          (active:ℝ)^lam*(s.guard:ℝ)^Parameters.tau) := by
  have hact : ∀ pc∈(synPcs K X active activeOffset J active).map (compactRebasePc R),
      pc.Ok ds s.chunk n w R := by
    intro pc hp
    apply hok pc
    simp only [compactReservedPcs,List.map_append,List.mem_append]
    exact Or.inr hp
  have hsum := compactActiveCost_sum_with T ds D K X active activeOffset J R n o r w ρ s
    hactive hK hr hw hρ hG hbits hpayload hN hl htl hal hact
  by_cases hb : B=0
  · simpa [compactReservedPcs,hb] using hsum
  · have hback : (⟨0,B,R,oS⟩ : TopPc).Ok ds s.chunk n w R := by
      apply hok
      simp [compactReservedPcs,hb,compactRebasePc]
    have hleaf := compactPieceCost_leaf_with T ds D s n o r w ρ B R oS
      (by omega) hback.hR₀ hr hw hρ hback.hfit hN
    have hleafR : (compactPieceCostWith T ds D s n o r w ρ ⟨0,B,R,oS⟩:ℝ) ≤
        512*(B:ℝ)*((R*2^(o+n)*(r*w):ℕ):ℝ) := by exact_mod_cast hleaf
    simp only [compactReservedPcs,hb,↓reduceIte,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,Nat.cast_add]
    simp only [compactRebasePc,pow_zero,Nat.div_one,Nat.cast_zero,add_zero] at *
    nlinarith only [hsum,hleafR]

/-- Canonical host specialization; no scalar proof unfolds its finite register type. -/
abbrev compactActiveCost_sum := compactActiveCost_sum_with (nT CompactBReg)
abbrev compactPieceCost_leaf := compactPieceCost_leaf_with (nT CompactBReg)
abbrev compactReservedCost_sum := compactReservedCost_sum_with (nT CompactBReg)

end
end IntegerMultBounds.MathlibTM2.Cost
