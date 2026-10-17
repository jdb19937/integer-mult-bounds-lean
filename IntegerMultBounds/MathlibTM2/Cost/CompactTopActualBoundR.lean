module
import IntegerMultBounds.MathlibTM2.Cost.CompactLayerR
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecutionR
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopCoordinates
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The rounded pieces of the top cost the closed layer bound of the exact pieces. A rounded
piece needs its geometry (`OkS`: the fields of `TopPc.OkR`) and child scales below the width
in place of the compounding `expZ`, and its recursive cost is `compactLayerCostR`. The sum over
the reserved pieces and the top kernel have the bounds of `compactTopCallCost_reserved_sum` and
`compactTopCallCost_kernel`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

/-- The conditions of a rounded piece for its cost: geometry and child scales below `w`. -/
structure TopPcOkS (ds : ComplexFramedExecution.Directions) (K n w R₂ : ℕ) (pc : TopPc) :
    Prop where
  hu : 1 ≤ pc.u
  hR₀ : 1 ≤ pc.R₀
  hR : R₂ = rowsAt pc.R₀ pc.j
  hs : ∀ i < pc.j, expSeq (gateCount (program ds)) 0 pc.u i ≤ w
  hfit : pc.a₀ + K * bits pc.u pc.j ≤ n

/-- Canonical rounded layer cost attached to a piece record. -/
def compactPieceCostWithR (T : ℕ) (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ : ℕ) (pc : TopPc) : ℕ :=
  compactLayerCostR ds pc.u s.chunk ρ pc.R₀ n o r w
    (compactLayerBasisBudget T D s pc.u pc.R₀ n) pc.j pc.a₀

private theorem listSumMono {α : Type} (xs : List α) (f g : α→ℝ)
    (h : ∀ x∈xs,f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem compactLayerCostR_closed_with (ds : ComplexFramedExecution.Directions)
    (T D : ℕ) (s : CompactGadgetReservationShape.Shape) (u R₀ n o r w : ℕ) {ρ : ℕ} {lam : ℝ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hτl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (j : ℕ) (hs : ∀ i<j,expSeq (gateCount (program ds)) 0 u i≤w) (a : ℕ)
    (hfit : (o+a)+s.chunk*bits u j≤o+n) :
    (compactLayerCostR ds u s.chunk ρ R₀ n o r w
      (compactLayerBasisBudget T D s u R₀ n) j a:ℝ) ≤
      ((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst T D ds lam*((m:ℝ)^j*u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^j*u) := by
  have hM := compactLayerCostR_majorant ds (compactLayerBasisBudget T D s u R₀ n)
    (compactLayerBasisBound T D s u R₀ n)
    hu hr hw hR₀ hρ (fun _ _ _ _ => le_rfl) j hs a hfit
  have hclosed := compactLayerNormalized_closed ds T D s u R₀ n o r w
    hu hR₀ hr hw hG hbits hpayload hN hτl hal j
  have hV : (0:ℝ)<((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j)
      (pow_pos (by decide : 0<2) _)) (Nat.mul_pos hr hw)
  have hh := (div_le_iff₀ hV).mp hclosed
  exact (Nat.cast_le.mpr hM).trans (by simpa only [mul_comm] using hh)

theorem compactPieceCostWithR_closed (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D R n o r w ρ : ℕ) (s : CompactGadgetReservationShape.Shape) (pc : TopPc)
    {lam : ℝ} (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hbits : s.bits≤n) (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : TopPcOkS ds s.chunk n w R pc) :
    (compactPieceCostWithR T ds D s n o r w ρ pc:ℝ) ≤
      ((R*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst T D ds lam*((m:ℝ)^pc.j*pc.u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^pc.j*pc.u) := by
  have hfit : (o+pc.a₀)+s.chunk*bits pc.u pc.j≤o+n := by
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hok.hfit o
  have hc := compactLayerCostR_closed_with ds T D s pc.u pc.R₀ n o r w
    hok.hu hok.hR₀ hr hw hρ hG hbits hpayload hN htl hal pc.j hok.hs pc.a₀ hfit
  change (compactPieceCostWithR T ds D s n o r w ρ pc:ℝ)≤_ at hc
  have heq := congrArg (fun rows : ℕ => ((rows*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst T D ds lam*((m:ℝ)^pc.j*pc.u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst T D ds lam*((factorCount (program ds):ℝ)/NW)^pc.j*pc.u)) hok.hR.symm
  exact hc.trans_eq heq

theorem compactActiveCostR_sum_with (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D K X active oS J R n o r w ρ : ℕ) (s : CompactGadgetReservationShape.Shape)
    {lam : ℝ} (hactive : active≠0)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hbits : s.bits≤n) (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : ∀ pc∈(synPcs K X active oS J active).map (compactRebasePc R),
      TopPcOkS ds s.chunk n w R pc) :
    ((((synPcs K X active oS J active).map (compactRebasePc R)).map
      (compactPieceCostWithR T ds D s n o r w ρ)).sum:ℝ) ≤
      ((R*2^(o+n)*(r*w):ℕ):ℝ)*
        (compactDigitSumConst (compactLayerClosedConst T D ds lam) m lam*
          (active:ℝ)^lam*(s.guard:ℝ)^Parameters.tau) := by
  let C := compactLayerClosedConst T D ds lam
  let V : ℝ := ((R*2^(o+n)*(r*w):ℕ):ℝ)
  let f := fun pc : TopPc => C*((m:ℝ)^pc.j*pc.u)^lam*(s.guard:ℝ)^Parameters.tau+
    C*((factorCount (program ds):ℝ)/NW)^pc.j*pc.u
  have hper : ∀ pc∈synPcs K X active oS J active,
      (compactPieceCostWithR T ds D s n o r w ρ (compactRebasePc R pc):ℝ)≤V*f pc := by
    intro pc hp
    have hokpc := hok _ (List.mem_map.mpr ⟨pc,hp,rfl⟩)
    cases pc with
    | mk j u R₀ a =>
      exact compactPieceCostWithR_closed T ds D R n o r w ρ s ⟨j,u,R/NW^j,a⟩
        hr hw hρ hG hbits hpayload hN htl hal hokpc
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def]
  have hp := listSumMono (synPcs K X active oS J active) _ _ hper
  have hs := compactSynPcs_envelope_sum K X active oS J (a:=((factorCount (program ds):ℝ)/NW))
    (lam:=lam) (tau:=Parameters.tau) (C:=C) (g:=(s.guard:ℝ)) hactive
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

theorem compactPieceCostR_leaf_with (T : ℕ) (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ u R a : ℕ)
    (hu : 1≤u) (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hfit : a+s.chunk*u≤n) (hN : o+n≤r*w) :
    compactPieceCostWithR T ds D s n o r w ρ ⟨0,u,R,a⟩ ≤
      512*u*(R*2^(o+n)*(r*w)) := by
  have hc := lc_leaf_nat 0 ds (n:=o+n) (a₀:=o+a) hu hr hw hR hρ
    (by simpa only [Nat.add_assoc] using Nat.add_le_add_left hfit o)
  have hn := Nat.mul_le_mul_left (R*2^(o+n)) hN
  change leafCost u s.chunk ρ (o+a) R (o+n) r w+4≤_ at hc ⊢
  nlinarith only [hc,hn,Nat.mul_le_mul_left (200*u) hn]

theorem compactReservedCostR_sum_with (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D K X active oS activeOffset B J R n o r w ρ : ℕ)
    (s : CompactGadgetReservationShape.Shape) {lam : ℝ}
    (hactive : active≠0)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hbits : s.bits≤n) (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : ∀ pc∈(compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R),
      TopPcOkS ds s.chunk n w R pc) :
    ((((compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R)).map
      (compactPieceCostWithR T ds D s n o r w ρ)).sum:ℝ) ≤
      ((R*2^(o+n)*(r*w):ℕ):ℝ)*
        (512*(B:ℝ)+compactDigitSumConst (compactLayerClosedConst T D ds lam) m lam*
          (active:ℝ)^lam*(s.guard:ℝ)^Parameters.tau) := by
  have hact : ∀ pc∈(synPcs K X active activeOffset J active).map (compactRebasePc R),
      TopPcOkS ds s.chunk n w R pc := by
    intro pc hp
    apply hok pc
    simp only [compactReservedPcs,List.map_append,List.mem_append]
    exact Or.inr hp
  have hsum := compactActiveCostR_sum_with T ds D K X active activeOffset J R n o r w ρ s
    hactive hr hw hρ hG hbits hpayload hN hl htl hal hact
  by_cases hb : B=0
  · simpa [compactReservedPcs,hb] using hsum
  · have hback : TopPcOkS ds s.chunk n w R (⟨0,B,R,oS⟩ : TopPc) := by
      apply hok
      simp [compactReservedPcs,hb,compactRebasePc]
    have hleaf := compactPieceCostR_leaf_with T ds D s n o r w ρ B R oS
      (by omega) hback.hR₀ hr hw hρ hback.hfit hN
    have hleafR : (compactPieceCostWithR T ds D s n o r w ρ ⟨0,B,R,oS⟩:ℝ) ≤
        512*(B:ℝ)*((R*2^(o+n)*(r*w):ℕ):ℝ) := by exact_mod_cast hleaf
    simp only [compactReservedPcs,hb,↓reduceIte,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,Nat.cast_add]
    simp only [compactRebasePc,pow_zero,Nat.div_one,Nat.cast_zero,add_zero] at *
    nlinarith only [hsum,hleafR]

theorem compactRelativePc_okS (ds : ComplexFramedExecution.Directions)
    {o K n w R : ℕ} {pc : TopPc} (ho : o≤pc.a₀) (h : TopPcOkS ds K n w R pc) :
    TopPcOkS ds K (n-o) w R (compactRelativePc o pc) := by
  refine ⟨h.hu,h.hR₀,h.hR,h.hs,?_⟩
  have hfit := h.hfit
  change pc.a₀-o+K*bits pc.u pc.j≤n-o
  omega

/-- **The rounded reserved pieces** in the caller's absolute coordinates. -/
theorem compactTopCallCostR_reserved_sum (ds : ComplexFramedExecution.Directions)
    (D K X active oS activeOffset B J R n o r w ρ : ℕ)
    (s : CompactGadgetReservationShape.Shape) {lam : ℝ}
    (hactive : active≠0)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hn : o≤n) (hoffset : o≤activeOffset)
    (hbits : s.bits≤n-o) (hpayload : s.payload=2^o*(3*(r*w))) (hN : n≤r*w)
    (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : ∀ pc∈(compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R),
      TopPcOkS ds s.chunk n w R pc)
    (hbase : ∀ pc∈(compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R),
      o≤pc.a₀) :
    ((((compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R)).map
      (compactTopCallCostR ds s D n o r w ρ)).sum:ℝ) ≤
      ((R*2^n*(r*w):ℕ):ℝ)*
        (512*(B:ℝ)+compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) D ds lam) m lam*
          (active:ℝ)^lam*(s.guard:ℝ)^Parameters.tau) := by
  let pcs := (compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R)
  have hmap : pcs.map (compactRelativePc o) =
      (compactReservedPcs K X (oS-o) B (activeOffset-o) J active).map (compactRebasePc R) := by
    calc
      _ = ((compactReservedPcs K X oS B activeOffset J active).map (compactRelativePc o)).map
          (compactRebasePc R) := by
        simp only [pcs,List.map_map]
        apply List.map_congr_left
        intro pc _
        exact compactRelativePc_rebase o R pc
      _ = _ := congrArg (List.map (compactRebasePc R))
        (compactRelativePc_reserved o K X oS B activeOffset J active hoffset)
  have hrel : ∀ pc∈(compactReservedPcs K X (oS-o) B (activeOffset-o) J active).map
      (compactRebasePc R), TopPcOkS ds s.chunk (n-o) w R pc := by
    intro pc hp
    rw [←hmap] at hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact compactRelativePc_okS ds (hbase q hq) (hok q hq)
  have hs := compactReservedCostR_sum_with (nT CompactBReg) ds D K X active (oS-o)
    (activeOffset-o) B J R (n-o) o r w ρ s
    hactive hr hw hρ hG hbits hpayload (by simpa only [Nat.add_sub_of_le hn] using hN)
    hl htl hal hrel
  have heq : (pcs.map (compactTopCallCostR ds s D n o r w ρ)).sum =
      ((pcs.map (compactRelativePc o)).map
        (compactPieceCostWithR (nT CompactBReg) ds D s (n-o) o r w ρ)).sum := by
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pc _
    cases pc
    rfl
  change ((pcs.map (compactTopCallCostR ds s D n o r w ρ)).sum:ℝ)≤_
  rw [heq,hmap]
  simpa only [Nat.add_sub_of_le hn] using hs

/-- The rounded top-kernel call: a level-zero layer, as for the exact top. -/
theorem compactTopCallCostR_kernel (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ q R a : ℕ)
    (hq : 1≤q) (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hn : o≤n) (ha : o≤a) (hfit : a+s.chunk*q≤n) (hN : n≤r*w) :
    compactTopCallCostR ds s D n o r w ρ ⟨0,q,R,a⟩ ≤512*q*(R*2^n*(r*w)) := by
  have hf : a-o+s.chunk*q≤n-o := by omega
  have hs := compactPieceCostR_leaf_with (nT CompactBReg) ds D s (n-o) o r w ρ q R (a-o)
    hq hR hr hw hρ hf (by simpa only [Nat.add_sub_of_le hn] using hN)
  simpa only [Nat.add_sub_of_le hn,compactTopCallCostR,compactPieceCostWithR] using hs

end
end IntegerMultBounds.MathlibTM2.Cost
