module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Data

/-! Helper registers. A helper hosts a slice of its family: the word must apply `C` on the
slice's basis axes and leave the family otherwise unchanged. Its chart orders its port basis
with the slice axes first, so the slice becomes the C gates on the first `w` local coordinates.
The helper's own word transition lowers as `R · C_w · L` with monomial words `L` and `R`
(`Realization.lowering`); wrapping the helper by `L⁻¹` before and `R⁻¹` after leaves exactly
the C gates of the slice, whatever frame the family is in. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli Multiplicative

/-! ### The split lowering of a realization -/

theorem Realization.scalar_ne_zero_smul (K : Realization) {κ : ℂ} {g : State → State}
    (h : ∀ f, K.scalar f = κ • g f) : κ ≠ 0 := by
  intro hκ
  have hf : (Pi.single 0 1 : State) ≠ 0 := by
    intro e
    have := congrFun e 0
    simp at this
  apply hf
  have h0 : K.scalar (Pi.single 0 1) = 0 := by rw [h, hκ, zero_smul]
  rw [← K.scalar.symm_apply_apply (Pi.single 0 1), h0, map_zero]

/-- **Split lowering.** Every realization is a monomial word, the C gates on the first `r`
local coordinates and another monomial word, with `r` its X-block rank. -/
theorem Realization.exists_split (K : Realization) :
    ∃ Lw Rw : List Prim, (∀ p ∈ Lw ++ Rw, p.Invertible) ∧ childCount Lw = 0 ∧
      childCount Rw = 0 ∧
      Lowers K (Lw ++ cPrims (Module.finrank Geometry.F (Tableau.xRange K.binary)) ++ Rw) ∧
      (K.Dyadic → ∀ p ∈ Lw ++ Rw, p.Ready) := by
  obtain ⟨A₂, G, S₂, S, hS₂, hS, c, κ, h⟩ := K.lowering
  set r := Module.finrank Geometry.F (Tableau.xRange K.binary)
  have hκ : κ ≠ 0 := Realization.scalar_ne_zero_smul K h
  have hl := lowers_smul_operator κ c h
    ((lowers_monomial A₂ S₂ hS₂).then ((lowers_hadamard r).then
      ((lowers_shear S hS).then (lowers_permutation G))))
  refine ⟨[Prim.perm (liftGL A₂), .diag (fun x => qValue (shearMatrix S₂)
      (defaultAlpha (shearMatrix S₂)) (lowPart x)),
      .diag (fun x => qValue (shearMatrix (Tableau.cut r))
        (defaultAlpha (shearMatrix (Tableau.cut r))) (lowPart x))],
    [.diag (fun x => qValue (shearMatrix (Tableau.cut r))
        (defaultAlpha (shearMatrix (Tableau.cut r))) (lowPart x)),
      .diag (fun x => qValue (shearMatrix S) (defaultAlpha (shearMatrix S)) (lowPart x)),
      .perm (liftGL G)] ++ (pauliPrims c ++ [.scale κ]), ?_, rfl, rfl, ?_, fun hK => ?_⟩
  · intro p hp
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, pauliPrims] at hp
    rcases hp with ((rfl | rfl | rfl) | ((rfl | rfl | rfl) | (rfl | rfl | rfl) | rfl)) <;>
      first | trivial | exact phase_ne_zero c.phase
  · intro f
    rw [hl f]
    simp only [hadamardPrims, List.append_assoc, List.cons_append, List.nil_append]
  · obtain ⟨j, hj⟩ := phase_of_good hK.1 (((dyadic_monomial A₂ S₂ hS₂).then ((dyadic_hadamard r).then
      ((dyadic_shear S hS).then (dyadic_permutation G)))).1.comp (good_operator c)) h
    refine List.forall_mem_append.mpr ⟨?_, List.forall_mem_append.mpr ⟨?_,
      List.forall_mem_append.mpr ⟨ready_pauliPrims c, ?_⟩⟩⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact trivial
      · exact quadratic_qValue _ _
      · exact quadratic_qValue _ _
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact quadratic_qValue _ _
      · exact quadratic_qValue _ _
      · exact trivial
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨j, hj⟩

theorem wordOp_invPrims_right (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) (f : Arrays 73) :
    wordOp ws (wordOp (invPrims ws) f) = f := by
  have hinv : invPrims (invPrims ws) = ws := by
    simp only [invPrims, List.map_reverse, List.map_map, List.reverse_reverse]
    conv_rhs => rw [← List.map_id ws]
    apply List.map_congr_left
    intro p _
    cases p <;> simp [Prim.inv]
  have hinv' : ∀ p ∈ invPrims ws, p.Invertible := by
    intro p hp
    simp only [invPrims, List.mem_reverse, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := hws q hq
    cases q <;> simp_all [Prim.inv, Prim.Invertible]
  have h := wordOp_invPrims (invPrims ws) hinv' f
  rwa [hinv] at h

theorem wordLin_invPrims_mul (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) :
    wordLin (invPrims ws) * wordLin ws = 1 :=
  LinearMap.ext fun f => by
    rw [Module.End.mul_apply, wordLin_apply, wordLin_apply, wordOp_invPrims ws hws]; rfl

theorem wordLin_mul_invPrims (ws : List Prim) (hws : ∀ p ∈ ws, p.Invertible) :
    wordLin ws * wordLin (invPrims ws) = 1 :=
  LinearMap.ext fun f => by
    rw [Module.End.mul_apply, wordLin_apply, wordLin_apply, wordOp_invPrims_right ws hws]; rfl

theorem wordLin_append (ps qs : List Prim) : wordLin (ps ++ qs) = wordLin qs * wordLin ps :=
  LinearMap.ext fun f => by
    rw [Module.End.mul_apply, wordLin_apply, wordLin_apply, wordLin_apply, wordOp_append]

/-! ### The helper chart -/

/-- Basis indices in a mask, then the others. -/
def maskOrder (m : ℕ) : List (Fin 73) :=
  (List.finRange 73).filter (fun k : Fin 73 => m.testBit k.val) ++
    (List.finRange 73).filter (fun k : Fin 73 => !m.testBit k.val)

/-- The basis indices in a mask. -/
def maskIndices (m : ℕ) : List (Fin 73) := (List.finRange 73).filter fun k : Fin 73 => m.testBit k.val

theorem maskOrder_nodup (m : ℕ) : (maskOrder m).Nodup := by
  rw [maskOrder, List.nodup_append]
  refine ⟨(List.nodup_finRange 73).filter _, (List.nodup_finRange 73).filter _, ?_⟩
  intro a ha b hb e
  subst e
  simp_all

theorem mem_maskOrder (m : ℕ) (k : Fin 73) : k ∈ maskOrder m := by
  by_cases h : m.testBit k <;> simp [maskOrder, h]

theorem maskOrder_length (m : ℕ) : (maskOrder m).length = 73 := by
  have h := (maskOrder_nodup m).length_le_card
  have h' : (List.finRange 73).length ≤ (maskOrder m).length := by
    apply List.Subperm.length_le
    exact List.subperm_of_subset (List.nodup_finRange 73) (fun k _ => mem_maskOrder m k)
  simp at h h'
  omega

/-- The permutation listing a mask's indices first. -/
noncomputable def maskPerm (m : ℕ) : Equiv.Perm (Fin 73) :=
  (finCongr (maskOrder_length m).symm).trans
    ((maskOrder_nodup m).getEquivOfForallMemList _ (mem_maskOrder m))

theorem maskPerm_apply (m : ℕ) (j : Fin 73) :
    maskPerm m j = (maskOrder m)[j.val]'(by rw [maskOrder_length]; exact j.isLt) := rfl

theorem maskPerm_symm_index (m : ℕ) (i : ℕ) (hi : i < (maskIndices m).length) :
    ((maskPerm m).symm ((maskIndices m)[i])).val = i := by
  have hlen : (maskIndices m).length ≤ 73 := by
    have h1 := maskOrder_length m
    rw [maskOrder, List.length_append] at h1
    change (maskIndices m).length + _ = 73 at h1
    omega
  have h : maskPerm m ⟨i, by omega⟩ = (maskIndices m)[i] := by
    rw [maskPerm_apply]
    simp only [maskOrder]
    rw [List.getElem_append_left (by simpa [maskIndices] using hi)]
    rfl
  rw [← h, Equiv.symm_apply_apply]

/-- The chart of a helper hosting the axes of `m` in the basis of `P`. -/
noncomputable def helperChart {P : PortData} (hP : portCheck P = true) (m : ℕ) :
    Addr ≃ₗ[ZMod 2] Addr :=
  basisChart (portBasis P) (portBasis_orthonormal hP) (maskPerm m)

theorem helperChart_orth {P : PortData} (hP : portCheck P = true) (m : ℕ) :
    IsOrth (helperChart hP m) := basisChart_orth _ _ _

theorem helperChart_pull {P : PortData} (hP : portCheck P = true) (m : ℕ) (k : Fin 73) :
    (helperChart hP m).symm (portBasis P k) = Pi.single ((maskPerm m).symm k) 1 :=
  basisChart_symm_basis _ _ _ k

/-- The frame of a hosted slice: coefficient one on the axes of the mask. -/
def maskFrame (m : ℕ) : Fin 73 → ZMod 4 := fun k => if m.testBit k.val then 1 else 0

theorem maskFrame_eq (m : ℕ) : maskFrame m = (Vec.toFun (m, 0)) := by
  funext k
  simp [maskFrame, Vec.toFun, Vec.coeff]

/-- The nine-bit coordinate vector. -/
def e9 (j : Fin 9) : Address 9 := Pi.single j 1

theorem single_local (j : Fin 73) (hj : j.val < 9) :
    (Pi.single j (1 : ZMod 2) : Addr) = padLow (e9 ⟨j.val, hj⟩) := by
  funext i
  simp only [padLow, joinAddr, e9]
  refine Fin.addCases (m := 9) (n := 64) (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h; ext; simp [← h]
    · intro h; ext; have := congrArg Fin.val h; simpa using this
  · simp only [Fin.append_right, Pi.zero_apply, Pi.single_apply]
    rw [ite_eq_right_iff]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

theorem maskPerm_symm_lt (m : ℕ) (k : Fin 73) (hk : k ∈ maskIndices m) :
    ((maskPerm m).symm k).val < (maskIndices m).length := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  rw [maskPerm_symm_index m i hi]
  exact hi

/-- The split of a hosted slice through its helper chart. -/
noncomputable def helperSplit {P : PortData} (hP : portCheck P = true) (m : ℕ)
    (hw : (maskIndices m).length ≤ 9) : ChartSplit (helperChart hP m) (portBasis P) (maskFrame m) :=
  ChartSplit.ofLocal _ (helperChart_orth hP m) _ (maskFrame m) (maskIndices m)
    ((List.nodup_finRange 73).filter _)
    (fun k hk => by
      have hlt := maskPerm_symm_lt m k hk
      rw [helperChart_pull, single_local _ (by omega), padLow, lowPart_join]
      rfl)
    (fun k hk hf => by
      exfalso
      apply hf
      simp only [maskIndices, List.mem_filter, List.mem_finRange, true_and] at hk
      simp [maskFrame, hk])

/-! ### Kernel lists as words -/

/-- The primitive word of a kernel list. -/
noncomputable def kernelPrims (gs : List (ZMod 4 × Address 9)) : List Prim :=
  gs.map fun g => .kernel g.1 (padLow g.2)

theorem lift9_kernelList (gs : List (ZMod 4 × Address 9)) :
    lift9 (kernelList gs) = wordLin (kernelPrims gs) := by
  induction gs with
  | nil => exact LinearMap.ext lift9_id
  | cons g gs ih =>
    rw [kernelList, kernelPrims, List.map_cons, wordLin, ← kernelPrims, ← ih]
    apply LinearMap.ext
    intro f
    rw [← lift9_comp, Module.End.mul_apply, lift9_kernel]
    rfl

theorem cPrims_eq (r : ℕ) (hr : r ≤ 9) :
    cPrims r = kernelPrims ((List.finRange r).map fun j => (1, e9 ⟨j.val, by omega⟩)) := by
  induction r with
  | zero => rfl
  | succ k ih =>
    rw [cPrims, ih (by omega)]
    simp only [show k < 9 from by omega, ↓reduceDIte]
    rw [List.finRange_succ_last, List.map_append, kernelPrims, kernelPrims, List.map_append]
    simp [e9]

theorem helperSplit_gs {P : PortData} (hP : portCheck P = true) (m : ℕ)
    (hw : (maskIndices m).length ≤ 9) :
    (helperSplit hP m hw).gs =
      (List.finRange (maskIndices m).length).map fun j => (1, e9 ⟨j.val, by omega⟩) := by
  change (maskIndices m).map (fun k => (maskFrame m k,
    lowPart ((helperChart hP m).symm (portBasis P k)))) = _
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange]
  have hmem : (maskIndices m)[i]'(by simpa using h1) ∈ maskIndices m := List.getElem_mem _
  have hbit : m.testBit ((maskIndices m)[i]'(by simpa using h1)).val = true := by
    simp only [maskIndices, List.mem_filter] at hmem
    exact hmem.2
  have hidx := maskPerm_symm_index m i (by simpa using h1)
  rw [helperChart_pull]
  have hlt : ((maskPerm m).symm ((maskIndices m)[i]'(by simpa using h1))).val < 9 := by
    rw [hidx]; simp at h1; omega
  rw [single_local _ hlt, padLow, lowPart_join]
  simp only [maskFrame, hbit, ite_true, Prod.mk.injEq, true_and]
  congr 1
  ext
  simp [hidx]

/-- The C gates of a hosted slice, lifted, are its primitive child calls. -/
theorem helperSplit_lift {P : PortData} (hP : portCheck P = true) (m : ℕ)
    (hw : (maskIndices m).length ≤ 9) :
    lift9 (kernelList (helperSplit hP m hw).gs) = wordLin (cPrims (maskIndices m).length) := by
  rw [helperSplit_gs, lift9_kernelList, cPrims_eq _ hw]

/-- **Wrapped helper.** Wrapping a helper's word frames by the inverse halves of the split
lowering of its transition realizes exactly the C gates of its hosted slice. -/
theorem helper_wrapped {P : PortData} (hP : portCheck P = true) (m : ℕ)
    (hw : (maskIndices m).length ≤ 9) (a b : ℕ) (Lw Rw : List Prim)
    (hinv : ∀ p ∈ Lw ++ Rw, p.Invertible)
    (hlow : Lowers (edgeRealization a b) (Lw ++ cPrims (maskIndices m).length ++ Rw)) :
    (permOp (helperChart hP m) * wordLin (invPrims Rw)) *
        lift9 (nativeRealization b).scalar.toLinearMap *
        lift9 (nativeRealization a).scalar.symm.toLinearMap *
        (wordLin (invPrims Lw) * permOp (helperChart hP m).symm) =
      basisOp (portBasis P) (ofAdd (maskFrame m)) := by
  set χ := helperChart hP m
  set w := (maskIndices m).length
  have hL : ∀ p ∈ Lw, p.Invertible := fun p hp => hinv p (List.mem_append_left _ hp)
  have hR : ∀ p ∈ Rw, p.Invertible := fun p hp => hinv p (List.mem_append_right _ hp)
  have hedge : lift9 (nativeRealization b).scalar.toLinearMap *
      lift9 (nativeRealization a).scalar.symm.toLinearMap =
        wordLin Rw * wordLin (cPrims w) * wordLin Lw := by
    rw [← lift9Hom_apply, ← lift9Hom_apply, ← map_mul, lift9Hom_apply,
      show (nativeRealization b).scalar.toLinearMap * (nativeRealization a).scalar.symm.toLinearMap =
        (edgeRealization a b).scalar.toLinearMap from rfl, hlow.lin, wordLin_append, wordLin_append,
      mul_assoc]
  have hM : basisOp (portBasis P) (ofAdd (maskFrame m)) =
      permOp χ * wordLin (cPrims w) * permOp χ.symm := by
    have hs := (helperSplit hP m hw).split
    have hext : (helperSplit hP m hw).ext = 0 := by
      funext k
      change (if k ∈ maskIndices m then 0 else maskFrame m k) = 0
      split_ifs with h
      · rfl
      · simp only [maskIndices, List.mem_filter, List.mem_finRange, true_and] at h
        simp [maskFrame, h]
    rw [hext, ofAdd_zero, map_one, mul_one, helperSplit_lift] at hs
    calc basisOp (portBasis P) (ofAdd (maskFrame m))
        = permOp χ * (permOp χ.symm * basisOp (portBasis P) (ofAdd (maskFrame m))) := by
          rw [← mul_assoc, permOp_mul_symm, one_mul]
      _ = _ := by rw [hs, mul_assoc]
  rw [hM]
  calc permOp χ * wordLin (invPrims Rw) * lift9 (nativeRealization b).scalar.toLinearMap *
        lift9 (nativeRealization a).scalar.symm.toLinearMap * (wordLin (invPrims Lw) * permOp χ.symm)
      = permOp χ * wordLin (invPrims Rw) * (lift9 (nativeRealization b).scalar.toLinearMap *
          lift9 (nativeRealization a).scalar.symm.toLinearMap) *
          (wordLin (invPrims Lw) * permOp χ.symm) := by simp only [mul_assoc]
    _ = permOp χ * (wordLin (invPrims Rw) * wordLin Rw) * wordLin (cPrims w) *
          (wordLin Lw * wordLin (invPrims Lw)) * permOp χ.symm := by
          rw [hedge]; simp only [mul_assoc]
    _ = _ := by rw [wordLin_invPrims_mul Rw hR, wordLin_mul_invPrims Lw hL, mul_one, mul_one]

end IntegerMultBounds.Networks.Certificates.T16.Impl
