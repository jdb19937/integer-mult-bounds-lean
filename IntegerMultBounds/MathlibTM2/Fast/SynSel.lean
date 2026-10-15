module

public import IntegerMultBounds.MathlibTM2.Fast.SynRecB

/-!
# The records of round `h` meet the hypotheses of the layer

Paper §6, proof of `lem:synthetic-transform-cost`. For the layout `L = layPerm es ℓ K` and round
`h`, the records `synCfg`, `synPcsR` of `Fast/SynRec.lean` describe the selected bits of the round
(`selBits es h` stored at the physical bits `twPosL L`):

* `synPcs_vals`: the active bits of the pieces of a chunk round are `ρ + oS + K i`, `i < D'`,
  each once, and the top kernels cover `D' ≤ i < D` (`synSel_vals`); `synPcs_ok`: every piece
  meets `TopPc.Ok` (levels `j ≤ J'`, row counts `R₂ = rowsAt R₀ j`, exponents of the lower
  levels below `w'`, active bits inside the `n = N - a'` address bits below the rows).
* `synSel_chunk`, `synSel_top`, `synSel_low`: the selected bits of the layer are a permutation of
  the physical selected bits of the round (`layPerm_sel_chunk_perm`, `layPerm_sel_top`,
  `layPerm_sel_low`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ### Active bits of the pieces -/

section Vals

/-- The active bits of a machine piece with offset `ρ` and stride `K`. -/
def synPcVals (ρ K : ℕ) (pc : TopPc) : List ℕ :=
  (List.range (bits pc.u pc.j)).map fun i => pc.a₀ + ρ + K * i

theorem map_val_actMap {a₀ ρ K N n : ℕ} (hfit : ∀ i < N, a₀ + ρ + K * i < n) :
    ((List.finRange N).map (actMap a₀ ρ K N n hfit)).map Fin.val =
      (List.range N).map fun i => a₀ + ρ + K * i := by
  rw [List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [actMap]

theorem topPieces_vals {ds : ComplexFramedExecution.Directions} {ρ K n w R₂ Gd : ℕ} (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (h : ∀ pc ∈ pcs, pc.Ok ds K n w R₂ Gd),
      ((topPieces hρ pcs h).flatMap Piece.bitsList).map Fin.val = pcs.flatMap (synPcVals ρ K)
  | [], _ => rfl
  | pc :: pcs, h => by
      rw [topPieces, List.flatMap_cons, List.map_append, List.flatMap_cons,
        topPieces_vals hρ pcs]
      congr 1
      simp only [TopPc.piece, Piece.bitsList]
      rw [map_val_actMap]
      rfl

theorem synPc_vals (K a D oS J ρ t : ℕ) :
    synPcVals ρ K (synPc K a D oS J t) =
      (List.range (synDg D t * m ^ t)).map fun i => oS + K * (D % m ^ t) + ρ + K * i := by
  simp [synPcVals, synPc, bits_eq_mul]

theorem range_add_map (x y : ℕ) (f : ℕ → ℕ) :
    (List.range (x + y)).map f = (List.range x).map f ++ (List.range y).map fun i => f (x + i) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- The pieces of the digits `j < t` cover `ρ + oS + K i`, `i < D mod m^t`, once each. -/
theorem synPcs_vals (K a D oS J ρ : ℕ) : ∀ t,
    ((synPcs K a D oS J t).flatMap (synPcVals ρ K)).Perm
      ((List.range (D % m ^ t)).map fun i => ρ + oS + K * i)
  | 0 => by simp [synPcs, Nat.mod_one]
  | t + 1 => by
      rw [synPcs_succ, mod_pow_succ_dg, range_add_map, List.flatMap_append]
      refine List.Perm.trans (List.perm_append_comm) (List.Perm.append (synPcs_vals K a D oS J ρ t) ?_)
      by_cases h0 : synDg D t = 0
      · simp [h0]
      · rw [if_neg h0, List.flatMap_singleton, synPc_vals]
        refine List.Perm.of_eq (List.map_congr_left fun i _ => ?_)
        ring

theorem synPcs_vals_full (K a D oS J ρ : ℕ) :
    ((synPcs K a D oS J D).flatMap (synPcVals ρ K)).Perm
      ((List.range D).map fun i => ρ + oS + K * i) := by
  have := synPcs_vals K a D oS J ρ D
  rwa [mod_pow_self] at this

end Vals

/-! ### The pieces meet the conditions of the layer -/

section Ok

theorem expSeq_le_add (G F u : ℕ) {i j : ℕ} (hij : i < j) :
    expSeq G F u i ≤ expSeq G F u j + u := by
  rcases Nat.eq_zero_or_pos F with hF | hF
  · rcases i with _ | i
    · simp [expSeq]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp [expSeq, hF]
  · have mono : ∀ k, expSeq G F u k ≤ expSeq G F u (k + 1) := fun k => by
      rw [expSeq]
      nlinarith [Nat.zero_le G]
    have : expSeq G F u i ≤ expSeq G F u j := by
      induction j with
      | zero => omega
      | succ j ih =>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
          · exact (ih h).trans (mono j)
          · rw [h]; exact mono j
    omega

theorem synDg_le (D j : ℕ) : synDg D j ≤ D :=
  (Nat.mod_le _ _).trans (Nat.div_le_self _ _)

theorem synDg_pos_div {D j : ℕ} (h : synDg D j ≠ 0) : 0 < D / m ^ j := by
  by_contra h'
  exact h (synDg_of_zero (Nat.eq_zero_of_not_pos h'))

theorem lt_synJ {D j : ℕ} (hj : j < D) (h : 0 < D / m ^ j) : j < synJ D D := by
  have : synJ D (j + 1) = j + 1 := by rw [synJ_succ, synJ_eq_of_pos h]; simp [h]
  have mono : ∀ t, synJ D t ≤ synJ D (t + 1) := fun t => by rw [synJ_succ]; omega
  have : synJ D (j + 1) ≤ synJ D D := monotone_nat_of_le_succ mono (by omega)
  omega

theorem synE_ge (G F D : ℕ) {j : ℕ} (hj : j < D) (h : synDg D j ≠ 0) :
    expSeq G F (synDg D j) j ≤ synE G F D D := by
  unfold synE
  have := Finset.single_le_sum (f := fun j => if synDg D j = 0 then 0 else
    expSeq G F (synDg D j) j) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
  simpa [h] using this

theorem mem_synPcs {K a D oS J t : ℕ} {pc : TopPc} (h : pc ∈ synPcs K a D oS J t) :
    ∃ j < t, synDg D j ≠ 0 ∧ pc = synPc K a D oS J j := by
  unfold synPcs at h
  rw [List.mem_filterMap] at h
  obtain ⟨j, hj, hpc⟩ := h
  rw [List.mem_reverse, List.mem_range] at hj
  by_cases h0 : synDg D j = 0
  · simp [h0] at hpc
  · rw [if_neg h0, Option.some.injEq] at hpc
    exact ⟨j, hj, h0, hpc.symm⟩

/-- **The pieces of the digits of `D` meet `TopPc.Ok`.** The pieces sit at `oS + K i`, `i < D`;
`D Gd` bits below them and `H ≥ 3 D Gd` bits above them stay inside the `n` address bits, so
every node finds the control fields of its compact slot XORs (`hres`); a node needs `D ≥ m`. -/
theorem synPcs_ok (ds : ComplexFramedExecution.Directions) {K a D oS n w' Gd H : ℕ}
    (hfit : oS + K * D + H ≤ n) (hfront : D * Gd ≤ oS) (hback : 3 * (D * Gd) ≤ H)
    (hGK : m ≤ D → 1 ≤ Gd ∧ Gd + 3 ≤ K)
    (hw : synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w') :
    ∀ pc ∈ synPcs K a D oS (synJ D D - 1) D,
      pc.Ok ds K n w' (rowsAt (2 ^ a) (synJ D D - 1)) Gd := by
  intro pc hpc
  obtain ⟨j, hj, h0, rfl⟩ := mem_synPcs hpc
  have hpos := synDg_pos_div h0
  have hJ := lt_synJ hj hpos
  have h1 : D % m ^ j + synDg D j * m ^ j ≤ D := by
    rw [← mod_pow_succ_dg]; exact Nat.mod_le _ _
  have h2 : K * (D % m ^ j) + K * (synDg D j * m ^ j) ≤ K * D := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h1
  refine ⟨Nat.pos_of_ne_zero h0, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [synPc, rowsAt_eq]
    have : 0 < NW := Nat.pos_of_ne_zero (NeZero.ne _)
    exact Nat.mul_pos (pow_pos this _) (by positivity)
  · simp only [synPc, rowsAt_eq]
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  · intro i hi
    simp only [synPc] at hi ⊢
    rw [expZ_eq_expSeq]
    have h1 := expSeq_le_add (gateCount (program ds)) (factorCount (program ds)) (synDg D j) hi
    have h2 := synE_ge (gateCount (program ds)) (factorCount (program ds)) D hj h0
    have h3 := synDg_le D j
    omega
  · simp only [synPc, bits_eq_mul]
    omega
  · intro hj1 _
    simp only [synPc, bits_eq_mul]
    have hmj : m ^ j ≤ D := (div_pow_pos_iff m_pos).1 hpos
    have hm1 : m ≤ m ^ j := by
      calc m = m ^ 1 := (pow_one m).symm
        _ ≤ m ^ j := Nat.pow_le_pow_right m_pos hj1
    obtain ⟨hG1, hGK'⟩ := hGK (hm1.trans hmj)
    have h3 : synDg D j * m ^ (j - 1) ≤ synDg D j * m ^ j :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right m_pos (by omega))
    have h4 : (synDg D j * m ^ (j - 1) - 1) * Gd ≤ D * Gd :=
      Nat.mul_le_mul_right _ ((Nat.sub_le _ _).trans (h3.trans ((Nat.le_add_left _ _).trans h1)))
    generalize (synDg D j * m ^ (j - 1) - 1) * Gd = P at h4 ⊢
    refine ⟨hG1, hGK', by omega, by omega⟩

end Ok

/-! ### The selected bits in the layout -/

section Layout

variable {es : List ℕ} {ℓ K : ℕ}

theorem filter_range_map_rank (p : ℕ → Bool) : ∀ n : ℕ,
    ((List.range n).filter p).map (fun i => ((List.range i).filter p).length) =
      List.range ((List.range n).filter p).length
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.filter_append]
      by_cases hp : p n
      · simp only [List.filter_singleton, hp, cond_true, List.map_append,
          filter_range_map_rank p n, List.length_append, List.range_succ, List.length_singleton,
          List.map_singleton]
      · simp only [List.filter_singleton, hp, cond_false, List.append_nil,
          filter_range_map_rank p n]

theorem layLongs_map_rank (es : List ℕ) (ℓ : ℕ) :
    (layLongs es ℓ).map (layLrank es ℓ) = List.range (synLg es ℓ) := by
  have := filter_range_map_rank (fun j => decide (ax es j = ℓ)) es.length
  unfold synLg layLongs layLrank
  exact this

/-- The physical selected bits of round `h` in a layout. -/
theorem synSelBits_eq (L : Equiv.Perm (Fin es.sum)) (h : ℕ) :
    (selBits es h).map (twPosL L) = (selFin es h).map fun x => (L x : ℕ) := by
  rw [← selFin_map_val, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp [twPosL]

theorem synA_le (H : LayHyp es ℓ K) : synA es ℓ K ≤ es.sum := by
  have := layPre_length_le H
  rw [layPre_length] at this
  exact this

/-- Chunk rounds: the selected bits are `ρ + oS + K i`, `i < D`. -/
theorem synSel_chunk (H : LayHyp es ℓ K) {h : ℕ} (hc : synChunk ℓ K h) :
    ((selBits es h).map (twPosL (layPerm es ℓ K))).Perm
      ((List.range es.length).map fun i => synRh ℓ K h + synOS es ℓ K h + K * i) := by
  obtain ⟨h1, h2⟩ := hc
  rw [synSelBits_eq]
  have hh : h < ℓ - 1 := by omega
  have := layPerm_sel_chunk_perm H h2 hh
  rw [lay_parts_all H hh, List.length_range] at this
  refine this.trans (List.Perm.of_eq (List.map_congr_left fun i _ => ?_))
  have hc' : synChunk ℓ K h := ⟨h1, h2⟩
  simp only [synRh, synOS, hc', if_true, h1, layRho, layC0, show ¬ h < layB ℓ K by omega,
    if_false]
  ring

/-- The top round `h = ℓ - 1`: the selected bits are `N - Lg + i`, `i < Lg`. -/
theorem synSel_top (H : LayHyp es ℓ K) {h : ℕ} (h1 : ¬ h + 1 < ℓ) (h2 : h + 1 ≤ ℓ) :
    ((selBits es h).map (twPosL (layPerm es ℓ K))).Perm
      ((List.range (synLg es ℓ)).map fun i => es.sum - synLg es ℓ + i) := by
  have hh : h = ℓ - 1 := by omega
  subst hh
  rw [synSelBits_eq, layPerm_sel_top H]
  have hLN : synLg es ℓ ≤ es.sum := by have := synA_le H; unfold synA at this; omega
  have e : (layLongs es ℓ).map (fun i => es.sum - 1 - layLrank es ℓ i) =
      (List.range (synLg es ℓ)).map fun i => es.sum - 1 - i := by
    rw [← layLongs_map_rank, List.map_map]; rfl
  rw [e]
  have e2 : (List.range (synLg es ℓ)).map (fun i => es.sum - 1 - i) =
      (List.range (synLg es ℓ)).map (fun i => (fun k => es.sum - synLg es ℓ + k)
        (synLg es ℓ - 1 - i)) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.1 hi
      simp only
      omega
  rw [e2, lay_map_range_rev]
  exact List.reverse_perm _

/-- Low rounds `h < b`: the selected bits are `N - Lg - (b - h) D + i`, `i < D`. -/
theorem synSel_low (H : LayHyp es ℓ K) {h : ℕ} (hl : h < layB ℓ K) :
    ((selBits es h).map (twPosL (layPerm es ℓ K))).Perm
      ((List.range es.length).map fun i =>
        es.sum - synLg es ℓ - (layB ℓ K - h) * es.length + i) := by
  rw [synSelBits_eq, layPerm_sel_low H hl]
  have hA := synA_le H
  unfold synA at hA
  have hbh : (layB ℓ K - h) * es.length ≤ layB ℓ K * es.length :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hsplit : (layB ℓ K - h) * es.length = (layB ℓ K - 1 - h) * es.length + es.length := by
    rw [← Nat.succ_mul]; congr 1; omega
  have e2 : (List.range es.length).map (fun i =>
      es.sum - 1 - (synLg es ℓ + ((layB ℓ K - 1 - h) * es.length + i))) =
      (List.range es.length).map (fun i => (fun k =>
        es.sum - synLg es ℓ - (layB ℓ K - h) * es.length + k) (es.length - 1 - i)) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.1 hi
      simp only
      omega
  rw [e2, lay_map_range_rev]
  exact List.reverse_perm _

end Layout

/-! ### Exponents of the pieces -/

section Exps

theorem synPcs_exp_sum (ds : ComplexFramedExecution.Directions) (K a D oS J : ℕ) : ∀ t,
    ((synPcs K a D oS J t).map fun pc => expZ pc.u ds pc.j).sum =
      synE (gateCount (program ds)) (factorCount (program ds)) D t
  | 0 => by simp [synPcs, synE]
  | t + 1 => by
      rw [synPcs_succ, synE_succ, List.map_append, List.sum_append, synPcs_exp_sum ds K a D oS J t]
      by_cases h0 : synDg D t = 0
      · simp [h0]
      · simp [h0, synPc, expZ_eq_expSeq, Nat.add_comm]

theorem topPieces_exp {ds : ComplexFramedExecution.Directions} {ρ K n w R₂ Gd : ℕ} (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (h : ∀ pc ∈ pcs, pc.Ok ds K n w R₂ Gd),
      (topPieces hρ pcs h).map (Piece.exp ds) = pcs.map fun pc => expZ pc.u ds pc.j
  | [], _ => rfl
  | pc :: pcs, h => by
      rw [topPieces, List.map_cons, List.map_cons, topPieces_exp hρ pcs]
      rfl

end Exps

/-! ### The step bounds do not depend on the alphabet

The alphabet size `A` enters the step bound of the layer only through the lengths of the
register contents cleared by the compact slot XORs, which do not depend on it. -/

section Indep

theorem sxBc_length_indep (A A' : ℕ) (d : SxD) (x : SXReg) :
    (sxBc A d x).length = (sxBc A' d x).length := by
  cases x <;> simp [sxBc] <;> split_ifs <;> simp

theorem cxBc_length_indep (A A' : ℕ) (d : CxD) (x : CXReg) :
    (cxBc A d x).length = (cxBc A' d x).length := by
  cases x with
  | sx r => exact sxBc_length_indep A A' _ r
  | _ => simp [cxBc]

theorem cxCleanupCost_indep (A A' : ℕ) (d : CxD) :
    cxCleanupCost (A := A) d = cxCleanupCost (A := A') d := by
  unfold cxCleanupCost
  simp only [sxBc_length_indep A A', cxBc_length_indep A A']

theorem cxCost_indep (A A' : ℕ) (d : CxD) (T : ℕ) : cxCost A d T = cxCost A' d T := by
  unfold cxCost
  rw [cxCleanupCost_indep A A']

theorem basisCostN_indep (A A' T a₀ K ρ L R n rw k G : ℕ) (vv : BinaryWalsh.Address m)
    (s : Fin m) :
    basisCostN A T a₀ K ρ L R n rw k G vv s = basisCostN A' T a₀ K ρ L R n rw k G vv s := by
  simp only [basisCostN, basisCostNC, basisCostC, cxCost_indep A A']

theorem factorCost_indep (A A' T : ℕ) (ds : ComplexFramedExecution.Directions)
    (j u K ρ a₀ R₀ n r w Gd : ℕ) (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ) :
    factorCost A T ds j u K ρ a₀ R₀ n r w Gd g cc =
      factorCost A' T ds j u K ρ a₀ R₀ n r w Gd g cc := by
  simp only [factorCost, basisCostN_indep A A']

theorem layerCost_indep (A A' T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w Gd : ℕ) : ∀ j a₀,
    layerCost A T ds u K ρ R₀ n r w Gd j a₀ = layerCost A' T ds u K ρ R₀ n r w Gd j a₀
  | 0, _ => rfl
  | j + 1, a₀ => by
      simp only [layerCost, factorCost_indep A A', layerCost_indep A A' T ds u K ρ R₀ n r w Gd j]

theorem topPcsCost_indep (A A' Gd : ℕ) (ds : ComplexFramedExecution.Directions)
    (cfg : List ℕ) (K ρ n r w : ℕ) : ∀ pcs : List TopPc,
    topPcsCost A Gd ds cfg K ρ n r w pcs = topPcsCost A' Gd ds cfg K ρ n r w pcs
  | [] => rfl
  | pc :: pcs => by
      simp only [topPcsCost, topPcCost, layerCost_indep A A',
        topPcsCost_indep A A' Gd ds cfg K ρ n r w pcs]

theorem topCost_indep (A A' Gd : ℕ) (ds : ComplexFramedExecution.Directions)
    (w w' s n a R r K ρ q aT oS D R₂ q₂ aT₂ : ℕ) (pcs : List TopPc) :
    topCost A Gd ds w w' s n a R r K ρ q aT oS D R₂ q₂ aT₂ pcs =
      topCost A' Gd ds w w' s n a R r K ρ q aT oS D R₂ q₂ aT₂ pcs := by
  simp only [topCost, topKerSCost, topBlockCost, layerCost_indep A A',
    topPcsCost_indep A A']

end Indep

/-! ### The layer of round `h` -/

section LayerRound

variable {Q Ka : ℕ} {U : Type}

/-- The componentwise truncation toward zero of a complex record array. -/
noncomputable def synTrunc {r : ℕ} (B : Recs r) : ℕ → Fin r → GaussianInt :=
  fun x c => ⟨IntegerMultBounds.MathlibTM2.Layer.truncR (B x c).re, IntegerMultBounds.MathlibTM2.Layer.truncR (B x c).im⟩

/-- The step bound of the layer in round `h` (`topCost_indep`: for every alphabet). -/
noncomputable def synLayerCost (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K l w h : ℕ) : ℕ :=
  topCost 0 (synGd es.sum) ds w
    (synW2 es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h)
    (synS es ℓ K (gateCount (program ds)) (factorCount (program ds)) h)
    (es.sum - synAR es ℓ K h) (synAR es ℓ K h) 1 (2 ^ l) (synKh ℓ K h) (synRh ℓ K h)
    (synQ es ℓ K h) (synAT es ℓ K h) (synOS es ℓ K h) (synDp es ℓ h) (synR2 es ℓ K h)
    (synQ2 es ℓ K h) (synOS es ℓ K h) (synPcsR es ℓ K h)

theorem synKh_pos {ℓ K h : ℕ} (hK : 1 ≤ K) : 1 ≤ synKh ℓ K h := by
  unfold synKh; split_ifs <;> omega

theorem synRh_lt {ℓ K h : ℕ} (hK : 1 ≤ K) : synRh ℓ K h < synKh ℓ K h := by
  unfold synRh synKh; split_ifs
  · exact Nat.mod_lt _ (by omega)
  · norm_num

/-- The chunk bits of a chunk round lie below the prefix: `oS + K D + a ≤ N`. -/
theorem synChunk_fit {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {h : ℕ}
    (hc : synChunk ℓ K h) : synOS es ℓ K h + K * es.length + synA es ℓ K ≤ es.sum := by
  obtain ⟨h1, h2⟩ := hc
  have hb := layC0_bound H h2 (by omega)
  have hcs := lay_chunk_size H
  have hAN := synA_le H
  rw [layPre_length] at hcs
  simp only [synOS, h1, if_true, show ¬ h < layB ℓ K by omega, if_false]
  have : K * ((h - layB ℓ K) / K * es.length) + K * es.length =
      K * (layC0 es ℓ K h + es.length) := by unfold layC0; ring
  have h3 : K * (layC0 es ℓ K h + es.length) ≤ K * (es.length * layQ ℓ K) :=
    Nat.mul_le_mul_left _ hb.2.1
  unfold synA at hAN ⊢
  simp only [synLg] at hcs hAN ⊢
  omega

/-- `K q₂ + K D' + K q = K D`. -/
theorem synK_mul_split (es : List ℕ) (K : ℕ) :
    K * synQF es K + K * synDpp es K + K * synQB es K = K * es.length := by
  rw [← Nat.mul_add, ← Nat.mul_add]
  congr 1
  have := synDpp_add_synQB_add_synQF es K
  omega

/-- `K q₀ ≤ K q`. -/
theorem synK_mul_le (es : List ℕ) (K : ℕ) : K * synQK es ≤ K * synQB es K :=
  Nat.mul_le_mul_left _ (synQK_le_synQB es K)

/-- The row bits of every round lie inside the address bits. -/
theorem synAR_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (h : ℕ) :
    synAR es ℓ K h ≤ es.sum := by
  unfold synAR
  split_ifs with hc
  · have hf := synChunk_fit H hc
    have := synK_mul_split es K
    have := synK_mul_le es K
    unfold synAc
    omega
  · exact synA_le H

/-- `oS ≤ N` in every round. -/
theorem synOS_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (h : ℕ) :
    synOS es ℓ K h ≤ es.sum := by
  by_cases hc : synChunk ℓ K h
  · have := synChunk_fit H hc
    omega
  · unfold synChunk at hc
    unfold synOS
    split_ifs <;> omega

/-- The values of the selected bits of the layer in round `h`: the pieces, the top kernels and
the front kernels together are `ρ + oS + K_h i`, `i < D`, once each. -/
theorem synSel_vals {es : List ℕ} {ℓ K : ℕ} (_H : LayHyp es ℓ K)
    (ds : ComplexFramedExecution.Directions) {h n a w' R₂ Gd : ℕ}
    (hρ : synRh ℓ K h < synKh ℓ K h)
    (hpcs : ∀ pc ∈ synPcsR es ℓ K h, pc.Ok ds (synKh ℓ K h) n w' R₂ Gd)
    (hfitT : ∀ i < synQ es ℓ K h, synAT es ℓ K h + synRh ℓ K h + synKh ℓ K h * i < n + a)
    (hfitT₂ : ∀ i < synQ2 es ℓ K h,
      synOS es ℓ K h + synRh ℓ K h + synKh ℓ K h * i < n + a) :
    ((topSel a ((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList)
      (topTop (synAT es ℓ K h) (synRh ℓ K h) (synKh ℓ K h) (synQ es ℓ K h) (n + a) hfitT ++
        topTop (synOS es ℓ K h) (synRh ℓ K h) (synKh ℓ K h) (synQ2 es ℓ K h) (n + a)
          hfitT₂)).map Fin.val).Perm
      ((List.range (synDp es ℓ h)).map fun i =>
        synRh ℓ K h + synOS es ℓ K h + synKh ℓ K h * i) := by
  have e1 : (topSel a ((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList)
      (topTop (synAT es ℓ K h) (synRh ℓ K h) (synKh ℓ K h) (synQ es ℓ K h) (n + a) hfitT ++
        topTop (synOS es ℓ K h) (synRh ℓ K h) (synKh ℓ K h) (synQ2 es ℓ K h) (n + a)
          hfitT₂)).map Fin.val =
      (synPcsR es ℓ K h).flatMap (synPcVals (synRh ℓ K h) (synKh ℓ K h)) ++
        (((List.range (synQ es ℓ K h)).map fun i =>
            synAT es ℓ K h + synRh ℓ K h + synKh ℓ K h * i) ++
          (List.range (synQ2 es ℓ K h)).map fun i =>
            synOS es ℓ K h + synRh ℓ K h + synKh ℓ K h * i) := by
    rw [topSel, List.map_append, List.map_append, List.map_map]
    have : (Fin.val ∘ Fin.castAdd a) = (Fin.val : Fin n → ℕ) := rfl
    rw [this, topPieces_vals, topTop, topTop, map_val_actMap, map_val_actMap]
  rw [e1]
  by_cases hc : synChunk ℓ K h
  · have hq : synQ es ℓ K h = synQB es K := by simp [synQ, hc]
    have hq₂ : synQ2 es ℓ K h = synQF es K := by simp [synQ2, hc]
    have hD : synDp es ℓ h = synQF es K + (synDpp es K + synQB es K) := by
      have := synDpp_add_synQB_add_synQF es K
      simp only [synDp, hc.1, if_true]
      omega
    have hat : synAT es ℓ K h = synOS es ℓ K h + K * (synQF es K + synDpp es K) := by
      simp [synAT, hc]
    have hKh : synKh ℓ K h = K := by simp [synKh, hc]
    rw [hq, hq₂, hD, hat, hKh, range_add_map, range_add_map]
    simp only [synPcsR, hc, if_true]
    rw [← List.append_assoc]
    refine List.Perm.trans (List.Perm.append (List.Perm.append
      ((synPcs_vals_full _ _ _ _ _ _).trans (List.Perm.of_eq ?_)) (List.Perm.of_eq ?_))
      (List.Perm.of_eq ?_)) List.perm_append_comm
    all_goals
      refine List.map_congr_left fun i _ => ?_
      try simp only [synOP]
      ring
  · have hp : synPcsR es ℓ K h = [] := by simp [synPcsR, hc]
    have hq : synQ es ℓ K h = synDp es ℓ h := by simp [synQ, hc]
    have hq₂ : synQ2 es ℓ K h = 0 := by simp [synQ2, hc]
    rw [hp, hq, hq₂]
    simp only [List.flatMap_nil, List.nil_append, List.range_zero, List.map_nil,
      List.append_nil]
    refine List.Perm.of_eq (List.map_congr_left fun i _ => ?_)
    simp [synAT, synRh, synKh, hc]

/-- **The layer of round `h`.** With the records of round `h` on `park` and `ph .arr`
(`TopIn`), the layer machine at rest for `N` address bits, `2^l` coefficients, words of
`w' = synW2` symbols and the control width `Gd = synGd N` (`TopRegs`), and the stream of the
physical numerator records `Y` (modulus at most `2^p`, `p + 2 ≤ w`) on `io`, `topProg` leaves on
`io` the stream of the componentwise truncation toward zero of the normalized butterflies on the
physical selected bits of the round in the layout `L = layPerm es ℓ K`. The compact slot XORs
of the pieces need `Gd + 3 ≤ K` once a piece has a node, which needs `D ≥ m` (`hGK`). -/
theorem synLayer_runs (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (hGK : m ≤ es.length → synGd es.sum + 3 ≤ K)
    {l w p h : ℕ} (hh : h + 1 ≤ ℓ)
    (hpw : p + 2 ≤ w) (Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hY : ∀ x c, ‖GaussianInt.toComplex (Y x c)‖ ≤ 2 ^ p)
    (R : Fin (nT CReg) → List (Fin (prime + Ka + 4)))
    (hT : TopRegs R es.sum (2 ^ l)
      (synW2 es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h)
      (synKh ℓ K h) (synRh ℓ K h) (synGd es.sum))
    (hI : TopIn R (synCfg es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h)
      (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h)))
    (hio : R (reg (BReg := CReg) .io) = cstream (prime + Ka) w (rpStream (2 ^ es.sum) Y)) :
    LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) topProg R
      (Function.update R (reg (BReg := CReg) .io) (cstream (prime + Ka) w (rpStream (2 ^ es.sum)
        (synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)))))))
      (synLayerCost ds es ℓ K l w h) := by
  intro v S hL hS
  set a := synAR es ℓ K h with ha
  set n := es.sum - a with hn
  set Gd := synGd es.sum with hGd
  have hna : n + a = es.sum := Nat.sub_add_cancel (synAR_le H h)
  have hK1 : 1 ≤ synKh ℓ K h := synKh_pos H.K_pos
  have hρ : synRh ℓ K h < synKh ℓ K h := synRh_lt H.K_pos
  have hAN : synA es ℓ K ≤ es.sum := synA_le H
  have hOS := synOS_le H h
  have hpcs : ∀ pc ∈ synPcsR es ℓ K h,
      pc.Ok ds (synKh ℓ K h) n
        (synW2 es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h)
        (synR2 es ℓ K h) Gd := by
    by_cases hc : synChunk ℓ K h
    · simp only [synPcsR, hc, if_true, synKh]
      rw [synR2_chunk es ℓ K hc]
      have hf := synChunk_fit H hc
      have hmul := synK_mul_split es K
      have hle := synK_mul_le es K
      have hsub : K * (synQB es K - synQK es) + K * synQK es = K * synQB es K := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (synQK_le_synQB es K)]
      have hDl : synDpp es K ≤ es.length := by
        have := synDpp_add_synQB_add_synQF es K; omega
      have hG6 : 6 ≤ Gd := by rw [hGd]; unfold synGd; omega
      -- the reservation is full when there are piece bits
      have hres : synDpp es K * Gd ≤ K * synQF es K ∧
          3 * (synDpp es K * Gd) ≤ K * (synQB es K - synQK es) := by
        by_cases hD0 : synDpp es K = 0
        · simp [hD0]
        obtain ⟨hF, hB⟩ := synQF_synQB_of_synDpp_ne_zero es K hD0
        have hR : K * synQB es K - K * synQK es = K * synQR es K := by
          rw [hB, Nat.mul_add]; omega
        have hlt : 3 * es.length * Gd < K * synQR es K := by
          simp only [synQR, synQRn, ← hGd]
          exact Nat.lt_mul_div_succ _ H.K_pos
        have h1 : synDpp es K * Gd ≤ es.length * Gd := Nat.mul_le_mul_right _ hDl
        have h3 : 3 * es.length * Gd = 3 * (es.length * Gd) := by ring
        rw [hF]
        omega
      apply synPcs_ok (H := K * (synQB es K - synQK es))
      · rw [hn, ha]
        simp only [synAR, hc, if_true, synAc, synOP]
        omega
      · simp only [synOP]
        omega
      · exact hres.2
      · intro hmD
        exact ⟨by omega, hGK (le_trans hmD hDl)⟩
      · simp only [synW2, synS, synER, hc, if_true]
        omega
    · simp [synPcsR, hc]
  have hfitT : ∀ i < synQ es ℓ K h, synAT es ℓ K h + synRh ℓ K h + synKh ℓ K h * i < n + a := by
    intro i hi
    rw [hna]
    by_cases hc : synChunk ℓ K h
    · simp only [synQ, synAT, synRh, synKh, hc, if_true] at hi ⊢
      have hf := synChunk_fit H hc
      have hmul := synK_mul_split es K
      have hρ' : (h - layB ℓ K) % K < K := Nat.mod_lt _ H.K_pos
      have h1 : K * (i + 1) ≤ K * synQB es K := Nat.mul_le_mul_left _ hi
      rw [Nat.mul_succ] at h1
      rw [Nat.mul_add]
      omega
    · simp only [synQ, synAT, synRh, synKh, hc, if_false] at hi ⊢
      unfold synA at hAN
      by_cases ht : h + 1 < ℓ
      · have hl : h < layB ℓ K := by unfold synChunk at hc; omega
        simp only [synDp, synOS, ht, hl, if_true] at hi ⊢
        have h1 : es.length ≤ (layB ℓ K - h) * es.length := Nat.le_mul_of_pos_left _ (by omega)
        have h2 : (layB ℓ K - h) * es.length ≤ layB ℓ K * es.length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · simp only [synDp, synOS, ht, if_false] at hi ⊢
        omega
  have hTL : synAT es ℓ K h + synKh ℓ K h * synQ es ℓ K h ≤ n + a := by
    rw [hna]
    by_cases hc : synChunk ℓ K h
    · simp only [synQ, synAT, synKh, hc, if_true]
      have hf := synChunk_fit H hc
      have hmul := synK_mul_split es K
      rw [Nat.mul_add]
      omega
    · simp only [synQ, synAT, synKh, hc, if_false, one_mul]
      unfold synA at hAN
      by_cases ht : h + 1 < ℓ
      · have hl : h < layB ℓ K := by unfold synChunk at hc; omega
        simp only [synDp, synOS, ht, hl, if_true]
        have h1 : es.length ≤ (layB ℓ K - h) * es.length := Nat.le_mul_of_pos_left _ (by omega)
        have h2 : (layB ℓ K - h) * es.length ≤ layB ℓ K * es.length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · simp only [synDp, synOS, ht, if_false]
        omega
  have hfitT₂ : ∀ i < synQ2 es ℓ K h,
      synOS es ℓ K h + synRh ℓ K h + synKh ℓ K h * i < n + a := by
    intro i hi
    rw [hna]
    by_cases hc : synChunk ℓ K h
    · simp only [synQ2, synRh, synKh, hc, if_true] at hi ⊢
      have hf := synChunk_fit H hc
      have hmul := synK_mul_split es K
      have hρ' : (h - layB ℓ K) % K < K := Nat.mod_lt _ H.K_pos
      have h1 : K * (i + 1) ≤ K * synQF es K := Nat.mul_le_mul_left _ hi
      rw [Nat.mul_succ] at h1
      omega
    · simp [synQ2, hc] at hi
  have hTL₂ : synOS es ℓ K h + synKh ℓ K h * synQ2 es ℓ K h ≤ n + a := by
    rw [hna]
    by_cases hc : synChunk ℓ K h
    · simp only [synQ2, synKh, hc, if_true]
      have hf := synChunk_fit H hc
      have hmul := synK_mul_split es K
      omega
    · simp only [synQ2, hc, if_false, mul_zero, add_zero]
      exact hOS
  have hR₂ : 1 * 2 ^ a ≤ synR2 es ℓ K h := by
    rw [one_mul, ha]
    unfold synR2 synAR
    split_ifs
    · exact synR2c_ge es ℓ K H.K_pos
    · exact le_rfl
  have hinj : ∀ P ∈ topPieces hρ (synPcsR es ℓ K h) hpcs, Function.Injective P.e := by
    intro P hP
    have : ∀ (pcs : List TopPc) (h' : ∀ pc ∈ pcs, pc.Ok ds (synKh ℓ K h) n
        (synW2 es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h) (synR2 es ℓ K h)
        Gd),
        ∀ P ∈ topPieces hρ pcs h', Function.Injective P.e := by
      intro pcs
      induction pcs with
      | nil => intro _ P hP; simp [topPieces] at hP
      | cons pc pcs ih =>
          intro h' P hP
          rw [topPieces, List.mem_cons] at hP
          rcases hP with rfl | hP
          · simp only [TopPc.piece]
            exact actMap_injective hK1 _
          · exact ih _ P hP
    exact this _ hpcs P hP
  have hvals := synSel_vals (n := n) (a := a) H ds hρ hpcs hfitT hfitT₂
  set top := topTop (synAT es ℓ K h) (synRh ℓ K h) (synKh ℓ K h) (synQ es ℓ K h) (n + a) hfitT ++
    topTop (synOS es ℓ K h) (synRh ℓ K h) (synKh ℓ K h) (synQ2 es ℓ K h) (n + a) hfitT₂
    with htop
  set sel := topSel a ((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList) top
    with hsel
  have hnodupT : ((List.range (synDp es ℓ h)).map fun i =>
      synRh ℓ K h + synOS es ℓ K h + synKh ℓ K h * i).Nodup := by
    refine List.nodup_range.map fun i j hij => ?_
    have : synKh ℓ K h * i = synKh ℓ K h * j := by simpa using hij
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hselnd : (sel.map Fin.val).Nodup := hvals.nodup_iff.2 hnodupT
  have hselN : sel.Nodup := List.Nodup.of_map _ hselnd
  have hselm : ∀ t : Fin (n + a), t ∈ sel ↔
      ∃ i < synDp es ℓ h, (t : ℕ) = synRh ℓ K h + synOS es ℓ K h + synKh ℓ K h * i := by
    intro t
    constructor
    · intro ht
      have := hvals.mem_iff.1 (List.mem_map_of_mem (f := Fin.val) ht)
      simp only [List.mem_map, List.mem_range] at this
      obtain ⟨i, hi, he⟩ := this
      exact ⟨i, hi, he.symm⟩
    · rintro ⟨i, hi, he⟩
      have : (t : ℕ) ∈ sel.map Fin.val := hvals.mem_iff.2 (by
        simp only [List.mem_map, List.mem_range]; exact ⟨i, hi, he.symm⟩)
      obtain ⟨t', ht', e⟩ := List.mem_map.1 this
      rwa [Fin.ext e] at ht'
  have hD : sel.length = synDp es ℓ h := by
    have := hvals.length_eq; simpa using this
  have hphys : (sel.map Fin.val).Perm ((selBits es h).map (twPosL (layPerm es ℓ K))) := by
    refine hvals.trans ?_
    by_cases hc : synChunk ℓ K h
    · have := (synSel_chunk H hc).symm
      have hDp : synDp es ℓ h = es.length := by simp [synDp, hc.1]
      have hKh : synKh ℓ K h = K := by simp [synKh, hc]
      rw [hDp, hKh]
      exact this
    · by_cases ht : h + 1 < ℓ
      · have hl : h < layB ℓ K := by unfold synChunk at hc; omega
        refine List.Perm.trans (List.Perm.of_eq ?_) (synSel_low H hl).symm
        simp only [synDp, synRh, synOS, synKh, ht, hl, hc, if_true, if_false]
        refine List.map_congr_left fun i _ => ?_
        ring
      · refine List.Perm.trans (List.Perm.of_eq ?_) (synSel_top H ht hh).symm
        simp only [synDp, synRh, synOS, synKh, ht, hc, if_false]
        refine List.map_congr_left fun i _ => ?_
        ring
  have htl : top.length = synQ es ℓ K h + synQ2 es ℓ K h := by simp [htop, topTop]
  have hs : synS es ℓ K (gateCount (program ds)) (factorCount (program ds)) h =
      (((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList).length +
        (synQ es ℓ K h + synQ2 es ℓ K h) + 1) / 2 + (synQ es ℓ K h + synQ2 es ℓ K h) +
        ((topPieces hρ (synPcsR es ℓ K h) hpcs).map (Piece.exp ds)).sum := by
    have hl : ((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList).length +
        (synQ es ℓ K h + synQ2 es ℓ K h) = synDp es ℓ h := by
      rw [← hD, hsel, topSel, List.length_append, List.length_map, htl]
    rw [hl, topPieces_exp]
    unfold synS synER
    by_cases hc : synChunk ℓ K h
    · simp only [hc, if_true, synPcsR]
      rw [synPcs_exp_sum]
    · simp [hc, synPcsR]
  have hZ : ∀ q, TopFitsZ w (synZ (n + a) Y q) := fun q => topFitsZ_of_norm (hY _ _) hpw
  have hw' : synS es ℓ K (gateCount (program ds)) (factorCount (program ds)) h + p + 2 ≤
      synW2 es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h := by
    unfold synW2; omega
  have hX := topPre_fits ds hd a ((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList)
    top hR₂ (topPieces hρ (synPcsR es ℓ K h) hpcs) hinj (List.Perm.refl _) hselN _
    (by rw [htl]; exact hs) (synZ (n + a) Y) (fun q => hY _ _) hw'
  have hT' : TopRegs S.R (n + a) (2 ^ l)
      (synW2 es ℓ K (gateCount (program ds)) (factorCount (program ds)) w h)
      (synKh ℓ K h) (synRh ℓ K h) Gd := by rw [hS, hna]; exact hT
  have hI' : TopIn S.R (topCfg w (synS es ℓ K (gateCount (program ds))
      (factorCount (program ds)) h) a 1 (synR2 es ℓ K h) (synQ es ℓ K h) (synAT es ℓ K h)
      (synKh ℓ K h) (synOS es ℓ K h) (synDp es ℓ h) (synQ2 es ℓ K h) (synOS es ℓ K h))
      (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h)) :=
    by rw [hS]; exact hI
  have hio' : S.R (reg (BReg := CReg) .io) = encZ (prime + Ka) w (synZ (n + a) Y) := by
    rw [hS, hio, encZ_synZ, hna]
  obtain ⟨v', c, hu, hc, he⟩ := topProg_exec_Hl (U := U) hQ ds hd hA hA9 hNW hgate
    ((topPieces hρ (synPcsR es ℓ K h) hpcs).flatMap Piece.bitsList) (synPcsR es ℓ K h)
    (Nat.one_le_two_pow) (by omega) (by unfold synW2; omega) hρ le_rfl hfitT hTL hfitT₂ hTL₂
    hR₂ hpcs hinj (List.Perm.refl _) hselm hselN hD hs (synZ (n + a) Y) hZ hX v S hL
    hT' hI' hio'
  have hH := Hl_synZ (n := n + a) Y sel
  have e1 : (fun q : (Fin 1 × Fin (2 ^ l)) × (Fin (n + a) → ZMod 2) =>
      (⟨IntegerMultBounds.MathlibTM2.Layer.truncR ((Hl _ sel (toC (synZ (n + a) Y))) q).re,
        IntegerMultBounds.MathlibTM2.Layer.truncR ((Hl _ sel (toC (synZ (n + a) Y))) q).im⟩ : GaussianInt)) =
      synZ (n + a) (synTrunc (bflyL (sel.map Fin.val)
        (fun x c => GaussianInt.toComplex (Y x c)))) := by
    funext q
    rw [hH]
    rfl
  have hio_eq := congrArg (encZ (prime + Ka) w) e1
  rw [encZ_synZ, bflyL_perm hphys hselnd] at hio_eq
  refine ⟨v', c, hu, hc.trans (topCost_indep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).le,
    Exec.cast he rfl ?_⟩
  rw [hS, hio_eq, hna]

end LayerRound

end IntegerMultBounds.MathlibTM2.Fast
