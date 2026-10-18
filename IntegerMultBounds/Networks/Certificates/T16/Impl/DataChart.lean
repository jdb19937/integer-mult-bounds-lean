module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Data

/-! The charts of the data registers. At stage zero a data register is its family array: the
nine low basis vectors are local and the coordinate vectors exterior. At stage `s ≥ 1` the chart
exchanges the low basis vectors `B_1, …, B_8` with the eight coordinate vectors
`e_{9 + 8 (s-1) + i}` entering at this stage; `B_0` stays local and every other vector stays
exterior. Either way every frame splits through the chart. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Multiplicative

variable {P : PortData}

theorem portBasis_high (k : Fin 73) (hk : 9 ≤ k.val) : portBasis P k = Pi.single k 1 := by
  simp [portBasis, show ¬ k.val < 9 by omega]

theorem lowPart_single_high (k : Fin 73) (hk : 9 ≤ k.val) : lowPart (Pi.single k (1 : ZMod 2)) = 0 := by
  funext i
  simp only [lowPart, Pi.single_apply, Pi.zero_apply]
  refine ite_eq_right_iff.mpr fun e => ?_
  have := congrArg Fin.val e
  simp at this
  omega

theorem highPart_low (hP : portCheck P = true) (k : Fin 73) (hk : k.val < 9) :
    highPart (portBasis P k) = 0 := by
  funext j
  simp only [highPart, portBasis, hk, ite_true, Pi.zero_apply]
  exact decodeMask_high ((portFacts hP).low k hk) (by simp)

theorem portBasis_local (hP : portCheck P = true) (k : Fin 73) (hk : k.val < 9) :
    portBasis P k = padLow (lowPart (portBasis P k)) := by
  rw [padLow, ← highPart_low hP k hk, join_parts]

/-! ### Stage zero -/

theorem mem_lowIndices (k : Fin 73) : k ∈ lowIndices ↔ k.val < 9 := by simp [lowIndices]

theorem lowIndices_nodup : lowIndices.Nodup := (List.nodup_finRange 73).filter _

theorem refl_orth : IsOrth (LinearEquiv.refl (ZMod 2) Addr) := fun _ _ => rfl

/-- The split of a frame at stage zero. -/
noncomputable def split0 (hP : portCheck P = true) (f : Fin 73 → ZMod 4) :
    ChartSplit (LinearEquiv.refl (ZMod 2) Addr) (portBasis P) f :=
  ChartSplit.ofLocal _ refl_orth _ f lowIndices lowIndices_nodup
    (fun k hk => portBasis_local hP k ((mem_lowIndices k).mp hk))
    (fun k hk _ => by
      have h9 : 9 ≤ k.val := by rw [mem_lowIndices] at hk; omega
      change lowPart (portBasis P k) = 0
      rw [portBasis_high k h9, lowPart_single_high k h9])

/-! ### Stages one to eight -/

/-- The exchanged pairs `B_{i+1} + e_{entering i}`. -/
def stageSwap (P : PortData) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (i : Fin 8) : Addr :=
  portBasis P ⟨i.val + 1, by omega⟩ + Pi.single (entering s hs i) 1

theorem entering_injective (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) : Function.Injective (entering s hs) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [entering] at this
  exact Fin.ext (by omega)

theorem entering_ge (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (i : Fin 8) : 9 ≤ (entering s hs i).val := by
  simp only [entering]
  omega

/-- A low basis vector against a high coordinate vector. -/
theorem binary_low_high (hP : portCheck P = true) (k j : Fin 73) (hk : k.val < 9) (hj : 9 ≤ j.val) :
    Labels.binary 73 (portBasis P k) (Pi.single j 1) = 0 := by
  rw [binary_single]
  simp only [portBasis, hk, ite_true]
  exact decodeMask_high ((portFacts hP).low k hk) hj

theorem binary_high_low (hP : portCheck P = true) (k j : Fin 73) (hk : k.val < 9) (hj : 9 ≤ j.val) :
    Labels.binary 73 (Pi.single j 1) (portBasis P k) = 0 := by
  rw [Labels.binary, Labels.form_symm, ← Labels.binary, binary_low_high hP k j hk hj]

theorem binary_single_single (i j : Fin 73) :
    Labels.binary 73 (Pi.single i (1 : ZMod 2)) (Pi.single j 1) = if i = j then 1 else 0 := by
  rw [binary_single]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem stageSwap_isotropic (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (i j : Fin 8) :
    Labels.binary 73 (stageSwap P s hs i) (stageSwap P s hs j) = 0 := by
  have hB : ∀ i j, Labels.binary 73 (portBasis P i) (portBasis P j) = if i = j then 1 else 0 :=
      portBasis_orthonormal hP
  simp only [stageSwap, map_add, LinearMap.add_apply]
  rw [hB, binary_low_high hP _ _ (by simp; omega) (entering_ge s hs j),
    binary_high_low hP _ _ (by simp; omega) (entering_ge s hs i), binary_single_single]
  by_cases h : i = j
  · subst h; simp [CharTwo.add_self_eq_zero]
  · have h1 : (⟨i.val + 1, by omega⟩ : Fin 73) ≠ ⟨j.val + 1, by omega⟩ := by
      intro e; apply h; ext; simpa using congrArg Fin.val e
    have h2 : entering s hs i ≠ entering s hs j := fun e => h (entering_injective s hs e)
    simp [h1, h2]

/-- The chart of a data register at stage `s ≥ 1`. -/
noncomputable def stageChart (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) :
    Addr ≃ₗ[ZMod 2] Addr :=
  swapChart (stageSwap P s hs) (stageSwap_isotropic hP s hs)

theorem swapMap_of_pairing {n : ℕ} (w : Fin n → Addr) (x : Addr) (c : Fin n → ZMod 2)
    (hc : ∀ i, Labels.binary 73 x (w i) = c i) : swapMap w x = x + ∑ i, c i • w i := by
  simp [swapMap, hc]

theorem stageChart_low0 (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) :
    (stageChart hP s hs).symm (portBasis P 0) = portBasis P 0 := by
  rw [stageChart, swapChart_symm, swapChart_apply,
    swapMap_of_pairing _ _ (fun _ => 0) (fun i => ?_)]
  · simp
  · have hB : ∀ i j, Labels.binary 73 (portBasis P i) (portBasis P j) = if i = j then 1 else 0 :=
      portBasis_orthonormal hP
    simp only [stageSwap, map_add, hB]
    rw [binary_low_high hP 0 _ (by simp) (entering_ge s hs i)]
    have : (0 : Fin 73) ≠ ⟨i.val + 1, by omega⟩ := by
      intro e; have := congrArg Fin.val e; simp at this
    simp [this]

theorem stageChart_lowSucc (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (i : Fin 8) :
    (stageChart hP s hs).symm (portBasis P ⟨i.val + 1, by omega⟩) =
      Pi.single (entering s hs i) 1 := by
  rw [stageChart, swapChart_symm, swapChart_apply,
    swapMap_of_pairing _ _ (fun j => if j = i then 1 else 0) (fun j => ?_)]
  · simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      stageSwap]
    rw [← add_assoc, ZModModule.add_self, zero_add]
  · have hB : ∀ i j, Labels.binary 73 (portBasis P i) (portBasis P j) = if i = j then 1 else 0 :=
      portBasis_orthonormal hP
    simp only [stageSwap, map_add, hB]
    rw [binary_low_high hP _ _ (by simp; omega) (entering_ge s hs j)]
    by_cases h : j = i
    · subst h; simp
    · have h1 : (⟨i.val + 1, by omega⟩ : Fin 73) ≠ ⟨j.val + 1, by omega⟩ := by
        intro e; apply h; ext; have := congrArg Fin.val e; simp at this; omega
      simp [h1, h]

theorem stageChart_entering (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (i : Fin 8) :
    (stageChart hP s hs).symm (portBasis P (entering s hs i)) = portBasis P ⟨i.val + 1, by omega⟩ := by
  rw [portBasis_high _ (entering_ge s hs i), stageChart, swapChart_symm, swapChart_apply,
    swapMap_of_pairing _ _ (fun j => if j = i then 1 else 0) (fun j => ?_)]
  · simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      stageSwap]
    rw [add_comm (portBasis P _), ← add_assoc, ZModModule.add_self, zero_add]
  · simp only [stageSwap, map_add]
    rw [binary_high_low hP _ _ (by simp; omega) (entering_ge s hs i), binary_single_single]
    by_cases h : j = i
    · subst h; simp
    · have h2 : entering s hs i ≠ entering s hs j := fun e => h (entering_injective s hs e).symm
      simp [h2, h]

theorem stageChart_other (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (k : Fin 73)
    (hk : 9 ≤ k.val) (hne : ∀ i, k ≠ entering s hs i) :
    (stageChart hP s hs).symm (portBasis P k) = portBasis P k := by
  rw [portBasis_high k hk, stageChart, swapChart_symm, swapChart_apply,
    swapMap_of_pairing _ _ (fun _ => 0) (fun i => ?_)]
  · simp
  · simp only [stageSwap, map_add]
    rw [binary_high_low hP _ _ (by simp; omega) hk, binary_single_single]
    simp [hne i]

theorem stageChart_orth (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) :
    IsOrth (stageChart hP s hs) := swapChart_orth _ _

theorem stageIndices_nodup (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) : (stageIndices s hs).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, (List.nodup_finRange 8).map (entering_injective s hs)⟩
  simp only [List.mem_map, List.mem_finRange, true_and, not_exists]
  intro i e
  have := congrArg Fin.val e
  simp [entering] at this

/-- The split of a frame at stage `s ≥ 1`. -/
noncomputable def splitStage (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8)
    (f : Fin 73 → ZMod 4) : ChartSplit (stageChart hP s hs) (portBasis P) f :=
  ChartSplit.ofLocal _ (stageChart_orth hP s hs) _ f (stageIndices s hs) (stageIndices_nodup s hs)
    (fun k hk => by
      simp only [stageIndices, List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hk
      rcases hk with rfl | ⟨i, rfl⟩
      · rw [stageChart_low0]
        exact portBasis_local hP 0 (by simp)
      · rw [stageChart_entering]
        exact portBasis_local hP _ (by simp; omega))
    (fun k hk _ => by
      simp only [stageIndices, List.mem_cons, List.mem_map, List.mem_finRange, true_and,
        not_or, not_exists] at hk
      by_cases h9 : k.val < 9
      · have hk0 : k.val ≠ 0 := fun e => hk.1 (Fin.ext e)
        have e : k = ⟨(k.val - 1 : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [e, stageChart_lowSucc hP s hs ⟨k.val - 1, by omega⟩]
        exact lowPart_single_high _ (entering_ge s hs _)
      · rw [stageChart_other hP s hs k (by omega) (fun i e => hk.2 i e.symm),
          portBasis_high k (by omega)]
        exact lowPart_single_high k (by omega))

end IntegerMultBounds.Networks.Certificates.T16.Impl
