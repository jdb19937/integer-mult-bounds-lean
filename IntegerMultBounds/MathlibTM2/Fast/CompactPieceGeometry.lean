module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection

/-! Root layouts of the actual serialized and row-rebased compact pieces. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity
noncomputable section

/-- Every actual piece starts at or above the original selected offset. -/
theorem compactTopPcs_offset {d g K D o R₂ : ℕ} {pc : TopPc}
    (hpc : pc∈compactTopPcs d g K D o R₂) : o≤pc.a₀ := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hpc
  rcases List.mem_append.1 hq with hb | ha
  · by_cases hz : backChunks d g K=0
    · simp [hz] at hb
    · simp only [hz,ite_false,List.mem_singleton] at hb
      subst q
      simp [compactRebasePc]
  · obtain ⟨j,_,_,rfl⟩ := mem_synPcs ha
    simp only [compactRebasePc,synPc]
    omega

/-- Every positive-level piece has a literal root layout in the shared shape.
The back-reservation record is a leaf, so it never needs a compact node layout. -/
theorem compactTopPcs_layout {d g K D o R₂ payload ρ j : ℕ} {pc : TopPc}
    (hK : 0<K) (h : CompactReservationFits d g K D) (hD : D≤d) (hρ : ρ<K)
    (hpc : pc∈compactTopPcs d g K D o R₂) (hj : pc.j=j+1) :
    ∃ left right, CompactRecursiveLayout (compactReservationShape d g K D payload)
      (K*(D-CompactGlobalRowPadding.rowAxes NW m d)) (pc.a₀-o)
      (bits pc.u j) ρ left right := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hpc
  rcases List.mem_append.1 hq with hb | ha
  · by_cases hz : backChunks d g K=0
    · simp [hz] at hb
    · simp only [hz,ite_false,List.mem_singleton] at hb
      subst q
      simp [compactRebasePc] at hj
  · obtain ⟨i,_,h0,rfl⟩ := mem_synPcs ha
    change i=j+1 at hj
    subst i
    refine ⟨compactReservationActive d g K D-compactReservationActive d g K D % m^(j+1)-
      m*bits (synDg (compactReservationActive d g K D) (j+1)) j,
      compactReservationActive d g K D % m^(j+1),?_⟩
    simpa [compactRebasePc,synPc,Nat.add_assoc] using
      (compactReservationDigitLayout (payload:=payload) hK h hD hρ h0)

/-- The reserved row-bit allowance places every top kernel inside the original
address, including its complete slot extent. -/
theorem compactTopKernel_geometry {d g K D o a ρ : ℕ}
    (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a) :
    (∀ i<compactTopKernelCount d g K,
      compactTopKernelOffset d g K D o+ρ+K*i<o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)+a) ∧
    compactTopKernelOffset d g K D o+K*compactTopKernelCount d g K≤
      o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)+a := by
  have hq : CompactGlobalRowPadding.rowAxes NW m d≤D := by
    have := compactReservation_axes h
    omega
  have he := congrArg (fun x => K*x) (Nat.sub_add_cancel hq)
  simp only [Nat.mul_add] at he
  have hf : o+K*D≤o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)+a := by
    rw [Nat.mul_comm] at ha
    omega
  refine ⟨compactTopKernel_fits h hρ hf,?_⟩
  rw [compactTopKernel_end h]
  exact hf

end
end IntegerMultBounds.MathlibTM2.Fast
