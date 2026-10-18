module

public import IntegerMultBounds.Networks.GlobalBinaryResiduals
public import IntegerMultBounds.Networks.NeighborResidual

/-! Enclosure labels for a rectangle of disjoint triples in the binary label
space `Fin h → ZMod 2`. A rectangle with one source uses that source's line, a
rectangle with one target uses that target's orthogonal complement, and any
other rectangle uses the coordinate subspace on the union of its sources.
Each source line grows into the enclosure and the enclosure grows into each
target complement, with a norm-one vector in every nonzero residual. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Enclosure

open Labels NeighborResidual GlobalBinaryResiduals

variable {h : ℕ}

/-- Vectors vanishing outside `A`. -/
def coord (A : Finset (Fin h)) : Submodule (ZMod 2) (Fin h → ZMod 2) where
  carrier := {x | ∀ i, i ∉ A → x i = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

theorem mem_coord {A : Finset (Fin h)} {x : Fin h → ZMod 2} :
    x ∈ coord A ↔ ∀ i, i ∉ A → x i = 0 := Iff.rfl

/-- The enclosure label of a rectangle with source family `𝒮` and target family `𝒰`. -/
def encl (𝒮 𝒰 : Finset (Finset (Fin h))) : Submodule (ZMod 2) (Fin h → ZMod 2) :=
  if 𝒮.card = 1 then (ZMod 2) ∙ indicator (𝒮.sup id)
  else if 𝒰.card = 1 then (binary h).orthogonal ((ZMod 2) ∙ indicator (𝒰.sup id))
  else coord (𝒮.sup id)

/-- The facts about a rectangle used by its enclosure label. -/
structure Valid (𝒮 𝒰 : Finset (Finset (Fin h))) : Prop where
  sources_card : ∀ S ∈ 𝒮, S.card = 3
  targets_card : ∀ T ∈ 𝒰, T.card = 3
  disjoint : ∀ S ∈ 𝒮, ∀ T ∈ 𝒰, Disjoint S T
  sources_nonempty : 𝒮.Nonempty
  targets_nonempty : 𝒰.Nonempty

/-- Exchanging sources and targets preserves validity, for the inverse stage. -/
theorem Valid.swap {𝒮 𝒰 : Finset (Finset (Fin h))} (hv : Valid 𝒮 𝒰) : Valid 𝒰 𝒮 :=
  ⟨hv.targets_card, hv.sources_card, fun T hT S hS => (hv.disjoint S hS T hT).symm,
    hv.targets_nonempty, hv.sources_nonempty⟩

/-! ### Elementary pairings -/

theorem binary_symm : (binary h).IsSymm := ⟨form_symm 0⟩

theorem binary_comm (x y : Fin h → ZMod 2) : binary h x y = binary h y x := form_symm 0 x y

theorem binary_single (x : Fin h → ZMod 2) (i : Fin h) : binary h x (Pi.single i 1) = x i := by
  simp [binary, form_single]

theorem single_mem_coord {A : Finset (Fin h)} {i : Fin h} (hi : i ∈ A) :
    (Pi.single i 1 : Fin h → ZMod 2) ∈ coord A := by
  intro j hj
  have hji : j ≠ i := fun hji => hj (hji ▸ hi)
  simp [hji]

theorem single_orthogonal_coord {A : Finset (Fin h)} {i : Fin h} (hi : i ∉ A) :
    (Pi.single i 1 : Fin h → ZMod 2) ∈ (binary h).orthogonal (coord A) := by
  intro x hx
  rw [binary_single]
  exact hx i hi

theorem indicator_mem_coord {A S : Finset (Fin h)} (hS : S ⊆ A) :
    (indicator S : Fin h → ZMod 2) ∈ coord A := by
  intro i hi
  have : i ∉ S := fun h => hi (hS h)
  simp [indicator, this]

theorem coord_orthogonal_indicator {A T : Finset (Fin h)} (hd : Disjoint A T)
    {x : Fin h → ZMod 2} (hx : x ∈ coord A) : binary h (indicator T) x = 0 := by
  rw [binary, form_apply]
  have hz : ∑ i, (indicator T i : ZMod 2) * x i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ T
    · rw [hx i (Finset.disjoint_right.mp hd hi), mul_zero]
    · simp [indicator, hi]
  rw [hz, zero_mul, zero_mul, sub_zero]

theorem mem_orthogonal_line {v x : Fin h → ZMod 2} (hvx : binary h v x = 0) :
    x ∈ (binary h).orthogonal ((ZMod 2) ∙ v) := by
  intro n hn
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
  simp [hvx]

theorem mem_orthogonal_bot (x : Fin h → ZMod 2) : x ∈ (binary h).orthogonal ⊥ := by
  simp

theorem indicator_norm {S : Finset (Fin h)} (hs : S.card = 3) :
    binary h (indicator S) (indicator S) = 1 := binary_self S hs

theorem disjoint_pairing {S T : Finset (Fin h)} (hd : Disjoint S T) :
    binary h (indicator S) (indicator T) = 0 :=
  binary_neighbors S T (by rw [Finset.disjoint_iff_inter_eq_empty.mp hd]; exact ⟨0, rfl⟩)

/-- Certified growth from a vector in the larger space orthogonal to the smaller one. -/
theorem up_of_unit {U V : Submodule (ZMod 2) (Fin h → ZMod 2)} (hle : U ≤ V)
    (x : Fin h → ZMod 2) (hxV : x ∈ V) (hxU : x ∈ (binary h).orthogonal U)
    (hx : binary h x x = 1) : Up (binary h) U V :=
  Or.inr ⟨hle, ⟨⟨x, Submodule.mem_inf.mpr ⟨hxV, hxU⟩⟩, hx⟩⟩

theorem coordinate_outside {S : Finset (Fin h)} (hs : S.card < h) : ∃ i : Fin h, i ∉ S :=
  exists_coordinate_outside S hs

theorem coord_nondegenerate (A : Finset (Fin h)) :
    ((binary h).restrict (coord A)).Nondegenerate := by
  have hl : ((binary h).restrict (coord A)).SeparatingLeft := by
    rintro ⟨x, hx⟩ hxy
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ A
    · have := hxy ⟨Pi.single i 1, single_mem_coord hi⟩
      simpa [binary_single] using this
    · exact hx i hi
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  change binary h (x : Fin h → ZMod 2) y = 0
  rw [binary_comm]
  exact hx y

/-! ### Case facts -/

theorem sup_singleton_eq {𝒮 : Finset (Finset (Fin h))} (h1 : 𝒮.card = 1) :
    ∃ S, 𝒮 = {S} ∧ 𝒮.sup id = S := by
  obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp h1
  exact ⟨S, rfl, by simp⟩

theorem le_sup_of_mem {𝒮 : Finset (Finset (Fin h))} {S : Finset (Fin h)} (hS : S ∈ 𝒮) :
    S ⊆ 𝒮.sup id := Finset.le_sup (f := id) hS

theorem sup_disjoint {𝒮 𝒰 : Finset (Finset (Fin h))} (hv : Valid 𝒮 𝒰) {T : Finset (Fin h)}
    (hT : T ∈ 𝒰) : Disjoint (𝒮.sup id) T :=
  Finset.disjoint_sup_left.mpr fun S hS => hv.disjoint S hS T hT

/-- Two distinct triples differ in a point of the first. -/
theorem exists_mem_not_mem {S S' : Finset (Fin h)} (hs : S.card = 3) (hs' : S'.card = 3)
    (hne : S' ≠ S) : ∃ i ∈ S', i ∉ S := by
  by_contra! hall
  exact hne (Finset.eq_of_subset_of_card_le hall (by omega))

theorem two_le_card {𝒮 : Finset (Finset (Fin h))} (hne : 𝒮.Nonempty) (h1 : 𝒮.card ≠ 1) :
    1 < 𝒮.card := by
  have := hne.card_pos
  omega

/-! ### The five label facts -/

theorem encl_nondegenerate {𝒮 𝒰 : Finset (Finset (Fin h))} (hv : Valid 𝒮 𝒰) :
    ((binary h).restrict (encl 𝒮 𝒰)).Nondegenerate := by
  by_cases h1 : 𝒮.card = 1
  · rw [encl, if_pos h1]
    obtain ⟨S, rfl, hsup⟩ := sup_singleton_eq h1
    rw [hsup]
    exact binary_line_nondegenerate S (hv.sources_card S (by simp))
  by_cases h2 : 𝒰.card = 1
  · rw [encl, if_neg h1, if_pos h2]
    obtain ⟨T, rfl, hsup⟩ := sup_singleton_eq h2
    rw [hsup]
    exact ProjectionRank.orthogonal_nondegenerate _ binary_symm binary_nondegenerate _
      (binary_line_nondegenerate T (hv.targets_card T (by simp)))
  · rw [encl, if_neg h1, if_neg h2]
    exact coord_nondegenerate _

theorem up_line {𝒮 𝒰 : Finset (Finset (Fin h))} (hh : 6 < h) (hv : Valid 𝒮 𝒰)
    {S : Finset (Fin h)} (hS : S ∈ 𝒮) :
    Up (binary h) ((ZMod 2) ∙ indicator S) (encl 𝒮 𝒰) := by
  have hs := hv.sources_card S hS
  unfold encl
  split_ifs with h1 h2
  · obtain ⟨S₀, rfl, hsup⟩ := sup_singleton_eq h1
    rw [hsup]
    rw [Finset.mem_singleton.mp hS]
  · obtain ⟨T, rfl, hsup⟩ := sup_singleton_eq h2
    rw [hsup]
    have hT := hv.targets_card T (by simp)
    have hd := hv.disjoint S hS T (by simp)
    obtain ⟨i, hi⟩ := coordinate_outside (S := S ∪ T)
      (lt_of_le_of_lt (Finset.card_union_le S T) (by omega))
    refine up_of_unit ?_ (Pi.single i 1) ?_ ?_ (coordinate_norm i)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact mem_orthogonal_line (disjoint_pairing hd.symm)
    · exact coordinate_orthogonal T i (fun h => hi (Finset.mem_union_right S h))
    · exact coordinate_orthogonal S i (fun h => hi (Finset.mem_union_left T h))
  · obtain ⟨S', hS', hne⟩ := Finset.exists_mem_ne (two_le_card hv.sources_nonempty h1) S
    obtain ⟨i, hiS', hiS⟩ := exists_mem_not_mem hs (hv.sources_card S' hS') hne
    refine up_of_unit ?_ (Pi.single i 1) ?_ ?_ (coordinate_norm i)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact indicator_mem_coord (le_sup_of_mem hS)
    · exact single_mem_coord (le_sup_of_mem hS' hiS')
    · exact coordinate_orthogonal S i hiS

theorem up_compl {𝒮 𝒰 : Finset (Finset (Fin h))} (hh : 6 < h) (hv : Valid 𝒮 𝒰)
    {T : Finset (Fin h)} (hT : T ∈ 𝒰) :
    Up (binary h) (encl 𝒮 𝒰) ((binary h).orthogonal ((ZMod 2) ∙ indicator T)) := by
  have ht := hv.targets_card T hT
  unfold encl
  split_ifs with h1 h2
  · obtain ⟨S, rfl, hsup⟩ := sup_singleton_eq h1
    rw [hsup]
    have hs := hv.sources_card S (by simp)
    have hd := hv.disjoint S (by simp) T hT
    obtain ⟨i, hi⟩ := coordinate_outside (S := S ∪ T)
      (lt_of_le_of_lt (Finset.card_union_le S T) (by omega))
    refine up_of_unit ?_ (Pi.single i 1) ?_ ?_ (coordinate_norm i)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact mem_orthogonal_line (disjoint_pairing hd.symm)
    · exact coordinate_orthogonal T i (fun h => hi (Finset.mem_union_right S h))
    · exact coordinate_orthogonal S i (fun h => hi (Finset.mem_union_left T h))
  · obtain ⟨T₀, rfl, hsup⟩ := sup_singleton_eq h2
    rw [hsup, Finset.mem_singleton.mp hT]
  · obtain ⟨T', hT', hne⟩ := Finset.exists_mem_ne (two_le_card hv.targets_nonempty h2) T
    obtain ⟨i, hiT', hiT⟩ := exists_mem_not_mem ht (hv.targets_card T' hT') hne
    have hiA : i ∉ 𝒮.sup id := Finset.disjoint_right.mp (sup_disjoint hv hT') hiT'
    refine up_of_unit ?_ (Pi.single i 1) ?_ ?_ (coordinate_norm i)
    · intro x hx
      exact mem_orthogonal_line (coord_orthogonal_indicator (sup_disjoint hv hT) hx)
    · exact coordinate_orthogonal T i hiT
    · exact single_orthogonal_coord hiA

theorem up_bot {𝒮 𝒰 : Finset (Finset (Fin h))} (hh : 6 < h) (hv : Valid 𝒮 𝒰) :
    Up (binary h) ⊥ (encl 𝒮 𝒰) := by
  unfold encl
  split_ifs with h1 h2
  · obtain ⟨S, rfl, hsup⟩ := sup_singleton_eq h1
    rw [hsup]
    have hs := hv.sources_card S (by simp)
    exact up_of_unit bot_le (indicator S) (Submodule.mem_span_singleton_self _)
      (mem_orthogonal_bot _) (indicator_norm hs)
  · obtain ⟨T, rfl, hsup⟩ := sup_singleton_eq h2
    rw [hsup]
    have ht := hv.targets_card T (by simp)
    obtain ⟨i, hi⟩ := coordinate_outside (S := T) (by omega)
    exact up_of_unit bot_le (Pi.single i 1) (coordinate_orthogonal T i hi)
      (mem_orthogonal_bot _) (coordinate_norm i)
  · obtain ⟨S, hS⟩ := hv.sources_nonempty
    have hs := hv.sources_card S hS
    obtain ⟨i, hi⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    exact up_of_unit bot_le (Pi.single i 1) (single_mem_coord (le_sup_of_mem hS hi))
      (mem_orthogonal_bot _) (coordinate_norm i)

theorem up_top {𝒮 𝒰 : Finset (Finset (Fin h))} (hh : 6 < h) (hv : Valid 𝒮 𝒰) :
    Up (binary h) (encl 𝒮 𝒰) ⊤ := by
  unfold encl
  split_ifs with h1 h2
  · obtain ⟨S, rfl, hsup⟩ := sup_singleton_eq h1
    rw [hsup]
    have hs := hv.sources_card S (by simp)
    obtain ⟨i, hi⟩ := coordinate_outside (S := S) (by omega)
    exact up_of_unit le_top (Pi.single i 1) Submodule.mem_top
      (coordinate_orthogonal S i hi) (coordinate_norm i)
  · obtain ⟨T, rfl, hsup⟩ := sup_singleton_eq h2
    rw [hsup]
    have ht := hv.targets_card T (by simp)
    refine up_of_unit le_top (indicator T) Submodule.mem_top ?_ (indicator_norm ht)
    intro n hn
    rw [binary_comm]
    exact hn _ (Submodule.mem_span_singleton_self _)
  · obtain ⟨T, hT⟩ := hv.targets_nonempty
    have ht := hv.targets_card T hT
    obtain ⟨i, hi⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    exact up_of_unit le_top (Pi.single i 1) Submodule.mem_top
      (single_orthogonal_coord (Finset.disjoint_right.mp (sup_disjoint hv hT) hi))
      (coordinate_norm i)

end IntegerMultBounds.Networks.Mixer.Enclosure
