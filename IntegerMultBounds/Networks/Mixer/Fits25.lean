module

public import IntegerMultBounds.Networks.Mixer.Instance25
public import IntegerMultBounds.Networks.Mixer.Enclosure
public import IntegerMultBounds.Networks.Mixer.Residuals

/-! The label hypotheses of the size-25 mixer network. Rectangle `k` carries the
enclosure `encl (sources k) (targets k)` in the forward stages and the swapped
enclosure in the inverse stage; every role's growth along its label chain is
certified by `Mixer.Enclosure`. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Fits25

open Instance25 Scalar GlobalBinaryResiduals

/-- Forward rectangle enclosures. -/
noncomputable def U (k : Fin K25) : Submodule (ZMod 2) (Fin 25 → ZMod 2) :=
  Enclosure.encl (rect k).1 (rect k).2

/-- Inverse rectangle enclosures. -/
noncomputable def U' (k : Fin K25) : Submodule (ZMod 2) (Fin 25 → ZMod 2) :=
  Enclosure.encl (rect k).2 (rect k).1

/-- Triple indicator vectors in local data indices. -/
noncomputable abbrev t (i : Fin 2300) : Fin 25 → ZMod 2 := Labels.indicator (L i)

/-- The injection matrix of the size-25 mixer invocation. -/
noncomputable abbrev J : Fin 2300 → Fin a25 → ℚ := injectMatrix kind weight

theorem weight_ne {p : Fin a25} (h : (kind p).target ≠ none) : weight p ≠ 0 := by
  unfold weight
  unfold kind at h
  rcases hp : sideEquiv p with σ | τ | d <;> rw [hp] at h <;>
    simp [kindOf, weightOf, Kind.target] at h ⊢

theorem support (i : Fin 2300) (p : Fin a25) : J i p ≠ 0 ↔ (kind p).target = some i := by
  simp only [J, injectMatrix]
  constructor
  · intro h
    by_contra hne
    exact h (if_neg hne)
  · intro h
    rw [if_pos h]
    exact weight_ne (by rw [h]; simp)

theorem out_exists (k : Fin K25) : ∃ p, (kind p).outRect = some k := by
  obtain ⟨T, hT⟩ := (rect_valid k).targets_nonempty
  refine ⟨sideEquiv.symm (.inr (.inl ⟨k, ⟨T, hT⟩⟩)), ?_⟩
  simp [kind, kindOf, Kind.outRect]

theorem U_nondegenerate (k : Fin K25) : ((Labels.binary 25).restrict (U k)).Nondegenerate :=
  Enclosure.encl_nondegenerate (rect_valid k)

theorem U'_nondegenerate (k : Fin K25) : ((Labels.binary 25).restrict (U' k)).Nondegenerate :=
  Enclosure.encl_nondegenerate (rect_valid k).swap

theorem hh : 6 < 25 := by norm_num

/-- Certified growth along every rectangle chain, in both orientations. -/
theorem enclosureFit : Residuals.EnclosureFit t kind U U' where
  input_line hp := Enclosure.up_line hh (rect_valid _) (kind_input hp)
  input_top _ := Enclosure.up_top hh (rect_valid _)
  output_bot _ := Enclosure.up_bot hh (rect_valid _)
  output_compl hp := Enclosure.up_compl hh (rect_valid _) (kind_output hp)
  inverse_input_bot _ := Enclosure.up_bot hh (rect_valid _).swap
  inverse_input_compl hp := Enclosure.up_compl hh (rect_valid _).swap (kind_input hp)
  inverse_output_line hp := Enclosure.up_line hh (rect_valid _).swap (kind_output hp)
  inverse_output_top _ := Enclosure.up_top hh (rect_valid _).swap

theorem direct_even {p : Fin a25} {i j : Fin 2300} (hp : kind p = .direct i j) :
    Even (L i ∩ L j).card := by
  rw [kind_direct hp]
  exact even_two

theorem direct_orth {p : Fin a25} {i j : Fin 2300} (hp : kind p = .direct i j) :
    Labels.binary 25 (t i) (t j) = 0 :=
  Labels.binary_neighbors _ _ (direct_even hp)

theorem direct_orth' {p : Fin a25} {i j : Fin 2300} (hp : kind p = .direct i j) :
    Labels.binary 25 (t j) (t i) = 0 := by
  rw [Labels.binary, Labels.form_symm]
  exact direct_orth hp

theorem input_le {p : Fin a25} {k : Fin K25} {i : Fin 2300} (hp : kind p = .input k i) :
    (ZMod 2) ∙ t i ≤ U k := (enclosureFit.input_line hp).le _

theorem output_le {p : Fin a25} {k : Fin K25} {j : Fin 2300} (hp : kind p = .output k j) :
    U k ≤ (Labels.binary 25).orthogonal ((ZMod 2) ∙ t j) := (enclosureFit.output_compl hp).le _

theorem inverse_input_le {p : Fin a25} {k : Fin K25} {i : Fin 2300} (hp : kind p = .input k i) :
    U' k ≤ (Labels.binary 25).orthogonal ((ZMod 2) ∙ t i) :=
  (enclosureFit.inverse_input_compl hp).le _

theorem inverse_output_le {p : Fin a25} {k : Fin K25} {j : Fin 2300}
    (hp : kind p = .output k j) : (ZMod 2) ∙ t j ≤ U' k :=
  (enclosureFit.inverse_output_line hp).le _

end IntegerMultBounds.Networks.Mixer.Fits25
