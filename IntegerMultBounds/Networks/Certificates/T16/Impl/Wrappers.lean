module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Helper
public import IntegerMultBounds.Networks.Certificates.T16.Impl.LocalRun

/-! The wrapper words of data and helper registers, and the operators they realize through a
local word. A data register is read through its chart and adapted from the local list of its
stream frame into its native entry label, and back from its native exit label; through the word
it realizes the change of frame. A helper register is read through its chart and unwound by the
inverse halves of the split lowering of its transition; through the word it realizes the C gates
of its hosted slice. Neither wrapper makes a child call. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli Multiplicative

/-! ### Data wrappers -/

/-- The pre-wrapper of a data register. -/
noncomputable def adapterIn (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (a : ℕ) :
    List Prim :=
  Prim.perm χ.symm :: Classical.choose (Realization.exists_prims (preAdapter gs a))

/-- The post-wrapper of a data register. -/
noncomputable def adapterOut (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (b : ℕ) :
    List Prim :=
  Classical.choose (Realization.exists_prims (postAdapter gs b)) ++ [Prim.perm χ]

theorem wordLin_perm (G : Addr ≃ₗ[ZMod 2] Addr) : wordLin [Prim.perm G] = permOp G := by
  apply LinearMap.ext
  intro f
  rfl

theorem wordLin_cons_perm (G : Addr ≃ₗ[ZMod 2] Addr) (ps : List Prim) :
    wordLin (Prim.perm G :: ps) = wordLin ps * permOp G := rfl

theorem wordLin_adapterIn (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (a : ℕ) :
    wordLin (adapterIn χ gs a) = lift9 (preAdapter gs a).scalar.toLinearMap * permOp χ.symm := by
  rw [adapterIn, wordLin_cons_perm,
    ← (Classical.choose_spec (Realization.exists_prims (preAdapter gs a))).1.lin]

theorem wordLin_adapterOut (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (b : ℕ) :
    wordLin (adapterOut χ gs b) = permOp χ * lift9 (postAdapter gs b).scalar.toLinearMap := by
  rw [adapterOut, wordLin_append, wordLin_perm,
    ← (Classical.choose_spec (Realization.exists_prims (postAdapter gs b))).1.lin]

theorem childCount_adapterIn (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (a : ℕ)
    (h : Matches gs a) : childCount (adapterIn χ gs a) = 0 := by
  rw [adapterIn, show ∀ (p : Prim) ps, p :: ps = [p] ++ ps from fun _ _ => rfl, childCount_append,
    (Classical.choose_spec (Realization.exists_prims (preAdapter gs a))).2.1,
    show (preAdapter gs a).binary =
      (kernelListRealization gs).binary.symm.trans (nativeRealization a).binary from rfl,
    finrank_xRange_eq_zero h.inverseZ]
  rfl

theorem childCount_adapterOut (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (b : ℕ)
    (h : Matches gs b) : childCount (adapterOut χ gs b) = 0 := by
  rw [adapterOut, childCount_append,
    (Classical.choose_spec (Realization.exists_prims (postAdapter gs b))).2.1,
    show (postAdapter gs b).binary =
      (nativeRealization b).binary.symm.trans (kernelListRealization gs).binary from rfl,
    finrank_xRange_eq_zero h.inverseZ.symm]
  rfl

/-- **Data registers through a word.** -/
theorem data_through {χ : Addr ≃ₗ[ZMod 2] Addr} {B : Fin 73 → Addr} {f f' : Fin 73 → ZMod 4}
    (s : ChartSplit χ B f) (s' : ChartSplit χ B f') (he : s.ext = s'.ext) (a b : ℕ) :
    throughOp (adapterOut χ s'.gs b) (adapterIn χ s.gs a) a b =
      basisOp B (ofAdd f') * basisOp B (ofAdd (-f)) := by
  rw [throughOp, wordLin_adapterOut, wordLin_adapterIn]
  exact wrapped_change s s' he a b

/-! ### Helper wrappers -/

/-- The monomial halves of the split lowering of a transition. -/
noncomputable def splitL (a b : ℕ) : List Prim :=
  Classical.choose (Realization.exists_split (edgeRealization a b))

noncomputable def splitR (a b : ℕ) : List Prim :=
  Classical.choose (Classical.choose_spec (Realization.exists_split (edgeRealization a b)))

theorem split_spec (a b : ℕ) :
    (∀ p ∈ splitL a b ++ splitR a b, p.Invertible) ∧ childCount (splitL a b) = 0 ∧
      childCount (splitR a b) = 0 ∧
      Lowers (edgeRealization a b) (splitL a b ++
        cPrims (Module.finrank Geometry.F (Tableau.xRange (edgeRealization a b).binary)) ++
          splitR a b) :=
  let h := Classical.choose_spec (Classical.choose_spec (Realization.exists_split (edgeRealization a b)))
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem split_ready (a b : ℕ) : ∀ p ∈ splitL a b ++ splitR a b, p.Ready :=
  (Classical.choose_spec (Classical.choose_spec
    (Realization.exists_split (edgeRealization a b)))).2.2.2.2 (dyadic_edge a b)

/-- The pre-wrapper of a helper register. -/
noncomputable def helperIn {P : PortData} (hP : portCheck P = true) (m a b : ℕ) : List Prim :=
  Prim.perm (helperChart hP m).symm :: invPrims (splitL a b)

/-- The post-wrapper of a helper register. -/
noncomputable def helperOut {P : PortData} (hP : portCheck P = true) (m a b : ℕ) : List Prim :=
  invPrims (splitR a b) ++ [Prim.perm (helperChart hP m)]

theorem childCount_helperIn {P : PortData} (hP : portCheck P = true) (m a b : ℕ) :
    childCount (helperIn hP m a b) = 0 := by
  rw [helperIn, show ∀ (p : Prim) ps, p :: ps = [p] ++ ps from fun _ _ => rfl, childCount_append,
    childCount_invPrims, (split_spec a b).2.1]
  rfl

theorem childCount_helperOut {P : PortData} (hP : portCheck P = true) (m a b : ℕ) :
    childCount (helperOut hP m a b) = 0 := by
  rw [helperOut, childCount_append, childCount_invPrims, (split_spec a b).2.2.1]
  rfl

/-- **Helper registers through a word.** -/
theorem helper_through {P : PortData} (hP : portCheck P = true) (m : ℕ)
    (hw : (maskIndices m).length ≤ 9) (a b : ℕ)
    (hr : Module.finrank Geometry.F (Tableau.xRange (edgeRealization a b).binary) =
      (maskIndices m).length) :
    throughOp (helperOut hP m a b) (helperIn hP m a b) a b =
      basisOp (portBasis P) (ofAdd (maskFrame m)) := by
  obtain ⟨hinv, -, -, hlow⟩ := split_spec a b
  rw [hr] at hlow
  rw [throughOp, helperOut, helperIn, wordLin_cons_perm, wordLin_append, wordLin_perm]
  have := helper_wrapped hP m hw a b _ _ hinv hlow
  rw [← this]

end IntegerMultBounds.Networks.Certificates.T16.Impl
