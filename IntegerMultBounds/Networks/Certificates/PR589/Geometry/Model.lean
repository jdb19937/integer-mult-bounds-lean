module

public import IntegerMultBounds.Networks.Certificates.PR589.Copy.Boundary
public import IntegerMultBounds.Networks.ShearFrame
public import IntegerMultBounds.Networks.ProjectionTrace
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The selected E8 labels are rational subspaces with form dot/2.
Their address shears act on binary-valued streams; rational coordinates are
never reduced modulo two or identified with the stream coefficient field. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry

abbrev Address := Fin 8 → ℚ
abbrev Stream := (Address × Address) → ZMod 2

def form : LinearMap.BilinForm ℚ Address := (1 / 2 : ℚ) • Labels.form 0

theorem form_apply (x y : Address) : form x y = (1 / 2 : ℚ) * ∑ i, x i * y i := by
  simp [form, Labels.form_apply]

theorem form_symm : form.IsSymm := by
  constructor
  intro x y
  simp only [form_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem self_eq_zero (x : Address) (h : form x x = 0) : x = 0 := by
  rw [form_apply] at h
  have hs : ∑ i, x i * x i = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hz := (Finset.sum_mul_self_eq_zero_iff Finset.univ x).mp hs
  funext i
  exact hz i (Finset.mem_univ i)

theorem nondegenerate : form.Nondegenerate := by
  constructor
  · intro x hx
    exact self_eq_zero x (hx x)
  · intro x hx
    exact self_eq_zero x (hx x)

theorem restrict_nondegenerate (U : Submodule ℚ Address) : (form.restrict U).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact self_eq_zero x.val (hx x)
  · intro x hx
    apply Subtype.ext
    exact self_eq_zero x.val (hx x)

def root (i : ℕ) : Address := fun j => ((Frames.lines i).getD j.val 0 : ℤ)

def label (i : ℕ) : Submodule ℚ Address :=
  Submodule.span ℚ (root '' {j | j ∈ Frames.labels i})

theorem root_mem (i j : ℕ) (h : j ∈ Frames.labels i) : root j ∈ label i :=
  Submodule.subset_span ⟨j, h, rfl⟩

noncomputable def projector (i : ℕ) : Address →ₗ[ℚ] Address :=
  ProjectionTrace.projector form form_symm (label i)

theorem projector_eq (i : ℕ) :
    projector i = ProjectionRank.project form form_symm (label i) (restrict_nondegenerate _) :=
  ProjectionTrace.projector_eq form form_symm _ _

noncomputable def frame (i : ℕ) : Stream ≃ₗ[ZMod 2] Stream := ShearFrame.frame (projector i)

theorem frame_apply (i : ℕ) (f : Stream) (p : Address × Address) :
    frame i f p = f (p.1 - projector i p.2, p.2) := rfl

/-- Exact old-to-new address action, with the source inverse on the correct side. -/
theorem frame_change (i j : ℕ) (f : Stream) :
    frame j ((frame i).symm f) = ShearFrame.frame (projector j - projector i) f :=
  ShearFrame.frame_change _ _ _

noncomputable def moveRank (i j : ℕ) : ℕ :=
  Module.finrank ℚ (LinearMap.range (projector j - projector i))

theorem moveRank_eq (i j : ℕ) (h : label i ≤ label j ∨ label j ≤ label i) :
    moveRank i j = (Module.finrank ℚ (label j) - Module.finrank ℚ (label i)) +
      (Module.finrank ℚ (label i) - Module.finrank ℚ (label j)) :=
  ProjectionTrace.edgeRank_eq form form_symm _ _ (restrict_nondegenerate _) (restrict_nondegenerate _) h

theorem label_zero : label 0 = ⊥ := by
  change Submodule.span ℚ (root '' {j | j ∈ ([] : List ℕ)}) = ⊥
  simp

theorem projector_zero : projector 0 = 0 := by
  rw [projector_eq]
  apply LinearMap.ext
  intro x
  have h := ProjectionRank.project_mem form form_symm (label 0) (restrict_nondegenerate _) x
  simpa [label_zero] using h

/-- COPY from a retained frame to zero is the inverse rational address shear. -/
theorem copy_operator (i : ℕ) (f : Stream) :
    frame 0 ((frame i).symm f) = ShearFrame.frame (-projector i) f := by
  rw [frame_change, projector_zero, zero_sub]

theorem copyRank_eq (i : ℕ) :
    Module.finrank ℚ (LinearMap.range (-projector i)) = Module.finrank ℚ (label i) := by
  rw [projector_eq]
  exact ProjectionRank.negative_source_rank form form_symm _ _

/-- The checked nine-lifecycle COPY semantics now uses concrete rational shears. -/
theorem decoded_scatter (stored : Fin 661 → Stream) (i : Fin 661) :
    Copy.run frame Copy.lifecycles
      (FramedCircuit.encode (fun j => frame (Frames.beforeScatter j)) (Copy.extendStored stored)) i.val =
    frame (Frames.beforeScatter i.val)
      (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (Copy.extendStored stored) i.val) :=
  Copy.decoded_scatter frame stored i

end IntegerMultBounds.Networks.Certificates.PR589.Geometry
