module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortData
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.All
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The port certificates are the word's own frames

`port t` is the certificate of port `t`. Its line is the word's line `t` (`root_port`), and its
two projectors are the orthogonal projectors (`Geometry.projector`) of the word's port frames:
* source `t` starts in the frame of line `t`, with projector `P` (`projector_source_initial`), and
  ends in the full frame, with projector `1` (`projector_source_final`);
* target `111 + t` starts in frame zero, with projector `0` (`projector_target_initial`), and ends
  in the hyperplane frame orthogonal to line `t`, with projector `1 - P`
  (`projector_target_final`).

These are the four local frames that `Stage` lifts to the nine-stage window, so its stage boundary
identities hold for the word's frames.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix
open Geometry (Address form form_apply form_symm root label projector)

/-- The certificate of port `t`. -/
def port (t : ℕ) : PortCertificate := ports.getD t default

theorem port_checked (t : ℕ) (ht : t < 111) : (port t).Checked := by
  apply ports_checked
  rw [port, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [ports_length]; exact ht), Option.getD_some]
  exact List.getElem_mem _

theorem port_lines : ∀ t < 111, ∀ i : Fin 8, (port t).line i = (Frames.lines t).getD i.val 0 := by
  decide +kernel

theorem source_frames : ∀ t < 111,
    Frames.initialRefs t = 2 + t ∧ Frames.labels (2 + t) = [t] ∧ Frames.finalRefs t = 1 := by
  decide +kernel

theorem target_frames : ∀ t < 111,
    Frames.initialRefs (111 + t) = 0 ∧ Frames.finalRefs (111 + t) = 525 + t ∧
      Geometry.Dimensions.value (525 + t) = 7 ∧
      ∀ j ∈ Frames.labels (525 + t),
        ∑ i : Fin 8, (port t).line i * (Frames.lines j).getD i.val 0 = 0 := by
  decide +kernel

theorem full_dimension : Geometry.Dimensions.value 1 = 8 := by
  decide +kernel

/-- The port's line as an address. -/
def lineVec (c : PortCertificate) : Address := fun i => (c.line i : ℚ)

theorem root_port (t : ℕ) (ht : t < 111) : root t = lineVec (port t) := by
  funext i
  simp [root, lineVec, port_lines t ht i]

theorem form_eq_dot (x y : Address) : form x y = (x ⬝ᵥ y) / 2 := by
  rw [form_apply, dotProduct]
  ring

theorem lineVec_dot {c : PortCertificate} (h : c.Checked) : lineVec c ⬝ᵥ lineVec c = 4 := by
  have hn := congrArg (Int.cast : ℤ → ℚ) h.1
  push_cast at hn
  simpa [dotProduct, lineVec] using hn

theorem lineProj_mulVec (c : PortCertificate) (x : Address) :
    c.lineProj *ᵥ x = ((lineVec c ⬝ᵥ x) / 4) • lineVec c := by
  funext i
  simp only [mulVec, dotProduct, PortCertificate.lineProj, of_apply, lineVec, Pi.smul_apply,
    smul_eq_mul]
  calc ∑ j, (c.line i : ℚ) * c.line j / 4 * x j
      = (∑ j, (c.line j : ℚ) * x j) * ((c.line i : ℚ) / 4) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j, (c.line j : ℚ) * x j) / 4 * c.line i := by ring

/-- A linear map onto `L` whose residual is orthogonal to `L` is the orthogonal projector. -/
theorem projector_eq_of {L : Submodule ℚ Address} (f : Address →ₗ[ℚ] Address)
    (hmem : ∀ x, f x ∈ L) (horth : ∀ x, ∀ n ∈ L, form n (x - f x) = 0) :
    ProjectionTrace.projector form form_symm L = f := by
  rw [ProjectionTrace.projector_eq form form_symm L (Geometry.restrict_nondegenerate L)]
  refine LinearMap.ext fun x => ?_
  have hl := ProjectionRank.project_left form form_symm L (Geometry.restrict_nondegenerate L)
    (hmem x)
  have hr := ProjectionRank.project_right form form_symm L (Geometry.restrict_nondegenerate L)
    (x := x - f x) ((LinearMap.BilinForm.mem_orthogonal_iff).mpr fun n hn => horth x n hn)
  calc _ = ProjectionRank.project form form_symm L (Geometry.restrict_nondegenerate L)
        (f x + (x - f x)) := by rw [add_sub_cancel]
    _ = f x := by rw [map_add, hl, hr, add_zero]

theorem label_source (t : ℕ) (ht : t < 111) : label (2 + t) = Submodule.span ℚ {root t} := by
  rw [label, (source_frames t ht).2.1]
  congr 1
  ext y
  simp [eq_comm]

/-- The source's initial frame has the port's line projector. -/
theorem projector_source_initial (t : ℕ) (ht : t < 111) :
    projector (Frames.initialRefs t) = Matrix.toLin' (port t).lineProj := by
  have hc := port_checked t ht
  rw [(source_frames t ht).1]
  apply projector_eq_of
  · intro x
    rw [label_source t ht, Matrix.toLin'_apply, lineProj_mulVec, root_port t ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro x n hn
    rw [label_source t ht, root_port t ht] at hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [Matrix.toLin'_apply, lineProj_mulVec, form_eq_dot, smul_dotProduct, dotProduct_sub,
      dotProduct_smul, lineVec_dot hc, smul_eq_mul, smul_eq_mul]
    ring

/-- The source's final frame is the full frame. -/
theorem projector_source_final (t : ℕ) (ht : t < 111) :
    projector (Frames.finalRefs t) = LinearMap.id := by
  rw [(source_frames t ht).2.2]
  have htop : label 1 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Geometry.Dimensions.dimension 1 (by norm_num), full_dimension, Module.finrank_fin_fun]
  apply projector_eq_of
  · intro x
    rw [htop]
    exact Submodule.mem_top
  · intro x n _
    simp

/-- The target's initial frame is frame zero. -/
theorem projector_target_initial (t : ℕ) (ht : t < 111) :
    projector (Frames.initialRefs (111 + t)) = 0 := by
  rw [(target_frames t ht).1, Geometry.projector_zero]

/-- The target's final frame is the hyperplane orthogonal to the port's line. -/
theorem label_target (t : ℕ) (ht : t < 111) :
    label (525 + t) = form.orthogonal (Submodule.span ℚ {root t}) := by
  obtain ⟨_, _, hdim, horth⟩ := target_frames t ht
  have hle : label (525 + t) ≤ form.orthogonal (Submodule.span ℚ {root t}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
    have hz := congrArg (Int.cast : ℤ → ℚ) (horth j hj)
    push_cast at hz
    rw [LinearMap.BilinForm.smul_left, form_apply, root_port t ht]
    simp only [lineVec, root]
    rw [hz]
    ring
  have hroot : root t ≠ 0 := by
    intro h0
    have hd := lineVec_dot (port_checked t ht)
    rw [← root_port t ht, h0, zero_dotProduct] at hd
    norm_num at hd
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [Geometry.Dimensions.dimension (525 + t) (by omega), hdim,
    LinearMap.BilinForm.finrank_orthogonal Geometry.nondegenerate, finrank_span_singleton hroot,
    Module.finrank_fin_fun]

theorem projector_target_final (t : ℕ) (ht : t < 111) :
    projector (Frames.finalRefs (111 + t)) = Matrix.toLin' (1 - (port t).lineProj) := by
  have hc := port_checked t ht
  have hperp : ∀ y : Address, y ∈ form.orthogonal (Submodule.span ℚ {root t}) ↔
      lineVec (port t) ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hy
      have h1 := hy (root t) (Submodule.mem_span_singleton_self _)
      rw [form_eq_dot, root_port t ht] at h1
      linarith
    · intro hy n hn
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
      rw [form_eq_dot, root_port t ht, smul_dotProduct, hy,
        smul_zero, zero_div]
  rw [(target_frames t ht).2.1]
  apply projector_eq_of
  · intro x
    rw [label_target t ht, hperp, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      lineProj_mulVec, dotProduct_sub, dotProduct_smul, lineVec_dot hc, smul_eq_mul]
    ring
  · intro x n hn
    rw [label_target t ht, hperp] at hn
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel, lineProj_mulVec,
      form_eq_dot, dotProduct_smul, dotProduct_comm n (lineVec (port t)), hn, smul_zero, zero_div]

end IntegerMultBounds.Networks.Certificates.PR589.Nine
