module

public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootKernel
public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
public import IntegerMultBounds.MathlibTM2.M8.Local.Scalar

/-! A root complement containing the output vector lies below the output
hyperplane or centre star. These facts use only the certified Gram unit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames
noncomputable section
open IntegerMultBounds Matrix Local RootCheck

/-- A certified root complement lies in every output hyperplane whose vector it contains. -/
theorem rootFrame_le_hyper_of_unit {B : List Nat}
    (hB : IsUnit ((rootMat B)ᵀ * formG * rootMat B).det)
    {T : Finset Nat} (hT : tvec T ∈ rspan B) : Nested (rootFrame B) (hyperFrame T) := by
  apply nested_one_sub
  apply proj_le_root hB
  intro a
  obtain ⟨S, hS, ha⟩ := Finset.mem_image.mp (basisOf_sub {T} a.2)
  change a.1 ∈ rspan B
  rw [← ha, Finset.mem_singleton.mp hS]
  exact hT

theorem rootFrame_le_star_of_unit {B : List Nat}
    (hB : IsUnit ((rootMat B)ᵀ * formG * rootMat B).det)
    {c : Nat} (hc : c < 23) (h : wvec c ∈ rspan B) : Nested (rootFrame B) (starFrame c) := by
  rw [eq_sub_of_add_eq (starFrame_add_centreLine hc)]
  exact nested_one_sub (proj_le_root hB fun _ => h)

theorem rvec_code3 (a b c : Nat) (ha : a < 32) (hb : b < 32) (hc : c < 32) :
    rvec (a + 32 * b + 1024 * c) = tvec {a, b, c} := by
  have hlt : a + 32 * b + 1024 * c < cen := by unfold cen; omega
  rw [rvec, ite_eq_left hlt]
  have he : a + 32 * b + 1024 * c = a + 32 * (b + 32 * c) := by omega
  have h0 : p0 (a + 32 * b + 1024 * c) = a := by
    change (a + 32 * b + 1024 * c) % 32 = a
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h1 : p1 (a + 32 * b + 1024 * c) = b := by
    change ((a + 32 * b + 1024 * c) / 32) % 32 = b
    rw [he, Nat.add_mul_div_left _ _ (by decide : 0 < 32)]
    simp [Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have h2 : p2 (a + 32 * b + 1024 * c) = c := by
    change (a + 32 * b + 1024 * c) / 1024 = c
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 1024),
      Nat.div_eq_of_lt (show a + 32 * b < 1024 by omega), Nat.zero_add]
  rw [tripleOf, h0, h1, h2]

theorem rootCode_output (j : Nat) (hj : j < 3 * leafCount) :
    rvec (GeometryB.rootCode j) = tvec (leafTriple (j / 3)) := by
  have ht : j / 3 < leafCount := by omega
  obtain ⟨a, b, c, hs, hab, hbc, hc⟩ := leaf_supp ht
  rw [GeometryB.rootCode, ite_eq_left hj, show records.get width (j / 3) = recAt (j / 3) from rfl,
    hs, leafTriple_of hs]
  exact rvec_code3 a b c (by omega) (by omega) (by omega)

theorem rootCode_centre (c : Nat) :
    rvec (GeometryB.rootCode (3 * leafCount + c)) = wvec c := by
  rw [GeometryB.rootCode, ite_eq_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [rvec, ite_eq_right (by omega), Nat.add_sub_cancel_left]

end
end IntegerMultBounds.MathlibTM2.M8.Frames
