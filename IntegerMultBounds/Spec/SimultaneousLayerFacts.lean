import IntegerMultBounds.Spec.SimultaneousLayer

/-! The numerical guarantees of `prop:simultaneous-layer` follow from the
statement's definitions: for disk grid input, every coefficient of the
returned array `Q_p(ℋ z)` lies in the unit disk (`layerOut_norm_le`), and
the array is within `√2 2^(-p)` of `ℋ z` coefficientwise (`layerOut_close`). -/

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

theorem arrayVec_norm_le {r p : ℕ} {zs : List (Rec r)} (hz : ∀ z ∈ zs, DiskGrid p z.1 z.2)
    (n : ℕ) (k : Fin r) : ‖arrayVec p zs n k‖ ≤ 1 := by
  unfold arrayVec
  cases h : zs[n]? with
  | none => simp
  | some f => exact (hz f (List.mem_of_getElem? h)).norm_le k

/-- `ℋ` maps the unit disk into itself coefficientwise. -/
theorem norm_hadamard_le {r D K ρ S : ℕ} {z : ℕ → Fin r → ℂ} (hz : ∀ y k, ‖z y k‖ ≤ 1)
    (x : ℕ) (k : Fin r) : ‖hadamard D K ρ S z x k‖ ≤ 1 := by
  unfold hadamard
  rw [norm_mul]
  have hs : ‖∑ b : Fin D → Bool, (-1 : ℂ) ^ (Finset.univ.filter fun j => selBit K ρ S x j && b j).card *
      z (setSel K ρ S x b) k‖ ≤ 2 ^ D := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ b : Fin D → Bool, ‖(-1 : ℂ) ^ (Finset.univ.filter fun j => selBit K ρ S x j && b j).card *
        z (setSel K ρ S x b) k‖ ≤ 1 := fun b => by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]; exact hz _ _
    refine (Finset.sum_le_sum fun b _ => this b).trans ?_
    simp
  have h2 : ‖(1 / (2 ^ D : ℂ))‖ = 1 / 2 ^ D := by simp
  rw [h2]
  calc 1 / 2 ^ D * _ ≤ 1 / 2 ^ D * (2 : ℝ) ^ D := by gcongr
    _ = 1 := by field_simp

/-- The returned records are `Q_p` of `ℋ z`. -/
theorem arrayVec_layerOut {r p D K ρ S M : ℕ} (zs : List (Rec r)) {x : ℕ} (hx : x < M) :
    arrayVec p (layerOut p D K ρ S M zs) x = fun k => rhoC p (hadamard D K ρ S (arrayVec p zs) x k) := by
  simp [arrayVec, layerOut, List.getElem?_map, List.getElem?_range hx]
  rfl

/-- Every returned coefficient lies in the unit disk. -/
theorem layerOut_norm_le {r p D K ρ S M : ℕ} {zs : List (Rec r)} (hz : ∀ z ∈ zs, DiskGrid p z.1 z.2)
    (x : ℕ) (k : Fin r) : ‖arrayVec p (layerOut p D K ρ S M zs) x k‖ ≤ 1 := by
  by_cases hx : x < M
  · rw [arrayVec_layerOut zs hx]
    exact (norm_rhoC_le _ _).trans (norm_hadamard_le (arrayVec_norm_le hz) x k)
  · have : (layerOut p D K ρ S M zs)[x]? = none := by simp [layerOut]; omega
    simp [arrayVec, this]

/-- `‖Q_p(ℋ z) - ℋ z‖_∞ < √2 2^(-p)`. -/
theorem layerOut_close {r p D K ρ S M : ℕ} (zs : List (Rec r)) :
    Close M (arrayVec p (layerOut p D K ρ S M zs)) (hadamard D K ρ S (arrayVec p zs))
      (Real.sqrt 2 / 2 ^ p) := by
  intro x hx k
  rw [arrayVec_layerOut zs hx]
  exact norm_rhoC_sub_lt p _

end IntegerMultBounds.Spec.SignedRingProduct
