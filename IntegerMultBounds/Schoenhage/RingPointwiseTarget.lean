module

import IntegerMultBounds.Schoenhage.RingPointwiseBound
public import IntegerMultBounds.Spec.PointwiseProducts

/-! The pointwise-product step of the synthetic convolution meets its
statement in the paper's formats within `O(T p log (r p) log log (r p))`
steps plus the header (`pointwise_polylog : pointwisePolylogTarget 1`). The
extra `log log` factor is the Schönhage–Strassen overhead, absorbed by the
packed-product margin of the cost table. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct

theorem prod_pos_of_axes {d l : ℕ} {ts : List ℕ} (h : AxisLengths d l ts) : 1 ≤ ts.prod := by
  have : ∀ t ∈ ts, 1 ≤ t := fun t ht => by
    rcases h.2 t ht with rfl | rfl <;> exact Nat.one_le_two_pow
  clear h
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.prod_cons]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := this t (by simp); omega)
      (by have := ih (fun x hx => this x (by simp [hx])); omega))

theorem pointwise_polylog : pointwisePolylogTarget 1 := by
  intro Cw hCw
  obtain ⟨C, hC⟩ := pointwiseTime_le Cw hCw
  refine ⟨𝕌, _, 0, pointwiseProgram, C, by norm_num, ?_⟩
  intro p d l K w ts fs gs hl hp hpr hd hK hw hwC hax hfl hgl hf hg
  refine (pointwise_meets Cw p d l K w ts fs gs hl hp hpr hd hK hw hwC hax hfl hgl hf hg).consequence
    (fun _ h => h) (fun _ h => h) ?_
  have hlp : l < p := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpr
  have := hC p l ts.prod (transformHeader p d (2 ^ l) K w ts).length hl hp hlp (prod_pos_of_axes hax)
  simpa only [pow_one] using this

end IntegerMultBounds.Schoenhage
