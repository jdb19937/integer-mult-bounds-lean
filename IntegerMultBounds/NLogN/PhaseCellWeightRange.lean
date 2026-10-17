module

public import IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients

/-! Every actual executable similarity weight lies in `[2^-(8p+1), 1]` at the
selected precision. This fixes the scale of the reciprocal-weighted inputs of
the interior Toeplitz solves. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients

theorem selected_similarity_range {s t u p : ℕ} {α d : ℝ} (j : ℤ)
    (hp : 0<p) (hs : 0<s) (hu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p) :
    1/(2 : ℝ)^(8*p+1)≤similarity (2^15*p) s t u j ∧ (similarity (2^15*p) s t u j : ℝ)≤1 := by
  obtain ⟨-, hle, herr⟩ := (similarityArg s t u j).value_spec (2^15*p) (selected_precision p hp).1
  have htarget := (similarityArg s t u j).target_bounds
  have hmargin := denominator_margin (P := 2^15*p) j htheta hgap hbudget (selected_precision p hp).2
  rw [←similarity_target s t u hs α hu htheta j] at hmargin
  have hlow := (abs_le.mp herr).1
  have hsc : 1/(2 : ℝ)^(8*p+1)=(1/(2 : ℝ)^(8*p))/2 := by rw [pow_succ]; ring
  unfold similarity
  constructor
  · rw [hsc]
    linarith
  · linarith [htarget.2]

end IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients
