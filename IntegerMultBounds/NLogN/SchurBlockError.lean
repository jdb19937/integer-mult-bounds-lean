module

public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! Error composition for the four-step interior/boundary solve. Each computed
stage may deviate from the exact map applied to the previous computed value;
under a dominance margin `μ` and coupling row masses at most `K`, the boundary
and interior errors are bounded explicitly, with no growth in the number of
cells or the line length. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem couple_sub (A : Matrix ι ι ℝ) (B : Finset ι) (x y : ι → ℝ) (i : ι) :
    couple A B (x-y) i=couple A B x i-couple A B y i := by
  simp [couple, mul_sub, sum_sub_distrib]

omit [DecidableEq ι] in
/-- A row of mass at most `K` maps values at most `E` to at most `K*E`. -/
theorem row_bound (A : Matrix ι ι ℝ) (T : Finset ι) (x : ι → ℝ) (i : ι) (K E : ℝ)
    (hK : ∑ j∈T, |A i j|≤K) (hE : 0≤E) (hx : ∀ j∈T, |x j|≤E) :
    |∑ j∈T, A i j*x j|≤K*E := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j∈T, |A i j*x j|≤∑ j∈T, |A i j| * E := sum_le_sum fun j hj => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx j hj) (abs_nonneg _)
    _=(∑ j∈T, |A i j|) * E := by rw [sum_mul]
    _≤K*E := mul_le_mul_of_nonneg_right hK hE

theorem schurOp_sub (A : Matrix ι ι ℝ) (I B : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hAI : DominatesOn A I μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (x y : ι → ℝ) (i : ι) : schurOp A I B R (x-y) i=schurOp A I B R x i-schurOp A I B R y i := by
  have hc : couple A B (x-y)=couple A B x-couple A B y := funext (couple_sub A B x y)
  simp only [schurOp, hc, couple_sub]
  rw [sum_congr rfl fun j hj => by rw [solver_sub A I μ hμ hAI R hR _ _ j hj]]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- The exact full solution satisfies the Schur boundary equation. -/
theorem exact_schur (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (b x : ι → ℝ) (hx : Solves A (I∪B) x b) :
    (∀ j∈I, x j=R (b-couple A B x) j) ∧ ∀ i∈B, schurOp A I B R x i=residual A I R b i := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  have hint : Solves A I x (b-couple A B x) := by
    intro i hi
    have h := hx i (mem_union_left _ hi)
    rw [sum_union hIB] at h
    simp only [Pi.sub_apply, couple]
    linarith
  have hxI : ∀ j∈I, x j=R (b-couple A B x) j := fun j hj =>
    solves_unique A I μ hμ hAI x _ _ hint (hR _) j hj
  refine ⟨hxI, fun i hi => ?_⟩
  have h := hx i (mem_union_right _ hi)
  rw [sum_union hIB] at h
  rw [sum_congr rfl fun j hj => by rw [hxI j hj, solver_sub A I μ hμ hAI R hR _ _ j hj]] at h
  simp only [mul_sub, sum_sub_distrib] at h
  simp only [schurOp, residual, couple] at h ⊢
  linarith

/-- The Schur operator has inverse bounded by `1/μ` on the boundary. -/
theorem schur_bound (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (v Z : ι → ℝ) (hZ : ∀ i∈B, schurOp A I B R Z i=v i) (C : ℝ) (hC : 0≤C)
    (hv : ∀ i∈B, |v i|≤C) (j : ι) (hj : j∈B) : |Z j|≤C/μ := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  set b : ι → ℝ := fun i => if i∈B then v i else 0 with hb
  have hzero : ∀ k∈I, R b k=0 := by
    refine fun k hk => solves_unique A I μ hμ hAI _ 0 b (hR b) (fun i hi => ?_) k hk
    simp [hb, disjoint_left.mp hIB hi]
  refine four_step_bound A I B hIB μ hμ hA R hR b Z (fun i hi => ?_) C (fun i _ => ?_) j hj
  · rw [hZ i hi]
    unfold residual
    rw [sum_congr rfl fun k hk => by rw [hzero k hk]]
    simp [hb, hi]
  · simp only [hb]
    split
    · exact hv i ‹_›
    · simpa using hC

/-- Rounded four-step solve. The computed interior pass `y`, boundary residual
`r`, boundary solve `xB`, interior right-hand side `c` and interior pass `xI`
each deviate from the exact map of the previous computed value by `e₁…e₅`. -/
theorem rounded_four_step (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ)
    (hμ : 0<μ) (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ)
    (hR : ∀ c, Solves A I (R c) c) (b x : ι → ℝ) (hx : Solves A (I∪B) x b)
    (K : ℝ) (hK : 0≤K) (hBI : ∀ i∈B, ∑ j∈I, |A i j|≤K) (hIB' : ∀ i∈I, ∑ j∈B, |A i j|≤K)
    (e₁ e₂ e₃ e₄ e₅ : ℝ) (he₁ : 0≤e₁) (he₂ : 0≤e₂) (he₃ : 0≤e₃)
    (y r Z xB c xI : ι → ℝ)
    (hy : ∀ j∈I, |y j-R b j|≤e₁)
    (hr : ∀ i∈B, |r i-(b i-∑ j∈I, A i j*y j)|≤e₂)
    (hZ : ∀ i∈B, schurOp A I B R Z i=r i) (hxB : ∀ j∈B, |xB j-Z j|≤e₃)
    (hc : ∀ i∈I, |c i-(b i-couple A B xB i)|≤e₄)
    (hxI : ∀ j∈I, |xI j-R c j|≤e₅) :
    (∀ j∈B, |xB j-x j|≤e₃+(K*e₁+e₂)/μ) ∧
      ∀ j∈I, |xI j-x j|≤e₅+(e₄+K*(e₃+(K*e₁+e₂)/μ))/μ := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  obtain ⟨hxint, hxS⟩ := exact_schur A I B hIB μ hμ hA R hR b x hx
  have hEr : 0≤K*e₁+e₂ := by positivity
  -- Boundary: `Z - x` solves the Schur system with the residual error.
  have hres : ∀ i∈B, |(r-residual A I R b) i|≤K*e₁+e₂ := by
    intro i hi
    have hrow := row_bound A I (y-R b) i K e₁ (hBI i hi) he₁ (fun j hj => hy j hj)
    simp only [Pi.sub_apply, mul_sub, sum_sub_distrib] at hrow
    have := hr i hi
    simp only [Pi.sub_apply, residual]
    calc |r i-(b i-∑ j∈I, A i j*R b j)|
        =|(r i-(b i-∑ j∈I, A i j*y j))-(∑ j∈I, A i j*y j-∑ j∈I, A i j*R b j)| := by ring_nf
      _≤|r i-(b i-∑ j∈I, A i j*y j)|+|∑ j∈I, A i j*y j-∑ j∈I, A i j*R b j| := abs_sub _ _
      _≤e₂+K*e₁ := add_le_add this hrow
      _=K*e₁+e₂ := by ring
  have hZx : ∀ j∈B, |(Z-x) j|≤(K*e₁+e₂)/μ :=
    schur_bound A I B hIB μ hμ hA R hR _ (Z-x) (fun i hi => by
      rw [schurOp_sub A I B μ hμ hAI R hR, hZ i hi, hxS i hi]; rfl) _ hEr hres
  have hB : ∀ j∈B, |xB j-x j|≤e₃+(K*e₁+e₂)/μ := by
    intro j hj
    have h1 := hxB j hj
    have h2 := hZx j hj
    simp only [Pi.sub_apply] at h2
    calc |xB j-x j|=|(xB j-Z j)+(Z j-x j)| := by ring_nf
      _≤|xB j-Z j|+|Z j-x j| := abs_add_le _ _
      _≤_ := add_le_add h1 h2
  refine ⟨hB, fun j hj => ?_⟩
  -- Interior: `R c - x_I = R (c - (b - A_IB x_B))`, bounded by the margin.
  have hEB : 0≤e₃+(K*e₁+e₂)/μ := by positivity
  set EB := e₃+(K*e₁+e₂)/μ
  have hv : ∀ i∈I, |(c-(b-couple A B x)) i|≤e₄+K*EB := by
    intro i hi
    have hcpl := row_bound A B (xB-x) i K EB (hIB' i hi) hEB (fun k hk => by
      simpa only [Pi.sub_apply] using hB k hk)
    have hcs : ∑ k∈B, A i k*(xB-x) k=couple A B xB i-couple A B x i := by
      rw [←couple_sub]; rfl
    rw [hcs] at hcpl
    have := hc i hi
    simp only [Pi.sub_apply]
    calc |c i-(b i-couple A B x i)|
        =|(c i-(b i-couple A B xB i))-(couple A B xB i-couple A B x i)| := by ring_nf
      _≤|c i-(b i-couple A B xB i)|+|couple A B xB i-couple A B x i| := abs_sub _ _
      _≤e₄+K*EB := add_le_add this hcpl
  have hRv := solves_bound A I μ hμ hAI _ _ (hR (c-(b-couple A B x))) _ hv j hj
  rw [solver_sub A I μ hμ hAI R hR _ _ j hj, ←hxint j hj] at hRv
  have h5 := hxI j hj
  calc |xI j-x j|=|(xI j-R c j)+(R c j-x j)| := by ring_nf
    _≤|xI j-R c j|+|R c j-x j| := abs_add_le _ _
    _≤_ := add_le_add h5 hRv

end IntegerMultBounds.NLogN.SchurDominance
