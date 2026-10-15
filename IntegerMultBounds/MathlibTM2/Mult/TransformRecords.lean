module

public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRounds
public import IntegerMultBounds.Spec.SimultaneousLayerFacts

/-! The computed forward and opposite transforms return explicit public signed
records satisfying the numerical clauses of the existing transform interface.
This is a record-format bridge, not a tape execution or cost theorem. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.TransformRecords

open NLogN Spec.SignedRingProduct Rounds SynthErr

/-- Canonical signed grid numerators for the first `M` records. -/
noncomputable def records {r : ℕ} (p M : ℕ) (u : ℕ → Fin r → ℂ) : List (Rec r) :=
  (List.range M).map fun n =>
    (fun c => rho0 (2 ^ p * (u n c).re), fun c => rho0 (2 ^ p * (u n c).im))

@[simp] theorem records_length {r : ℕ} (p M : ℕ) (u : ℕ → Fin r → ℂ) :
    (records p M u).length = M := by simp [records]

theorem records_read {r : ℕ} (p M : ℕ) (u : ℕ → Fin r → ℂ) (hg : GridR p u)
    {n : ℕ} (hn : n < M) (c : Fin r) : arrayVec p (records p M u) n c = u n c := by
  simp only [records, arrayVec, List.getElem?_map, List.getElem?_range hn, Option.map_some]
  exact rhoC_of_isFixed (hg n c)

theorem records_disk {r : ℕ} (p M : ℕ) (u : ℕ → Fin r → ℂ)
    (hd : ∀ n < M, ∀ c, ‖u n c‖ ≤ 1) :
    ∀ f ∈ records p M u, DiskGrid p f.1 f.2 := by
  intro f hf
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
  have hn := List.mem_range.mp hn
  intro c
  have hnorm := (norm_rhoC_le p (u n c)).trans (hd n hn c)
  rw [Complex.norm_def, Real.sqrt_le_one, Complex.normSq_apply] at hnorm
  simp only [rhoC] at hnorm
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div,
    div_le_one (by positivity : (0 : ℝ) < 2 ^ p * 2 ^ p)] at hnorm
  have hbound : (rho0 (2 ^ p * (u n c).re) : ℝ) ^ 2 +
      (rho0 (2 ^ p * (u n c).im) : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2*p) := by
    simpa only [← sq, ← pow_mul'] using hnorm
  exact_mod_cast hbound

/-- Numerical clauses of `MeetsForward` and `MeetsOpposite` for one explicit
record list: exact length, disk-grid numerators and strict error. -/
def NumericalOutput {r : ℕ} (p M : ℕ) (fs : List (Rec r))
    (exact : ℕ → Fin r → ℂ) (ε : ℝ) : Prop :=
  fs.length = M ∧ (∀ f ∈ fs, DiskGrid p f.1 f.2) ∧ Close M (arrayVec p fs) exact ε

theorem numericalOutput_of_guarantees {r : ℕ} (p M : ℕ) (u exact : ℕ → Fin r → ℂ)
    (ε : ℝ) (hg : GridR p u) (hd : ∀ n < M, ∀ c, ‖u n c‖ ≤ 1)
    (he : Close M u exact ε) : NumericalOutput p M (records p M u) exact ε := by
  refine ⟨records_length p M u, records_disk p M u hd, ?_⟩
  intro n hn c
  rw [records_read p M u hg hn]
  exact he n hn c

theorem arrayVec_grid {r : ℕ} (p : ℕ) (fs : List (Rec r)) : GridR p (arrayVec p fs) := by
  intro n c
  unfold arrayVec
  cases h : fs[n]? with
  | none => exact ⟨0,0,by apply Complex.ext <;> simp⟩
  | some f => exact ⟨f.1 c,f.2 c,rfl⟩

variable {r d : ℕ} [NeZero r] (a : Fin d → ℕ) (hr : ∀ i, 2 ^ a i ∣ 2*r)
    (p ℓ : ℕ) (hA : nRounds a ≤ ℓ) (hℓ : 1 ≤ ℓ) (u : ℕ → Fin r → ℂ)
    (hg : GridR p u) (hd : SupLe (List.ofFn a).sum u 1)

include hr hA hℓ hg hd

/-- The computed forward transform in the public record format. -/
theorem forward_numerical :
    NumericalOutput p (tsA a).prod
      (records p (tsA a).prod (fwdRoundsC p (List.ofFn a) (nRounds a) u))
      (fwdExact (tsA a) 1 u) (Real.sqrt 2 * ℓ / 2 ^ p) := by
  obtain ⟨hgrid,hdisk⟩ := fwdRoundsC_diskGrid p _ (nRounds a) hg hd
  exact numericalOutput_of_guarantees p _ _ _ _ hgrid
    (fun n hn => hdisk n (lt_two_pow_of_lt_prod a hn)) (fwdRoundsC_close a hr p hA hℓ u)

/-- The computed opposite transform in the same public record format. -/
theorem opposite_numerical :
    NumericalOutput p (tsA a).prod
      (records p (tsA a).prod (oppRoundsC p (List.ofFn a) (nRounds a) u))
      (oppExact (tsA a) 1 u) (Real.sqrt 2 * ℓ / 2 ^ p) := by
  obtain ⟨hgrid,hdisk⟩ := oppRoundsC_diskGrid p _ (nRounds a) hg hd
  exact numericalOutput_of_guarantees p _ _ _ _ hgrid
    (fun n hn => hdisk n (lt_two_pow_of_lt_prod a hn)) (oppRoundsC_close a hr p hA hℓ u)

omit hg hd in
/-- The public forward numerical contract follows from original disk-grid records. -/
theorem forward_records (fs : List (Rec r)) (hfs : ∀ f ∈ fs, DiskGrid p f.1 f.2) :
    NumericalOutput p (tsA a).prod
      (records p (tsA a).prod (fwdRoundsC p (List.ofFn a) (nRounds a) (arrayVec p fs)))
      (fwdExact (tsA a) 1 (arrayVec p fs)) (Real.sqrt 2 * ℓ / 2 ^ p) :=
  forward_numerical a hr p ℓ hA hℓ (arrayVec p fs) (arrayVec_grid p fs)
    (fun n _ c => arrayVec_norm_le hfs n c)

omit hg hd in
/-- The public opposite numerical contract follows from the same original record format. -/
theorem opposite_records (fs : List (Rec r)) (hfs : ∀ f ∈ fs, DiskGrid p f.1 f.2) :
    NumericalOutput p (tsA a).prod
      (records p (tsA a).prod (oppRoundsC p (List.ofFn a) (nRounds a) (arrayVec p fs)))
      (oppExact (tsA a) 1 (arrayVec p fs)) (Real.sqrt 2 * ℓ / 2 ^ p) :=
  opposite_numerical a hr p ℓ hA hℓ (arrayVec p fs) (arrayVec_grid p fs)
    (fun n _ c => arrayVec_norm_le hfs n c)

end IntegerMultBounds.MathlibTM2.Mult.TransformRecords
