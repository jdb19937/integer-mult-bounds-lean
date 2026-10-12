module

public import IntegerMultBounds.Machine.FixedMulValue
public import IntegerMultBounds.Machine.SignExtendAdd
public import IntegerMultBounds.Machine.Negate
public import IntegerMultBounds.Machine.RecordRewind
public import IntegerMultBounds.Machine.RecordCopy
public import IntegerMultBounds.Machine.PairJoin
public import IntegerMultBounds.Machine.GaussianLineFast
public import IntegerMultBounds.Resampling.B0TapeFast
public import IntegerMultBounds.Resampling.TableValue
public import IntegerMultBounds.Resampling.PiTape
public import IntegerMultBounds.LineCost
public import IntegerMultBounds.NLogN.ResamplingManuscript
public import IntegerMultBounds.NLogN.ResamplingPermutedNumeric

/-! The milestone theorems of §7 in `plan/07-gaussian-resampling.md`: each
packages the results that close one sub-problem. -/

@[expose] public section

namespace IntegerMultBounds.Machine.FixedMul

open TwosComplement (signed addMod negWord)

/-- The signed word layer: sign-extending add, negate and truncating multiply on
two's-complement words. -/
theorem signed_word_ops :
    (∀ xs acc : List Bool, xs.length ≤ acc.length → acc ≠ [] →
      -(2 : ℤ) ^ (acc.length - 1) ≤ signed xs + signed acc → signed xs + signed acc < 2 ^ (acc.length - 1) →
      signed (addMod xs acc) = signed xs + signed acc) ∧
    (∀ bs : List Bool, bs ≠ [] → signed bs ≠ -(2 : ℤ) ^ (bs.length - 1) → signed (negWord bs) = -signed bs) ∧
    (∀ (x y : List Bool) (p w : ℕ), x.length = w → y.length = w → p + 2 ≤ w →
      |signed x| ≤ 2 ^ p → |signed y| ≤ 2 ^ p → signed (result x y p w) = (signed x * signed y).tdiv (2 ^ p)) :=
  ⟨fun xs acc h hacc hlo hhi => TwosComplement.signed_addMod xs acc h hacc hlo hhi,
   fun bs hne h => TwosComplement.signed_negWord bs hne h,
   fun x y p w hx hy hw hxb hyb => signed_result x y p w hx hy hw hxb hyb⟩

end IntegerMultBounds.Machine.FixedMul

namespace IntegerMultBounds.Schoenhage

/-- The word and record machines of the resampling line machines, with their contracts. -/
theorem wordRecordLayer_hoare :
    (type_of% @Machine.SignExtendAdd.add_hoare) ∧ (type_of% @Machine.Negate.neg_hoare) ∧
    (type_of% @fastMul_hoare) ∧ (type_of% @Machine.RecordRewind.rewind_hoare) ∧
    (type_of% @Machine.RecordCopy.walk_hoare) ∧ (type_of% @Machine.BackWord.back_hoare) ∧
    (type_of% @Machine.PairJoin.join_hoare) ∧ (type_of% @Machine.PairJoin.split_hoare) :=
  ⟨@Machine.SignExtendAdd.add_hoare, @Machine.Negate.neg_hoare, @fastMul_hoare,
    @Machine.RecordRewind.rewind_hoare, @Machine.RecordCopy.walk_hoare, @Machine.BackWord.back_hoare,
    @Machine.PairJoin.join_hoare, @Machine.PairJoin.split_hoare⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Resampling.TableValue

/-- The `π`, `exp` and table machines, and their tables fed to the `Ã` and `B̃₀` machines. -/
theorem tables_on_tapes :
    (type_of% @PiTape.pi_hoare) ∧ (type_of% @TabATape.tableA_hoare) ∧ (type_of% @TabETape.tableE_hoare) ∧
    (type_of% @TabDTape.tableD_hoare) ∧ (type_of% @a_tables) ∧ (type_of% @b0_tables) :=
  ⟨@PiTape.pi_hoare, @TabATape.tableA_hoare, @TabETape.tableE_hoare, @TabDTape.tableD_hoare, @a_tables,
    @b0_tables⟩

end IntegerMultBounds.Resampling.TableValue

namespace IntegerMultBounds.Resampling.B0Value

/-- The words of the `Ã`, `Ẽ`, Neumann and `B̃₀` machines are the numerators of the numerical maps. -/
theorem maps_value_W :
    (type_of% @WindowSum.accumulators_eq) ∧ (type_of% @TabledMaps.accumulators_eq_W) ∧
    (type_of% @OffDiagSum.accumulators_eq) ∧ (type_of% @NeumannWords.resampJNumH_eq_iter) ∧
    (type_of% @b0_value_W) :=
  ⟨@WindowSum.accumulators_eq, @TabledMaps.accumulators_eq_W, @OffDiagSum.accumulators_eq,
    @NeumannWords.resampJNumH_eq_iter, @b0_value_W⟩

end IntegerMultBounds.Resampling.B0Value

namespace IntegerMultBounds.Resampling.B0Tape

/-- The fast `Ã` line machine and the `B̃₀` machine halt within their bounds, and their words are
the numerators of the numerical maps. -/
theorem maps_hoareF :
    (type_of% @Machine.GaussianLine.line_hoareF) ∧ (type_of% @b0_hoareF) ∧
    (type_of% @WindowSum.accumulators_eq) ∧ (type_of% @B0Value.b0_value_W) :=
  ⟨@Machine.GaussianLine.line_hoareF, @b0_hoareF, @WindowSum.accumulators_eq, @B0Value.b0_value_W⟩

end IntegerMultBounds.Resampling.B0Tape

namespace IntegerMultBounds.LineCost

/-- Lemma 7.2's costs: the Gaussian row times `T p`, at most `2 d T / r` lines, and negligible
polynomial setup per line. -/
theorem tensor_line_costs :
    (type_of% @linewise_sum) ∧ (type_of% @gaussian_lines_eq) ∧ (type_of% @lines_le) ∧
    (type_of% @setup_isLittleO) ∧ (type_of% @eventually_setup_le) :=
  ⟨@linewise_sum, @gaussian_lines_eq, @lines_le, @setup_isLittleO, @eventually_setup_le⟩

end IntegerMultBounds.LineCost

namespace IntegerMultBounds.NLogN

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] {α : ℝ}

/-- Lemma 7.2 with the manuscript's maps: the `d`-dimensional permutation-left identity with
contractions, and the tensor products of the explicit `Ã` and the clamp-free `B̃₀` approximating
`𝒜` and `ℬ₀` with errors `d·errA` and `d·errB₀H`, each per-axis error below `p²`, both mapping the
unit disk to itself. -/
theorem permuted_multi_numeric_manuscript (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 2 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1)) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p) :
    ∃ J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ),
      permRCLM s t ∘L dftDCLM s = ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) •
        (tensorRCLM (fun i => resampB₀ (s i) (t i) α (J i)) ∘L permQCLM s t ∘L dftDCLM t ∘L
          tensorRCLM (fun i => resampA (s i) (t i) α)) ∧
      ‖tensorRCLM (fun i => resampA (s i) (t i) α)‖ ≤ 1 ∧
      ‖tensorRCLM (fun i => resampB₀ (s i) (t i) α (J i))‖ ≤ 1 ∧
      ApproxMap p (tensorZR d s t fun i => resampANum (s i) (t i) m (resampTermNum p (s i) (t i) α))
        (tensorRCLM fun i => resampA (s i) (t i) α) (d * errA m) ∧
      ApproxMap p (tensorZR d t s fun i => resampB₀NumH p (sqrtWindow p) (s i) (t i) α)
        (tensorRCLM fun i => resampB₀ (s i) (t i) α (J i)) (d * errB₀H (sqrtWindow p)) ∧
      errA m < (p : ℝ) ^ 2 ∧ errB₀H (sqrtWindow p) < (p : ℝ) ^ 2 ∧
      (∀ u, ‖u‖ ≤ 1 → ‖tensorZR d s t (fun i => resampANum (s i) (t i) m (resampTermNum p (s i) (t i) α)) u‖ ≤ 1) ∧
      (∀ w, ‖w‖ ≤ 1 → ‖tensorZR d t s (fun i => resampB₀NumH p (sqrtWindow p) (s i) (t i) α) w‖ ≤ 1) := by
  have h := fun i => permuted_numeric_manuscript (hst i) (hcop i) hα (hθ i) hαp hm hm1 hmp hp
  choose J hJ using h
  refine ⟨J, permuted_factorization_multi α J fun i => (hJ i).1,
    opNorm_tensorRCLM_le _ fun i => (hJ i).2.1, opNorm_tensorRCLM_le _ fun i => (hJ i).2.2.1,
    ?_, ?_, errA_lt_sq' hmp (by omega), errB₀H_sqrt_lt_sq hp,
    tensorZR_ball d s t _ fun i v hv => (hJ i).2.2.2.2.2.2.2.1 v hv,
    tensorZR_ball d t s _ fun i v hv => (hJ i).2.2.2.2.2.2.2.2 v hv⟩
  · rw [← tensorZRCLM_eq_tensorRCLM]
    have := approxMap_tensorZR d s t (fun i => resampANum (s i) (t i) m (resampTermNum p (s i) (t i) α))
      (fun i => resampA (s i) (t i) α) (fun _ => errA m) (fun i => (hJ i).2.1)
      (fun i => (hJ i).2.2.2.1) (fun i v hv => (hJ i).2.2.2.2.2.2.2.1 v hv)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  · rw [← tensorZRCLM_eq_tensorRCLM]
    have := approxMap_tensorZR d t s (fun i => resampB₀NumH p (sqrtWindow p) (s i) (t i) α)
      (fun i => resampB₀ (s i) (t i) α (J i)) (fun _ => errB₀H (sqrtWindow p)) (fun i => (hJ i).2.2.1)
      (fun i => (hJ i).2.2.2.2.1) (fun i v hv => (hJ i).2.2.2.2.2.2.2.2 v hv)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

end IntegerMultBounds.NLogN
