module

public import IntegerMultBounds.NLogN.Clamp
public import IntegerMultBounds.NLogN.DFT
public import IntegerMultBounds.NLogN.ErrorBudget
public import IntegerMultBounds.NLogN.FFT
public import IntegerMultBounds.NLogN.Multiplier
public import IntegerMultBounds.NLogN.SynthConvApproxD
public import IntegerMultBounds.NLogN.TensorApproxD
public import IntegerMultBounds.Schoenhage.Alu
public import IntegerMultBounds.Schoenhage.BatchMath
public import IntegerMultBounds.Schoenhage.Cmd
public import IntegerMultBounds.Schoenhage.FMachine
public import IntegerMultBounds.Schoenhage.IterCorrect
public import IntegerMultBounds.Schoenhage.Level
public import IntegerMultBounds.Schoenhage.Recomb
public import IntegerMultBounds.Schoenhage.Recursive
public import IntegerMultBounds.Schoenhage.RingBridgeMath
public import IntegerMultBounds.Schoenhage.RingLemma
public import IntegerMultBounds.Schoenhage.RingMath
public import IntegerMultBounds.Schoenhage.RingPointwiseTarget
public import IntegerMultBounds.Schoenhage.SSCost
public import IntegerMultBounds.Schoenhage.Schedule
public import IntegerMultBounds.Schoenhage.Stream
public import IntegerMultBounds.Schoenhage.Wp
public import IntegerMultBounds.Spec.PointwiseProducts
public import IntegerMultBounds.Spec.SignedRingProductFacts
public import IntegerMultBounds.Spec.SimultaneousLayerFacts
public import IntegerMultBounds.Spec.SyntheticTransformFacts

/-! Part A milestones (plan/A-schoenhage-strassen.md): one theorem per sub-problem, each bundling the exact statements of its proved pieces. -/

@[expose] public section

namespace IntegerMultBounds.NLogN

/-- The DFT convolution theorem and inversion, radix-2 FFT cost counts, the fixed-point pipeline error budget, the d-dimensional tensor approximation law, exactness of the plain FFT multiplier, the clamp approximation, and Proposition 3.4 for the d-dimensional synthetic convolution all hold. -/
theorem fourier_foundations :
    (type_of% @IntegerMultBounds.NLogN.dft_cconv) ∧
    (type_of% @IntegerMultBounds.NLogN.dft_dft) ∧
    (type_of% @IntegerMultBounds.NLogN.fftCost_le) ∧
    (type_of% @IntegerMultBounds.NLogN.pipeline_exact_recovery) ∧
    (type_of% @IntegerMultBounds.NLogN.approxMap_tensorD) ∧
    (type_of% @IntegerMultBounds.NLogN.mulFixed_correct) ∧
    (type_of% @IntegerMultBounds.NLogN.approxMap_clamp) ∧
    (type_of% @IntegerMultBounds.NLogN.synthConvNormD_approx) :=
  ⟨@IntegerMultBounds.NLogN.dft_cconv, @IntegerMultBounds.NLogN.dft_dft, @IntegerMultBounds.NLogN.fftCost_le, @IntegerMultBounds.NLogN.pipeline_exact_recovery, @IntegerMultBounds.NLogN.approxMap_tensorD, @IntegerMultBounds.NLogN.mulFixed_correct, @IntegerMultBounds.NLogN.approxMap_clamp, @IntegerMultBounds.NLogN.synthConvNormD_approx⟩

end IntegerMultBounds.NLogN

namespace IntegerMultBounds.Schoenhage

/-- For every scheduled N and residues x, y < 2^N+1, ssMul N x y = x*y mod 2^N+1, and the recursion's cost is at most C (N+1)(log N+1)(log log N+1). -/
theorem ssMul_correct_cost :
    (type_of% @IntegerMultBounds.Schoenhage.level_correct) ∧
    (type_of% @IntegerMultBounds.Schoenhage.ssMul_correct) ∧
    (type_of% @IntegerMultBounds.Schoenhage.Schedule.cost_le) :=
  ⟨@IntegerMultBounds.Schoenhage.level_correct, @IntegerMultBounds.Schoenhage.ssMul_correct, @IntegerMultBounds.Schoenhage.Schedule.cost_le⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

/-- Compiled finite-type machines have the same runs as the source machine and inherit its HoareTime contracts, and the weakest-precondition evaluator for word programs is sound. -/
theorem wordLayer_sound :
    (type_of% @IntegerMultBounds.Schoenhage.FMachine.run_toProgram) ∧
    (type_of% @IntegerMultBounds.Schoenhage.FMachine.hoare) ∧
    (type_of% @IntegerMultBounds.Schoenhage.wp_sound) :=
  ⟨@IntegerMultBounds.Schoenhage.FMachine.run_toProgram, @IntegerMultBounds.Schoenhage.FMachine.hoare, @IntegerMultBounds.Schoenhage.wp_sound⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

/-- Every big-step word-program execution is a run of the compiled literal program within its cost, the streaming transducer has its exact run and step count, and modular sub, add and multiply-by-2^t mod 2^N+1 run exactly in O(N) steps. -/
theorem wordLayer_runs :
    (type_of% @IntegerMultBounds.Schoenhage.compile_correct) ∧
    (type_of% @IntegerMultBounds.Schoenhage.Strm.stream_run) ∧
    (type_of% @IntegerMultBounds.Schoenhage.runs_subMod) ∧
    (type_of% @IntegerMultBounds.Schoenhage.runs_addMod) ∧
    (type_of% @IntegerMultBounds.Schoenhage.runs_mulPow2) :=
  ⟨@IntegerMultBounds.Schoenhage.compile_correct, @IntegerMultBounds.Schoenhage.Strm.stream_run, @IntegerMultBounds.Schoenhage.runs_subMod, @IntegerMultBounds.Schoenhage.runs_addMod, @IntegerMultBounds.Schoenhage.runs_mulPow2⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

/-- The layer-by-layer forward/inverse transforms, the up-sweep and level-batched recursion exactly as the tapes run them compute ssMul, with step count at most the schedule recurrence plus a linear term. -/
theorem tapeRecursion_eq_ssMul :
    (type_of% @IntegerMultBounds.Schoenhage.fwdIter_eq_fwd) ∧
    (type_of% @IntegerMultBounds.Schoenhage.invIter_eq_inv) ∧
    (type_of% @IntegerMultBounds.Schoenhage.levelTape_eq) ∧
    (type_of% @IntegerMultBounds.Schoenhage.upList_nextBatch) ∧
    (type_of% @IntegerMultBounds.Schoenhage.ssCost_le) :=
  ⟨@IntegerMultBounds.Schoenhage.fwdIter_eq_fwd, @IntegerMultBounds.Schoenhage.invIter_eq_inv, @IntegerMultBounds.Schoenhage.levelTape_eq, @IntegerMultBounds.Schoenhage.upList_nextBatch, @IntegerMultBounds.Schoenhage.ssCost_le⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

/-- Packing operands into digits, four products mod 2^N+1 and decoding give the negacyclic product coefficients, and the reversed output words are exactly the paper's record Q_p(fg/r). -/
theorem ringProduct_records :
    (type_of% @IntegerMultBounds.Schoenhage.ev_ncMul) ∧
    (type_of% @IntegerMultBounds.Schoenhage.encode_res) ∧
    (type_of% @IntegerMultBounds.Schoenhage.decode_pieces) ∧
    (type_of% @IntegerMultBounds.Schoenhage.ringOut_records) :=
  ⟨@IntegerMultBounds.Schoenhage.ev_ncMul, @IntegerMultBounds.Schoenhage.encode_res, @IntegerMultBounds.Schoenhage.decode_pieces, @IntegerMultBounds.Schoenhage.ringOut_records⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

/-- polylogTarget 1 ∧ pointwisePolylogTarget 1: fixed literal programs meet lem:signed-ring-product and the transform-header pointwise statement within O(T p log(rp) loglog(rp)) plus the header. -/
theorem ring_pointwise_polylog :
    (type_of% @IntegerMultBounds.Schoenhage.ring_polylog) ∧
    (type_of% @IntegerMultBounds.Schoenhage.pointwise_polylog) :=
  ⟨@IntegerMultBounds.Schoenhage.ring_polylog, @IntegerMultBounds.Schoenhage.pointwise_polylog⟩

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Spec.SignedRingProduct

/-- The paper-format statements are consistent: transform and ring headers read back, address bit reversal is an involution, the opposite exact transform undoes the forward one up to 1/M, and layer outputs lie in the unit disk within sqrt2 2^(-p) of H z. -/
theorem statements_consistent :
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.transformHeader_read) ∧
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.header_read) ∧
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.bitrevAddr_bitrevAddr) ∧
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.oppT_fwdT) ∧
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.oppExact_fwdExact) ∧
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.layerOut_norm_le) ∧
    (type_of% @IntegerMultBounds.Spec.SignedRingProduct.layerOut_close) :=
  ⟨@IntegerMultBounds.Spec.SignedRingProduct.transformHeader_read, @IntegerMultBounds.Spec.SignedRingProduct.header_read, @IntegerMultBounds.Spec.SignedRingProduct.bitrevAddr_bitrevAddr, @IntegerMultBounds.Spec.SignedRingProduct.oppT_fwdT, @IntegerMultBounds.Spec.SignedRingProduct.oppExact_fwdExact, @IntegerMultBounds.Spec.SignedRingProduct.layerOut_norm_le, @IntegerMultBounds.Spec.SignedRingProduct.layerOut_close⟩

end IntegerMultBounds.Spec.SignedRingProduct
