module

public import IntegerMultBounds.LayoutCost
public import IntegerMultBounds.NLogN.Bluestein
public import IntegerMultBounds.NLogN.BluesteinApprox
public import IntegerMultBounds.NLogN.ExplicitNumeric
public import IntegerMultBounds.NLogN.SynthConv
public import IntegerMultBounds.NLogN.SynthEmbed
public import IntegerMultBounds.NLogN.SynthFFT
public import IntegerMultBounds.NLogN.SynthMultiD

/-! §6 milestones (plan/06-synthetic-transforms-tape.md): one theorem per sub-problem, each bundling the exact statements of its proved pieces. -/

@[expose] public section

namespace IntegerMultBounds.NLogN

/-- Over C[y]/(y^r+1) with shift twiddles the 1- and d-dimensional synthetic DFTs satisfy the convolution theorem and inversion, the radix-2 FFT with per-level error eps is within n*eps of them in one and d dimensions, and the twisted embedding is an isometry carrying complex convolution to synthetic convolution. -/
theorem synth_transform_bounds :
    (type_of% @IntegerMultBounds.NLogN.synthDFT_conv) ∧
    (type_of% @IntegerMultBounds.NLogN.synthDFTInv_synthDFT) ∧
    (type_of% @IntegerMultBounds.NLogN.synth_fft_err) ∧
    (type_of% @IntegerMultBounds.NLogN.synthDFTD_conv) ∧
    (type_of% @IntegerMultBounds.NLogN.synthDFTDInv_synthDFTD) ∧
    (type_of% @IntegerMultBounds.NLogN.approxMap_synthDFTDNumC) ∧
    (type_of% @IntegerMultBounds.NLogN.norm_twist) ∧
    (type_of% @IntegerMultBounds.NLogN.synthConvG_toSynth) :=
  ⟨@IntegerMultBounds.NLogN.synthDFT_conv, @IntegerMultBounds.NLogN.synthDFTInv_synthDFT, @IntegerMultBounds.NLogN.synth_fft_err, @IntegerMultBounds.NLogN.synthDFTD_conv, @IntegerMultBounds.NLogN.synthDFTDInv_synthDFTD, @IntegerMultBounds.NLogN.approxMap_synthDFTDNumC, @IntegerMultBounds.NLogN.norm_twist, @IntegerMultBounds.NLogN.synthConvG_toSynth⟩

end IntegerMultBounds.NLogN

namespace IntegerMultBounds.NLogN

/-- The d-dimensional DFT of even lengths equals the chirp-convolution-chirp pipeline exactly, and with approximate chirps (eps_a) and approximate normalized convolution (eps_M) the pipeline has scaled error at most eps_M + 3 eps_a + 4. -/
theorem bluesteinD_exact_approx :
    (type_of% @IntegerMultBounds.NLogN.bluesteinD) ∧
    (type_of% @IntegerMultBounds.NLogN.bluesteinApproxD_err) :=
  ⟨@IntegerMultBounds.NLogN.bluesteinD, @IntegerMultBounds.NLogN.bluesteinApproxD_err⟩

end IntegerMultBounds.NLogN

namespace IntegerMultBounds.LayoutCost

/-- Eventually: prefix slots are at most dK, chunk reordering needs at most Dq-1 exchanges costing at most d l K^(tau-1), there are exactly l rounds with error l*sqrt2*2^(-p) staying in the disk, descriptors have length at most C_desc p, K < l, and the resulting bracket equals the sum of the four cost-table rows. -/
theorem transform_layout_bracket :
    (type_of% @IntegerMultBounds.LayoutCost.prefix_slots_le) ∧
    (type_of% @IntegerMultBounds.LayoutCost.chunk_exchanges_le) ∧
    (type_of% @IntegerMultBounds.LayoutCost.exchange_cost_le) ∧
    (type_of% @IntegerMultBounds.LayoutCost.rounds_eq) ∧
    (type_of% @IntegerMultBounds.LayoutCost.compIter_error) ∧
    (type_of% @IntegerMultBounds.LayoutCost.compIter_disk) ∧
    (type_of% @IntegerMultBounds.LayoutCost.descriptor_length_le) ∧
    (type_of% @IntegerMultBounds.LayoutCost.eventually_K_lt_ℓ) ∧
    (type_of% @IntegerMultBounds.LayoutCost.bracket_eq_rows) :=
  ⟨@IntegerMultBounds.LayoutCost.prefix_slots_le, @IntegerMultBounds.LayoutCost.chunk_exchanges_le, @IntegerMultBounds.LayoutCost.exchange_cost_le, @IntegerMultBounds.LayoutCost.rounds_eq, @IntegerMultBounds.LayoutCost.compIter_error, @IntegerMultBounds.LayoutCost.compIter_disk, @IntegerMultBounds.LayoutCost.descriptor_length_le, @IntegerMultBounds.LayoutCost.eventually_K_lt_ℓ, @IntegerMultBounds.LayoutCost.bracket_eq_rows⟩

end IntegerMultBounds.LayoutCost
