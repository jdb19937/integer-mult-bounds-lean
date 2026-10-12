module

public import IntegerMultBounds.Machine.Counter
public import IntegerMultBounds.Machine.CounterTape
public import IntegerMultBounds.Machine.CountedCopy
public import IntegerMultBounds.Machine.CountedReverse
public import IntegerMultBounds.Machine.CountedSpanSeek
public import IntegerMultBounds.Machine.CountedSpanReset
public import IntegerMultBounds.Machine.CountedLoop
public import IntegerMultBounds.Machine.CountedLoopReuse
public import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
public import IntegerMultBounds.Machine.FlatCoordinateDimensions
public import IntegerMultBounds.Machine.Shared50RecursiveRootExecution
public import IntegerMultBounds.InterchangeMilestones

/-! §2 milestones for counters and counted loops
(plan/02-machine-model-streams.md), bundling the exact statements of the
proved pieces. -/

@[expose] public section

namespace IntegerMultBounds.Machine.StreamScheduler

/-- Counter increments cost amortized two flips each; the canonical dimension
words alone determine every common-coordinate descriptor with its value and
length bounds; and along every recursive child path the child headers, exact
volume division and descriptor costs are absorbed by the child volume. -/
theorem descriptors_exact :
    (type_of% @IntegerMultBounds.Counter.total_potential) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateDimensions.output_descriptors) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateDimensions.descriptor_value_bounds) ∧
    (type_of% @IntegerMultBounds.Machine.RecursiveInterchangeVolume.call_cost_absorbed) :=
  ⟨@IntegerMultBounds.Counter.total_potential, @IntegerMultBounds.Machine.FlatCoordinateDimensions.output_descriptors,
    @IntegerMultBounds.Machine.FlatCoordinateDimensions.descriptor_value_bounds, @IntegerMultBounds.Machine.RecursiveInterchangeVolume.call_cost_absorbed⟩

/-- The counted machines on tapes: counter increment, counted copy and reverse
copy, counted seek and reset, the counted body loops (binary, reusable and
radix-alphabet) with full clock cleanup, the physical construction of the
coordinate descriptors from the canonical b/W words, and the recursive network
scheduler halting with the exact transpose within its power-width bound. -/
theorem realizes_hoare :
    (type_of% @IntegerMultBounds.Machine.CounterTape.increment_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedCopy.copy_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedReverse.reverse_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedReverse.Reusable.reverse_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedSpanSeek.seek_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedSpanReset.reset_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedLoop.loop_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedLoopReuse.loop_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedLoopReuseAlphabet.loop_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateDimensions.construct_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveRootExecution.halts_power_bound) :=
  ⟨@IntegerMultBounds.Machine.CounterTape.increment_hoare, @IntegerMultBounds.Machine.CountedCopy.copy_hoare, @IntegerMultBounds.Machine.CountedReverse.reverse_hoare,
    @IntegerMultBounds.Machine.CountedReverse.Reusable.reverse_hoare, @IntegerMultBounds.Machine.CountedSpanSeek.seek_hoare,
    @IntegerMultBounds.Machine.CountedSpanReset.reset_hoare, @IntegerMultBounds.Machine.CountedLoop.loop_hoare, @IntegerMultBounds.Machine.CountedLoopReuse.loop_hoare,
    @IntegerMultBounds.Machine.CountedLoopReuseAlphabet.loop_hoare, @IntegerMultBounds.Machine.FlatCoordinateDimensions.construct_hoare,
    @IntegerMultBounds.Machine.Shared50RecursiveRootExecution.halts_power_bound⟩

end IntegerMultBounds.Machine.StreamScheduler
