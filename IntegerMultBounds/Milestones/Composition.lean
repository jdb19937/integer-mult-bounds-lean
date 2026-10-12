module

public import IntegerMultBounds.Machine.Alphabet
public import IntegerMultBounds.Machine.AnyFlag
public import IntegerMultBounds.Machine.BinaryAdd
public import IntegerMultBounds.Machine.BinaryCompare
public import IntegerMultBounds.Machine.BinaryDivide
public import IntegerMultBounds.Machine.BinaryMultiply
public import IntegerMultBounds.Machine.BinarySub
public import IntegerMultBounds.Machine.Branch
public import IntegerMultBounds.Machine.Copy
public import IntegerMultBounds.Machine.CountedSeek
public import IntegerMultBounds.Machine.FiberLayoutData
public import IntegerMultBounds.Machine.FixedMul
public import IntegerMultBounds.Machine.FlatControlledShiftArray
public import IntegerMultBounds.Machine.FlatControlledShiftReady
public import IntegerMultBounds.Machine.FlatCoordinateLayout
public import IntegerMultBounds.Machine.FlatCoordinateScaling
public import IntegerMultBounds.Machine.FlatCoordinateShift
public import IntegerMultBounds.Machine.Frame
public import IntegerMultBounds.Machine.Gather
public import IntegerMultBounds.Machine.GaussianLine
public import IntegerMultBounds.Machine.GuardGadget
public import IntegerMultBounds.Machine.Hoare
public import IntegerMultBounds.Machine.KeyRoutine
public import IntegerMultBounds.Machine.Loop
public import IntegerMultBounds.Machine.OrderedSelect
public import IntegerMultBounds.Machine.PackedLine
public import IntegerMultBounds.Machine.Placement
public import IntegerMultBounds.Machine.PrefixAddressData
public import IntegerMultBounds.Machine.Protected
public import IntegerMultBounds.Machine.RadixAdd
public import IntegerMultBounds.Machine.RadixRational
public import IntegerMultBounds.Machine.RadixSort
public import IntegerMultBounds.Machine.RadixToBinary
public import IntegerMultBounds.Machine.RationalTranslationAffineBridge
public import IntegerMultBounds.Machine.Rewind
public import IntegerMultBounds.Machine.ScalingAffineBridge
public import IntegerMultBounds.Machine.Shared50InitializedSegments
public import IntegerMultBounds.Networks.AffineFieldSegments
public import IntegerMultBounds.Networks.OrderedAffine
public import IntegerMultBounds.Networks.Shared50CoefficientMachines

/-! Section 2 milestones (plan/02-composition-loops-frames.md): one theorem per sub-problem, each bundling the exact statements of its proved pieces. -/

@[expose] public section

namespace IntegerMultBounds.Machine.HoareTime

/-- Sequential composition, symbol branching, potential-bounded while loops, tape extension and reindexing, alphabet widening and protected overlays each turn the parts' Hoare contracts into the exact composed contract with the stated cost. -/
theorem combinator_rules :
    (type_of% @IntegerMultBounds.Machine.HoareTime.seq) ∧
    (type_of% @IntegerMultBounds.Machine.branch_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.while_hoare_potential) ∧
    (type_of% @IntegerMultBounds.Machine.HoareTime.extend) ∧
    (type_of% @IntegerMultBounds.Machine.HoareTime.reindex) ∧
    (type_of% @IntegerMultBounds.Machine.Alphabet.map_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.Alphabet.overlay_hoare) :=
  ⟨@IntegerMultBounds.Machine.HoareTime.seq, @IntegerMultBounds.Machine.branch_hoare, @IntegerMultBounds.Machine.while_hoare_potential, @IntegerMultBounds.Machine.HoareTime.extend, @IntegerMultBounds.Machine.HoareTime.reindex, @IntegerMultBounds.Machine.Alphabet.map_hoare, @IntegerMultBounds.Machine.Alphabet.overlay_hoare⟩

end IntegerMultBounds.Machine.HoareTime

namespace IntegerMultBounds.Machine.Placement

/-- The literal rewind, copy and counted forward/backward seek machines meet their exact contracts and runtimes, and placed on any selected slots of a larger bank they keep that contract and runtime while leaving every other tape untouched. -/
theorem basic_machines_hoare :
    (type_of% @IntegerMultBounds.Machine.Placement.hoare_at) ∧
    (type_of% @IntegerMultBounds.Machine.Rewind.rewind_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.Copy.copy_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedSeek.seek_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.CountedSeek.seek_backward_hoare) :=
  ⟨@IntegerMultBounds.Machine.Placement.hoare_at, @IntegerMultBounds.Machine.Rewind.rewind_hoare, @IntegerMultBounds.Machine.Copy.copy_hoare, @IntegerMultBounds.Machine.CountedSeek.seek_hoare, @IntegerMultBounds.Machine.CountedSeek.seek_backward_hoare⟩

end IntegerMultBounds.Machine.Placement

namespace IntegerMultBounds.Machine.ArithmeticWords

/-- The word-level outputs of binary add, subtract, compare, multiply and divide, fixed-radix add, radix-to-binary conversion and the rational-coefficient transducer equal the intended integer or modular values. -/
theorem values_exact :
    (type_of% @IntegerMultBounds.Machine.BinaryAdd.add_exact) ∧
    (type_of% @IntegerMultBounds.Machine.BinarySub.sub_exact) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryCompare.compare_exact) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryMultiply.horner_value) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryDivide.div_correct) ∧
    (type_of% @IntegerMultBounds.Machine.RadixAdd.add_exact) ∧
    (type_of% @IntegerMultBounds.Machine.RadixToBinary.output_binary) ∧
    (type_of% @IntegerMultBounds.Machine.RadixRational.output_ratMod) :=
  ⟨@IntegerMultBounds.Machine.BinaryAdd.add_exact, @IntegerMultBounds.Machine.BinarySub.sub_exact, @IntegerMultBounds.Machine.BinaryCompare.compare_exact, @IntegerMultBounds.Machine.BinaryMultiply.horner_value, @IntegerMultBounds.Machine.BinaryDivide.div_correct, @IntegerMultBounds.Machine.RadixAdd.add_exact, @IntegerMultBounds.Machine.RadixToBinary.output_binary, @IntegerMultBounds.Machine.RadixRational.output_ratMod⟩

end IntegerMultBounds.Machine.ArithmeticWords

namespace IntegerMultBounds.Machine.ArithmeticWords

/-- Each literal arithmetic machine (binary add, subtract, compare, multiply, divide, signed fixed-point multiply, radix add, radix-to-binary conversion and every actual Shared50 coefficient kernel) halts with its exact output word, preserved operands and its stated cost. -/
theorem machines_hoare :
    (type_of% @IntegerMultBounds.Machine.BinaryAdd.add_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinarySub.sub_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryCompare.compare_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryMultiply.multiply_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.BinaryDivide.divide_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.FixedMul.mul_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RadixAdd.add_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.RadixToBinary.convert_hoare) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50CoefficientMachines.coefficient_to_blank) :=
  ⟨@IntegerMultBounds.Machine.BinaryAdd.add_hoare, @IntegerMultBounds.Machine.BinarySub.sub_hoare, @IntegerMultBounds.Machine.BinaryCompare.compare_hoare, @IntegerMultBounds.Machine.BinaryMultiply.multiply_hoare, @IntegerMultBounds.Machine.BinaryDivide.divide_hoare, @IntegerMultBounds.Machine.FixedMul.mul_hoare, @IntegerMultBounds.Machine.RadixAdd.add_hoare, @IntegerMultBounds.Machine.RadixToBinary.convert_hoare, @IntegerMultBounds.Networks.Shared50CoefficientMachines.coefficient_to_blank⟩

end IntegerMultBounds.Machine.ArithmeticWords

namespace IntegerMultBounds.Machine.FlatCoordinateScaling

/-- For every actual network scale r and every width, the signed numerator/denominator/negation recipe applied on every fiber of the flat array realizes OrderedAffine.execute (.scale t (ratMod r)) on the whole array. -/
theorem scale_semantics :
    (type_of% @IntegerMultBounds.Machine.ScalingAffineBridge.actual_signed_get) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateScaling.array_entry) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.scale_destination) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.scale_transport) :=
  ⟨@IntegerMultBounds.Machine.ScalingAffineBridge.actual_signed_get, @IntegerMultBounds.Machine.FlatCoordinateScaling.array_entry, @IntegerMultBounds.Machine.FlatCoordinateLayout.scale_destination, @IntegerMultBounds.Machine.FlatCoordinateLayout.scale_transport⟩

end IntegerMultBounds.Machine.FlatCoordinateScaling

namespace IntegerMultBounds.Machine.FlatCoordinateLayout

/-- Rotating each fiber of the flat array by ratMod(r) times its earlier control coordinate, as read from the prefix counters, realizes OrderedAffine.execute (.shift t k r) on the whole array. -/
theorem shift_semantics :
    (type_of% @IntegerMultBounds.Machine.FiberLayoutData.translated_entry) ∧
    (type_of% @IntegerMultBounds.Machine.PrefixAddressData.enumeration_selected) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_destination) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_transport) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_offset) ∧
    (type_of% @IntegerMultBounds.Machine.RationalTranslationAffineBridge.actual_ordered_affine_symbol) :=
  ⟨@IntegerMultBounds.Machine.FiberLayoutData.translated_entry, @IntegerMultBounds.Machine.PrefixAddressData.enumeration_selected, @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_destination, @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_transport, @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_offset, @IntegerMultBounds.Machine.RationalTranslationAffineBridge.actual_ordered_affine_symbol⟩

end IntegerMultBounds.Machine.FlatCoordinateLayout

namespace IntegerMultBounds.Machine.FlatControlledShiftReady

/-- From blank workspace the fixed machine halts with the canonical common input holding the whole flat array shifted by the rational multiple of the earlier coordinate (explicit entry equation in the post), within (878+4c)·volume+29(c+1)+29 steps. -/
theorem realizes_shift :
    (type_of% @IntegerMultBounds.Machine.FlatControlledShiftReady.realizes_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.FlatControlledShiftReady.output_symbol) ∧
    (type_of% @IntegerMultBounds.Machine.FlatControlledShiftArray.array_entry) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateShift.realizes_hoare) :=
  ⟨@IntegerMultBounds.Machine.FlatControlledShiftReady.realizes_hoare, @IntegerMultBounds.Machine.FlatControlledShiftReady.output_symbol, @IntegerMultBounds.Machine.FlatControlledShiftArray.array_entry, @IntegerMultBounds.Machine.FlatCoordinateShift.realizes_hoare⟩

end IntegerMultBounds.Machine.FlatControlledShiftReady

namespace IntegerMultBounds.Machine.FlatCoordinateLayout

/-- On the common row-major coordinate layout, the ordered scale/shift stages of any nonrecursive Shared50 segment move each array entry exactly as the segment's field-program run, and every lower-triangular transform factors into such stages. -/
theorem segment_semantics :
    (type_of% @IntegerMultBounds.Networks.OrderedAffine.program_run) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.scale_transport) ∧
    (type_of% @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_transport) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50InitializedSegments.array_entry) ∧
    (type_of% @IntegerMultBounds.Networks.AffineFieldSegments.split_run_spec) :=
  ⟨@IntegerMultBounds.Networks.OrderedAffine.program_run, @IntegerMultBounds.Machine.FlatCoordinateLayout.scale_transport, @IntegerMultBounds.Machine.FlatCoordinateLayout.shift_transport, @IntegerMultBounds.Machine.Shared50InitializedSegments.array_entry, @IntegerMultBounds.Networks.AffineFieldSegments.split_run_spec⟩

end IntegerMultBounds.Machine.FlatCoordinateLayout

namespace IntegerMultBounds.Machine.PackedGadgets

/-- The gather, packed arithmetic line, guard flag word, any-flag scan, modular-counter record selection and Gaussian window line produce exactly their specified packed words and window sums. -/
theorem word_semantics :
    (type_of% @IntegerMultBounds.Machine.Gather.gather_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.PackedLine.line_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.GuardGadget.program_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.AnyFlag.any_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.OrderedSelect.select_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.GaussianLine.line_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.KeyRoutine.routine_hoare) :=
  ⟨@IntegerMultBounds.Machine.Gather.gather_hoare, @IntegerMultBounds.Machine.PackedLine.line_hoare, @IntegerMultBounds.Machine.GuardGadget.program_hoare, @IntegerMultBounds.Machine.AnyFlag.any_hoare, @IntegerMultBounds.Machine.OrderedSelect.select_hoare, @IntegerMultBounds.Machine.GaussianLine.line_hoare, @IntegerMultBounds.Machine.KeyRoutine.routine_hoare⟩

end IntegerMultBounds.Machine.PackedGadgets

namespace IntegerMultBounds.Machine.PackedGadgets

/-- The fixed gather, packed-line, guard-test, any-flag, ordered-select, key-routine and Gaussian-line machines each halt with their exact output words, restored scratch and their stated linear costs. -/
theorem machines_hoare :
    (type_of% @IntegerMultBounds.Machine.Gather.gather_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.PackedLine.line_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.GuardGadget.program_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.AnyFlag.any_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.OrderedSelect.select_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.KeyRoutine.routine_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.GaussianLine.line_hoare) :=
  ⟨@IntegerMultBounds.Machine.Gather.gather_hoare, @IntegerMultBounds.Machine.PackedLine.line_hoare, @IntegerMultBounds.Machine.GuardGadget.program_hoare, @IntegerMultBounds.Machine.AnyFlag.any_hoare, @IntegerMultBounds.Machine.OrderedSelect.select_hoare, @IntegerMultBounds.Machine.KeyRoutine.routine_hoare, @IntegerMultBounds.Machine.GaussianLine.line_hoare⟩

end IntegerMultBounds.Machine.PackedGadgets

namespace IntegerMultBounds.Machine.RadixSort

/-- RadixSort.sort is a permutation of the input records, ordered by key value and stable on equal keys. -/
theorem sort_spec :
    (type_of% @IntegerMultBounds.Machine.RadixSort.sort_pairwise) ∧
    (type_of% @IntegerMultBounds.Machine.RadixSort.sort_perm) ∧
    (type_of% @IntegerMultBounds.Machine.RadixSort.filter_sort_key) :=
  ⟨@IntegerMultBounds.Machine.RadixSort.sort_pairwise, @IntegerMultBounds.Machine.RadixSort.sort_perm, @IntegerMultBounds.Machine.RadixSort.filter_sort_key⟩

end IntegerMultBounds.Machine.RadixSort
