module

public import IntegerMultBounds.Machine.OneSourceCircuit
public import IntegerMultBounds.Machine.Shared50RecursiveInduction
public import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
public import IntegerMultBounds.Machine.Shared50RecursiveSegments
public import IntegerMultBounds.Machine.Shared50TapeInvocation
public import IntegerMultBounds.Machine.Shared50XorLists
public import IntegerMultBounds.Networks.BinaryOrthonormal
public import IntegerMultBounds.Networks.BinaryPhase
public import IntegerMultBounds.Networks.ComplexEndpoints
public import IntegerMultBounds.Networks.GaussianPrecision
public import IntegerMultBounds.Networks.GlobalBinaryResiduals
public import IntegerMultBounds.Networks.GlobalCircuit
public import IntegerMultBounds.Networks.GlobalCircuitBits
public import IntegerMultBounds.Networks.GroupedFrames
public import IntegerMultBounds.Networks.Labels
public import IntegerMultBounds.Networks.NeighborCounts
public import IntegerMultBounds.Networks.NeighborResidual
public import IntegerMultBounds.Networks.Shared50Certificate
public import IntegerMultBounds.Networks.Shared50Finite
public import IntegerMultBounds.Networks.Shared50FiniteFramed
public import IntegerMultBounds.Networks.Shared50FiniteInterchange
public import IntegerMultBounds.Networks.Shared50GlobalShear
public import IntegerMultBounds.Networks.Shared50ModularExecution
public import IntegerMultBounds.Networks.ShearFrame
public import IntegerMultBounds.Networks.TensorLabels
public import IntegerMultBounds.Networks.Wires

/-! Section 3 milestones (plan/03-finite-networks-rank.md): one theorem per sub-problem, each bundling the exact statements of its proved pieces. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GlobalCircuit

/-- For the actual complex (rational) and binary motif matrices, the global three-stage circuit sends (X, Y, scratch) to (-Y, X, scratch) on every triple address, restoring every invocation scratch bank. -/
theorem motif_program_run :
    (type_of% @IntegerMultBounds.Networks.GlobalCircuit.program_run) ∧
    (type_of% @IntegerMultBounds.Networks.GlobalCircuit.complexProgram_run) ∧
    (type_of% @IntegerMultBounds.Networks.GlobalCircuit.bitProgram_run) :=
  ⟨@IntegerMultBounds.Networks.GlobalCircuit.program_run, @IntegerMultBounds.Networks.GlobalCircuit.complexProgram_run, @IntegerMultBounds.Networks.GlobalCircuit.bitProgram_run⟩

end IntegerMultBounds.Networks.GlobalCircuit

namespace IntegerMultBounds.Networks.StageLabels

/-- At ground size 100 the triple, neighbor and role counts equal the manuscript totals, and the degree-one, tensor-cube and stage-boundary label spaces are nondegenerate with exact isometries. -/
theorem census_and_labels :
    (type_of% @IntegerMultBounds.Networks.Wires.complex_role_card) ∧
    (type_of% @IntegerMultBounds.Networks.Wires.complex_role_card_100) ∧
    (type_of% @IntegerMultBounds.Networks.NeighborCounts.complex_neighbor_card_100) ∧
    (type_of% @IntegerMultBounds.Networks.NeighborCounts.bit_neighbor_card_100) ∧
    (type_of% @IntegerMultBounds.Networks.Labels.binary_nondegenerate) ∧
    (type_of% @IntegerMultBounds.Networks.Labels.rational_nondegenerate) ∧
    (type_of% @IntegerMultBounds.Networks.Labels.cube_nondegenerate) ∧
    (type_of% @IntegerMultBounds.Networks.Labels.cube_line_decomposition) :=
  ⟨@IntegerMultBounds.Networks.Wires.complex_role_card, @IntegerMultBounds.Networks.Wires.complex_role_card_100, @IntegerMultBounds.Networks.NeighborCounts.complex_neighbor_card_100, @IntegerMultBounds.Networks.NeighborCounts.bit_neighbor_card_100, @IntegerMultBounds.Networks.Labels.binary_nondegenerate, @IntegerMultBounds.Networks.Labels.rational_nondegenerate, @IntegerMultBounds.Networks.Labels.cube_nondegenerate, @IntegerMultBounds.Networks.Labels.cube_line_decomposition⟩

end IntegerMultBounds.Networks.StageLabels

namespace IntegerMultBounds.Networks.GroupedFrames

/-- The compiled grouped network acts as the grouped scalar run through the label frames, every residual factor is a binary unit (orthonormal, phase and neighbor-residual factorizations), and all Gaussian-dyadic numerators meet the explicit bounds. -/
theorem grouped_units_identity :
    (type_of% @IntegerMultBounds.Networks.GroupedFrames.network_identity) ∧
    (type_of% @IntegerMultBounds.Networks.GroupedFrames.projection_rank_balance) ∧
    (type_of% @IntegerMultBounds.Networks.BinaryOrthonormal.exists_orthonormal_basis) ∧
    (type_of% @IntegerMultBounds.Networks.BinaryPhase.exists_phase_decomposition) ∧
    (type_of% @IntegerMultBounds.Networks.NeighborResidual.binary_neighbor_residual) ∧
    (type_of% @IntegerMultBounds.Networks.GlobalBinaryResiduals.network_residuals) ∧
    (type_of% @IntegerMultBounds.Networks.GaussianPrecision.bounded_projection_edges) :=
  ⟨@IntegerMultBounds.Networks.GroupedFrames.network_identity, @IntegerMultBounds.Networks.GroupedFrames.projection_rank_balance, @IntegerMultBounds.Networks.BinaryOrthonormal.exists_orthonormal_basis, @IntegerMultBounds.Networks.BinaryPhase.exists_phase_decomposition, @IntegerMultBounds.Networks.NeighborResidual.binary_neighbor_residual, @IntegerMultBounds.Networks.GlobalBinaryResiduals.network_residuals, @IntegerMultBounds.Networks.GaussianPrecision.bounded_projection_edges⟩

end IntegerMultBounds.Networks.GroupedFrames

namespace IntegerMultBounds.Networks.Shared50FiniteFramed

/-- The certified Shared50 program writes the paired-exclusion support sum at every output, has at most 450,394 additions, 509,194 roles and 959,588 XOR updates, and compiles into forward and complementary-inverse framed scalar programs with exact frame identities. -/
theorem certified_compilation :
    (type_of% @IntegerMultBounds.Networks.Shared50Finite.run_output) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50Certificate.addition_bound) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50Certificate.role_bound) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50Certificate.instruction_bound) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50FiniteFramed.forward_identity) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50FiniteFramed.inverse_identity) :=
  ⟨@IntegerMultBounds.Networks.Shared50Finite.run_output, @IntegerMultBounds.Networks.Shared50Certificate.addition_bound, @IntegerMultBounds.Networks.Shared50Certificate.role_bound, @IntegerMultBounds.Networks.Shared50Certificate.instruction_bound, @IntegerMultBounds.Networks.Shared50FiniteFramed.forward_identity, @IntegerMultBounds.Networks.Shared50FiniteFramed.inverse_identity⟩

end IntegerMultBounds.Networks.Shared50FiniteFramed

namespace IntegerMultBounds.Machine.Shared50TapeInvocation

/-- The certified Shared50 forward program and its complementary inverse run on fixed role tapes with exact paired-exclusion outputs and restored dirty scratch and heads, within the certified instruction count times (14L + 14·width + 34) steps. -/
theorem compiled_hoare :
    (type_of% @IntegerMultBounds.Machine.Shared50TapeInvocation.invocation_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50TapeInvocation.invocation_cost50) ∧
    (type_of% @IntegerMultBounds.Machine.OneSourceCircuit.circuit_hoare) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50XorLists.finite) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50XorLists.inverse) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50Finite.run_output) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50Certificate.instruction_bound) :=
  ⟨@IntegerMultBounds.Machine.Shared50TapeInvocation.invocation_hoare, @IntegerMultBounds.Machine.Shared50TapeInvocation.invocation_cost50, @IntegerMultBounds.Machine.OneSourceCircuit.circuit_hoare, @IntegerMultBounds.Machine.Shared50XorLists.finite, @IntegerMultBounds.Machine.Shared50XorLists.inverse, @IntegerMultBounds.Networks.Shared50Finite.run_output, @IntegerMultBounds.Networks.Shared50Certificate.instruction_bound⟩

end IntegerMultBounds.Machine.Shared50TapeInvocation

namespace IntegerMultBounds.Networks.Shared50FiniteInterchange

/-- At every radix exponent over the one good prime, the pre/network/post program transposes both finite address chunks of every routed array including dirty scratch, is realized by its ordered physical field programs, and uses exactly the improved interchange count. -/
theorem certified_interchange :
    (type_of% @IntegerMultBounds.Networks.Shared50FiniteInterchange.program_identity) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50FiniteInterchange.physical_realizes) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50FiniteInterchange.interchanges_exact) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50GlobalShear.program_identity) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50ModularExecution.program_identity) :=
  ⟨@IntegerMultBounds.Networks.Shared50FiniteInterchange.program_identity, @IntegerMultBounds.Networks.Shared50FiniteInterchange.physical_realizes, @IntegerMultBounds.Networks.Shared50FiniteInterchange.interchanges_exact, @IntegerMultBounds.Networks.Shared50GlobalShear.program_identity, @IntegerMultBounds.Networks.Shared50ModularExecution.program_identity⟩

end IntegerMultBounds.Networks.Shared50FiniteInterchange

namespace IntegerMultBounds.Machine.Shared50RecursiveNodeExecution

/-- Every node segment runs on tapes with its exact field action, the node pre/child/post decomposition composes to the full transpose, the recursive depth contract runs the fixed machine to the exact transpose within the node budget, and the finite interchange program is exact. -/
theorem finite_interchange_hoare :
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveSegments.realizes) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose.transpose_all) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50RecursiveInduction.contract) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50FiniteInterchange.program_identity) :=
  ⟨@IntegerMultBounds.Machine.Shared50RecursiveSegments.realizes, @IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose.transpose_all, @IntegerMultBounds.Machine.Shared50RecursiveInduction.contract, @IntegerMultBounds.Networks.Shared50FiniteInterchange.program_identity⟩

end IntegerMultBounds.Machine.Shared50RecursiveNodeExecution

namespace IntegerMultBounds.Networks.ShearFrame

/-- The Shared50 XOR lists compute exactly the sparse invocation and global scalar programs, the rational address shear is the framed full shear, and the corrected physical network applies the full forward tensor transform on data and dirty scratch. -/
theorem tape_interface_semantics :
    (type_of% @IntegerMultBounds.Networks.ComplexEndpoints.corrected_network_run) ∧
    (type_of% @IntegerMultBounds.Networks.ShearFrame.full_shear) ∧
    (type_of% @IntegerMultBounds.Machine.Shared50XorLists.invocation) ∧
    (type_of% @IntegerMultBounds.Networks.Shared50GlobalShear.program_identity) :=
  ⟨@IntegerMultBounds.Networks.ComplexEndpoints.corrected_network_run, @IntegerMultBounds.Networks.ShearFrame.full_shear, @IntegerMultBounds.Machine.Shared50XorLists.invocation, @IntegerMultBounds.Networks.Shared50GlobalShear.program_identity⟩

end IntegerMultBounds.Networks.ShearFrame
