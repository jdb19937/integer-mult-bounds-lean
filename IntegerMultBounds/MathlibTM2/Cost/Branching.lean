module

public import IntegerMultBounds.MathlibTM2.Node.Body
public import IntegerMultBounds.Machine.CompactComplexActualCallLoweredNetwork
import Mathlib.Tactic.Positivity.Finset
import IntegerMultBounds.Networks.NetworkBudget

/-!
# The branching ratio of the layer recursion

A node of level `j + 1` of the layer machine runs `F = factorCount (program ds)` child calls on
`NW` wires. This file computes `F` and bounds the ratio `F / NW` by `m ^ σ`.

* `br_factorCount_program`: `F` is the total length of the first `brEdges skeleton` direction
  lists (`lowerSkel` consumes one list per edge of the skeleton and ignores the rest).
* `br_edges_eq_length`: for directions realizing the edge operators (`Realizes ds`), there is one
  list per edge, so `F = (ds.map List.length).sum` (`br_factorCount_realizes`). `Realizes` fixes
  the product of each list and leaves its length free.
* `br_directions_realizes`, `br_factorCount_directions`: the directions `brDirs` of the original
  recursive call schema (`CompactComplexActualCallLoweredNetwork.directions`) realize the edges,
  and `F = rankSum` for them, the sum of the projector-difference ranks of the edges.
* `br_NW_eq`: `NW = 58645352620000`.
* `br_branching`: `F / NW < m ^ σ` for `brDirs`, with `σ < 1` (`br_sigma_lt_one`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks
  IntegerMultBounds.Machine ComplexFramedExecution

/-! ### Factor count of a lowered skeleton -/

/-- The number of edges of a skeleton. -/
def brEdges : List Skel → ℕ
  | [] => 0
  | .edge _ :: rest => brEdges rest + 1
  | .gate _ :: rest => brEdges rest

lemma br_factorCount_append (p q : List Instr) :
    factorCount (p ++ q) = factorCount p + factorCount q := by
  induction p with
  | nil => simp [factorCount]
  | cons i rest ih =>
      cases i with
      | factor w g => simp only [List.cons_append, factorCount, ih]; ring
      | gate g => simp only [List.cons_append, factorCount, ih]

lemma br_factorCount_factors (w : NWire) (gs : List (ZMod 4 × BinaryWalsh.Address m)) :
    factorCount (gs.map (Instr.factor w)) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, factorCount, ih, List.length_cons]

/-- The factor count of a lowered skeleton: one direction list per edge, in order. -/
theorem br_factorCount_lowerSkel (s : List Skel) (ds : Directions) :
    factorCount (lowerSkel s ds) = ((ds.take (brEdges s)).map List.length).sum := by
  induction s generalizing ds with
  | nil => simp [lowerSkel, factorCount, brEdges]
  | cons x rest ih =>
      cases x with
      | edge w =>
          rw [lowerSkel, br_factorCount_append, br_factorCount_factors, ih, brEdges]
          cases ds with
          | nil => simp
          | cons d ds => simp [List.take_succ_cons]
      | gate g => rw [lowerSkel, factorCount, brEdges, ih]

/-- The factor count of the node program. -/
theorem br_factorCount_program (ds : Directions) :
    factorCount (program ds) = ((ds.take (brEdges skeleton)).map List.length).sum :=
  br_factorCount_lowerSkel skeleton ds

/-! ### Edges of the skeleton -/

lemma br_edges_map {E : Type*} [AddCommGroup E] [Module ℚ E]
    (p : List (FramedCircuit.Instruction NWire ℚ E)) :
    brEdges (p.map skel) = (FramedFactorExecution.edgeOperators p).length := by
  induction p with
  | nil => rfl
  | cons instr rest ih =>
      cases instr with
      | edge w old next =>
          simp only [List.map_cons, skel, brEdges, FramedFactorExecution.edgeOperators,
            List.length_cons, ih]
      | gate g => simp only [List.map_cons, skel, brEdges, FramedFactorExecution.edgeOperators, ih]

/-- A realizing family has one direction list per edge of the skeleton. -/
theorem br_edges_eq_length (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) :
    brEdges skeleton = ds.length := by
  rw [skeleton, br_edges_map, (factor_certificate 0 ds hd).length_eq, factorMaps,
    List.length_map]

/-- The skeleton has one edge per physical edge of the network. -/
theorem br_edges_skeleton : brEdges skeleton = ComplexPhaseBudget.edges.length :=
  (br_edges_eq_length _ CompactComplexActualCallLoweredNetwork.realizes).trans
    CompactComplexActualCallLoweredNetwork.realizes.length_eq.symm

/-- For a realizing family the factor count is the total length of the direction lists. -/
theorem br_factorCount_realizes (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) :
    factorCount (program ds) = (ds.map List.length).sum := by
  rw [br_factorCount_program, br_edges_eq_length ds hd, List.take_length]

/-! ### The directions of the recursive call schema -/

/-- The directions of the original recursive call schema. -/
noncomputable abbrev brDirs : Directions := CompactComplexActualCallLoweredNetwork.directions

theorem br_directions_realizes : ComplexPhaseBudget.Realizes brDirs :=
  CompactComplexActualCallLoweredNetwork.realizes

/-- With the call-schema directions, a node makes `rankSum` child calls. -/
theorem br_factorCount_directions : factorCount (program brDirs) = ComplexRank25.rankSum := by
  rw [br_factorCount_realizes _ br_directions_realizes]
  exact CompactComplexActualCallLoweredNetwork.direction_count

theorem br_factorCount_le : factorCount (program brDirs) ≤ 916333630984500000 :=
  br_factorCount_directions ▸ ComplexRank25.rank_budget

/-! ### The branching ratio -/

/-- The number of wire roles. -/
theorem br_NW_eq : NW = 58645352620000 := NetworkBudget.complex_role_card_25

theorem br_sigma_lt_one : Parameters.sigma < 1 := by
  norm_num [Parameters.sigma]

/-- The branching ratio: `F / NW < m ^ σ` with `σ < 1`. -/
theorem br_branching :
    (factorCount (program brDirs) : ℝ) / NW < (m : ℝ) ^ Parameters.sigma := by
  rw [br_factorCount_directions, br_NW_eq,
    show ((m : ℕ) : ℝ) = 15625 by norm_num [m]]
  exact_mod_cast ComplexRank25.branching_bound

/-- Some realizing family of directions makes `rankSum` child calls per node, with branching
ratio below `m ^ σ`. -/
theorem br_exists_branching :
    ∃ ds : Directions, ComplexPhaseBudget.Realizes ds ∧
      factorCount (program ds) = ComplexRank25.rankSum ∧
      (factorCount (program ds) : ℝ) / NW < (m : ℝ) ^ Parameters.sigma :=
  ⟨brDirs, br_directions_realizes, br_factorCount_directions, br_branching⟩

end IntegerMultBounds.MathlibTM2.Cost
