module

public import IntegerMultBounds.Networks.ComplexPhaseBudget
public import IntegerMultBounds.Networks.BinaryColumnFrame
public import IntegerMultBounds.Networks.GroupedModuleFrames
public import IntegerMultBounds.Networks.FramedFactorExecution

/-! Actual framed execution of the size-25 complex network on complex arrays.
Rational gates retain their original graph and coefficients. The theorem
identifies the whole physical run with the signed bank exchange conjugated
by its actual endpoint frames, including every scratch wire. -/

@[expose] public section

namespace IntegerMultBounds.Networks.ComplexFramedExecution

open ComplexRank25 ComplexPhaseBudget

abbrev Wire := Wires.ComplexRole 25

/-- The actual signed exchange sends each output bank to the other input bank. -/
def route : Wire → Wire
  | Sum.inl b => Sum.inr (Sum.inl b)
  | Sum.inr (Sum.inl b) => Sum.inl b
  | Sum.inr (Sum.inr s) => Sum.inr (Sum.inr s)

def sign : Wire → ℚ
  | Sum.inl _ => -1
  | _ => 1

noncomputable def rows := GroupedCircuit.compileGroups (program.map GroupedFrames.Vertex.group)

/-- The exact existing rational scalar program, in routed form. -/
theorem scalar_route (x : Wire → ℚ) : Circuit.run rows x = fun i => sign i * x (route i) := by
  have he := GlobalGrouped.complexProgram_run triples pairs
    (fun b => x (Sum.inl b)) (fun b => x (Sum.inr (Sum.inl b)))
    (fun s => x (Sum.inr (Sum.inr s)))
  have hx : GlobalCircuit.contents (fun b => x (Sum.inl b))
      (fun b => x (Sum.inr (Sum.inl b))) (fun s => x (Sum.inr (Sum.inr s))) = x := by
    funext i
    rcases i with b | b | s <;> rfl
  rw [hx] at he
  unfold rows
  rw [program_groups, GroupedCircuit.compileGroups_run, he]
  funext i
  rcases i with b | b | s <;> simp [GlobalCircuit.contents, sign, route]

/-- The same actual complex column frame viewed as a rational-linear frame. -/
noncomputable def frameOf (k : ℕ) (U : Label) :
    FramedCircuit.Frame ℚ (BinaryColumns.Arrays (25 ^ 3) k) :=
  BinaryColumnFrame.rationalLabelFrame coordinateSymm k
    (LabelTransport.label (TensorCoordinates.coordinates 25) U)

/-- The complete physical grouped schedule and terminal edge instructions. -/
noncomputable def network (k : ℕ) :=
  GroupedModuleFrames.network (frameOf k) wires (GlobalLabels.source vector)
    (GlobalLabels.sink (Labels.binary 25) vector) program

abbrev Directions := List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3)))

noncomputable def factorMaps (k : ℕ) (directions : Directions) :
    List (List (BinaryColumns.Arrays (25 ^ 3) k →ₗ[ℚ] BinaryColumns.Arrays (25 ^ 3) k)) :=
  directions.map (fun gs => gs.map (fun g => (BinaryColumns.vectorFactor k g).restrictScalars ℚ))

/-- Executable finite instructions place each factor on the original wire,
retaining all scalar gates in their original order. These are array operations. -/
noncomputable def lowered (k : ℕ) (directions : Directions) :=
  FramedFactorExecution.lower (network k) (factorMaps k directions)

end IntegerMultBounds.Networks.ComplexFramedExecution
