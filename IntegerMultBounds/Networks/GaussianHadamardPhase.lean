module

public import IntegerMultBounds.Networks.GaussianHadamardBridge

/-! Literal diagonal readout of the two phase corrections in the exact
Gaussian-to-Hadamard bridge. These identities are shared with physical scanners. -/

@[expose] public section
namespace IntegerMultBounds.Networks.GaussianHadamardPhase
noncomputable section
open BinaryWalsh BinaryPhase GaussianHadamardBridge
variable {addressBits : ℕ}

theorem addressPhase_apply (coordinates : List (Fin addressBits))
    (input : Arrays addressBits) (address : Address addressBits) :
    addressPhase coordinates input address =
      (coordinates.map (fun coordinate => phase (bitLift (address coordinate)))).prod * input address := by
  induction coordinates with
  | nil => simp [addressPhase]
  | cons coordinate coordinates inductionHypothesis =>
    change phase (bitLift (address coordinate)) * (addressPhase coordinates input address) = _
    rw [inductionHypothesis]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

theorem allCoordinates_apply (input : Arrays addressBits) (address : Address addressBits) :
    addressPhase (allCoordinates addressBits) input address = phase (weightPhase address)*input address := by
  rw [addressPhase_apply]
  simp only [allCoordinates,List.map_ofFn,Function.comp_def,List.prod_ofFn]
  rw [weightPhase,phase_sum]

/-- The same correction on every genuine tensor column. -/
def tensorPhase (columnCount : ℕ) : BinaryColumns.Operator addressBits columnCount :=
  BinaryColumns.tensorColumns columnCount (addressPhase (allCoordinates addressBits))

theorem tensorPhase_apply (columnCount : ℕ) (input : BinaryColumns.Arrays addressBits columnCount)
    (address : BinaryColumns.Address addressBits columnCount) :
    tensorPhase columnCount input address =
      (∏ column : Fin columnCount, phase (weightPhase (address column))) * input address := by
  have oneColumn (column : Fin columnCount) (array : BinaryColumns.Arrays addressBits columnCount) :
      BinaryColumns.liftColumn column (addressPhase (allCoordinates addressBits)) array address =
        phase (weightPhase (address column)) * array address := by
    change addressPhase (allCoordinates addressBits)
      (fun updated => array (Function.update address column updated)) (address column) = _
    rw [allCoordinates_apply,Function.update_eq_self]
  have productColumns (columns : List (Fin columnCount))
      (array : BinaryColumns.Arrays addressBits columnCount) :
      ((columns.map (fun column => BinaryColumns.liftColumn column
        (addressPhase (allCoordinates addressBits)))).prod) array address =
        (columns.map (fun column => phase (weightPhase (address column)))).prod * array address := by
    induction columns generalizing array with
    | nil => simp
    | cons column columns inductionHypothesis =>
      simp only [List.map_cons,List.prod_cons]
      change BinaryColumns.liftColumn column (addressPhase (allCoordinates addressBits))
        ((columns.map (fun column => BinaryColumns.liftColumn column
          (addressPhase (allCoordinates addressBits)))).prod array) address = _
      rw [oneColumn,inductionHypothesis,mul_assoc]
  have readout := productColumns (List.ofFn (fun column : Fin columnCount => column)) input
  simpa only [tensorPhase,BinaryColumns.tensorColumns,List.map_ofFn,Function.comp_def,List.prod_ofFn] using readout

end
end IntegerMultBounds.Networks.GaussianHadamardPhase
