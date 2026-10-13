module

public import IntegerMultBounds.Networks.GaussianHadamardBridge
public import IntegerMultBounds.Machine.ButterflyAxisWalsh
public import IntegerMultBounds.Schoenhage.DifHadamard

/-! The native most-significant-first address codec and the public natural
record addresses describe the same normalized selected-bit butterflies. -/

@[expose] public section
namespace IntegerMultBounds.Machine.PublicHadamardAddressBridge
noncomputable section
open Networks Networks.BinaryWalsh Networks.GaussianHadamardBridge
open Schoenhage
variable {addressBits coefficientCount : ℕ}

/-- The physical bit position of an original native binary coordinate. -/
def physicalBit (coordinate : Fin addressBits) : ℕ :=
  FlatCoordinateLayout.suffixFields coordinate

/-- Read one original coefficient in the unchanged native row-major codec. -/
def pullback (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    Arrays addressBits := fun address => input (FlatCoordinateLayout.rank address).val coefficient

theorem rank_bit (address : Address addressBits) (coordinate : Fin addressBits) :
    bitAt (FlatCoordinateLayout.rank address).val (physicalBit coordinate) =
      (address coordinate).val :=
  FlatCoordinateLayout.coordinate_value address coordinate

/-- Flipping the native coordinate has exactly the public addition/subtraction
partner address; no permutation or supplied partner identity is assumed. -/
theorem rank_flip (address : Address addressBits) (coordinate : Fin addressBits) :
    (FlatCoordinateLayout.rank (address + Pi.single coordinate 1)).val =
      flip (FlatCoordinateLayout.rank address).val (physicalBit coordinate) := by
  have updateEquation : address + Pi.single coordinate 1 =
      Function.update address coordinate (address coordinate+1) := by
    funext other
    by_cases same : other=coordinate
    · subst other; simp
    · simp [Pi.single_eq_of_ne same,Function.update_of_ne same]
  rw [updateEquation]
  have balance := FlatCoordinateLayout.rank_update_balance address coordinate (address coordinate+1)
  have binaryCases : ∀ value : ZMod 2, value=0 ∨ value=1 := by
    intro value
    fin_cases value
    · exact Or.inl rfl
    · exact Or.inr rfl
  unfold Schoenhage.flip
  rw [rank_bit]
  rcases binaryCases (address coordinate) with bitZero | bitOne
  · simp only [bitZero,zero_add,ZMod.val_zero,ZMod.val_one,zero_mul,one_mul,add_zero] at balance ⊢
    simp only [ite_true]
    exact balance
  · simp only [bitOne,show (1 : ZMod 2)+1=0 from rfl,ZMod.val_zero,ZMod.val_one,
      zero_mul,one_mul,add_zero] at balance ⊢
    simp only [ite_eq_right (by decide : (1 : ℕ)≠0)]
    unfold physicalBit
    omega

/-- Exact intertwining with the public H-zero butterfly on the literal original
record address, independently for every coefficient. -/
theorem coordinate_bfly (coordinate : Fin addressBits)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    coordinateHadamard coordinate (pullback input coefficient) =
      pullback (bfly (physicalBit coordinate) input) coefficient := by
  funext address
  rw [coordinate_hadamard_apply]
  have bitZeroIff : bitAt (FlatCoordinateLayout.rank address).val (physicalBit coordinate)=0 ↔
      address coordinate=0 := by
    rw [rank_bit]
    exact ZMod.val_eq_zero (address coordinate)
  simp only [pullback,bfly]
  by_cases bitZero : address coordinate=0
  · rw [ite_eq_left bitZero,ite_eq_left (bitZeroIff.mpr bitZero)]
    have partner := rank_flip address coordinate
    rw [Schoenhage.flip,ite_eq_left (bitZeroIff.mpr bitZero)] at partner
    rw [partner]
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  · rw [ite_eq_right bitZero,ite_eq_right (fun zero => bitZero (bitZeroIff.mp zero))]
    have partner := rank_flip address coordinate
    rw [Schoenhage.flip,ite_eq_right (fun zero => bitZero (bitZeroIff.mp zero))] at partner
    rw [partner]
    simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    ring

/-- The product convention and the public execution-list convention agree on
the same literal original addresses. Reversal only accounts for composition order. -/
theorem product_bflys (coordinates : List (Fin addressBits))
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    hadamardProduct coordinates (pullback input coefficient) =
      pullback (bflys (coordinates.reverse.map physicalBit) input) coefficient := by
  induction coordinates with
  | nil => rfl
  | cons coordinate coordinates inductionHypothesis =>
    simp only [hadamardProduct,List.map_cons,List.prod_cons] at inductionHypothesis ⊢
    change coordinateHadamard coordinate
      ((coordinates.map coordinateHadamard).prod (pullback input coefficient)) = _
    rw [inductionHypothesis,coordinate_bfly]
    simp only [List.reverse_cons,List.map_append,List.map_singleton,bflys,List.map_append,
      List.map_singleton,run_append,Schoenhage.run]

/-- Public selected physical bits in increasing chunk order. Their native
coordinates use the existing reversed coordinate codec. -/
def layerCoordinates (addressBits chunkCount chunkWidth selectedBit suffixBits : ℕ)
    (selectedFits : suffixBits+chunkCount*chunkWidth≤addressBits)
    (bitFits : selectedBit<chunkWidth) : List (Fin addressBits) :=
  List.ofFn (fun chunk : Fin chunkCount => ButterflyAxisWalsh.coordinate addressBits
    (suffixBits+Spec.SignedRingProduct.selPos chunkWidth selectedBit chunk.val)
    (by unfold Spec.SignedRingProduct.selPos; have := chunk.isLt; nlinarith))

theorem layerCoordinates_length (chunkCount chunkWidth selectedBit suffixBits : ℕ)
    (selectedFits : suffixBits+chunkCount*chunkWidth≤addressBits)
    (bitFits : selectedBit<chunkWidth) :
    (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits).length=
      chunkCount := by simp [layerCoordinates]

theorem layerCoordinates_nodup (chunkCount chunkWidth selectedBit suffixBits : ℕ)
    (selectedFits : suffixBits+chunkCount*chunkWidth≤addressBits)
    (bitFits : selectedBit<chunkWidth) :
    (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits).Nodup := by
  apply List.nodup_ofFn.mpr
  intro first second equal
  have physicalEqual := congrArg (fun coordinate : Fin addressBits => coordinate.rev.val) equal
  simp only [ButterflyAxisWalsh.coordinate,Fin.rev_rev] at physicalEqual
  apply Fin.ext
  unfold Spec.SignedRingProduct.selPos at physicalEqual
  have chunkPositive : 0<chunkWidth := by omega
  nlinarith

private theorem selected_positions (chunkCount chunkWidth selectedBit suffixBits : ℕ) :
    (List.ofFn (fun chunk : Fin chunkCount =>
      suffixBits+Spec.SignedRingProduct.selPos chunkWidth selectedBit chunk.val)).reverse =
      selList suffixBits chunkWidth selectedBit chunkCount := by
  induction chunkCount generalizing suffixBits with
  | zero => rfl
  | succ chunkCount inductionHypothesis =>
    rw [List.ofFn_succ,List.reverse_cons,selList]
    have tailPositions : (fun chunk : Fin chunkCount =>
        suffixBits+Spec.SignedRingProduct.selPos chunkWidth selectedBit chunk.succ.val) =
        (fun chunk : Fin chunkCount =>
          (suffixBits+chunkWidth)+Spec.SignedRingProduct.selPos chunkWidth selectedBit chunk.val) := by
      funext chunk
      simp only [Spec.SignedRingProduct.selPos,Fin.val_succ]
      ring
    rw [tailPositions,inductionHypothesis]
    simp only [Spec.SignedRingProduct.selPos,Fin.val_zero,Nat.zero_mul,Nat.zero_add]

theorem layerCoordinates_positions (chunkCount chunkWidth selectedBit suffixBits : ℕ)
    (selectedFits : suffixBits+chunkCount*chunkWidth≤addressBits)
    (bitFits : selectedBit<chunkWidth) :
    (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits).reverse.map
      physicalBit = selList suffixBits chunkWidth selectedBit chunkCount := by
  rw [List.map_reverse]
  simp only [layerCoordinates,List.map_ofFn,Function.comp_def,physicalBit,
    ButterflyAxisWalsh.suffix_fields]
  exact selected_positions chunkCount chunkWidth selectedBit suffixBits

/-- The public layer on its original natural-number record addresses is exactly
the native selected-coordinate Hadamard product. Only geometric fit is required. -/
theorem layer_hadamard (chunkCount chunkWidth selectedBit suffixBits : ℕ)
    (selectedFits : suffixBits+chunkCount*chunkWidth≤addressBits)
    (bitFits : selectedBit<chunkWidth)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    hadamardProduct (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits)
      (pullback input coefficient) =
      pullback (Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit (2^suffixBits) input)
        coefficient := by
  rw [product_bflys,layerCoordinates_positions,←hadamard_eq_bflys bitFits]

/-- Exact public selected-bit layer from the native Gaussian product, without a
supplied transform assertion, output equality, or execution premise. -/
theorem layer_gaussian (chunkCount chunkWidth selectedBit suffixBits : ℕ)
    (selectedFits : suffixBits+chunkCount*chunkWidth≤addressBits)
    (bitFits : selectedBit<chunkWidth)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    pullback (Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit (2^suffixBits) input)
      coefficient =
      (normalization^chunkCount •
        (addressPhase (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits) *
          gaussianProduct (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits) *
          addressPhase (layerCoordinates addressBits chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits)))
        (pullback input coefficient) := by
  rw [←layer_hadamard chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits,
    product_bridge _ (layerCoordinates_nodup chunkCount chunkWidth selectedBit suffixBits selectedFits bitFits),
    layerCoordinates_length]

/-- A public suffix of arbitrary positive cardinality is an unchanged spectator;
selected bits are read from the quotient, without a power-of-two restriction. -/
theorem selBit_block {chunkCount : ℕ} (chunkWidth selectedBit suffixSize record offset : ℕ)
    (suffixPositive : 0<suffixSize) (offsetFits : offset<suffixSize) (chunk : Fin chunkCount) :
    Spec.SignedRingProduct.selBit chunkWidth selectedBit suffixSize (suffixSize*record+offset) chunk =
      Spec.SignedRingProduct.selBit chunkWidth selectedBit 1 record chunk := by
  simp only [Spec.SignedRingProduct.selBit,Nat.mul_add_div suffixPositive,
    Nat.div_eq_of_lt offsetFits,Nat.add_zero,Nat.div_one]

theorem setSel_block (chunkCount chunkWidth selectedBit suffixSize record offset : ℕ)
    (bitFits : selectedBit<chunkWidth) (suffixPositive : 0<suffixSize) (offsetFits : offset<suffixSize)
    (newBits : Fin chunkCount → Bool) :
    Spec.SignedRingProduct.setSel chunkWidth selectedBit suffixSize (suffixSize*record+offset) newBits =
      suffixSize*Spec.SignedRingProduct.setSel chunkWidth selectedBit 1 record newBits+offset := by
  have clearedFits : (∑ chunk : Fin chunkCount,
      if Spec.SignedRingProduct.selBit chunkWidth selectedBit 1 record chunk then
        2^Spec.SignedRingProduct.selPos chunkWidth selectedBit chunk.val else 0) ≤ record := by
    have bound := clearSum_le bitFits chunkCount 0 record
    rw [←sum_sel_eq_clearSum] at bound
    simpa only [pow_zero,Nat.one_mul] using bound
  unfold Spec.SignedRingProduct.setSel
  simp only [selBit_block chunkWidth selectedBit suffixSize record offset suffixPositive offsetFits,Nat.one_mul]
  rw [Nat.add_comm (suffixSize*record) offset,
    Nat.add_sub_assoc (Nat.mul_le_mul_left suffixSize clearedFits),←Nat.mul_sub_left_distrib,
    Nat.mul_add]
  omega

/-- Exact public Hadamard action on a quotient-address slice with any positive
suffix size. This retains every original suffix offset and every coefficient. -/
theorem hadamard_block (chunkCount chunkWidth selectedBit suffixSize record offset : ℕ)
    (bitFits : selectedBit<chunkWidth) (suffixPositive : 0<suffixSize) (offsetFits : offset<suffixSize)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit suffixSize input
      (suffixSize*record+offset) coefficient =
      Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit 1
        (fun index => input (suffixSize*index+offset)) record coefficient := by
  unfold Spec.SignedRingProduct.hadamard
  simp only [selBit_block chunkWidth selectedBit suffixSize record offset suffixPositive offsetFits,
    setSel_block chunkCount chunkWidth selectedBit suffixSize record offset bitFits suffixPositive offsetFits]

/-- Factoring an arbitrary positive unchanged suffix outside a binary-address
slice preserves the exact public selected bits and replacement addresses. -/
theorem hadamard_scaled_suffix (chunkCount chunkWidth selectedBit baseSuffix suffixSize record offset : ℕ)
    (bitFits : selectedBit<chunkWidth)
    (suffixPositive : 0<suffixSize) (offsetFits : offset<suffixSize)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit (suffixSize*baseSuffix) input
      (suffixSize*record+offset) coefficient =
      Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit baseSuffix
        (fun index => input (suffixSize*index+offset)) record coefficient := by
  have quotientEquation : (suffixSize*record+offset)/(suffixSize*baseSuffix)=record/baseSuffix := by
    rw [←Nat.div_div_eq_div_mul,Nat.mul_add_div suffixPositive,
      Nat.div_eq_of_lt offsetFits,Nat.add_zero]
  have bitsEquation (chunk : Fin chunkCount) :
      Spec.SignedRingProduct.selBit chunkWidth selectedBit (suffixSize*baseSuffix)
          (suffixSize*record+offset) chunk =
        Spec.SignedRingProduct.selBit chunkWidth selectedBit baseSuffix record chunk := by
    unfold Spec.SignedRingProduct.selBit
    rw [quotientEquation]
  have clearedFits : baseSuffix*(∑ chunk : Fin chunkCount,
      if Spec.SignedRingProduct.selBit chunkWidth selectedBit baseSuffix record chunk then
        2^Spec.SignedRingProduct.selPos chunkWidth selectedBit chunk.val else 0) ≤ record := by
    have quotientBound := clearSum_le bitFits chunkCount 0 (record/baseSuffix)
    rw [←sum_sel_eq_clearSum] at quotientBound
    simp only [pow_zero,Nat.one_mul,Spec.SignedRingProduct.selBit,Nat.div_one] at quotientBound
    exact (Nat.mul_le_mul_left baseSuffix quotientBound).trans (Nat.mul_div_le record baseSuffix)
  have replacementEquation (newBits : Fin chunkCount → Bool) :
      Spec.SignedRingProduct.setSel chunkWidth selectedBit (suffixSize*baseSuffix)
          (suffixSize*record+offset) newBits =
        suffixSize*Spec.SignedRingProduct.setSel chunkWidth selectedBit baseSuffix record newBits+offset := by
    unfold Spec.SignedRingProduct.setSel
    simp only [bitsEquation,Nat.mul_assoc]
    rw [Nat.add_comm (suffixSize*record) offset,
      Nat.add_sub_assoc (Nat.mul_le_mul_left suffixSize clearedFits),←Nat.mul_sub_left_distrib,
      Nat.mul_add]
    omega
  unfold Spec.SignedRingProduct.hadamard
  simp only [bitsEquation,replacementEquation]

/-- The exact public layer with arbitrary positive suffix cardinality is the
phase-corrected native Gaussian product on the original quotient-address codec.
There is no execution, desired-output or transform-equivalence hypothesis. -/
theorem layer_gaussian_block (chunkCount chunkWidth selectedBit suffixSize offset : ℕ)
    (selectedFits : chunkCount*chunkWidth≤addressBits) (bitFits : selectedBit<chunkWidth)
    (suffixPositive : 0<suffixSize) (offsetFits : offset<suffixSize)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    (fun address : Address addressBits =>
      Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit suffixSize input
        (suffixSize*(FlatCoordinateLayout.rank address).val+offset) coefficient) =
      (normalization^chunkCount •
        (addressPhase (layerCoordinates addressBits chunkCount chunkWidth selectedBit 0 (by omega) bitFits) *
          gaussianProduct (layerCoordinates addressBits chunkCount chunkWidth selectedBit 0 (by omega) bitFits) *
          addressPhase (layerCoordinates addressBits chunkCount chunkWidth selectedBit 0 (by omega) bitFits)))
        (pullback (fun index => input (suffixSize*index+offset)) coefficient) := by
  have blockEquation : (fun address : Address addressBits =>
      Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit suffixSize input
        (suffixSize*(FlatCoordinateLayout.rank address).val+offset) coefficient) =
      pullback (Spec.SignedRingProduct.hadamard chunkCount chunkWidth selectedBit 1
        (fun index => input (suffixSize*index+offset))) coefficient := by
    funext address
    exact hadamard_block chunkCount chunkWidth selectedBit suffixSize _ offset
      bitFits suffixPositive offsetFits input coefficient
  rw [blockEquation]
  exact layer_gaussian chunkCount chunkWidth selectedBit 0 (by omega) bitFits _ coefficient

end
end IntegerMultBounds.Machine.PublicHadamardAddressBridge
