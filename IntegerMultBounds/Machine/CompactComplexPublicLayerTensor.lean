module

public import IntegerMultBounds.Machine.PublicHadamardAddressBridge
public import IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics

/-! The public selected-bit layer is the phase-corrected full tensor used by
the actual native root certificates, on the original immutable address codec. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexPublicLayerTensor
noncomputable section
open Networks Networks.BinaryWalsh Networks.GaussianHadamardBridge
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open PublicHadamardAddressBridge
variable {shape : Shape} {left childExponent coefficientCount : ℕ}

/-- Original lower spectators below the whole selected visit interval. -/
def suffixBits (shape : Shape) (left exponent : ℕ) : ℕ :=
  shape.H+shape.B+(shape.active-left-arity^exponent)*shape.chunk

theorem interval_fits (visit : Visit shape.active left (childExponent+1)) :
    suffixBits shape left (childExponent+1)+arity^(childExponent+1)*shape.chunk≤shape.bits := by
  have visitFits := visit.fits
  have intervalBalance : shape.active-left-arity^(childExponent+1)+arity^(childExponent+1)=shape.active-left := by
    omega
  have widthBalance := congrArg (fun count => count*shape.chunk) intervalBalance
  simp only [Nat.add_mul] at widthBalance
  unfold suffixBits Shape.bits
  have activeFits : (shape.active-left)*shape.chunk≤shape.active*shape.chunk :=
    Nat.mul_le_mul_right shape.chunk (Nat.sub_le _ _)
  omega

def coordinates (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active left (childExponent+1)) :=
  layerCoordinates shape.bits (arity^(childExponent+1)) shape.chunk phaseCoordinate.val
    (suffixBits shape left (childExponent+1)) (interval_fits visit) phaseCoordinate.isLt

/-- Reversing the public chunk ordinal gives exactly the native descending bit
positions, with no changed serialization or discarded spectators. -/
theorem coordinate_reversed (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active left (childExponent+1)) (ordinal : Fin (arity^(childExponent+1))) :
    ButterflyAxisWalsh.coordinate shape.bits
      (suffixBits shape left (childExponent+1)+
        Spec.SignedRingProduct.selPos shape.chunk phaseCoordinate.val ordinal.rev.val)
      (by have := interval_fits visit; have := ordinal.rev.isLt; have := phaseCoordinate.isLt;
          unfold Spec.SignedRingProduct.selPos; nlinarith) =
      ButterflyAxisWalsh.coordinate shape.bits
        (CompactSpectatorLeafSemantics.position shape phaseCoordinate visit ordinal)
        (CompactSpectatorLeafSemantics.position_lt shape phaseCoordinate visit ordinal) := by
  apply congrArg Fin.rev
  apply Fin.ext
  simp only [suffixBits,Spec.SignedRingProduct.selPos,Fin.val_rev,
    CompactSpectatorLeafSemantics.position,CompactSpectatorLeafHeaders.selected,
    CompactSpectatorVisitGeometry.selected]
  have visitFits := visit.fits
  have ordinalFits := ordinal.isLt
  have countPositive : 0<arity^(childExponent+1) := pow_pos (by decide) _
  have countBalance : shape.active-left-arity^(childExponent+1)+
      (arity^(childExponent+1)-(ordinal.val+1))=shape.active-1-(left+ordinal.val) := by omega
  have weightedBalance := congrArg (fun count => count*shape.chunk) countBalance
  simp only [Nat.add_mul] at weightedBalance
  simp only [Nat.add_zero]
  omega

theorem gaussian_native (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active left (childExponent+1)) (input : Arrays shape.bits) :
    gaussianProduct (coordinates phaseCoordinate visit) input =
      kernelRun (CompactSpectatorLeafSemantics.directions shape phaseCoordinate visit
        (arity^(childExponent+1)) le_rfl) input := by
  rw [kernelRun_eq_frame]
  unfold gaussianProduct coordinateGaussian
  have frameProduct := BinaryColumns.kernel_prod_eq_frame
    ((coordinates phaseCoordinate visit).map (fun coordinate => ((1 : ZMod 4),Pi.single coordinate 1)))
  simp only [List.map_map,Function.comp_def] at frameProduct
  rw [frameProduct]
  have phaseEquation :
      listPhase ((coordinates phaseCoordinate visit).map
        (fun coordinate => ((1 : ZMod 4),Pi.single coordinate 1))) =
      listPhase (CompactSpectatorLeafSemantics.directions shape phaseCoordinate visit
        (arity^(childExponent+1)) le_rfl) := by
    funext address
    simp only [coordinates,layerCoordinates,List.map_ofFn,Function.comp_def,
      CompactSpectatorLeafSemantics.directions,listPhase_ofFn]
    rw [←(Equiv.sum_comp Fin.revPerm _)]
    apply Finset.sum_congr rfl
    intro ordinal _
    simp only [Fin.revPerm_apply]
    rw [coordinate_reversed phaseCoordinate visit ordinal]
    rfl
  rw [phaseEquation]
  rfl

/-- Every public quotient-address Gaussian product has the identical fullFrame
readout used by stopped and recursive positive-root certificates. -/
theorem gaussian_tensor (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active left (childExponent+1)) (input : Arrays shape.bits) :
    gaussianProduct (coordinates phaseCoordinate visit) input =
      fun anchor => ComplexEndpoints.fullFrame (arity^childExponent)
        (CompactComplexStoppedLeafTensorSemantics.slice phaseCoordinate visit anchor input)
        (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor) := by
  rw [gaussian_native]
  funext anchor
  have tensorEquation := CompactComplexStoppedLeafTensorSemantics.forward_kernel_tensor
    phaseCoordinate visit anchor input
  have atAnchor := congrFun tensorEquation (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor)
  simpa only [CompactComplexStoppedLeafTensorSemantics.slice,
    CompactComplexNonleafChildAddress.insert_address] using atAnchor

/-- Exact public selected-bit Hadamard action around the same native tensor
certified by actual roots. Input/output phase operations and dyadic normalization
remain explicit physical-wrapper obligations; no desired-output hypothesis occurs. -/
theorem layer_tensor (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active left (childExponent+1))
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    pullback (Spec.SignedRingProduct.hadamard (arity^(childExponent+1)) shape.chunk phaseCoordinate.val
      (2^suffixBits shape left (childExponent+1)) input) coefficient =
      normalization^(arity^(childExponent+1)) •
        addressPhase (coordinates phaseCoordinate visit)
          (fun anchor => ComplexEndpoints.fullFrame (arity^childExponent)
            (CompactComplexStoppedLeafTensorSemantics.slice phaseCoordinate visit anchor
              (addressPhase (coordinates phaseCoordinate visit) (pullback input coefficient)))
            (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor)) := by
  rw [layer_gaussian _ _ _ _ (interval_fits visit) phaseCoordinate.isLt]
  change normalization^(arity^(childExponent+1)) •
    (addressPhase (coordinates phaseCoordinate visit)
      (gaussianProduct (coordinates phaseCoordinate visit)
        (addressPhase (coordinates phaseCoordinate visit) (pullback input coefficient)))) = _
  rw [gaussian_tensor]

/-- The same native root tensor realizes the exact public layer with an
arbitrary positive outer suffix. Original quotient records, every suffix offset
and every coefficient are retained; only the phase/normalization wrapper is exposed. -/
theorem layer_tensor_block (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active left (childExponent+1)) (suffixSize offset : ℕ)
    (suffixPositive : 0<suffixSize) (offsetFits : offset<suffixSize)
    (input : ℕ → Fin coefficientCount → ℂ) (coefficient : Fin coefficientCount) :
    (fun anchor : Address shape.bits =>
      Spec.SignedRingProduct.hadamard (arity^(childExponent+1)) shape.chunk phaseCoordinate.val
        (suffixSize*2^suffixBits shape left (childExponent+1)) input
        (suffixSize*(FlatCoordinateLayout.rank anchor).val+offset) coefficient) =
      normalization^(arity^(childExponent+1)) •
        addressPhase (coordinates phaseCoordinate visit)
          (fun anchor => ComplexEndpoints.fullFrame (arity^childExponent)
            (CompactComplexStoppedLeafTensorSemantics.slice phaseCoordinate visit anchor
              (addressPhase (coordinates phaseCoordinate visit)
                (pullback (fun index => input (suffixSize*index+offset)) coefficient)))
            (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor)) := by
  have blockEquation : (fun anchor : Address shape.bits =>
      Spec.SignedRingProduct.hadamard (arity^(childExponent+1)) shape.chunk phaseCoordinate.val
        (suffixSize*2^suffixBits shape left (childExponent+1)) input
        (suffixSize*(FlatCoordinateLayout.rank anchor).val+offset) coefficient) =
      pullback (Spec.SignedRingProduct.hadamard (arity^(childExponent+1)) shape.chunk phaseCoordinate.val
        (2^suffixBits shape left (childExponent+1))
        (fun index => input (suffixSize*index+offset))) coefficient := by
    funext anchor
    exact hadamard_scaled_suffix _ _ _ _ suffixSize _ offset phaseCoordinate.isLt
      suffixPositive offsetFits input coefficient
  rw [blockEquation]
  exact layer_tensor phaseCoordinate visit _ coefficient

end
end IntegerMultBounds.Machine.CompactComplexPublicLayerTensor
