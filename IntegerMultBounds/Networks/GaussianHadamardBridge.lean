module

public import IntegerMultBounds.Networks.BinaryColumns
public import IntegerMultBounds.Networks.ComplexEndpoints

/-! Exact conversion of the certified Gaussian phase frame to normalized
Hadamard butterflies. Input/output address phases and the dyadic Gaussian
normalization are explicit; no transform identity or machine run is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Networks.GaussianHadamardBridge
noncomputable section
open BinaryWalsh BinaryPhase
variable {addressBits : ℕ}

/-- One exact Gaussian-dyadic normalization factor per selected bit. -/
def normalization : ℂ := (1-Complex.I)/2

/-- Multiply the one-side of the selected address bit by I. -/
def coordinatePhase (coordinate : Fin addressBits) : Arrays addressBits →ₗ[ℂ] Arrays addressBits :=
  (phaseDiagonal (fun address => bitLift (address coordinate))).toLinearMap

/-- The ordinary normalized H-zero butterfly, defined independently of the
Gaussian kernel, with half-sum on bit zero and half-difference on bit one. -/
def coordinateHadamard (coordinate : Fin addressBits) : Arrays addressBits →ₗ[ℂ] Arrays addressBits :=
  (1/2 : ℂ) • ((phaseDiagonal (fun address => 2*bitLift (address coordinate))).toLinearMap+
    translation (Pi.single coordinate 1))

def coordinateGaussian (coordinate : Fin addressBits) : Arrays addressBits →ₗ[ℂ] Arrays addressBits :=
  kernel 1 (Pi.single coordinate 1)

private theorem gaussian_zero_algebra (current neighbor : ℂ) :
    ((1-Complex.I)/2)*(((1+Complex.I)/2)*current+((1-Complex.I)/2)*(Complex.I*neighbor))=
      (current+neighbor)/2 := by
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem gaussian_one_algebra (current neighbor : ℂ) :
    ((1-Complex.I)/2)*(Complex.I*(((1+Complex.I)/2)*(Complex.I*current)+((1-Complex.I)/2)*neighbor))=
      (neighbor-current)/2 := by
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-- The literal coordinate operator has exactly the public normalized
half-sum/half-difference action on the original address and its flipped bit. -/
theorem coordinate_hadamard_apply (coordinate : Fin addressBits) (input : Arrays addressBits) (address : Address addressBits) :
    coordinateHadamard coordinate input address=
      if address coordinate=0 then (input address+input (address+Pi.single coordinate 1))/2
      else (input (address+Pi.single coordinate 1)-input address)/2 := by
  change (1/2 : ℂ)*(phase (2*bitLift (address coordinate))*input address+input (address+Pi.single coordinate 1))=_
  have binaryCases : ∀ value : ZMod 2, value=0 ∨ value=1 := by
    intro value
    fin_cases value
    · exact Or.inl rfl
    · exact Or.inr rfl
  have phase_two : phase (2 : ZMod 4) = -1 := Complex.I_sq
  rcases binaryCases (address coordinate) with bitZero | bitOne
  · simp only [bitZero,bitLift_zero,mul_zero,phase_zero,one_mul,ite_true]
    ring
  · simp only [bitOne,bitLift_one,mul_one,phase_two,neg_one_mul,
      ite_eq_right (by decide : (1 : ZMod 2) ≠ 0)]
    ring

/-- Exact one-bit phase/normalization conversion; this is an operator equality
for every original array, not a supplied Hadamard assertion. -/
theorem coordinate_bridge (coordinate : Fin addressBits) :
    coordinateHadamard coordinate=
      normalization • (coordinatePhase coordinate*coordinateGaussian coordinate*coordinatePhase coordinate) := by
  apply LinearMap.ext
  intro input
  funext address
  rw [coordinate_hadamard_apply]
  change _=normalization*(phase (bitLift (address coordinate))*
    (((1+phase 1)/2)*(phase (bitLift (address coordinate))*input address)+
      ((1-phase 1)/2)*(phase (bitLift ((address+Pi.single coordinate 1 : Address addressBits) coordinate))*
        input (address+Pi.single coordinate 1))))
  rw [phase_one]
  simp only [Pi.add_apply,Pi.single_eq_same]
  have binaryCases : ∀ value : ZMod 2, value=0 ∨ value=1 := by
    intro value
    fin_cases value
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases binaryCases (address coordinate) with bitZero | bitOne
  · simpa only [bitZero,zero_add,bitLift_zero,bitLift_one,phase_one,phase_zero,one_mul,normalization,ite_true] using
      (gaussian_zero_algebra (input address) (input (address+Pi.single coordinate 1))).symm
  · simpa only [bitOne,show (1 : ZMod 2)+1=0 from rfl,bitLift_one,bitLift_zero,phase_one,phase_zero,
      one_mul,normalization,ite_eq_right (by decide : (1 : ZMod 2)≠0)] using
      (gaussian_one_algebra (input address) (input (address+Pi.single coordinate 1))).symm

/-- Address phases on any two bits commute, including a repeated bit. -/
theorem phase_commute (first second : Fin addressBits) : Commute (coordinatePhase first) (coordinatePhase second) := by
  apply LinearMap.ext
  intro input
  funext address
  change phase (bitLift (address first))*(phase (bitLift (address second))*input address)=
    phase (bitLift (address second))*(phase (bitLift (address first))*input address)
  ring

/-- A phase on one address bit commutes with the actual Gaussian kernel on a
different bit, allowing front/back corrections around one complete root call. -/
theorem phase_gaussian_commute (first second : Fin addressBits) (distinct : first≠second) :
    Commute (coordinatePhase first) (coordinateGaussian second) := by
  apply LinearMap.ext
  intro input
  funext address
  change phase (bitLift (address first))*
      (((1+phase 1)/2)*input address+((1-phase 1)/2)*input (address+Pi.single second 1))=
    ((1+phase 1)/2)*(phase (bitLift (address first))*input address)+
      ((1-phase 1)/2)*(phase (bitLift ((address+Pi.single second 1 : Address addressBits) first))*input (address+Pi.single second 1))
  rw [phase_one]
  simp only [Pi.add_apply,Pi.single_eq_of_ne distinct,add_zero]
  ring

/-- The exact original ordered products of coordinate operators. -/
def addressPhase (coordinates : List (Fin addressBits)) := (coordinates.map coordinatePhase).prod

def gaussianProduct (coordinates : List (Fin addressBits)) := (coordinates.map coordinateGaussian).prod

def hadamardProduct (coordinates : List (Fin addressBits)) := (coordinates.map coordinateHadamard).prod

private theorem regroup_products (coordinates : List (Fin addressBits)) (noDuplicates : coordinates.Nodup) :
    (coordinates.map (fun coordinate => coordinatePhase coordinate*coordinateGaussian coordinate*coordinatePhase coordinate)).prod=
      addressPhase coordinates*gaussianProduct coordinates*addressPhase coordinates := by
  induction coordinates with
  | nil => simp only [List.map_nil,List.prod_nil,addressPhase,gaussianProduct,mul_one]
  | cons coordinate coordinates inductionHypothesis =>
    obtain ⟨coordinateNew,noDuplicates⟩ := List.nodup_cons.mp noDuplicates
    have phaseTail := Commute.list_prod_right (coordinates.map coordinatePhase) (coordinatePhase coordinate)
      (by intro factor member; obtain ⟨other,_,rfl⟩ := List.mem_map.mp member; exact phase_commute coordinate other)
    have gaussianTail := Commute.list_prod_right (coordinates.map coordinateGaussian) (coordinatePhase coordinate)
      (by
        intro factor member
        obtain ⟨other,otherMember,rfl⟩ := List.mem_map.mp member
        exact phase_gaussian_commute coordinate other (by intro equal; subst other; exact coordinateNew otherMember))
    have tailPhaseGaussian := Commute.list_prod_left (coordinates.map coordinatePhase) (coordinateGaussian coordinate)
      (by
        intro factor member
        obtain ⟨other,otherMember,rfl⟩ := List.mem_map.mp member
        exact phase_gaussian_commute other coordinate (by intro equal; subst other; exact coordinateNew otherMember))
    simp only [List.map_cons,List.prod_cons,addressPhase,gaussianProduct] at inductionHypothesis ⊢
    rw [inductionHypothesis noDuplicates]
    change _=coordinatePhase coordinate*addressPhase coordinates*
      (coordinateGaussian coordinate*gaussianProduct coordinates)*(coordinatePhase coordinate*addressPhase coordinates)
    change Commute (coordinatePhase coordinate) (addressPhase coordinates) at phaseTail
    change Commute (coordinatePhase coordinate) (gaussianProduct coordinates) at gaussianTail
    change Commute (addressPhase coordinates) (coordinateGaussian coordinate) at tailPhaseGaussian
    calc
      coordinatePhase coordinate*coordinateGaussian coordinate*coordinatePhase coordinate*
          (addressPhase coordinates*gaussianProduct coordinates*addressPhase coordinates)=
        coordinatePhase coordinate*coordinateGaussian coordinate*(coordinatePhase coordinate*addressPhase coordinates)*
          gaussianProduct coordinates*addressPhase coordinates := by simp only [mul_assoc]
      _=coordinatePhase coordinate*coordinateGaussian coordinate*(addressPhase coordinates*coordinatePhase coordinate)*
          gaussianProduct coordinates*addressPhase coordinates := by rw [phaseTail.eq]
      _=coordinatePhase coordinate*(coordinateGaussian coordinate*addressPhase coordinates)*coordinatePhase coordinate*
          gaussianProduct coordinates*addressPhase coordinates := by simp only [mul_assoc]
      _=coordinatePhase coordinate*(addressPhase coordinates*coordinateGaussian coordinate)*coordinatePhase coordinate*
          gaussianProduct coordinates*addressPhase coordinates := by rw [←tailPhaseGaussian.eq]
      _=coordinatePhase coordinate*addressPhase coordinates*coordinateGaussian coordinate*
          (coordinatePhase coordinate*gaussianProduct coordinates)*addressPhase coordinates := by simp only [mul_assoc]
      _=coordinatePhase coordinate*addressPhase coordinates*coordinateGaussian coordinate*
          (gaussianProduct coordinates*coordinatePhase coordinate)*addressPhase coordinates := by rw [gaussianTail.eq]
      _=_ := by simp only [mul_assoc]

private theorem normalization_product (coordinates : List (Fin addressBits)) :
    (coordinates.map (fun coordinate => normalization •
      (coordinatePhase coordinate*coordinateGaussian coordinate*coordinatePhase coordinate))).prod=
      normalization^coordinates.length •
        (coordinates.map (fun coordinate => coordinatePhase coordinate*coordinateGaussian coordinate*coordinatePhase coordinate)).prod := by
  induction coordinates with
  | nil => simp
  | cons coordinate coordinates inductionHypothesis =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,inductionHypothesis,smul_mul_assoc,mul_smul_comm,
      smul_smul,pow_succ]

/-- One whole Gaussian root product becomes the original normalized Hadamard
product using explicit input/output address phases and one dyadic factor per
selected bit. No intermediate child or transform equality is assumed. -/
theorem product_bridge (coordinates : List (Fin addressBits)) (noDuplicates : coordinates.Nodup) :
    hadamardProduct coordinates=
      normalization^coordinates.length • (addressPhase coordinates*gaussianProduct coordinates*addressPhase coordinates) := by
  unfold hadamardProduct
  have coordinateEquality : coordinateHadamard (addressBits := addressBits) =
      fun coordinate => normalization • (coordinatePhase coordinate*coordinateGaussian coordinate*coordinatePhase coordinate) := by
    funext coordinate
    exact coordinate_bridge coordinate
  rw [coordinateEquality]
  rw [normalization_product,regroup_products coordinates noDuplicates]

/-- All original binary coordinates, without a supplied basis or transform identity. -/
def allCoordinates (addressBits : ℕ) : List (Fin addressBits) :=
  List.ofFn (fun coordinate => coordinate)

theorem gaussianProduct_allCoordinates :
    gaussianProduct (allCoordinates addressBits) = (frame weightPhase).toLinearMap := by
  have kernels := BinaryColumns.kernel_prod_eq_frame (ComplexEndpoints.coordinateKernels addressBits)
  rw [ComplexEndpoints.coordinateKernels_phase] at kernels
  simpa only [gaussianProduct,allCoordinates,coordinateGaussian,
    ComplexEndpoints.coordinateKernels,List.map_ofFn,Function.comp_def] using kernels

/-- The same full Gaussian tensor certified by the physical root execution
realizes normalized Hadamard on all original bits after exact front/back phases.
The normalization is paid once per bit and per column, including zero dimensions. -/
theorem fullFrame_bridge (columnCount : ℕ) :
    BinaryColumns.tensorColumns columnCount (hadamardProduct (allCoordinates addressBits)) =
      normalization^(addressBits*columnCount) •
        (BinaryColumns.tensorColumns columnCount (addressPhase (allCoordinates addressBits)) *
          (ComplexEndpoints.fullFrame (h := addressBits) columnCount).toLinearMap *
          BinaryColumns.tensorColumns columnCount (addressPhase (allCoordinates addressBits))) := by
  rw [product_bridge (allCoordinates addressBits)
    (List.nodup_ofFn.mpr (fun _ _ equal => equal))]
  rw [gaussianProduct_allCoordinates]
  simp only [allCoordinates,List.length_ofFn,ComplexEndpoints.tensorColumns_smul,
    BinaryColumns.tensorColumns_mul,←pow_mul]
  rfl

end
end IntegerMultBounds.Networks.GaussianHadamardBridge
