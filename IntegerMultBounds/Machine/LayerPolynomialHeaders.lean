module

public import IntegerMultBounds.Machine.LayerReservationSetup

@[expose] public section
namespace IntegerMultBounds.Machine.LayerPolynomialHeaders
noncomputable section
variable {alphabet : ℕ}
open ActiveRepairRankHeadersCommands (State put)

def exponent (coefficientCount : ℕ) := Nat.clog 2 coefficientCount
def paddedCount (coefficientCount : ℕ) := 2^exponent coefficientCount
def schedule : List CompactGlobalRowHeaderOps.Op := [
  .logarithm 2 ![2,23] (by decide),.power 2 ![23,24] (by decide)]
def state (original : State) (coefficientCount : ℕ) :=
  put (put original 23 (exponent coefficientCount)) 24 (paddedCount coefficientCount)
def core := (CompactGlobalRowHeaderOps.compile (a:=alphabet) schedule).2
def construct := Placement.placed (core (alphabet:=alphabet)) LayerControlBank.nativePlacement
def program (roleCount arity : ℕ) := seq (LayerReservationSetup.program (alphabet:=alphabet) roleCount arity) construct

theorem executes (original : State) (coefficientCount : ℕ) (originalCount : original 2=some coefficientCount) :
    CompactGlobalRowHeaderOps.execute schedule original=state original coefficientCount := by
  simp [schedule,CompactGlobalRowHeaderOps.execute,CompactGlobalRowHeaderOps.eval,state,put,
    originalCount,exponent,paddedCount]

theorem valid (original : State) (coefficientCount : ℕ) (originalCount : original 2=some coefficientCount)
    (exponentBlank : original 23=none) (countBlank : original 24=none) (countPositive : 0<coefficientCount) :
    CompactGlobalRowHeaderOps.validSchedule schedule original := by
  simp [schedule,CompactGlobalRowHeaderOps.validSchedule,CompactGlobalRowHeaderOps.valid,CompactGlobalRowHeaderOps.eval,
    put,originalCount,exponentBlank,countBlank,countPositive]

def constructionCost (coefficientCount : ℕ) :=
  CompactGlobalRowHeaderPrimitives.logConstant 2*coefficientCount+
    FixedBasePowerDescriptor.constant 2*paddedCount coefficientCount+2

theorem core_runs (original : State) (coefficientCount : ℕ) (originalCount : original 2=some coefficientCount)
    (exponentBlank : original 23=none) (countBlank : original 24=none) (countPositive : 0<coefficientCount) :
    HoareTime (core (alphabet:=alphabet)) (· = ActiveRepairRankHeadersCommands.bank original)
      (· = ActiveRepairRankHeadersCommands.bank (state original coefficientCount)) (constructionCost coefficientCount) := by
  have executed := CompactGlobalRowHeaderOps.schedule_runs (a:=alphabet) schedule original
    (valid original coefficientCount originalCount exponentBlank countBlank countPositive)
  rw [executes original coefficientCount originalCount] at executed
  apply executed.consequence (fun _ ready => ready) (fun _ finished => finished)
  simp [schedule,CompactGlobalRowHeaderOps.scheduleCost,CompactGlobalRowHeaderOps.cost,CompactGlobalRowHeaderOps.eval,
    originalCount,put,constructionCost,exponent,paddedCount]
  omega

def output (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) : Tapes 60 alphabet :=
  LayerControlBank.block
    (LayerSelectedBitSetup.output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      firstArray secondArray thirdArray)
    (state (LayerReservationHeaders.finished roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth) coefficientCount)

def cost (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  LayerReservationSetup.cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth+
    1+constructionCost coefficientCount

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (roleCount arity : ℕ) (rolesPositive : 2≤roleCount) (arityPositive : 2≤arity)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (program (alphabet:=alphabet) roleCount arity)
      (· = Spec.SignedRingProduct.bank
        (Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray)
      (· = output roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray)
      (cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  have reservationRun := LayerReservationSetup.runs_public (alphabet:=alphabet) parameters parametersValid roleCount arity rolesPositive arityPositive
    precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible firstArray secondArray thirdArray
  have coefficientLower := admissible.2.2.1
  have coefficientRealPositive : (0 : ℝ)<coefficientCount :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) _) coefficientLower
  have coefficientPositive : 0<coefficientCount := by exact_mod_cast coefficientRealPositive
  have arithmeticRun := core_runs (alphabet:=alphabet)
    (LayerReservationHeaders.finished roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    coefficientCount rfl rfl rfl coefficientPositive
  have placed := hoare_place arithmeticRun LayerControlBank.nativePlacement
    (LayerSelectedBitSetup.output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      firstArray secondArray thirdArray)
  rw [LayerControlBank.native_bank,LayerControlBank.native_bank] at placed
  unfold LayerReservationSetup.output at reservationRun
  unfold program construct output cost
  exact reservationRun.seq placed

theorem original_fields (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (slot : Fin 17) :
    let bank := output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    bank.head (Fin.castAdd 15 (Fin.castAdd 28 slot))=
      (LayerSelectedBitSetup.output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray).head slot ∧
      bank.tape (Fin.castAdd 15 (Fin.castAdd 28 slot))=
        (LayerSelectedBitSetup.output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
          firstArray secondArray thirdArray).tape slot := by
  simp only [output,LayerControlBank.block,Tapes.append,Fin.addCases_left,and_self]

theorem padded_bounds (coefficientCount : ℕ) (countPositive : 0<coefficientCount) :
    coefficientCount≤paddedCount coefficientCount ∧ paddedCount coefficientCount<2*coefficientCount := by
  refine ⟨Nat.le_pow_clog (by decide) _,?_⟩
  by_cases countOne : coefficientCount=1
  · subst coefficientCount
    norm_num [paddedCount,exponent]
  · have countLarge : 1<coefficientCount := by omega
    have exponentPositive := Nat.clog_pos (by decide : 1<2) countLarge
    have smaller := Nat.pow_pred_clog_lt_self (by decide : 1<2) countLarge
    simp only [Nat.pred_eq_sub_one] at smaller
    unfold paddedCount exponent
    rw [show Nat.clog 2 coefficientCount=(Nat.clog 2 coefficientCount-1)+1 by omega,pow_succ]
    omega

theorem construction_linear (coefficientCount : ℕ) (countPositive : 0<coefficientCount) :
    constructionCost coefficientCount≤
      (CompactGlobalRowHeaderPrimitives.logConstant 2+2*FixedBasePowerDescriptor.constant 2+2)*coefficientCount := by
  have paddingBound := (padded_bounds coefficientCount countPositive).2
  have powerBound := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) (Nat.le_of_lt paddingBound)
  unfold constructionCost
  nlinarith

theorem descriptors (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) :
    let bank := output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    bank.head 40=1 ∧ bank.tape 40=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (exponent coefficientCount)) ∧
      bank.head 41=1 ∧ bank.tape 41=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (paddedCount coefficientCount)) :=
  ⟨rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.LayerPolynomialHeaders
