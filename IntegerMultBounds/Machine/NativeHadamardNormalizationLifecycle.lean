module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationHeaders
public import IntegerMultBounds.Machine.NativeHadamardNormalizationGrid
public import IntegerMultBounds.Machine.PlacementBank

/-! Original native descriptors drive a complete physical normalization:
construct the exact stream count and denominator target, normalize the source
in place, commit the new live denominator once, and erase every generated word.
No count, target, source-result or execution callback is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationLifecycle
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open ActiveRepairRankHeadersCommands (bank)
open NativeHadamardNormalizationHeaders (liveBank targeted increase)
open NativeHadamardNormalizationArray (result)
open SharedPlacementAlphabet (setTape)
variable {shape : Shape} {rows ell : ℕ}

def sourceBank (coefficients : Array shape rows ell) : Tapes 16 2 :=
  (MarkedWordCleanup.one (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients)) 0).append
    (SharedBank.empty 15 2)

def input (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell) :=
  (NativeHadamardNormalizationHeaders.input stage rows ell metadataPrecision live).append (sourceBank coefficients)

def prepared (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell) :=
  ((bank (a:=2) (targeted stage rows ell metadataPrecision live)).append (liveBank live)).append (sourceBank coefficients)

def output (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell) :=
  (NativeHadamardNormalizationHeaders.output stage rows ell metadataPrecision live).append (sourceBank (result coefficients))

def scanSlots : Fin 17 → Fin 60 := ![44,45,46,47,48,49,50,51,52,53,54,55,56,57,20,58,59]
theorem scan_injective : Function.Injective scanSlots := by decide +kernel

def scanPlacement := InjectivePlacement.placement scanSlots scan_injective (by decide : 17+43=60)
def scan := Placement.placed NativeHadamardNormalizationStream.program scanPlacement

def program := seq (seq (seq (seq (extend NativeHadamardNormalizationHeaders.setup 16)
    (extend (extend NativeHadamardNormalizationHeaders.prepareProgram 1) 16)) scan)
    (extend NativeHadamardNormalizationHeaders.commit 16))
    (extend (extend (ButterflyAxisHeadersArithmetic.compile (a:=2) NativeHadamardNormalizationHeaders.cleanupSchedule).2 1) 16)

def cost (stage : Stage shape) (metadataPrecision live wordWidth : ℕ) :=
  NativeHadamardNormalizationHeaders.cost stage rows ell metadataPrecision live+1+
    220*(rows*(2^shape.bits*2^ell)*(2*(wordWidth+1))+
      (RecursiveChildQuotientsConstant.bits (rows*(2^shape.bits*2^ell))).length+1)

private theorem scan_active (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell) :
    Placement.active scanPlacement (prepared stage metadataPrecision live coefficients)=
      NativeHadamardNormalizationStream.initial coefficients := by
  rw [scanPlacement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  all_goals intro port; fin_cases port
  all_goals rfl

private theorem source_replaced (headers : Tapes 44 2) (coefficients newCoefficients : Array shape rows ell) :
    setTape (headers.append (sourceBank coefficients)) (44 : Fin 60)
      (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word newCoefficients)) 0=
      headers.append (sourceBank newCoefficients) := by
  change setTape (headers.append (sourceBank coefficients)) (Fin.natAdd 44 (0 : Fin 16)) _ _ = _
  rw [SharedPlacementAlphabet.setTape_append_right]
  congr 1
  change setTape ((MarkedWordCleanup.one _ 0).append (SharedBank.empty 15 2)) (Fin.castAdd 15 (0 : Fin 1)) _ _ = _
  rw [SharedPlacementAlphabet.setTape_append_left]
  congr 1
  apply Placement.Tapes.ext'
  all_goals intro port; fin_cases port; rfl

private theorem scan_runs (stage : Stage shape) (metadataPrecision live wordWidth : ℕ) (coefficients : Array shape rows ell)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth) :
    HoareTime scan (fun storage => storage=prepared stage metadataPrecision live coefficients)
      (fun storage => storage=prepared stage metadataPrecision live (result coefficients))
      (220*(rows*(2^shape.bits*2^ell)*(2*(wordWidth+1))+
        (RecursiveChildQuotientsConstant.bits (rows*(2^shape.bits*2^ell))).length+1)) := by
  have active := scan_active stage metadataPrecision live coefficients
  apply InjectivePlacement.hoare_exact (NativeHadamardNormalizationStream.runs coefficients wordWidth coefficientWidths)
    scanSlots scan_injective (by decide : 17+43=60) _ _ active
  unfold NativeHadamardNormalizationStream.output
  change Placement.replace scanPlacement _ (setTape _ (0 : Fin 17) _ 0) = _
  rw [←active,PlacedDescriptorConstruction.replace_setTape]
  rw [scanPlacement,InjectivePlacement.active_slot]
  exact source_replaced _ coefficients (result coefficients)

/-- The literal coefficient array and original geometry/live words suffice for
all setup, scanning, copy-back, denominator commit and complete private cleanup.
Both the emitted source and its actual live descriptor use the same normalization
increase. Every setup/scan/commit/cleanup join is included in the exact budget. -/
theorem runs (stage : Stage shape) (metadataPrecision live wordWidth : ℕ) (coefficients : Array shape rows ell)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth) :
    HoareTime program (fun storage => storage=input stage metadataPrecision live coefficients)
      (fun storage => storage=output stage metadataPrecision live coefficients)
      (cost (rows:=rows) (ell:=ell) stage metadataPrecision live wordWidth) := by
  have setupRun := hoare_extend_eq (NativeHadamardNormalizationHeaders.setup_runs stage rows ell metadataPrecision live
    guardPositive axesPositive chunkPositive) (sourceBank coefficients)
  have prepareRun := hoare_extend_eq
    (hoare_extend_eq (NativeHadamardNormalizationHeaders.prepare_runs stage rows ell metadataPrecision live chunkPositive)
      (liveBank live)) (sourceBank coefficients)
  have scanRun := scan_runs stage metadataPrecision live wordWidth coefficients coefficientWidths
  have commitRun := hoare_extend_eq (NativeHadamardNormalizationHeaders.commit_runs stage rows ell metadataPrecision live)
    (sourceBank (result coefficients))
  have cleanupRun := hoare_extend_eq
    (hoare_extend_eq (NativeHadamardNormalizationHeaders.cleanup_runs stage rows ell metadataPrecision live)
      (liveBank (live+increase stage))) (sourceBank (result coefficients))
  apply ((((setupRun.seq prepareRun).seq scanRun).seq commitRun).seq cleanupRun).consequence
    (fun _ equality => equality) (fun _ equality => equality) ?_
  unfold cost NativeHadamardNormalizationHeaders.cost
  omega


/-- Exact normalization on the actual installed array and physically advanced
live descriptor. The original Path/grid supplies every signed guard; no target,
count, result or machine-execution premise is required. Native root placement
and the global public-layer format/cost conversion remain separate. -/
theorem runs_from_path {left exponent levels frames returned : ℕ}
    (stage : Stage shape) (precision baseline growthConstant live pendingAxes : ℕ)
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (stageWidth : stage.slots*stage.f=CompactComplexRecursiveGeometry.arity^exponent)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (pendingFits : pendingAxes≤shape.bits)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (coefficients : Array shape rows ell)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rows ell precision coefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rows ell precision live
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes) coefficients) :
    let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits precision
    let bound := CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes
    HoareTime program (fun storage => storage=input stage metadataPrecision live coefficients)
      (fun storage => storage=output stage metadataPrecision live coefficients ∧
        storage.head 43=1 ∧ storage.tape 43=RadixZeroFill.encodedBinary
          (RecursiveChildQuotientsConstant.bits
            (live+NativeHadamardNormalizationFactor.denominatorIncrease (CompactComplexRecursiveGeometry.arity^exponent))) ∧
        storage.head 44=0 ∧ storage.tape 44=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (result coefficients)) ∧
        CompactSpectatorInheritedGrid.Grid shape rows ell precision
          (live+NativeHadamardNormalizationFactor.denominatorIncrease (CompactComplexRecursiveGeometry.arity^exponent))
          (2*bound) (result coefficients) ∧
        ∀ index,CompactSpectatorInheritedGrid.decoded shape rows ell precision
          (live+NativeHadamardNormalizationFactor.denominatorIncrease (CompactComplexRecursiveGeometry.arity^exponent))
          (result coefficients) index=
          Networks.GaussianHadamardBridge.normalization^(CompactComplexRecursiveGeometry.arity^exponent)*
            CompactSpectatorInheritedGrid.decoded shape rows ell precision live coefficients index)
      (cost (rows:=rows) (ell:=ell) stage metadataPrecision live (CompactSpectatorInheritedGrid.half shape precision+1)) := by
  let bound := CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes
  have widths : ∀ index,(coefficients index).1.length=CompactSpectatorInheritedGrid.half shape precision+1 ∧
      (coefficients index).2.length=CompactSpectatorInheritedGrid.half shape precision+1 := by
    intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth index
  have bounds : ∀ index,
      |ButterflySigned.signedValue (CompactSpectatorInheritedGrid.half shape precision) (coefficients index).1|≤(bound : ℤ) ∧
      |ButterflySigned.signedValue (CompactSpectatorInheritedGrid.half shape precision) (coefficients index).2|≤(bound : ℤ) :=
    fun index => ButterflyGuard.represented_bound _ _ live bound (inputGrid index)
  have guard := CompactSpectatorInheritedGrid.guard_from_path shape precision path baseline growthConstant pendingAxes
    baselineFits dependencyFits pendingFits
  have signedGuard : 2*bound<2^(CompactSpectatorInheritedGrid.half shape precision) := by dsimp only [bound]; omega
  have integerGuard : 2*(bound : ℤ)<(2^(CompactSpectatorInheritedGrid.half shape precision) : ℕ) := by exact_mod_cast signedGuard
  have increaseEquation : increase stage=NativeHadamardNormalizationFactor.denominatorIncrease
      (CompactComplexRecursiveGeometry.arity^exponent) := congrArg NativeHadamardNormalizationFactor.denominatorIncrease stageWidth
  apply (runs stage _ live _ coefficients guardPositive axesPositive chunkPositive widths).consequence
    (fun _ equality => equality) _ le_rfl
  intro storage equality
  refine ⟨equality,?_,?_,?_,?_,?_,?_⟩
  · rw [equality]; rfl
  · rw [equality]
    change RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (live+increase stage))=_
    rw [increaseEquation]
  · rw [equality]; rfl
  · rw [equality]; rfl
  · exact NativeHadamardNormalizationGrid.result_grid precision live bound coefficients inputWidth inputGrid signedGuard
  · exact NativeHadamardNormalizationArray.result_normalization coefficients _ live exponent widths
      (bound : ℤ) bounds integerGuard

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationLifecycle
