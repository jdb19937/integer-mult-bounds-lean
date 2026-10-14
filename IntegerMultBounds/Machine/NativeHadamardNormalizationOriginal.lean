module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationBudget
public import IntegerMultBounds.Machine.NativeEndpointCharacterCopy

/-! Place complete normalization on arbitrary actual caller source/live ports.
Original raw headers are physically copied into private storage, the existing
fixed lifecycle changes only source and live, and all 58 borrowed tapes are
erased. No canonical returned-bank equality or execution callback is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)
variable {shape : Shape} {rows ell tapeCount : ℕ}

def destination (header : Fin 15) : Fin 58 :=
  Fin.castAdd 15 (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))

theorem destination_injective : Function.Injective destination := by
  intro first second equality
  have values := congrArg Fin.val equality
  have original : NativeEndpointCharacterCopy.destination first=NativeEndpointCharacterCopy.destination second := Fin.ext values
  exact NativeEndpointCharacterCopy.destination_injective original

def privateBank (stage : Stage shape) (metadataPrecision : ℕ) : Tapes 58 2 :=
  (ActiveRepairRankHeadersCommands.bank (a:=2) (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)).append
    (FixedHeaderBankCopy.empty 15)

private theorem private_eq (stage : Stage shape) (metadataPrecision : ℕ) :
    privateBank (rows:=rows) (ell:=ell) stage metadataPrecision=
      FixedHeaderSparseBankCopy.headerBank destination (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision) := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective _
  · intro header
    fin_cases header <;> constructor <;> rfl
  · intro port outside
    have outsideInitial : ∀ header : Fin 15,NativeEndpointCharacterCopy.destination header≠Fin.castAdd 9 port := by
      intro header equality
      apply outside header
      have values := congrArg (fun originalSlot : Fin 67 => originalSlot.val) equality
      exact Fin.ext values
    have blankInitial := FixedHeaderSparseBankCopy.headerBank_blank (a:=2) NativeEndpointCharacterCopy.destination
      (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision) (Fin.castAdd 9 port) outsideInitial
    rw [←NativeEndpointCharacterCopy.initial_eq] at blankInitial
    induction port using Fin.addCases (m:=43) (n:=15) with
    | left port =>
      have casts : Fin.castAdd 9 (Fin.castAdd 15 port)=Fin.castAdd 24 port := by apply Fin.ext; rfl
      rw [casts] at blankInitial
      simpa only [privateBank,NativeEndpointCharacterPrepare.input,Tapes.append,Fin.addCases_left,
        Fin.castAdd_castAdd] using blankInitial
    | right port => simp [privateBank,Tapes.append,FixedHeaderBankCopy.empty]

def copy (focus : Fin 15 → Fin tapeCount) := FixedHeaderSparseBankCopy.program (a:=2)
  (by omega : 0<tapeCount+15) focus destination destination_injective (by decide : 15≤58)
def erase := FixedHeaderSparseBankCopy.cleanup (a:=2)
  (by omega : 0<tapeCount+15) destination destination_injective (by decide : 15≤58)

def slots (source live : Fin tapeCount) (port : Fin 60) : Fin (tapeCount+58) :=
  if rawPort : port.val<43 then ⟨tapeCount+port.val,by omega⟩
  else if port.val=43 then Fin.castAdd 58 live
  else if port.val=44 then Fin.castAdd 58 source
  else ⟨tapeCount+(port.val-2),by have := port.isLt; omega⟩

theorem slots_injective (source live : Fin tapeCount) (distinct : source≠live) : Function.Injective (slots source live) := by
  intro first second equality
  have values := congrArg Fin.val equality
  have sourceBound := source.isLt
  have liveBound := live.isLt
  have differentValues : source.val≠live.val := fun equality => distinct (Fin.ext equality)
  apply Fin.ext
  unfold slots at values
  split_ifs at values <;> simp only [Fin.val_mk,Fin.val_castAdd] at values <;> omega

def placement (source live : Fin tapeCount) (distinct : source≠live) : Fin (60+(tapeCount-2)) ≃ Fin (tapeCount+58) :=
  InjectivePlacement.placement (slots source live) (slots_injective source live distinct) (by
    have sourceBound := source.isLt
    have liveBound := live.isLt
    have differentValues : source.val≠live.val := fun equality => distinct (Fin.ext equality)
    omega)

@[simp] theorem slots_raw (source live : Fin tapeCount) (port : Fin 43) :
    slots source live (Fin.castAdd 17 port)=Fin.natAdd tapeCount (Fin.castAdd 15 port) := by
  apply Fin.ext
  simp [slots,port.isLt]

@[simp] theorem slots_live (source live : Fin tapeCount) : slots source live (43 : Fin 60)=Fin.castAdd 58 live := by
  simp [slots]
@[simp] theorem slots_source (source live : Fin tapeCount) : slots source live (44 : Fin 60)=Fin.castAdd 58 source := by
  simp [slots]
@[simp] theorem slots_work (source live : Fin tapeCount) (port : Fin 15) :
    slots source live (Fin.natAdd 45 port)=Fin.natAdd tapeCount (Fin.natAdd 43 port) := by
  apply Fin.ext
  simp only [slots,Fin.val_natAdd,Fin.val_castAdd,Fin.val_mk]
  have portBound := port.isLt
  split_ifs <;> (try simp only [Fin.val_mk]) <;> omega

def normalize (source live : Fin tapeCount) (distinct : source≠live) :=
  Placement.placed NativeHadamardNormalizationLifecycle.program (placement source live distinct)

def program (focus : Fin 15 → Fin tapeCount) (source live : Fin tapeCount) (distinct : source≠live) :=
  seq (seq (copy focus) (normalize source live distinct)) (erase (tapeCount:=tapeCount))

def resultCaller (caller : Tapes tapeCount 2) (source current : Fin tapeCount)
    (stage : Stage shape) (live : ℕ) (coefficients : Array shape rows ell) :=
  setTape (setTape caller current
    (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (live+NativeHadamardNormalizationHeaders.increase stage))) 1)
    source (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (NativeHadamardNormalizationArray.result coefficients))) 0

private theorem active_input (source current : Fin tapeCount) (distinct : source≠current)
    (caller : Tapes tapeCount 2) (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell)
    (sourceReady : caller.tape source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients))
    (sourceHead : caller.head source=0)
    (liveReady : caller.tape current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live))
    (liveHead : caller.head current=1) :
    Placement.active (placement source current distinct) (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision))=
      NativeHadamardNormalizationLifecycle.input stage metadataPrecision live coefficients := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  all_goals
    intro port
    dsimp only
    induction port using Fin.addCases (m:=44) (n:=16) with
    | left port =>
      induction port using Fin.addCases (m:=43) (n:=1) with
      | left port =>
        have selected : slots source current (Fin.castAdd 16 (Fin.castAdd 1 port))=
            Fin.natAdd tapeCount (Fin.castAdd 15 port) := slots_raw source current port
        rw [selected]
        simp only [privateBank,NativeHadamardNormalizationLifecycle.input,NativeHadamardNormalizationHeaders.input,
          Tapes.append,Fin.addCases_left,Fin.addCases_right]
      | right port =>
        fin_cases port
        first
          | (change (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision)).head (slots source current 43)=1
             rw [slots_live]; simpa only [Tapes.append,Fin.addCases_left] using liveHead)
          | (change (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision)).tape (slots source current 43)=
               RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live)
             rw [slots_live]; simpa only [Tapes.append,Fin.addCases_left] using liveReady)
    | right port =>
      induction port using Fin.addCases (m:=1) (n:=15) with
      | left port =>
        fin_cases port
        first
          | (change (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision)).head (slots source current 44)=0
             rw [slots_source]; simpa only [Tapes.append,Fin.addCases_left] using sourceHead)
          | (change (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision)).tape (slots source current 44)=
               putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients)
             rw [slots_source]; simpa only [Tapes.append,Fin.addCases_left] using sourceReady)
      | right port =>
        have casts : Fin.natAdd 44 (Fin.natAdd 1 port)=Fin.natAdd 45 port := by apply Fin.ext; simp only [Fin.val_natAdd]; omega
        have selected := (congrArg (slots source current) casts).trans (slots_work source current port)
        rw [selected]
        simp only [privateBank,NativeHadamardNormalizationLifecycle.input,NativeHadamardNormalizationLifecycle.sourceBank,
          Tapes.append,Fin.addCases_left,Fin.addCases_right,SharedBank.empty,FixedHeaderBankCopy.empty]

private theorem placed_endpoint (source current : Fin tapeCount) (distinct : source≠current)
    (caller : Tapes tapeCount 2) (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell)
    (sourceReady : caller.tape source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients))
    (sourceHead : caller.head source=0)
    (liveReady : caller.tape current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live))
    (liveHead : caller.head current=1) :
    Placement.replace (placement source current distinct)
      (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision))
      (NativeHadamardNormalizationLifecycle.output stage metadataPrecision live coefficients)=
      (resultCaller caller source current stage live coefficients).append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision) := by
  let finalCaller := resultCaller caller source current stage live coefficients
  have finalActive := active_input source current distinct finalCaller stage metadataPrecision
    (live+NativeHadamardNormalizationHeaders.increase stage) (NativeHadamardNormalizationArray.result coefficients)
    (by simp [finalCaller,resultCaller,setTape]) (by simp [finalCaller,resultCaller,setTape])
    (by simp [finalCaller,resultCaller,setTape,distinct.symm]) (by simp [finalCaller,resultCaller,setTape,distinct.symm])
  have extraFrame : Placement.extra (placement source current distinct)
        (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision))=
      Placement.extra (placement source current distinct)
        (finalCaller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision)) := by
    apply Placement.Tapes.ext'
    all_goals
      intro extraPort
      have notCurrent : placement source current distinct (Fin.natAdd 60 extraPort)≠Fin.castAdd 58 current := by
        intro equality
        have currentSlot : placement source current distinct (Fin.castAdd (tapeCount-2) (43 : Fin 60))=Fin.castAdd 58 current := by
          rw [placement,InjectivePlacement.active_slot,slots_live]
        have values := congrArg Fin.val ((placement source current distinct).injective (equality.trans currentSlot.symm))
        simp only [Fin.val_natAdd,Fin.val_castAdd] at values
        omega
      have notSource : placement source current distinct (Fin.natAdd 60 extraPort)≠Fin.castAdd 58 source := by
        intro equality
        have sourceSlot : placement source current distinct (Fin.castAdd (tapeCount-2) (44 : Fin 60))=Fin.castAdd 58 source := by
          rw [placement,InjectivePlacement.active_slot,slots_source]
        have values := congrArg Fin.val ((placement source current distinct).injective (equality.trans sourceSlot.symm))
        simp only [Fin.val_natAdd,Fin.val_castAdd] at values
        omega
      unfold Placement.extra
      dsimp only [finalCaller,resultCaller]
      rw [←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left]
      simp only [setTape,Function.update_of_ne notSource,Function.update_of_ne notCurrent]
  rw [Placement.replace,extraFrame]
  change Placement.combine (placement source current distinct)
    (NativeHadamardNormalizationLifecycle.input stage metadataPrecision
      (live+NativeHadamardNormalizationHeaders.increase stage) (NativeHadamardNormalizationArray.result coefficients)) _ = _
  rw [←finalActive]
  exact Placement.view _ _

def cost (stage : Stage shape) (metadataPrecision live wordWidth : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision)+1+
    NativeHadamardNormalizationLifecycle.cost (rows:=rows) (ell:=ell) stage metadataPrecision live wordWidth+1+
    FixedHeaderBankCopy.cleanupCost (t:=tapeCount) (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision)

/-- On arbitrary actual caller source/live ports, copied original headers drive
complete normalization and every borrowed tape returns wholly blank at zero.
Every complementary caller tape/head is retained exactly. -/
theorem runs (focus : Fin 15 → Fin tapeCount) (source current : Fin tapeCount) (distinct : source≠current)
    (caller : Tapes tapeCount 2) (stage : Stage shape) (metadataPrecision live wordWidth : ℕ)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (coefficients : Array shape rows ell)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth)
    (headersReady : ∀ header,caller.tape (focus header)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header))
    (headersPositioned : ∀ header,caller.head (focus header)=1)
    (sourceReady : caller.tape source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients))
    (sourcePositioned : caller.head source=0)
    (liveReady : caller.tape current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live))
    (livePositioned : caller.head current=1) :
    HoareTime (program focus source current distinct)
      (fun storage => storage=caller.append (FixedHeaderBankCopy.empty 58))
      (fun storage => storage=(resultCaller caller source current stage live coefficients).append (FixedHeaderBankCopy.empty 58))
      (cost (tapeCount:=tapeCount) (rows:=rows) (ell:=ell) stage metadataPrecision live wordWidth) := by
  have copyRun := FixedHeaderSparseBankCopy.constructs (a:=2) (by omega : 0<tapeCount+15) focus
    destination destination_injective (by decide : 15≤58) caller
    (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision) headersReady headersPositioned
  rw [←private_eq] at copyRun
  have normalizeRun := InjectivePlacement.hoare_exact
    (NativeHadamardNormalizationLifecycle.runs stage metadataPrecision live wordWidth coefficients
      guardPositive axesPositive chunkPositive coefficientWidths)
    (slots source current) (slots_injective source current distinct) _
    (caller.append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision))
    ((resultCaller caller source current stage live coefficients).append (privateBank (rows:=rows) (ell:=ell) stage metadataPrecision))
    (active_input source current distinct caller stage metadataPrecision live coefficients sourceReady sourcePositioned liveReady livePositioned)
    (placed_endpoint source current distinct caller stage metadataPrecision live coefficients sourceReady sourcePositioned liveReady livePositioned)
  have eraseRun := FixedHeaderSparseBankCopy.cleans (a:=2) (by omega : 0<tapeCount+15)
    destination destination_injective (by decide : 15≤58) (resultCaller caller source current stage live coefficients)
    (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision)
  rw [←private_eq] at eraseRun
  exact (copyRun.seq normalizeRun).seq eraseRun


def constant : ℕ := 20006000

/-- Actual copied originals and their final erasure are paid from native volume,
including retained precision metadata. One common coefficient covers the entire
caller adapter before every shape, count and input bank. -/
theorem cost_linear (stage : Stage shape) (metadataPrecision live : ℕ)
    (rowsPositive : 0<rows) (axesPositive : 0<shape.axes) (guardPositive : 0<shape.guard)
    (chunkPositive : 0<shape.chunk) (unitPayload : shape.payload=1)
    (selectedFits : stage.slots*stage.f≤shape.bits)
    (liveFits : live≤CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) :
    cost (tapeCount:=tapeCount) (rows:=rows) (ell:=ell) stage metadataPrecision live
      (NativePolynomialStageShape.width shape metadataPrecision)≤
      constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision := by
  let volume := CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision
  have volumePositive : 0<volume := Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape ell metadataPrecision)
  have scalarBudget := NativePolynomialStageHeaderBudget.scalar_le stage rows ell metadataPrecision
    rowsPositive axesPositive guardPositive chunkPositive unitPayload
  have originalValues : ∀ header,Counter.value (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header)≤18*volume := by
    intro header
    apply le_trans _ scalarBudget
    rw [NativeEndpointCharacterCopy.words,RecursiveChildQuotientsConstant.bits_value]
    fin_cases header <;> simp [NativeEndpointCharacterCopy.index,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw]
    all_goals unfold CompactSpectatorLeafSetupBudget.scalar; omega
  have copyBudget := FixedHeaderBankCopy.cost_linear (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision)
    (18*volume) (by positivity) (fun _ => RecursiveChildQuotientsConstant.bits_canonical _) originalValues
  have eraseBudget := FixedHeaderBankCopy.cleanup_cost_linear (t:=tapeCount)
    (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision)
    (18*volume) (by positivity) (fun _ => RecursiveChildQuotientsConstant.bits_canonical _) originalValues
  have volumeEquation : NativeHadamardNormalizationHeaders.count rows shape.bits ell*
      (2*(NativePolynomialStageShape.width shape metadataPrecision+1))=volume := by
    unfold NativeHadamardNormalizationHeaders.count volume CompactNativeRoleTransferBudget.volume
      CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
    change rows*(2^shape.bits*2^ell)*(2*(NativePolynomialStageShape.width shape metadataPrecision+1))=
      rows*((2^shape.bits*2^ell)*(2*(NativePolynomialStageShape.width shape metadataPrecision+1)))
    ring
  have normalizeBudget := NativeHadamardNormalizationBudget.cost_le_volume stage rows ell metadataPrecision live
    (NativePolynomialStageShape.width shape metadataPrecision) rowsPositive guardPositive axesPositive chunkPositive
    selectedFits (by rw [volumeEquation]; exact liveFits)
  rw [volumeEquation] at normalizeBudget
  unfold cost constant
  nlinarith

/-- The fixed original-header caller program has genuine source/live output,
complete 58-tape cleanup and one positive native-volume coefficient. -/
theorem runs_linear (focus : Fin 15 → Fin tapeCount) (source current : Fin tapeCount) (distinct : source≠current)
    (caller : Tapes tapeCount 2) (stage : Stage shape) (metadataPrecision live : ℕ)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (chunkPositive : 0<shape.chunk) (unitPayload : shape.payload=1)
    (selectedFits : stage.slots*stage.f≤shape.bits)
    (liveFits : live≤CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision)
    (coefficients : Array shape rows ell)
    (coefficientWidths : ∀ index,(coefficients index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (coefficients index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (headersReady : ∀ header,caller.tape (focus header)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header))
    (headersPositioned : ∀ header,caller.head (focus header)=1)
    (sourceReady : caller.tape source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients))
    (sourcePositioned : caller.head source=0)
    (liveReady : caller.tape current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live))
    (livePositioned : caller.head current=1) :
    HoareTime (program focus source current distinct)
      (fun storage => storage=caller.append (FixedHeaderBankCopy.empty 58))
      (fun storage => storage=(resultCaller caller source current stage live coefficients).append (FixedHeaderBankCopy.empty 58))
      (constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) :=
  (runs focus source current distinct caller stage metadataPrecision live _ guardPositive axesPositive chunkPositive
    coefficients coefficientWidths headersReady headersPositioned sourceReady sourcePositioned liveReady livePositioned).consequence
    (fun _ equality => equality) (fun _ equality => equality)
    (cost_linear stage metadataPrecision live rowsPositive axesPositive guardPositive chunkPositive unitPayload selectedFits liveFits)


/-- Reuse the existing 67-tape native leaf placement. The nine unused tapes
are a literal blank frame; extension and finite reindexing add no transitions. -/
def promotion : Fin ((tapeCount+58)+9) ≃ Fin (tapeCount+67) := finCongr (by omega)

def promotedProgram (focus : Fin 15 → Fin tapeCount) (source current : Fin tapeCount) (distinct : source≠current) :=
  reindex (extend (program focus source current distinct) 9) (promotion (tapeCount:=tapeCount))

private theorem promotion_bank (caller : Tapes tapeCount 2) :
    ((caller.append (FixedHeaderBankCopy.empty 58)).append (FixedHeaderBankCopy.empty 9)).reindex
      (promotion (tapeCount:=tapeCount))=caller.append (FixedHeaderBankCopy.empty 67) := by
  apply Placement.Tapes.ext'
  all_goals
    intro port
    induction port using Fin.addCases (m:=tapeCount) (n:=67) with
    | left port =>
      have original : (promotion (tapeCount:=tapeCount)).symm (Fin.castAdd 67 port)=Fin.castAdd 9 (Fin.castAdd 58 port) := by
        apply Fin.ext; rfl
      simp only [Tapes.reindex,original,Tapes.append,Fin.addCases_left]
    | right port =>
      by_cases borrowed : port.val<58
      · have original : (promotion (tapeCount:=tapeCount)).symm (Fin.natAdd tapeCount port)=
            Fin.castAdd 9 (Fin.natAdd tapeCount ⟨port.val,borrowed⟩) := by apply Fin.ext; rfl
        simp only [Tapes.reindex,original,Tapes.append,Fin.addCases_left,Fin.addCases_right,FixedHeaderBankCopy.empty]
      · have original : (promotion (tapeCount:=tapeCount)).symm (Fin.natAdd tapeCount port)=
            Fin.natAdd (tapeCount+58) (⟨port.val-58,by have := port.isLt; omega⟩ : Fin 9) := by
          apply Fin.ext
          simp only [promotion,finCongr_symm,finCongr_apply,Fin.val_cast,Fin.val_natAdd]
          omega
        simp only [Tapes.reindex,original,Tapes.append,Fin.addCases_right,FixedHeaderBankCopy.empty]

theorem promote_runs (focus : Fin 15 → Fin tapeCount) (source current : Fin tapeCount) (distinct : source≠current)
    (caller finalCaller : Tapes tapeCount 2) (elapsedSteps : ℕ)
    (execution : HoareTime (program focus source current distinct)
      (fun storage => storage=caller.append (FixedHeaderBankCopy.empty 58))
      (fun storage => storage=finalCaller.append (FixedHeaderBankCopy.empty 58)) elapsedSteps) :
    HoareTime (promotedProgram focus source current distinct)
      (fun storage => storage=caller.append (FixedHeaderBankCopy.empty 67))
      (fun storage => storage=finalCaller.append (FixedHeaderBankCopy.empty 67)) elapsedSteps := by
  have framed := hoare_reindex_eq (hoare_extend_eq execution (FixedHeaderBankCopy.empty 9))
    (promotion (tapeCount:=tapeCount))
  simpa only [promotedProgram,promotion_bank] using framed

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationOriginal
