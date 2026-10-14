module

public import IntegerMultBounds.Machine.LayerReservationSetup
public import IntegerMultBounds.Machine.ChirpPublicArray
public import IntegerMultBounds.Machine.PlacementBankEndpoint
public import IntegerMultBounds.Machine.WordTapeBridge

@[expose] public section
namespace IntegerMultBounds.Machine.LayerNativeRecords
noncomputable section
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram erased restored)
open ChirpPublicArray (Pair raw native)
open RecursiveChildQuotientsConstant (bits)

def rulerMap : Fin 3 → Fin 64 := ![60,61,62]
theorem rulerMap_injective : Function.Injective rulerMap := by decide
def rulerSlots := InjectivePlacement.placement rulerMap rulerMap_injective (by decide : 3+61=64)
def arrayMap : Fin 3 → Fin 64 := ![60,1,63]
theorem arrayMap_injective : Function.Injective arrayMap := by decide
def arraySlots := InjectivePlacement.placement arrayMap arrayMap_injective (by decide : 3+61=64)

def prepare := seq (seq (seq (seq (seq (BinaryDescriptorInstall.program 2 (14 : Fin 64) 62 (by decide))
  (Placement.placed (RecoverBinaryRuler.program (alphabet:=2)) rulerSlots))
  (Placement.placed ChirpPublicArray.program arraySlots))
  (atProgram RecoverArrayCleanup.eraseOrigin (60 : Fin 64)))
  (atProgram ReturnOrigin.program (1 : Fin 64))) (atProgram ReturnOrigin.program (63 : Fin 64))

def cost (width : ℕ) (pairs : List Pair) :=
  10*width+11*(bits width).length+31*(raw pairs).length+(native pairs).length+48

private theorem bits_nonblank (data : List Bool) : ∀ symbol ∈ data.map (bitSymbol (a:=2)),symbol≠blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem native_nonblank (pairs : List Pair) : ∀ symbol ∈ native pairs,symbol≠(blank : Fin 6) := by
  intro symbol member
  obtain ⟨pair,_,inPair⟩ := List.mem_flatMap.mp member
  simp only [DelimitedRadixRecord.complex,DelimitedRadixRecord.field,List.mem_append,List.mem_singleton] at inPair
  rcases inPair with (realMember | rfl) | (imaginaryMember | rfl)
  · obtain ⟨digit,_,rfl⟩ := List.mem_map.mp realMember
    intro equal
    have valueEquation := congrArg Fin.val equal
    change digit.val+4=0 at valueEquation
    omega
  · decide
  · obtain ⟨digit,_,rfl⟩ := List.mem_map.mp imaginaryMember
    intro equal
    have valueEquation := congrArg Fin.val equal
    change digit.val+4=0 at valueEquation
    omega
  · decide

theorem runs_prepare (caller : Tapes 64 2) (width : ℕ) (pairs : List Pair)
    (widthPositive : 0<width)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width)
    (widthReady : caller.tape 14=RadixZeroFill.encodedBinary (bits width)) (widthHead : caller.head 14=1)
    (sourceReady : caller.tape 1=word (raw pairs)) (sourceHead : caller.head 1=0)
    (rulerBlank : caller.head 60=0 ∧ caller.tape 60=(fun _ => blank))
    (clockBlank : caller.head 61=0 ∧ caller.tape 61=(fun _ => blank))
    (descriptorBlank : caller.head 62=0 ∧ caller.tape 62=(fun _ => blank))
    (nativeBlank : caller.head 63=0 ∧ caller.tape 63=(fun _ => blank)) :
    HoareTime prepare (· = caller) (· = setTape caller (63 : Fin 64) (putWord (fun _ => blank) 0 (native pairs)) 0)
      (cost width pairs) := by
  let copied := setTape caller (62 : Fin 64) (RadixZeroFill.encodedBinary (bits width)) 1
  let ruled := setTape caller (60 : Fin 64) (word (List.replicate width true)) 0
  let converted := setTape (setTape ruled (1 : Fin 64) (word (raw pairs)) (raw pairs).length)
    (63 : Fin 64) (putWord (fun _ => blank) 0 (native pairs)) (native pairs).length
  let rulerCleared := erased converted (60 : Fin 64)
  let sourceReturned := restored rulerCleared (1 : Fin 64)
  let nativeReturned := restored sourceReturned (63 : Fin 64)
  have copyRun := BinaryDescriptorInstall.install_hoare (14 : Fin 64) 62 (by decide) caller (bits width)
    widthReady widthHead descriptorBlank.2 descriptorBlank.1
  have rulerReady : Placement.active rulerSlots copied=RecoverBinaryRuler.input (bits width) := by
    rw [rulerSlots,InjectivePlacement.active_bank,RecoverBinaryRuler.input,CountedGuardConstantsFill.input,
      CountedGuardGadgetPosition.input,←GammaDescriptorRead.controller_descriptor]
    unfold rulerMap copied setTape
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [rulerBlank,clockBlank]
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have rulerRun := Placement.hoare_at (RecoverBinaryRuler.runs_build (alphabet:=2) (bits width) width
    (RecursiveChildQuotientsConstant.bits_value _)) rulerSlots copied rulerReady
  have rulerEndpoint : Placement.replace rulerSlots copied (RecoverBinaryRuler.output width)=ruled := by
    apply InjectivePlacement.replace_eq rulerMap rulerMap_injective (by decide : 3+61=64) copied ruled
    · rw [InjectivePlacement.active_bank]
      unfold rulerMap ruled RecoverBinaryRuler.output setTape
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp [clockBlank,descriptorBlank]
    · intro slot outside
      have notRuler : slot≠60 := by intro equal; exact outside 0 (by simpa [rulerMap] using equal.symm)
      have notDescriptor : slot≠62 := by intro equal; exact outside 2 (by simpa [rulerMap] using equal.symm)
      simp [ruled,copied,setTape,notRuler,notDescriptor]
  have rulerExact : HoareTime (Placement.placed (RecoverBinaryRuler.program (alphabet:=2)) rulerSlots)
      (· = copied) (· = ruled) (8*width+9*(bits width).length+31) := by
    apply rulerRun.consequence (fun _ ready => ready) _ le_rfl
    rintro resultBank ⟨small,smallReady,resultReady⟩
    rw [smallReady] at resultReady
    exact resultReady.trans rulerEndpoint
  have arrayReady : Placement.active arraySlots ruled=
      ChirpPublicField.bank (word (List.replicate width true)) (word ([]++raw pairs)) (fun _ => blank) 0 0 0 := by
    rw [arraySlots,InjectivePlacement.active_bank]
    unfold arrayMap ruled setTape ChirpPublicField.bank RulerCopy.cfg Config.tapes
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [sourceReady,sourceHead,nativeBlank]
  have arrayRun := Placement.hoare_at (ChirpPublicArray.runs_array_volume pairs (List.replicate width true) []
    (fun _ => blank) 0 (by simpa using widthPositive) (by simpa using fieldWidths)) arraySlots ruled arrayReady
  have arrayEndpoint : Placement.replace arraySlots ruled
      (ChirpPublicField.bank (word (List.replicate width true)) (word ([]++raw pairs))
        (putWord (fun _ => blank) 0 (native pairs)) 0 ([]++raw pairs).length (0+(native pairs).length))=converted := by
    simp only [List.nil_append,zero_add]
    apply InjectivePlacement.replace_eq arrayMap arrayMap_injective (by decide : 3+61=64) ruled converted
    · rw [InjectivePlacement.active_bank]
      unfold arrayMap converted ruled setTape ChirpPublicField.bank RulerCopy.cfg Config.tapes
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp
    · intro slot outside
      have notSource : slot≠1 := by intro equal; exact outside 1 (by simpa [arrayMap] using equal.symm)
      have notNative : slot≠63 := by intro equal; exact outside 2 (by simpa [arrayMap] using equal.symm)
      simp [converted,setTape,notSource,notNative]
  have arrayExact : HoareTime (Placement.placed ChirpPublicArray.program arraySlots) (· = ruled) (· = converted)
      (30*(raw pairs).length) := by
    apply arrayRun.consequence (fun _ ready => ready) _ le_rfl
    rintro resultBank ⟨small,smallReady,resultReady⟩
    rw [smallReady] at resultReady
    exact resultReady.trans arrayEndpoint
  have clearRuler := RecoverArrayCleanup.erase_origin_at (60 : Fin 64) converted
    ((List.replicate width true).map bitSymbol) (bits_nonblank _) (by simp [converted,ruled,setTape])
    (by simp [converted,ruled,setTape,word])
  have returnSource := RecoverWorkspace.return_at (1 : Fin 64) rulerCleared ((raw pairs).map bitSymbol)
    (bits_nonblank _) (by simp [rulerCleared,erased,converted,setTape,List.length_map])
    (by simp [rulerCleared,erased,converted,setTape]; rfl)
  have returnNative := RecoverWorkspace.return_at (63 : Fin 64) sourceReturned (native pairs) (native_nonblank _)
    (by simp [sourceReturned,restored,rulerCleared,erased,converted,setTape])
    (by simp [sourceReturned,restored,rulerCleared,erased,converted,setTape])
  have finalBank : nativeReturned=setTape caller (63 : Fin 64) (putWord (fun _ => blank) 0 (native pairs)) 0 := by
    apply Placement.Tapes.ext'
    all_goals
      intro slot
      by_cases isRuler : slot=60
      · subst slot
        simp [nativeReturned,sourceReturned,restored,rulerCleared,erased,converted,ruled,setTape,rulerBlank]
      · by_cases isSource : slot=1
        · subst slot
          simp [nativeReturned,sourceReturned,restored,rulerCleared,erased,converted,ruled,setTape,sourceReady,sourceHead]
        · by_cases isNative : slot=63
          · subst slot
            simp [nativeReturned,sourceReturned,restored,rulerCleared,erased,converted,ruled,setTape]
          · simp [nativeReturned,sourceReturned,restored,rulerCleared,erased,converted,ruled,setTape,isRuler,isSource,isNative]
  unfold prepare
  apply (((((copyRun.seq rulerExact).seq arrayExact).seq clearRuler).seq returnSource).seq returnNative).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans finalBank)
  simp only [List.length_map,List.length_replicate]
  unfold cost
  omega

end
end IntegerMultBounds.Machine.LayerNativeRecords
