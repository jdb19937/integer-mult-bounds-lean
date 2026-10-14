module

public import IntegerMultBounds.Machine.ChirpFastProduct
public import IntegerMultBounds.Machine.ChirpArithmeticCodec
public import IntegerMultBounds.Machine.PlacementBankEndpoint
public import IntegerMultBounds.Machine.RecoverArrayCleanup
public import IntegerMultBounds.Machine.WordTapeBridge

/-! Actual fast scalar multiplication followed by native publication and
raw-result reclamation on one fixed bank. The original raw operands and
precision/width rulers are retained; the native destination starts blank. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpFastNativeProduct
noncomputable section
open SharedPlacementAlphabet (setTape)
open Schoenhage Strm Tp

abbrev tapeCount := 92
def nativeSlot : Fin tapeCount := 91
def rawSlot : Fin tapeCount := Fin.castAdd 1 zO
def slots : Fin 3 → Fin tapeCount := ![Fin.castAdd 1 iW,rawSlot,nativeSlot]
theorem slots_injective : Function.Injective slots := by decide

def placement := InjectivePlacement.placement slots slots_injective (by decide : 3+89=92)
def publish := Placement.placed ChirpArithmeticCodec.toNative placement
def clearRaw := RecoverWorkspace.atProgram (RecoverArrayCleanup.eraseOrigin (alphabet := 2)) rawSlot
def program := seq (seq (extend ChirpFastProduct.program 1) publish) clearRaw

def empty : Tapes 1 2 := ⟨fun _ => 0,fun _ _ => blank⟩
def input (left right : List Bool) (dropPrecision width : ℕ) :=
  (ChirpFastProduct.input left right dropPrecision width).append empty

def multiplied (left right : List Bool) (dropPrecision width : ℕ) :=
  (ChirpFastProduct.output left right dropPrecision width).append empty

def published (left right : List Bool) (dropPrecision width : ℕ) :=
  setTape (multiplied left right dropPrecision width) nativeSlot
    (RulerWordMap.word ((ChirpArithmeticCodec.nativeBits (FixedMul.result left right dropPrecision width)).map RadixDigits.digitSymbol)) 0

def output (left right : List Bool) (dropPrecision width : ℕ) :=
  RecoverWorkspace.erased (published left right dropPrecision width) rawSlot

theorem mapped_word (bits : List Bool) :
    (fun position => ChirpFastProduct.encoding.encode (Spec.SignedRingProduct.wordAt (a := 0) bits position))=
      RulerWordMap.word (bits.map (bitSymbol (a := 2))) := by
  rw [RulerWordMap.word,putWord_blank_origin]
  funext position
  simp only [Spec.SignedRingProduct.wordAt,wordTape,ChirpFastProduct.encoding,Schoenhage.embed]
  split_ifs
  · apply Fin.ext
    simp only [List.getElem?_map]
    cases lookup : bits[position.toNat]? with
    | none => simp [blank]
    | some bit => cases bit <;> simp [bitSymbol]
  · rfl


/-- Installing one right operand changes exactly that original raw port;
all other input tapes, heads and the blank native destination are retained. -/
theorem input_right_update (left right : List Bool) (dropPrecision width : ℕ) :
    setTape (input left [] dropPrecision width) (Fin.castAdd 1 zG)
      (RulerWordMap.word (right.map bitSymbol)) 0=input left right dropPrecision width := by
  simp only [input,SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun bank : Tapes 91 2 => bank.append empty)
  apply Placement.Tapes.ext'
  · intro slot
    simp only [setTape,Function.update_apply,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM]
    split <;> rfl
  · intro slot
    by_cases isRight : slot=zG
    · subst slot
      simp only [setTape,Function.update_self]
      simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,zG,zF,iP,iW,zO]
        using (mapped_word right).symm
    · simp only [setTape,Function.update_of_ne isRight,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,
        isRight,↓reduceIte]

/-- Installing one left operand changes exactly that original raw port;
all other input tapes, heads and the blank native destination are retained. -/
theorem input_left_update (left right : List Bool) (dropPrecision width : ℕ) :
    setTape (input [] right dropPrecision width) (Fin.castAdd 1 zF)
      (RulerWordMap.word (left.map bitSymbol)) 0=input left right dropPrecision width := by
  simp only [input,SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun bank : Tapes 91 2 => bank.append empty)
  apply Placement.Tapes.ext'
  · intro slot
    simp only [setTape,Function.update_apply,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM]
    split <;> rfl
  · intro slot
    by_cases isLeft : slot=zF
    · subst slot
      simp only [setTape,Function.update_self]
      simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,zG,zF,iP,iW,zO]
        using (mapped_word left).symm
    · simp only [setTape,Function.update_of_ne isLeft,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,
        isLeft,↓reduceIte]

/-- Canonical zero-drop input ports, including the genuinely blank native
destination and every private tape. -/
theorem input_tape_zero (left right : List Bool) (width : ℕ) (slot : Fin tapeCount) :
    (input left right 0 width).tape slot=
      if slot.val=88 then RulerWordMap.word (left.map bitSymbol)
      else if slot.val=89 then RulerWordMap.word (right.map bitSymbol)
      else if slot.val=86 then RulerWordMap.word (List.replicate width (bitSymbol true))
      else fun _ => blank := by
  refine Fin.addCases (m := 91) (n := 1) (fun index => ?_) (fun index => ?_) slot
  · simp only [input,Tapes.append,Fin.addCases_left,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,Fin.val_castAdd]
    simp only [Fin.ext_iff,zF,zG,iP,iW,zO]
    by_cases isLeft : index.val=88
    · simpa [isLeft] using mapped_word left
    · by_cases isRight : index.val=89
      · simpa [isLeft,isRight] using mapped_word right
      · by_cases isWidth : index.val=86
        · simpa [isLeft,isRight,isWidth,Schoenhage.ones,List.map_replicate] using mapped_word (List.replicate width true)
        · by_cases isPrecision : index.val=84
          · simpa [isLeft,isRight,isWidth,isPrecision,Schoenhage.ones,RulerWordMap.word,putWord] using mapped_word []
          · by_cases isRaw : index.val=90
            · simpa [isLeft,isRight,isWidth,isPrecision,isRaw,RulerWordMap.word,putWord] using mapped_word []
            · simp [isLeft,isRight,isWidth,isPrecision,isRaw,ChirpFastProduct.encoding,Schoenhage.embed,blank]
  · fin_cases index
    rfl

private theorem multiplied_head (left right : List Bool) (dropPrecision width : ℕ) (slot : Fin tapeCount) :
    (multiplied left right dropPrecision width).head slot=0 := by
  refine Fin.addCases (m := 91) (n := 1) (fun index => ?_) (fun index => ?_) slot
  all_goals simp [multiplied,ChirpFastProduct.output,Alphabet.mapTapes,Schoenhage.rawFM,Tapes.append,empty]

private theorem active_multiplied (left right : List Bool) (dropPrecision width : ℕ)
    (resultLength : (FixedMul.result left right dropPrecision width).length=width) :
    Placement.active placement (multiplied left right dropPrecision width)=
      RulerWordMap.input ((FixedMul.result left right dropPrecision width).map (bitSymbol (a := 2))) := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  · intro slot; fin_cases slot <;> rfl
  · intro slot
    fin_cases slot
    · change (ChirpFastProduct.output left right dropPrecision width).tape iW =
        RulerWordMap.word (List.replicate ((FixedMul.result left right dropPrecision width).map bitSymbol).length (bitSymbol true))
      simpa [ChirpFastProduct.output,Alphabet.mapTapes,Schoenhage.rawFM,Schoenhage.ones,
        resultLength,List.map_replicate,iW,zF,zG,iP,zO] using mapped_word (List.replicate width true)
    · change (ChirpFastProduct.output left right dropPrecision width).tape zO =
        RulerWordMap.word ((FixedMul.result left right dropPrecision width).map bitSymbol)
      simpa [ChirpFastProduct.output,Alphabet.mapTapes,Schoenhage.rawFM,iW,zF,zG,iP,zO]
        using mapped_word (FixedMul.result left right dropPrecision width)
    · rfl

/-- Scalar execution, exact native publication, and physical erasure of the
raw result are composed without an intermediate execution premise. -/
theorem runs (left right : List Bool) (dropPrecision width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (widthPositive : 1≤width) (dropFits : dropPrecision≤width) :
    HoareTime program (· = input left right dropPrecision width) (· = output left right dropPrecision width)
      (Schoenhage.fmTime width+6*width+14) := by
  let result := FixedMul.result left right dropPrecision width
  have resultLength : result.length=width := by
    unfold result FixedMul.result
    split_ifs <;> simp [TwosComplement.negWord_length,Gather.field_length]
  have multipliedRun := FamilyPlacementAlphabet.extend_hoare
    (ChirpFastProduct.runs left right dropPrecision width leftWidth rightWidth widthPositive dropFits) empty
  have localRun := ChirpArithmeticCodec.runs_toNative result
  have activeBefore := active_multiplied left right dropPrecision width resultLength
  have publishRun := Placement.hoare_at localRun placement (multiplied left right dropPrecision width) activeBefore
  rw [placement,InjectivePlacement.active_bank] at activeBefore
  have notNativeWidth : Fin.castAdd 1 iW≠nativeSlot := by decide
  have notNativeRaw : rawSlot≠nativeSlot := by decide
  have widthTape : (multiplied left right dropPrecision width).tape (Fin.castAdd 1 iW)=
      RulerWordMap.word (List.replicate result.length (bitSymbol true)) := by
    simpa [RulerWordMap.input,RulerWordMap.bank,RulerCopy.cfg,Config.tapes,List.length_map,slots]
      using congrFun (congrArg Tapes.tape activeBefore) 0
  have resultTape : (multiplied left right dropPrecision width).tape rawSlot=RulerWordMap.word (result.map bitSymbol) := by
    simpa [RulerWordMap.input,RulerWordMap.bank,RulerCopy.cfg,Config.tapes,slots]
      using congrFun (congrArg Tapes.tape activeBefore) 1
  have publishedHead (slot : Fin tapeCount) : (published left right dropPrecision width).head slot=0 := by
    simp only [published,setTape,Function.update_apply,multiplied_head]
    split <;> rfl
  have activeAfter : Placement.active placement (published left right dropPrecision width)=
      RulerWordMap.bank (RulerWordMap.word (List.replicate result.length (bitSymbol true)))
        (RulerWordMap.word (result.map bitSymbol))
        (RulerWordMap.word ((ChirpArithmeticCodec.nativeBits result).map RadixDigits.digitSymbol)) 0 0 0 := by
    rw [placement,InjectivePlacement.active_bank]
    apply Placement.Tapes.ext'
    · intro slot
      simpa [RulerWordMap.bank,RulerCopy.cfg,Config.tapes] using publishedHead (slots slot)
    · intro slot
      fin_cases slot
      · change (published left right dropPrecision width).tape (Fin.castAdd 1 iW)=_
        simpa [published,setTape,Function.update_of_ne notNativeWidth,RulerWordMap.bank,RulerCopy.cfg,Config.tapes] using widthTape
      · change (published left right dropPrecision width).tape rawSlot=_
        simpa [published,setTape,Function.update_of_ne notNativeRaw,RulerWordMap.bank,RulerCopy.cfg,Config.tapes] using resultTape
      · rfl
  have endpoint := InjectivePlacement.replace_eq slots slots_injective (by decide : 3+89=92)
    (multiplied left right dropPrecision width) (published left right dropPrecision width) _ activeAfter (by
      intro slot outside
      have notNative : nativeSlot≠slot := outside 2
      simp [published,setTape,Function.update_of_ne notNative.symm])
  have publishedRun : HoareTime publish (· = multiplied left right dropPrecision width)
      (· = published left right dropPrecision width) (4*result.length+9) := by
    apply publishRun.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,rfl,rfl⟩
    exact endpoint
  have rawTape : (published left right dropPrecision width).tape rawSlot=RulerWordMap.word (result.map bitSymbol) := by
    simpa [published,setTape,Function.update_of_ne notNativeRaw,RulerWordMap.bank,RulerCopy.cfg,Config.tapes] using resultTape
  have nonblank : ∀ symbol ∈ result.map (bitSymbol (a := 2)),symbol≠blank := by
    intro symbol member
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
    cases bit <;> decide
  have cleared := RecoverArrayCleanup.erase_origin_at rawSlot (published left right dropPrecision width)
    (result.map bitSymbol) nonblank (publishedHead rawSlot) rawTape
  unfold program input output
  exact ((multipliedRun.seq publishedRun).seq cleared).consequence
    (fun _ ready => ready) (fun _ finished => finished) (by simp only [List.length_map,resultLength]; omega)

theorem output_head (left right : List Bool) (dropPrecision width : ℕ) (slot : Fin tapeCount) :
    (output left right dropPrecision width).head slot=0 := by
  simp only [output,RecoverWorkspace.erased,published,setTape,Function.update_apply,multiplied_head]
  split <;> (try rfl)
  split <;> rfl

theorem native_tape (left right : List Bool) (dropPrecision width : ℕ) :
    (output left right dropPrecision width).tape nativeSlot=
      RulerWordMap.word ((ChirpArithmeticCodec.nativeBits (FixedMul.result left right dropPrecision width)).map RadixDigits.digitSymbol) := by
  have different : nativeSlot≠rawSlot := by decide
  simp only [output,RecoverWorkspace.erased,published,setTape,Function.update_of_ne different,Function.update_self]

theorem raw_blank (left right : List Bool) (dropPrecision width : ℕ) :
    (output left right dropPrecision width).tape rawSlot=(fun _ => blank) := by
  simp only [output,RecoverWorkspace.erased,setTape,Function.update_self]

/-- Every entire scratch tape is blank; only original operands/rulers and
the newly published native word survive. -/
theorem workspace_blank (left right : List Bool) (dropPrecision width : ℕ) (slot : Fin 91)
    (notLeft : slot≠zF) (notRight : slot≠zG) (notPrecision : slot≠iP) (notWidth : slot≠iW) :
    (output left right dropPrecision width).tape (Fin.castAdd 1 slot)=(fun _ => blank) := by
  by_cases isRaw : slot=zO
  · subst slot
    exact raw_blank left right dropPrecision width
  · have notNative : Fin.castAdd 1 slot≠nativeSlot := by
      intro equal
      have values := congrArg Fin.val equal
      change slot.val=91 at values
      have bound := slot.isLt
      omega
    have notRaw : Fin.castAdd 1 slot≠rawSlot := by
      intro equal
      apply isRaw
      apply Fin.ext
      exact congrArg (fun index : Fin tapeCount => index.val) equal
    simp only [output,RecoverWorkspace.erased,published,setTape,Function.update_of_ne notNative,
      Function.update_of_ne notRaw,multiplied,Tapes.append,Fin.addCases_left]
    exact (ChirpFastProduct.workspace_blank left right dropPrecision width slot
      notLeft notRight notPrecision notWidth isRaw).1


/-- The complete scalar endpoint is the original input bank with exactly
one native destination written. This contract enables shared-workspace calls. -/
theorem output_eq_input_update (left right : List Bool) (dropPrecision width : ℕ) :
    output left right dropPrecision width=
      setTape (input left right dropPrecision width) nativeSlot
        (RulerWordMap.word ((ChirpArithmeticCodec.nativeBits (FixedMul.result left right dropPrecision width)).map RadixDigits.digitSymbol)) 0 := by
  apply Placement.Tapes.ext'
  · intro slot
    rw [output_head]
    simp only [setTape,Function.update_apply]
    split
    · rfl
    · refine Fin.addCases (m := 91) (n := 1) (fun index => ?_) (fun index => ?_) slot
      all_goals simp [input,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,Tapes.append,empty]
  · intro slot
    refine Fin.addCases (m := 91) (n := 1) (fun index => ?_) (fun index => ?_) slot
    · have notNative : Fin.castAdd 1 index≠nativeSlot := by
        intro equal
        have values := congrArg Fin.val equal
        change index.val=91 at values
        omega
      by_cases isRaw : index=zO
      · subst index
        rw [show Fin.castAdd 1 zO=rawSlot from rfl,raw_blank]
        change (fun _ => blank)=Function.update (input left right dropPrecision width).tape nativeSlot
          (RulerWordMap.word ((ChirpArithmeticCodec.nativeBits (FixedMul.result left right dropPrecision width)).map RadixDigits.digitSymbol)) rawSlot
        rw [Function.update_of_ne (by decide : rawSlot≠nativeSlot)]
        change (fun _ => blank)=(ChirpFastProduct.input left right dropPrecision width).tape zO
        simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,zO,zF,zG,iP,iW,RulerWordMap.word,putWord]
          using (mapped_word []).symm
      · have notRaw : Fin.castAdd 1 index≠rawSlot := by
          intro equal
          apply isRaw
          apply Fin.ext
          exact congrArg (fun slot : Fin tapeCount => slot.val) equal
        simp only [output,RecoverWorkspace.erased,published,setTape,Function.update_of_ne notRaw,
          Function.update_of_ne notNative,multiplied,input,Tapes.append,Fin.addCases_left,
          ChirpFastProduct.output,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM]
        simp only [isRaw,↓reduceIte]
    · have isNative : Fin.natAdd 91 index=nativeSlot := by fin_cases index; rfl
      rw [isNative,native_tape]
      simp only [setTape,Function.update_self]

/-- Exact full scalar products reach the actual native destination. Scale
slack derives all signed guards, and every head returns to origin. -/
theorem runs_exact (left right : List Bool) (operandScale width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (wideEnough : 2*operandScale+2≤width)
    (leftBound : |TwosComplement.signed left|≤(2 : ℤ)^operandScale)
    (rightBound : |TwosComplement.signed right|≤(2 : ℤ)^operandScale) :
    HoareTime program (· = input left right 0 width) (· = output left right 0 width)
      (Schoenhage.fmTime width+6*width+14) ∧
      (ChirpArithmeticCodec.nativeBits (FixedMul.result left right 0 width)).length=width ∧
      ButterflySigned.signedValue (width-1) (ChirpArithmeticCodec.nativeBits (FixedMul.result left right 0 width))=
        TwosComplement.signed left*TwosComplement.signed right ∧
      (∀ slot,(output left right 0 width).head slot=0) := by
  have exactProduct := ChirpFastProduct.runs_exact left right operandScale width
    leftWidth rightWidth wideEnough leftBound rightBound
  refine ⟨runs left right 0 width leftWidth rightWidth (by omega) (by omega),?_,?_,output_head left right 0 width⟩
  · simpa only [ChirpArithmeticCodec.nativeBits,List.length_map] using exactProduct.2.1
  · rw [ChirpArithmeticCodec.native_signed _ (width-1) (by rw [exactProduct.2.1]; omega)]
    exact exactProduct.2.2

end
end IntegerMultBounds.Machine.ChirpFastNativeProduct
