module

public import IntegerMultBounds.Machine.GammaHeaderRead
public import IntegerMultBounds.Machine.RecoverBinaryRuler

/-! Construct the public complex field-width ruler from the actual three-field
gamma header. The parser and binary countdown share blank work; all parsed
descriptors are consumed, and the original header is physically returned to
origin. Only the header and the generated ruler survive. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpHeaderWidth
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open Spec.SignedRingProduct (header)

def rulerSlots : Fin (3+3) ≃ Fin 6 where
  toFun := ![0,2,5,1,3,4]
  invFun := ![0,3,1,4,5,2]
  left_inv := by decide
  right_inv := by decide

def program := seq (seq (seq (seq (GammaHeaderRead.program (alphabet := alphabet))
  (Placement.placed RecoverBinaryRuler.program rulerSlots))
  (BinaryDescriptorCleanupList.oneProgram (3 : Fin 6)))
  (BinaryDescriptorCleanupList.oneProgram (4 : Fin 6)))
  (RecoverWorkspace.atProgram ReturnOrigin.program (1 : Fin 6))

def input (precision size width : ℕ) : Tapes 6 alphabet := GammaHeaderRead.input precision size width

def output (precision size width : ℕ) : Tapes 6 alphabet :=
  ⟨fun _ => 0,![word (List.replicate width true),word (header precision size width),fun _ => blank,
    fun _ => blank,fun _ => blank,fun _ => blank]⟩

def cost (precision size width : ℕ) := 5*(header precision size width).length+8*width+9*Nat.size width+
  2*(Nat.size precision+Nat.size size)+131

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)),symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

/-- Every control cell is generated from original encoded header bits.
No parsed width, binary descriptor, initialized clock or unary ruler is given. -/
theorem runs_setup (precision size width : ℕ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (widthPositive : 1≤width) :
    HoareTime (program (alphabet := alphabet)) (· = input precision size width) (· = output precision size width)
      (cost precision size width) := by
  let parsed := GammaHeaderRead.output (alphabet := alphabet) precision size width
  let ruled := Placement.replace rulerSlots parsed (RecoverBinaryRuler.output width)
  let precisionCleared := setTape ruled (3 : Fin 6) (fun _ => blank) 0
  let sizeCleared := setTape precisionCleared (4 : Fin 6) (fun _ => blank) 0
  have parsedRun := GammaHeaderRead.runs_header (alphabet := alphabet) precision size width precisionPositive sizePositive widthPositive
  have rulerReady : Placement.active rulerSlots parsed=RecoverBinaryRuler.input (GammaHeaderRead.bits width) := by
    rw [RecoverBinaryRuler.input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,
      ←GammaDescriptorRead.controller_descriptor]
    unfold Placement.active rulerSlots parsed GammaHeaderRead.output GammaHeaderRead.bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have rulerRun := Placement.hoare_at (RecoverBinaryRuler.runs_build (alphabet := alphabet) (GammaHeaderRead.bits width)
    width (GammaHeaderRead.decoded_value width)) rulerSlots parsed rulerReady
  have rulerExact : HoareTime (Placement.placed (RecoverBinaryRuler.program (alphabet := alphabet)) rulerSlots)
      (· = parsed) (· = ruled) (8*width+9*(GammaHeaderRead.bits width).length+31) := by
    apply rulerRun.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,rfl,rfl⟩
    rfl
  have clearPrecision := BinaryDescriptorCleanupList.one_hoare (3 : Fin 6) ruled (GammaHeaderRead.bits precision) rfl rfl
  have clearSize := BinaryDescriptorCleanupList.one_hoare (4 : Fin 6) precisionCleared (GammaHeaderRead.bits size) rfl rfl
  have returnHeader := RecoverWorkspace.return_at (1 : Fin 6) sizeCleared
    ((header precision size width).map bitSymbol) (bits_nonblank _) (by simp [sizeCleared,precisionCleared,setTape,List.length_map]; rfl)
    (by simp [sizeCleared,precisionCleared,setTape]; rfl)
  have endpoint : RecoverWorkspace.restored sizeCleared (1 : Fin 6)=output precision size width := by
    unfold RecoverWorkspace.restored sizeCleared precisionCleared ruled Placement.replace Placement.combine Placement.extra
      rulerSlots parsed GammaHeaderRead.output GammaHeaderRead.bank RecoverBinaryRuler.output Tapes.append Tapes.reindex setTape output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program input
  apply ((((parsedRun.seq rulerExact).seq clearPrecision).seq clearSize).seq returnHeader).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  simp only [GammaHeaderRead.bits,List.length_reverse,Spec.SignedRingProduct.length_msbBits,List.length_map]
  unfold cost
  omega

/-- All actual parsing, binary countdown, cleanup and header rewind steps are
paid linearly by the original header and generated field width. -/
theorem cost_le (precision size width : ℕ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (widthPositive : 1≤width) :
    cost precision size width ≤ 200*((header precision size width).length+width+1) := by
  have precisionSize := Nat.size_pos.mpr (show 0<precision by omega)
  have sizeSize := Nat.size_pos.mpr (show 0<size by omega)
  have widthSize := Nat.size_pos.mpr (show 0<width by omega)
  have descriptorVolume : Nat.size precision+Nat.size size+Nat.size width ≤ (header precision size width).length := by
    simp only [header,List.length_append,Spec.SignedRingProduct.length_gamma precisionPositive,
      Spec.SignedRingProduct.length_gamma sizePositive,Spec.SignedRingProduct.length_gamma widthPositive]
    omega
  unfold cost
  omega

end
end IntegerMultBounds.Machine.ChirpHeaderWidth
