module

public import IntegerMultBounds.Machine.RecoverRulerTrim
public import IntegerMultBounds.Schoenhage.ConvScale

/-! Read a power-of-two size descriptor and construct its exponent ruler.
The prefix scanner reads actual low zero bits, the size descriptor is restored,
and one excess ruler cell is removed with a physically initialized constant.
Only the exponent ruler and original size descriptor remain. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverExponentRuler
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)

def sizeBits (exponent : ℕ) := GammaHeaderRead.bits (2 ^ exponent)

theorem size_bits (exponent : ℕ) : sizeBits exponent = List.replicate exponent false ++ [true] := by
  simp only [sizeBits,GammaHeaderRead.bits,Nat.size_pow,Schoenhage.msbBits_two_pow,
    List.reverse_cons,List.reverse_replicate]

def bank (ruler source descriptor : ℤ → Fin (alphabet+4)) (rulerHead sourceHead descriptorHead : ℤ) : Tapes 4 alphabet :=
  ⟨![rulerHead,sourceHead,0,descriptorHead],![ruler,source,fun _ => blank,descriptor]⟩

def trimSlots : Fin (3+1) ≃ Fin 4 where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide
  right_inv := by decide

def program : Program 4 48 alphabet := seq (seq (seq (seq (extend GammaPrefix.program 2)
  (atProgram (Rewind.program separator) (1 : Fin 4)))
  (atProgram (MultiplicationInputSplit.shift .right) (1 : Fin 4)))
  (atProgram (RecursiveChildQuotientsConstant.program (a := alphabet) 1) (3 : Fin 4)))
  (Placement.placed RecoverRulerTrim.program trimSlots)

def input (exponent : ℕ) : Tapes 4 alphabet :=
  bank (fun _ => blank) (BinaryDescriptorStack.descriptor (sizeBits exponent)) (fun _ => blank) 0 1 0

def output (exponent : ℕ) : Tapes 4 alphabet :=
  bank (word (List.replicate exponent true)) (BinaryDescriptorStack.descriptor (sizeBits exponent)) (fun _ => blank) 0 1 0

private theorem prefix_bank (ruler source : ℤ → Fin (alphabet+4)) (rulerHead sourceHead : ℤ) (state : Fin 2) :
    (GammaPrefix.cfg ruler source rulerHead sourceHead state).tapes.append
      (⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 alphabet) =
        bank ruler source (fun _ => blank) rulerHead sourceHead 0 := by
  unfold GammaPrefix.cfg Config.tapes Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem trim_bank (ruler source descriptor : ℤ → Fin (alphabet+4)) (rulerHead descriptorHead : ℤ) :
    ((⟨![rulerHead,0,descriptorHead],![ruler,fun _ => blank,descriptor]⟩ : Tapes 3 alphabet).append
      (⟨fun _ => 1,fun _ => source⟩ : Tapes 1 alphabet)).reindex trimSlots =
        bank ruler source descriptor rulerHead 1 descriptorHead := by
  unfold Tapes.append Tapes.reindex trimSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- The size descriptor supplies the exponent through its actual low zero
bits. No exponent descriptor, parsed count or initialized private clock is
supplied. The original size cells and its head at one are retained literally. -/
theorem runs_derive (exponent : ℕ) :
    HoareTime (program (alphabet := alphabet)) (· = input exponent) (· = output exponent) (10 * exponent + 68) := by
  let source := BinaryDescriptorStack.descriptor (a := alphabet) (sizeBits exponent)
  have sourceCell (index : ℕ) (bound : index < exponent+1) :
      source (1+index) = bitSymbol ((List.replicate exponent false ++ [true])[index]'(by simpa using bound)) := by
    have cell := WordSegments.get BinaryDescriptorStack.empty 1 ((sizeBits exponent).map (bitSymbol (a := alphabet))) index (by simp [size_bits]; omega)
    simp only [source,BinaryDescriptorStack.descriptor] at *
    simp only [List.getElem_map] at cell
    simpa only [size_bits] using cell
  have scanned := FamilyPlacementAlphabet.extend_hoare
    (GammaPrefix.prefix_hoare (fun _ => (blank : Fin (alphabet+4))) source 0 1 exponent
      (by intro index bound; have cell := sourceCell index (by omega); simpa [bound] using cell)
      (by have cell := sourceCell exponent (by omega); simpa using cell))
    (⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 alphabet)
  rw [prefix_bank,prefix_bank] at scanned
  have rulerWritten : putWord (fun _ => (blank : Fin (alphabet+4))) 0 (List.replicate (exponent+1) (bitSymbol true)) =
      word (List.replicate (exponent+1) true) := by simp [word]
  rw [rulerWritten] at scanned
  simp only [zero_add] at scanned
  let ruler := word (alphabet := alphabet) (List.replicate (exponent+1) true)
  let scannedBank := bank ruler source (fun _ => blank) (exponent+1) (1+exponent) 0
  have rewindLocal := Rewind.rewind_hoare (separator : Fin (alphabet+4)) source (1+exponent) (exponent+1)
    (by
      intro index bound
      have position : (1 : ℤ)+exponent-index = 1+(exponent-index : ℕ) := by omega
      rw [position]
      have cell := sourceCell (exponent-index) (by omega)
      rw [cell]
      cases bit : (List.replicate exponent false ++ [true])[exponent-index]'(by simp) <;>
        simp [bitSymbol,separator,Fin.ext_iff])
    (by
      have position : (1 : ℤ)+exponent-(exponent+1 : ℕ) = 0 := by omega
      rw [position]
      change BinaryDescriptorStack.descriptor (a := alphabet) _ 0 = _
      rw [BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inl (by omega))]
      rfl)
  have rewound := RecoverWorkspace.runs_one_at (Rewind.program separator) (1 : Fin 4) scannedBank source source (1+exponent) 0 rfl rfl
    (by simpa only [Rewind.cfg,Config.tapes,FiniteReturnStack.bank,
      show (1 : ℤ)+exponent-(exponent+1 : ℕ) = 0 by omega] using rewindLocal)
  have rewindEndpoint : setTape scannedBank (1 : Fin 4) source 0 = bank ruler source (fun _ => blank) (exponent+1) 0 0 := by
    unfold scannedBank setTape bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [rewindEndpoint] at rewound
  let rewoundBank := bank ruler source (fun _ => blank) (exponent+1) 0 0
  have shifted := RecoverWorkspace.shift_at (1 : Fin 4) rewoundBank .right
  have shiftEndpoint : setTape rewoundBank (1 : Fin 4) (rewoundBank.tape 1) (rewoundBank.head 1+Move.right.offset) =
      bank ruler source (fun _ => blank) (exponent+1) 1 0 := by
    unfold rewoundBank setTape bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [shiftEndpoint] at shifted
  let readyBank := bank ruler source (fun _ => blank) (exponent+1) 1 0
  have constant := RecoverWorkspace.runs_one_at (RecursiveChildQuotientsConstant.program (a := alphabet) 1) (3 : Fin 4)
    readyBank (fun _ => blank) (BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits 1)) 0 1 rfl rfl
    (RecursiveChildQuotientsConstant.initialize_hoare 1)
  have constantEndpoint : setTape readyBank (3 : Fin 4)
      (BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits 1)) 1 =
        bank ruler source (BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits 1)) (exponent+1) 1 1 := by
    unfold readyBank setTape bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [constantEndpoint] at constant
  have trimmed := hoare_place
    (RecoverRulerTrim.runs_trim (alphabet := alphabet) (exponent+1) (RecursiveChildQuotientsConstant.bits 1) 1
      (RecursiveChildQuotientsConstant.bits_value 1) (by omega)) trimSlots
    (⟨fun _ => 1,fun _ => source⟩ : Tapes 1 alphabet)
  simp only [RecoverRulerTrim.input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,
    RecoverRulerTrim.output,RecoverBinaryRuler.output,Nat.add_sub_cancel] at trimmed
  rw [trim_bank,trim_bank] at trimmed
  unfold program
  apply ((((scanned.seq rewound).seq shifted).seq constant).seq trimmed).consequence (fun _ ready => ready) (fun _ finished => finished)
  norm_num [RecursiveChildQuotientsConstant.cost,RecursiveChildQuotientsConstant.bits]
  omega

end
end IntegerMultBounds.Machine.RecoverExponentRuler
