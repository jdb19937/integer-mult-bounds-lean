module

public import IntegerMultBounds.Machine.RecoverHeaderRulers

/-! Complete public-header recovery control construction: derive chunk and
exponent, synthesize rulers, subtract the scaling terms physically, and erase
all retained header/descriptor work. Only the three recovery rulers survive. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverHeaderControlSetup
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverWorkspace (atProgram erased)
open SharedPlacementAlphabet (setTape)
open Spec.SignedRingProduct (header)

def residualSlots : Fin (3+17) ≃ Fin 20 where
  toFun := ![17,18,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,19]
  invFun := ![2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,0,1,19]
  left_inv := by decide
  right_inv := by decide

def program := seq (seq (seq (seq (seq (RecoverHeaderRulers.program (alphabet := alphabet))
  (BinaryDescriptorCleanupList.oneProgram (4 : Fin 20)))
  (atProgram (MultiplicationInputSplit.scan blank) (17 : Fin 20)))
  (Placement.placed RecoverResidualPrecision.program residualSlots))
  (atProgram RecoverArrayCleanup.eraseOrigin (0 : Fin 20)))
  (atProgram EraseBack.program (1 : Fin 20))

def input (precision lengthExponent wordWidth : ℕ) : Tapes 20 alphabet :=
  RecoverHeaderRulers.input precision lengthExponent wordWidth

def output (precision lengthExponent wordWidth : ℕ) : Tapes 20 alphabet :=
  setTape (setTape (setTape (SharedBank.empty 20 alphabet)
    (17 : Fin 20) (word (List.replicate (precision-(2*(precision/6)+4+2*lengthExponent)) true)) 0)
    (18 : Fin 20) (word (List.replicate (precision/6) true)) 0)
    (19 : Fin 20) (word (List.replicate wordWidth true)) 0

def cost (precision lengthExponent wordWidth : ℕ) :=
  RecoverHeaderRulers.cost precision lengthExponent wordWidth +
  5 * precision + 2 * Nat.size (2 ^ lengthExponent) + 2 * lengthExponent +
  (header precision (2 ^ lengthExponent) wordWidth).length + 36

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

/-- All controls originate in the public header. Scaling subtraction executes
on the actual generated precision ruler; the original header, size descriptor
and exponent ruler are erased, leaving exactly the native recovery controls. -/
theorem runs_setup (precision lengthExponent wordWidth : ℕ)
    (precisionPositive : 1 ≤ precision) (widthPositive : 1 ≤ wordWidth)
    (scalingFits : 2*(precision/6)+4+2*lengthExponent ≤ precision) :
    HoareTime (program (alphabet := alphabet)) (· = input precision lengthExponent wordWidth)
      (· = output precision lengthExponent wordWidth) (cost precision lengthExponent wordWidth) := by
  have generated := RecoverHeaderRulers.runs_setup (alphabet := alphabet) precision lengthExponent wordWidth
    precisionPositive widthPositive
  let initial := RecoverHeaderRulers.output (alphabet := alphabet) precision lengthExponent wordWidth (precision/6)
  let sizeCleared := setTape initial (4 : Fin 20) (fun _ => blank) 0
  let scanned := setTape sizeCleared (17 : Fin 20) (word (List.replicate precision true)) precision
  let adjusted := Placement.replace residualSlots scanned (RecoverResidualPrecision.output precision (precision/6) lengthExponent)
  let exponentCleared := erased adjusted (0 : Fin 20)
  have sizeRun := BinaryDescriptorCleanupList.one_hoare (4 : Fin 20) initial
    (GammaHeaderRead.bits (2 ^ lengthExponent)) rfl rfl
  have localScan := MultiplicationInputSplit.scan_hoare (a := alphabet) blank (fun _ => blank) 0
    ((List.replicate precision true).map bitSymbol) (bits_nonblank _) (by rfl)
  simp only [MultiplicationInputSplit.oneCfg,Config.tapes,zero_add,List.length_map,List.length_replicate] at localScan
  have scanRun := RecoverWorkspace.runs_one_at (MultiplicationInputSplit.scan blank) (17 : Fin 20) sizeCleared
    (word (List.replicate precision true)) (word (List.replicate precision true)) 0 precision rfl rfl localScan
  have residualReady : Placement.active residualSlots scanned = RecoverResidualPrecision.input precision (precision/6) lengthExponent := by
    unfold Placement.active residualSlots scanned sizeCleared initial RecoverHeaderRulers.output
      RecoverResidualPrecision.input RecoverResidualPrecision.bank setTape
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have residualRun := Placement.hoare_at (RecoverResidualPrecision.runs_adjust (alphabet := alphabet)
    precision (precision/6) lengthExponent scalingFits) residualSlots scanned residualReady
  have residualExact := residualRun.consequence (fun _ ready => ready) (by
    rintro finalBank ⟨localBank,localReady,finalReady⟩
    rw [localReady] at finalReady
    exact finalReady) le_rfl
  have exponentRun := RecoverArrayCleanup.erase_origin_at (0 : Fin 20) adjusted
    ((List.replicate lengthExponent true).map bitSymbol) (bits_nonblank _) (by
      unfold adjusted Placement.replace Placement.combine Placement.extra residualSlots RecoverResidualPrecision.output
        RecoverResidualPrecision.bank Tapes.append Tapes.reindex
      rfl) (by
      unfold adjusted Placement.replace Placement.combine Placement.extra residualSlots RecoverResidualPrecision.output
        RecoverResidualPrecision.bank Tapes.append Tapes.reindex
      rfl)
  have headerRun := RecoverWorkspace.erase_at (1 : Fin 20) exponentCleared
    ((header precision (2 ^ lengthExponent) wordWidth).map bitSymbol) (bits_nonblank _) (by
      unfold exponentCleared erased adjusted Placement.replace Placement.combine Placement.extra residualSlots
        scanned sizeCleared initial RecoverHeaderRulers.output setTape Tapes.append Tapes.reindex
      simp only [List.length_map]
      rfl) (by
      unfold exponentCleared erased adjusted Placement.replace Placement.combine Placement.extra residualSlots
        scanned sizeCleared initial RecoverHeaderRulers.output setTape Tapes.append Tapes.reindex
      rfl)
  have endpoint : erased exponentCleared (1 : Fin 20) = output precision lengthExponent wordWidth := by
    unfold exponentCleared erased adjusted Placement.replace Placement.combine Placement.extra residualSlots
      scanned sizeCleared initial RecoverHeaderRulers.output RecoverResidualPrecision.output
      RecoverResidualPrecision.bank output SharedBank.empty setTape Tapes.append Tapes.reindex
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program input
  apply (((((generated.seq sizeRun).seq scanRun).seq residualExact).seq exponentRun).seq headerRun).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  simp only [List.length_map,List.length_replicate,GammaHeaderRead.bits,List.length_reverse,
    Spec.SignedRingProduct.length_msbBits]
  unfold cost
  omega

theorem workspace_blank (precision lengthExponent wordWidth : ℕ) (slot : Fin 20)
    (notPrecision : slot ≠ 17) (notChunk : slot ≠ 18) (notWidth : slot ≠ 19) :
    (output (alphabet := alphabet) precision lengthExponent wordWidth).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) precision lengthExponent wordWidth).head slot = 0 := by
  simp [output,setTape,SharedBank.empty,notPrecision,notChunk,notWidth]

/-- At manuscript precision the physically derived controls have exactly the
required chunk width and residual precision; no scaling-fit premise remains. -/
theorem runs_six (chunkWidth lengthExponent wordWidth : ℕ)
    (chunkLarge : 3 ≤ chunkWidth) (lengthFits : lengthExponent ≤ chunkWidth) (widthPositive : 1 ≤ wordWidth) :
    HoareTime (program (alphabet := alphabet)) (· = input (6*chunkWidth) lengthExponent wordWidth)
      (· = output (6*chunkWidth) lengthExponent wordWidth) (cost (6*chunkWidth) lengthExponent wordWidth) := by
  apply runs_setup (6*chunkWidth) lengthExponent wordWidth (by omega) widthPositive
  have quotient : 6*chunkWidth/6 = chunkWidth := by omega
  rw [quotient]
  omega

end
end IntegerMultBounds.Machine.RecoverHeaderControlSetup
