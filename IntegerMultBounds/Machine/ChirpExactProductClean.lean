module

public import IntegerMultBounds.Machine.ChirpExactProduct
public import IntegerMultBounds.Machine.MarkedBinaryCleanup

/-! Reclaim all eight retained scalar-product/control tapes after the exact
complex sums. Every erase is physical and uses discovered word boundaries;
original operands, width ruler and both exact native sums are retained. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpExactProductClean
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (erased atProgram)

attribute [local irreducible] ChirpFastProduct.stateCount

def slots : Fin 8 → Fin 97 := ![0,1,2,3,88,89,84,86]
def productIndex : Fin 8 → Fin 4 := ![0,1,2,3,0,1,2,3]
def scalarWords (operands : Fin 4 → List Bool) (width : ℕ) (index : Fin 8) :=
  ChirpScalarProducts.words operands width (productIndex index)

def clearOne (index : Fin 8) : Program 1 4 2 :=
  if index.val<4 then MarkedBinaryCleanup.program else RecoverArrayCleanup.eraseOrigin

def call (index : Fin 8) := atProgram (clearOne index) (slots index)
def cleanup := seq (seq (seq (call 0) (call 1)) (seq (call 2) (call 3)))
  (seq (seq (call 4) (call 5)) (seq (call 6) (call 7)))
def program := seq ChirpExactProduct.program cleanup

def stage (operands : Fin 4 → List Bool) (width completed : ℕ) :=
  (List.range completed).foldl (fun current index => erased current (slots ⟨index%8,by omega⟩))
    (ChirpExactProduct.bank operands width)

def input := ChirpExactProduct.input
def output (operands : Fin 4 → List Bool) (width : ℕ) := stage operands width 8

private theorem stage_next (operands : Fin 4 → List Bool) (width : ℕ) (index : Fin 8) :
    erased (stage operands width index.val) (slots index)=stage operands width (index.val+1) := by
  unfold stage
  rw [List.range_succ,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,Nat.mod_eq_of_lt index.isLt]

private theorem stage_head (operands : Fin 4 → List Bool) (width : ℕ) (index : Fin 8) :
    (stage operands width index.val).head (slots index)=if index.val<4 then 1 else 0 := by
  fin_cases index <;> simp [stage,List.range_succ,erased,setTape,slots,ChirpExactProduct.bank]

private theorem stage_tape (operands : Fin 4 → List Bool) (width : ℕ) (index : Fin 8) :
    (stage operands width index.val).tape (slots index)=
      if index.val<4 then MarkedRadixRefresh.source (scalarWords operands width index)
      else RulerWordMap.word ((scalarWords operands width index).map RadixDigits.digitSymbol) := by
  fin_cases index <;> simp [stage,List.range_succ,erased,setTape,slots,ChirpExactProduct.bank,scalarWords,productIndex,
    ChirpScalarProducts.output,ChirpScalarProducts.stage,ChirpScalarProducts.tapeCount]

private theorem runs_call (operands : Fin 4 → List Bool) (width : ℕ) (index : Fin 8) :
    HoareTime (call index) (· = stage operands width index.val) (· = stage operands width (index.val+1)) (2*width+4) := by
  let digits := scalarWords operands width index
  have nonblank : ∀ symbol ∈ digits.map RadixDigits.digitSymbol,symbol≠(blank : Fin 6) := by
    intro symbol member
    obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
    fin_cases digit <;> decide
  have wordLength : digits.length=width := ChirpScalarProducts.words_length _ _ _
  have headReady := stage_head operands width index
  have tapeReady := stage_tape operands width index
  have executed : HoareTime (call index) (· = stage operands width index.val)
      (· = erased (stage operands width index.val) (slots index)) (2*width+4) := by
    by_cases marked : index.val<4
    · simp only [marked,↓reduceIte] at headReady tapeReady
      unfold call clearOne
      rw [ite_eq_left marked]
      apply RecoverWorkspace.runs_one_at MarkedBinaryCleanup.program (slots index)
        (stage operands width index.val) (MarkedRadixRefresh.source digits) (fun _ => blank) 1 0 headReady tapeReady
      simpa only [MarkedRadixRefresh.source,MarkedWordCleanup.one,FiniteReturnStack.bank,List.length_map,wordLength]
        using MarkedBinaryCleanup.word_hoare (digits.map RadixDigits.digitSymbol) nonblank
    · simp only [marked,↓reduceIte] at headReady tapeReady
      unfold call clearOne
      rw [ite_eq_right marked]
      have cleared := RecoverArrayCleanup.erase_origin_at (slots index) (stage operands width index.val)
        (digits.map RadixDigits.digitSymbol) nonblank headReady tapeReady
      exact cleared.consequence (fun _ ready => ready) (fun _ finished => finished) (by simp only [List.length_map,wordLength]; omega)
  simpa only [stage_next] using executed

/-- Genuine eight-tape cleanup follows actual exact complex multiplication.
No supplied clean bank, cleanup execution or per-word bound is assumed. -/
theorem runs (operands : Fin 4 → List Bool) (width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width) (widthPositive : 1≤width) :
    HoareTime program (· = input operands width) (· = output operands width)
      (4*Schoenhage.fmTime width+88*width+267) := by
  have firstPair := (runs_call operands width 0).seq (runs_call operands width 1)
  have secondPair := (runs_call operands width 2).seq (runs_call operands width 3)
  have thirdPair := (runs_call operands width 4).seq (runs_call operands width 5)
  have fourthPair := (runs_call operands width 6).seq (runs_call operands width 7)
  have reclaimed := (firstPair.seq secondPair).seq (thirdPair.seq fourthPair)
  have zeroStage : stage operands width (0 : Fin 8).val=ChirpExactProduct.bank operands width := rfl
  have cleanupRun : HoareTime cleanup (· = ChirpExactProduct.bank operands width) (· = output operands width)
      (16*width+39) := reclaimed.consequence
    (fun _ ready => ready.trans zeroStage.symm) (fun _ finished => finished) (by omega)
  have exactRun := ChirpExactProduct.runs operands width operandWidths widthPositive
  rw [ChirpExactProduct.output_eq_bank] at exactRun
  exact HoareTime.seq_bound (M := ChirpExactProduct.program) (N := cleanup)
    exactRun cleanupRun (by omega)

/-- Only the original operands, width ruler and exact numerator fields survive. -/
def bank (operands : Fin 4 → List Bool) (width : ℕ) : Tapes 97 2 :=
  ⟨fun _ => 0,fun slot =>
    if slot.val=4 then MarkedWordCleanup.word ((ChirpExactProduct.words operands width 0).map RadixDigits.digitSymbol)
    else if slot.val=9 then MarkedWordCleanup.word ((ChirpExactProduct.words operands width 1).map RadixDigits.digitSymbol)
    else (ChirpScalarProducts.input operands width).tape slot⟩

theorem output_eq_bank (operands : Fin 4 → List Bool) (width : ℕ) :
    output operands width=bank operands width := by
  apply Placement.Tapes.ext'
  · intro slot
    fin_cases slot <;> rfl
  · intro slot
    fin_cases slot <;> rfl

end
end IntegerMultBounds.Machine.ChirpExactProductClean
