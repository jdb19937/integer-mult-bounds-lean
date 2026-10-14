module

public import IntegerMultBounds.Machine.ChirpMarkProduct

/-! Execute the four exact scalar products, then physically construct all
four marked controls consumed by the native complex numerator-sum machine. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpMarkedProducts
noncomputable section
open ChirpScalarProducts (words resultSlot)
open SharedPlacementAlphabet (setTape)

abbrev tapeCount := 97

def controlSlot (product : Fin 4) : Fin tapeCount := Fin.castAdd 93 product
def slots (product : Fin 4) : Fin 2 → Fin tapeCount := ![resultSlot product,controlSlot product]
theorem slots_injective (product : Fin 4) : Function.Injective (slots product) := by fin_cases product <;> decide

def placement (product : Fin 4) := InjectivePlacement.placement (slots product) (slots_injective product) (by decide : 2+95=97)
def call (product : Fin 4) := Placement.placed ChirpMarkProduct.program (placement product)
def markProgram := seq (seq (seq (call 0) (call 1)) (call 2)) (call 3)
def program := seq ChirpScalarProducts.program markProgram

def stage (operands : Fin 4 → List Bool) (width completed : ℕ) : Tapes tapeCount 2 :=
  ⟨fun slot => if slot.val<completed ∧ slot.val<4 then 1 else 0,
    fun slot =>
      if slot.val=0 ∧ 0<completed then MarkedRadixRefresh.source (words operands width 0)
      else if slot.val=1 ∧ 1<completed then MarkedRadixRefresh.source (words operands width 1)
      else if slot.val=2 ∧ 2<completed then MarkedRadixRefresh.source (words operands width 2)
      else if slot.val=3 ∧ 3<completed then MarkedRadixRefresh.source (words operands width 3)
      else (ChirpScalarProducts.output operands width).tape slot⟩

def input := ChirpScalarProducts.input
def output (operands : Fin 4 → List Bool) (width : ℕ) := stage operands width 4

private theorem stage_zero (operands : Fin 4 → List Bool) (width : ℕ) :
    stage operands width 0=ChirpScalarProducts.output operands width := by
  apply Placement.Tapes.ext'
  · intro slot; simp [stage,ChirpScalarProducts.output_head]
  · intro slot; simp [stage]

private theorem active_stage (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    Placement.active (placement product) (stage operands width product.val)=
      ChirpMarkProduct.input (words operands width product) := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  · intro slot
    fin_cases slot <;> fin_cases product <;> simp [stage,slots,controlSlot,resultSlot,tapeCount,
      ChirpMarkProduct.input,ChirpMarkProduct.bank,Copy.tapes,Copy.cfg,Config.tapes]
  · intro slot
    fin_cases slot <;> fin_cases product <;> simp [stage,slots,controlSlot,resultSlot,tapeCount,
      ChirpMarkProduct.input,ChirpMarkProduct.bank,Copy.tapes,Copy.cfg,Config.tapes,ChirpMarkProduct.raw,
      ChirpScalarProducts.output,ChirpScalarProducts.stage,ChirpScalarProducts.tapeCount]

private theorem stage_update (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    setTape (stage operands width product.val) (controlSlot product)
      (MarkedRadixRefresh.source (words operands width product)) 1=stage operands width (product.val+1) := by
  have selectedValue (slot : Fin tapeCount) (different : slot≠controlSlot product) : slot.val≠product.val := by
    intro equal
    apply different
    apply Fin.ext
    exact equal
  apply Placement.Tapes.ext'
  · intro slot
    by_cases same : slot=controlSlot product
    · subst slot
      simp only [setTape,Function.update_self,stage,controlSlot,Fin.val_castAdd]
      have bound := product.isLt
      simp [bound]
    · have different := selectedValue slot same
      simp only [setTape,Function.update_of_ne same,stage]
      have condition : (slot.val<product.val ∧ slot.val<4) ↔ (slot.val<product.val+1 ∧ slot.val<4) := by omega
      simp only [←condition]
  · intro slot
    by_cases same : slot=controlSlot product
    · subst slot
      simp only [setTape,Function.update_self]
      fin_cases product <;> simp [stage,controlSlot,tapeCount]
    · have different := selectedValue slot same
      simp only [setTape,Function.update_of_ne same]
      fin_cases product <;> simp [stage] at different ⊢
      all_goals simp [different]

private theorem runs_call (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    HoareTime (call product) (· = stage operands width product.val) (· = stage operands width (product.val+1))
      (3*width+9) := by
  have executed := Placement.hoare_at (ChirpMarkProduct.runs (words operands width product)) (placement product)
    (stage operands width product.val) (active_stage operands width product)
  apply executed.consequence (fun _ ready => ready) _ (by rw [ChirpScalarProducts.words_length])
  rintro finalBank ⟨localBank,rfl,rfl⟩
  rw [ChirpMarkProduct.output_eq_input_update,←active_stage operands width product,placement,InjectivePlacement.replace_set]
  exact stage_update operands width product

/-- One actual program executes multiplication and builds all four marked
control words, with all intermediate banks derived from the original input. -/
theorem runs (operands : Fin 4 → List Bool) (width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width) (widthPositive : 1≤width) :
    HoareTime program (· = input operands width) (· = output operands width)
      (4*Schoenhage.fmTime width+36*width+99) := by
  have marked := (((runs_call operands width 0).seq (runs_call operands width 1)).seq
    (runs_call operands width 2)).seq (runs_call operands width 3)
  change HoareTime markProgram (· = stage operands width 0) (· = stage operands width 4)
    (3*width+9+1+(3*width+9)+1+(3*width+9)+1+(3*width+9)) at marked
  rw [stage_zero] at marked
  unfold program input output
  exact ((ChirpScalarProducts.runs operands width operandWidths widthPositive).seq marked).consequence
    (fun _ ready => ready) (fun _ finished => finished) (by omega)

end
end IntegerMultBounds.Machine.ChirpMarkedProducts
