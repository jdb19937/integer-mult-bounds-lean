module

public import IntegerMultBounds.Machine.ChirpPublicPublished
public import IntegerMultBounds.Machine.WordTapeBridge

/-! Complete public-to-public complex conjugation in the manuscript bank:
header at zero, original record at one, conjugate output at three. Every other
whole tape is blank with a zero head; all actual setup, conversion, arithmetic,
serialization and erasure transitions are paid by original record volume. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicConjugation
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecoverCarryStep (word)
open Spec.SignedRingProduct (header record)

def slots : Fin 64 ≃ Fin 64 :=
  ((Equiv.swap (0 : Fin 64) 62).trans (Equiv.swap (1 : Fin 64) 61)).trans (Equiv.swap (3 : Fin 64) 63)

def program := reindex ChirpPublicPublished.program slots

def internalBank (headerBits sourceBits outputBits : List Bool) : Tapes 64 2 :=
  setTape (setTape (setTape (SharedBank.empty 64 2) 62 (word headerBits) 0) 61 (word sourceBits) 0) 63 (word outputBits) 0

private theorem public_bank (headerBits sourceBits outputBits : List Bool) :
    (internalBank headerBits sourceBits outputBits).reindex slots=
      Spec.SignedRingProduct.bank headerBits sourceBits [] outputBits := by
  have emptyWord : wordTape ([] : List (Fin 6))=(fun _ => blank) := by rw [←putWord_blank_origin]; rfl
  unfold internalBank Tapes.reindex slots setTape SharedBank.empty Spec.SignedRingProduct.bank
  apply Placement.Tapes.ext'
  all_goals intro slot; fin_cases slot
  all_goals simp [word,Spec.SignedRingProduct.wordAt,putWord_blank_origin,Function.update_apply,Equiv.swap_apply_def,emptyWord]

/-- The original disk-grid and width/size allowances prove an actual fixed
public-format program, with exact canonical output and completely blank private
workspace. No descriptor, unary control, decoded field, prebuilt output or
extra representability/cleanliness premise is supplied. -/
theorem runs_public {size : ℕ} (precision width : ℕ) (real imaginary : Fin size → ℤ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (precisionFits : precision+2≤width)
    (sizeFits : size<2^precision) (diskGrid : Spec.SignedRingProduct.DiskGrid precision real imaginary) :
    HoareTime program
      (· = Spec.SignedRingProduct.bank (header precision size width) (record width real imaginary) [] [])
      (· = Spec.SignedRingProduct.bank (header precision size width) (record width real imaginary) []
        (record width real (fun index => -imaginary index)))
      (3700*(record width real imaginary).length) := by
  obtain ⟨widthPred,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show width≠0 by omega)
  have execution := ChirpPublicPublished.runs_public precision widthPred real imaginary precisionPositive sizePositive
    precisionFits sizeFits diskGrid
  have beforeBank : ChirpPublicPublished.input precision size (widthPred+1)
      (ChirpPublicArray.publicPairs (widthPred+1) real imaginary)=
      internalBank (header precision size (widthPred+1)) (record (widthPred+1) real imaginary) [] := by
    unfold ChirpPublicPublished.input ChirpPublicConjugate.input internalBank
    rw [ChirpPublicArray.raw_public]
    unfold setTape SharedBank.empty word
    apply Placement.Tapes.ext'
    all_goals intro slot; fin_cases slot <;> rfl
  rw [beforeBank] at execution
  have afterBank : setTape (internalBank (header precision size (widthPred+1)) (record (widthPred+1) real imaginary) [])
      (63 : Fin 64) (word (record (widthPred+1) real (fun index => -imaginary index))) 0 =
      internalBank (header precision size (widthPred+1)) (record (widthPred+1) real imaginary)
        (record (widthPred+1) real (fun index => -imaginary index)) := by
    unfold internalBank setTape
    simp
  rw [afterBank] at execution
  have placed := hoare_reindex_eq execution slots
  rw [public_bank,public_bank] at placed
  exact placed

theorem workspace_blank (headerBits sourceBits outputBits : List Bool) (slot : Fin 64)
    (notHeader : slot≠0) (notSource : slot≠1) (notOutput : slot≠3) :
    (Spec.SignedRingProduct.bank headerBits sourceBits [] outputBits : Tapes 64 2).tape slot=(fun _ => blank) ∧
      (Spec.SignedRingProduct.bank headerBits sourceBits [] outputBits : Tapes 64 2).head slot=0 := by
  by_cases unusedOperand : slot=2
  · subst slot
    change Spec.SignedRingProduct.wordAt ([] : List Bool)=(fun _ => (blank : Fin 6)) ∧ (0 : ℤ)=0
    rw [Spec.SignedRingProduct.wordAt,←putWord_blank_origin]
    exact ⟨rfl,rfl⟩
  · have notHeaderValue : slot.val≠0 := by intro equal; exact notHeader (Fin.ext equal)
    have notSourceValue : slot.val≠1 := by intro equal; exact notSource (Fin.ext equal)
    have notOperandValue : slot.val≠2 := by intro equal; exact unusedOperand (Fin.ext equal)
    have notOutputValue : slot.val≠3 := by intro equal; exact notOutput (Fin.ext equal)
    simp [Spec.SignedRingProduct.bank,notHeader,notSource,notOutput,unusedOperand,notHeaderValue,notSourceValue,notOperandValue,notOutputValue]

/-- Actual halted public conjugation and every non-interface tape entirely
blank at origin, all from the original encoded header and source record. -/
theorem runs_correct {size : ℕ} (precision width : ℕ) (real imaginary : Fin size → ℤ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (precisionFits : precision+2≤width)
    (sizeFits : size<2^precision) (diskGrid : Spec.SignedRingProduct.DiskGrid precision real imaginary) :
    ∃ elapsed finalConfig,
      elapsed≤3700*(record width real imaginary).length ∧
      run program elapsed ((Spec.SignedRingProduct.bank (header precision size width)
        (record width real imaginary) [] [] : Tapes 64 2).start program)=some finalConfig ∧
      step program finalConfig=none ∧
      finalConfig.tapes=Spec.SignedRingProduct.bank (header precision size width) (record width real imaginary) []
        (record width real (fun index => -imaginary index)) ∧
      (∀ slot : Fin 64,slot≠0 → slot≠1 → slot≠3 → finalConfig.tapes.tape slot=(fun _ => blank) ∧ finalConfig.tapes.head slot=0) := by
  have execution := runs_public precision width real imaginary precisionPositive sizePositive precisionFits sizeFits diskGrid
  obtain ⟨elapsed,finalConfig,bounded,executed,halted,endpoint⟩ := execution _ rfl
  refine ⟨elapsed,finalConfig,bounded,executed,halted,endpoint,?_⟩
  intro slot notHeader notSource notOutput
  rw [endpoint]
  exact workspace_blank _ _ _ slot notHeader notSource notOutput

/-- The exact public result remains in the original disk grid, so subsequent
chirp/convolution callers need no new unit-ball allowance. -/
theorem output_diskGrid {size precision : ℕ} {real imaginary : Fin size → ℤ}
    (diskGrid : Spec.SignedRingProduct.DiskGrid precision real imaginary) :
    Spec.SignedRingProduct.DiskGrid precision real (fun index => -imaginary index) := by
  intro index
  simpa only [neg_sq] using diskGrid index

/-- At the original precision, the serialized result is exactly the complex
conjugate grid polynomial, with no approximation or rounding error. -/
theorem output_gridPoly {size : ℕ} (precision : ℕ) (real imaginary : Fin size → ℤ) :
    Spec.SignedRingProduct.gridPoly precision real (fun index => -imaginary index)=
      fun index => (starRingEnd ℂ) (Spec.SignedRingProduct.gridPoly precision real imaginary index) := by
  funext index
  apply Complex.ext <;> simp [Spec.SignedRingProduct.gridPoly,neg_div]

end
end IntegerMultBounds.Machine.ChirpPublicConjugation
