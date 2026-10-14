module

public import IntegerMultBounds.Machine.RecoverLoad
public import IntegerMultBounds.NLogN.Carry

/-! One fixed while-loop recovers a stream of signed dyadic coefficients.
Every record is loaded from the original immutable separator-terminated array,
rounded, carried, published and cleaned. The carried value identity and uniform
linear serialized-volume runtime are derived from the executed iterations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverArray
noncomputable section
variable {alphabet : ℕ}
open Schoenhage
open RecoverCarryStep (word)

structure Coefficient where
  bits : List Bool
  exact : ℕ

def Good (wordWidth precision : ℕ) (coefficient : Coefficient) : Prop :=
  coefficient.bits.length = wordWidth ∧
    |(TwosComplement.signed coefficient.bits : ℝ) / 2 ^ precision - coefficient.exact| < 1 / 2

def body : Program 11 86 alphabet := seq RecoverLoad.program (extend RecoverIteration.program 1)
def test (symbols : Fin 11 → Fin (alphabet+4)) := decide (symbols 10 ≠ blank)
def program : Program 11 87 alphabet := whileLoop body test

theorem published_bank (carryBits chunk emitted : List Bool) (chunkWidth precision : ℕ) :
    RecoverIterationFinish.output (alphabet := alphabet) carryBits chunk chunkWidth precision
      (word emitted) emitted.length =
      RecoverLoad.ready carryBits chunkWidth precision (word (emitted ++ chunk)) (emitted ++ chunk).length := by
  have appended : putWord (word (alphabet := alphabet) emitted) emitted.length (chunk.map bitSymbol) =
      word (emitted ++ chunk) := by
    have joined := putWord_append_forward (fun _ => (blank : Fin (alphabet+4))) 0
      (emitted.map bitSymbol) (chunk.map bitSymbol)
    simpa only [word,List.length_map,zero_add,← List.map_append] using joined
  unfold RecoverIterationFinish.output
  rw [appended]
  simp only [List.length_append,Nat.cast_add,RecoverLoad.ready]

theorem runs_body (done rest : List (List Bool)) (bits carryBits emitted : List Bool)
    (coefficient chunkWidth precision wordWidth : ℕ) (wordLength : bits.length = wordWidth)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (carryWidth : carryBits.length ≤ wordWidth)
    (approximationClose : |(TwosComplement.signed bits : ℝ) / 2 ^ precision - coefficient| < 1 / 2) :
    ∃ chunk nextCarry : List Bool, chunk.length = chunkWidth ∧
      Counter.value chunk = (coefficient + Counter.value carryBits) % 2 ^ chunkWidth ∧
      Counter.value nextCarry = (coefficient + Counter.value carryBits) / 2 ^ chunkWidth ∧
      nextCarry.length ≤ wordWidth ∧
      HoareTime (body (alphabet := alphabet))
        (· = RecoverLoad.input ⟨done,bits :: rest⟩ carryBits chunkWidth precision (word emitted) emitted.length)
        (· = RecoverLoad.input ⟨bits :: done,rest⟩ nextCarry chunkWidth precision (word (emitted ++ chunk)) (emitted ++ chunk).length)
        (134 * wordWidth) := by
  have bitsNonempty : bits ≠ [] := by intro empty; rw [empty] at wordLength; simp only [List.length_nil] at wordLength; omega
  let lowBits := bits.dropLast
  let sign := bits.getLast bitsNonempty
  have wordLayout : lowBits ++ [sign] = bits := List.dropLast_append_getLast bitsNonempty
  obtain ⟨chunk,nextCarry,chunkLength,chunkValue,carryValue,nextWidth,native⟩ :=
    RecoverIteration.runs_iteration_exists (alphabet := alphabet) lowBits sign carryBits coefficient chunkWidth precision
      (word emitted) emitted.length precisionPositive (by rw [wordLayout,wordLength]; exact precisionFits)
      chunkPositive (by rw [wordLayout,wordLength]; exact chunkFits) (by rw [wordLayout,wordLength]; exact carryWidth)
      (by simpa only [wordLayout] using approximationClose)
  rw [wordLayout,wordLength] at nextWidth
  refine ⟨chunk,nextCarry,chunkLength,chunkValue,carryValue,nextWidth,?_⟩
  have loaded := RecoverLoad.runs_load (alphabet := alphabet) done rest bits carryBits chunkWidth precision (word emitted) emitted.length
  have loadedEndpoint := RecoverLoad.loaded_native (alphabet := alphabet) done rest lowBits sign carryBits chunkWidth precision
    (word emitted) emitted.length
  rw [wordLayout] at loadedEndpoint
  have executed := FamilyPlacementAlphabet.extend_hoare native
    (⟨fun _ => (⟨bits :: done,rest⟩ : WTape).pos,fun _ => (⟨bits :: done,rest⟩ : WTape).tape⟩ : Tapes 1 alphabet)
  have readyRun := loaded.consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis.trans loadedEndpoint) le_rfl
  apply (readyRun.seq executed).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => by
      rw [published_bank] at hypothesis
      exact hypothesis)
  rw [wordLayout,wordLength]
  omega

theorem test_record (done rest : List (List Bool)) (bits carryBits emitted : List Bool) (chunkWidth precision : ℕ) :
    test (RecoverLoad.input (alphabet := alphabet) ⟨done,bits :: rest⟩ carryBits chunkWidth precision (word emitted) emitted.length).reads = true := by
  change decide ((⟨done,bits :: rest⟩ : WTape).tape (a := alphabet) (⟨done,bits :: rest⟩ : WTape).pos ≠ blank) = true
  have scanned := WTape.tape_at_pos (a := alphabet) (⟨done,bits :: rest⟩ : WTape) 0
  simp only [Nat.cast_zero,add_zero] at scanned
  rw [scanned]
  cases bits with
  | nil => simp [syms_cons,sym,separator,blank,Fin.ext_iff]
  | cons bit tail => cases bit <;> simp [syms_cons,sym,bitSymbol,blank,Fin.ext_iff]

theorem test_end (done : List (List Bool)) (carryBits emitted : List Bool) (chunkWidth precision : ℕ) :
    test (RecoverLoad.input (alphabet := alphabet) ⟨done,[]⟩ carryBits chunkWidth precision (word emitted) emitted.length).reads = false := by
  change decide ((⟨done,[]⟩ : WTape).tape (a := alphabet) (⟨done,[]⟩ : WTape).pos ≠ blank) = false
  have scanned := WTape.tape_end (a := alphabet) (⟨done,[]⟩ : WTape) rfl 0
  simp only [Nat.cast_zero,add_zero] at scanned
  rw [scanned]
  rfl

/-- Actual array execution and the carry value invariant, including the empty
array. The source cells are retained exactly, all scratch is ready, and the
remaining carry is bounded even when its representation contains high zeroes. -/
theorem runs_array (records : List Coefficient) (done : List (List Bool)) (carryBits emitted : List Bool)
    (chunkWidth precision wordWidth : ℕ) (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (carryWidth : carryBits.length ≤ wordWidth) (recordsGood : ∀ record ∈ records, Good wordWidth precision record) :
    ∃ chunks : List (List Bool), ∃ finalCarry : List Bool,
      chunks.flatten.length = chunkWidth * records.length ∧ finalCarry.length ≤ wordWidth ∧
      Counter.value chunks.flatten + (2 ^ chunkWidth) ^ records.length * Counter.value finalCarry =
        NLogN.evalBase (2 ^ chunkWidth) (records.map Coefficient.exact) + Counter.value carryBits ∧
      HoareTime (program (alphabet := alphabet))
        (· = RecoverLoad.input ⟨done,records.map Coefficient.bits⟩ carryBits chunkWidth precision (word emitted) emitted.length)
        (· = RecoverLoad.input ⟨(records.map Coefficient.bits).reverse ++ done,[]⟩ finalCarry chunkWidth precision
          (word (emitted ++ chunks.flatten)) (emitted ++ chunks.flatten).length)
        (136 * wordWidth * records.length) := by
  induction records generalizing done carryBits emitted with
  | nil =>
    refine ⟨[],carryBits,by simp,carryWidth,by simp [Counter.value,NLogN.evalBase],?_⟩
    intro current equal
    subst current
    refine ⟨0,_,by simp,rfl,?_,?_⟩
    · exact while_step_exit body test _ (test_end done carryBits emitted chunkWidth precision)
    · simp [Config.tapes,Tapes.start]
  | cons record records inductionHypothesis =>
    obtain ⟨wordLength,close⟩ := recordsGood record (by simp)
    obtain ⟨chunk,nextCarry,chunkLength,chunkValue,carryValue,nextWidth,bodyRun⟩ := runs_body (alphabet := alphabet)
      done (records.map Coefficient.bits) record.bits carryBits emitted record.exact chunkWidth precision wordWidth
      wordLength precisionPositive precisionFits chunkPositive chunkFits carryWidth close
    obtain ⟨chunks,finalCarry,tailLength,finalWidth,tailValue,tailRun⟩ :=
      inductionHypothesis (record.bits :: done) nextCarry (emitted ++ chunk) nextWidth
        (fun next member => recordsGood next (List.mem_cons_of_mem record member))
    have carryStep : Counter.value chunk + 2 ^ chunkWidth * Counter.value nextCarry =
        record.exact + Counter.value carryBits := by
      rw [chunkValue,carryValue]
      exact Nat.mod_add_div _ _
    refine ⟨chunk :: chunks,finalCarry,?_,finalWidth,?_,?_⟩
    · simp only [List.flatten_cons,List.length_append,List.length_cons,chunkLength,tailLength]
      ring
    · simp only [List.flatten_cons,TwosComplement.value_append,chunkLength,List.length_cons,pow_succ,
        List.map_cons,NLogN.evalBase]
      have scaledTail := congrArg (fun total : ℕ => 2 ^ chunkWidth * total) tailValue
      nlinarith [scaledTail,carryStep]
    · intro current equal
      subst current
      obtain ⟨bodyElapsed,bodyConfig,bodyBound,bodyExecuted,bodyHalted,bodyEndpoint⟩ := bodyRun _ rfl
      obtain ⟨tailElapsed,finalConfig,tailBound,tailExecuted,finalHalted,finalEndpoint⟩ := tailRun _ bodyEndpoint
      have firstIteration := while_run_iteration (body (alphabet := alphabet)) test _
        (test_record done (records.map Coefficient.bits) record.bits carryBits emitted chunkWidth precision)
        bodyExecuted bodyHalted
      refine ⟨bodyElapsed + 2 + tailElapsed,finalConfig,?_,?_,finalHalted,?_⟩
      · simp only [List.length_cons]
        have wordPositive : 0 < wordWidth := by omega
        nlinarith
      · simp only [program,List.map_cons]
        rw [run_add,firstIteration]
        exact tailExecuted
      · simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,List.flatten_cons]
          using finalEndpoint

/-- When the recovered coefficient value fits in the emitted chunk capacity,
the actual terminal carry has value zero and the published word is exact. The
carry may retain high zero bits; erasing this final descriptor is separate. -/
theorem runs_array_fit (records : List Coefficient) (chunkWidth precision wordWidth : ℕ)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (recordsGood : ∀ record ∈ records, Good wordWidth precision record)
    (valueFits : NLogN.evalBase (2 ^ chunkWidth) (records.map Coefficient.exact) <
      (2 ^ chunkWidth) ^ records.length) :
    ∃ recoveredWord finalCarry : List Bool,
      recoveredWord.length = chunkWidth * records.length ∧ finalCarry.length ≤ wordWidth ∧
      Counter.value finalCarry = 0 ∧
      Counter.value recoveredWord = NLogN.evalBase (2 ^ chunkWidth) (records.map Coefficient.exact) ∧
      HoareTime (program (alphabet := alphabet))
        (· = RecoverLoad.input ⟨[],records.map Coefficient.bits⟩ [] chunkWidth precision (fun _ => blank) 0)
        (· = RecoverLoad.input ⟨(records.map Coefficient.bits).reverse,[]⟩ finalCarry chunkWidth precision
          (word recoveredWord) recoveredWord.length)
        (136 * wordWidth * records.length) := by
  obtain ⟨chunks,finalCarry,wordLength,carryWidth,valueEquation,execution⟩ := runs_array (alphabet := alphabet)
    records [] [] [] chunkWidth precision wordWidth precisionPositive precisionFits chunkPositive chunkFits
    (by simp) recordsGood
  simp only [Counter.value,List.nil_append,List.append_nil] at valueEquation execution
  have carryZero : Counter.value finalCarry = 0 := by
    by_contra nonzero
    have capacityPositive : 0 < (2 ^ chunkWidth) ^ records.length := by positivity
    have atLeastOne : 1 ≤ Counter.value finalCarry := by omega
    nlinarith
  refine ⟨chunks.flatten,finalCarry,wordLength,carryWidth,carryZero,?_,?_⟩
  · simpa only [carryZero,Nat.mul_zero,Nat.add_zero] using valueEquation
  · exact execution

end
end IntegerMultBounds.Machine.RecoverArray
