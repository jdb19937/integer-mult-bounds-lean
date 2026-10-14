module

public import IntegerMultBounds.Machine.RecoverRecordField

/-! A fixed while-loop extracts every real field from a contiguous public
complex record. It produces separator-terminated LSB-first recovery words,
retains all source cells, and resets the width ruler after every iteration.
The source's actual blank end controls termination; no record-count oracle is
used. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverRecordArray
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverRecordField (bank)

abbrev Pair := List Bool × List Bool

def raw (pairs : List Pair) : List Bool := pairs.flatMap fun pair => pair.1 ++ pair.2
def native (pairs : List Pair) : List (Fin (alphabet+4)) :=
  pairs.flatMap fun pair => pair.1.reverse.map bitSymbol ++ [separator]
def test (symbols : Fin 3 → Fin (alphabet+4)) := decide (symbols 1 ≠ blank)
def program : Program 3 22 alphabet := whileLoop RecoverRecordField.program test

private theorem source_overwrite (done : List Bool) (pair : Pair) (rest : List Pair) :
    putWord (word (alphabet := alphabet) (done ++ raw (pair :: rest))) done.length
      (pair.1.map bitSymbol) = word (done ++ raw (pair :: rest)) := by
  have middle := WordSegments.middle (fun _ => (blank : Fin (alphabet+4))) 0
    (done.map bitSymbol) (pair.1.map bitSymbol) ((pair.2 ++ raw rest).map bitSymbol)
  simpa only [word, raw, List.flatMap_cons, List.map_append, List.length_map, zero_add, List.append_assoc] using middle

private theorem test_end (rulerBits done : List Bool) (destination : ℤ → Fin (alphabet+4)) (destinationHead : ℤ) :
    test (bank (word rulerBits) (word done) destination 0 done.length destinationHead).reads = false := by
  change decide (word (alphabet := alphabet) done done.length ≠ blank) = false
  rw [word, putWord_outside _ _ _ _ (Or.inr (by simp))]
  rfl

private theorem test_pair (rulerBits done : List Bool) (pair : Pair) (rest : List Pair)
    (destination : ℤ → Fin (alphabet+4)) (destinationHead : ℤ) (realNonempty : pair.1 ≠ []) :
    test (bank (word rulerBits) (word (done ++ raw (pair :: rest))) destination 0 done.length destinationHead).reads = true := by
  change decide (word (alphabet := alphabet) (done ++ raw (pair :: rest)) done.length ≠ blank) = true
  have view := source_overwrite (alphabet := alphabet) done pair rest
  rcases pair with ⟨real, imaginary⟩
  cases real with
  | nil => exact False.elim (realNonempty rfl)
  | cons bit tail =>
    have firstCell := congrFun view (done.length : ℤ)
    rw [List.map_cons, putWord_head] at firstCell
    rw [← firstCell]
    cases bit <;> simp [bitSymbol, blank, Fin.ext_iff]

/-- Exact whole-array extraction, including the empty array. Every real and
imaginary source field has the ruler's width; their bits may otherwise be
arbitrary. Runtime is linear in field width times record count. -/
theorem runs_array (pairs : List Pair) (rulerBits done : List Bool)
    (destination : ℤ → Fin (alphabet+4)) (destinationHead : ℤ)
    (widthPositive : 0 < rulerBits.length)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = rulerBits.length ∧ pair.2.length = rulerBits.length) :
    HoareTime program
      (· = bank (word rulerBits) (word (done ++ raw pairs)) destination 0 done.length destinationHead)
      (· = bank (word rulerBits) (word (done ++ raw pairs))
        (putWord destination destinationHead (native pairs)) 0 (done ++ raw pairs).length
        (destinationHead + (native (alphabet := alphabet) pairs).length))
      ((8 * rulerBits.length + 21) * pairs.length) := by
  induction pairs generalizing done destination destinationHead with
  | nil =>
    intro current equal
    subst current
    refine ⟨0, _, by simp, rfl, ?_, ?_⟩
    · exact while_step_exit RecoverRecordField.program test _ (by simpa [raw] using test_end rulerBits done destination destinationHead)
    · simp [raw, native, putWord, Config.tapes, Tapes.start]
  | cons pair rest inductionHypothesis =>
    obtain ⟨realWidth, imaginaryWidth⟩ := fieldWidths pair (by simp)
    have fieldRun := RecoverRecordField.runs_field rulerBits pair.1 realWidth.symm
      (word (done ++ raw (pair :: rest))) destination done.length destinationHead
    rw [source_overwrite] at fieldRun
    have nextSource : word (alphabet := alphabet) ((done ++ pair.1 ++ pair.2) ++ raw rest) =
        word (done ++ raw (pair :: rest)) := by simp [raw, List.append_assoc]
    have nextPosition : ((done ++ pair.1 ++ pair.2).length : ℤ) = done.length + 2 * pair.1.length := by
      simp only [List.length_append, realWidth, imaginaryWidth, Nat.cast_add]
      ring
    have tailRun := inductionHypothesis (done ++ pair.1 ++ pair.2)
      (putWord destination destinationHead (pair.1.reverse.map bitSymbol ++ [separator]))
      (destinationHead + pair.1.length + 1)
      (fun next member => fieldWidths next (List.mem_cons_of_mem pair member))
    rw [nextSource, nextPosition] at tailRun
    intro current equal
    subst current
    obtain ⟨bodyElapsed,bodyConfig,bodyBound,bodyExecuted,bodyHalted,bodyEndpoint⟩ := fieldRun _ rfl
    obtain ⟨tailElapsed,finalConfig,tailBound,tailExecuted,finalHalted,finalEndpoint⟩ := tailRun _ bodyEndpoint
    have firstIteration := while_run_iteration RecoverRecordField.program test _
      (test_pair rulerBits done pair rest destination destinationHead (by
        intro emptyReal
        have : pair.1.length = 0 := by rw [emptyReal]; rfl
        omega)) bodyExecuted bodyHalted
    refine ⟨bodyElapsed + 2 + tailElapsed, finalConfig, ?_, ?_, finalHalted, ?_⟩
    · simp only [List.length_cons]
      rw [realWidth] at bodyBound
      nlinarith
    · unfold program
      rw [run_add, firstIteration]
      exact tailExecuted
    · have destinationPosition : destinationHead + pair.1.length + 1 =
          destinationHead + (pair.1.reverse.map (bitSymbol (a := alphabet)) ++ [separator]).length := by
        simp only [List.length_append, List.length_map, List.length_reverse,
          List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      rw [destinationPosition, putWord_append_forward] at finalEndpoint
      simpa only [native, List.flatMap_cons, raw, List.length_append, List.length_map,
        List.length_reverse, List.length_singleton, Nat.cast_add, Nat.cast_one, List.append_assoc,
        add_assoc] using finalEndpoint

/-- The actual public polynomial format, real then imaginary in MSB order. -/
def publicPairs {size : ℕ} (wordWidth : ℕ) (real imaginary : Fin size → ℤ) : List Pair :=
  (List.finRange size).map fun index =>
    (Spec.SignedRingProduct.compWord wordWidth (real index),
      Spec.SignedRingProduct.compWord wordWidth (imaginary index))

theorem raw_public {size : ℕ} (wordWidth : ℕ) (real imaginary : Fin size → ℤ) :
    raw (publicPairs wordWidth real imaginary) = Spec.SignedRingProduct.record wordWidth real imaginary := by
  simp only [raw, publicPairs, Spec.SignedRingProduct.record, List.flatMap_map]

theorem native_public {size : ℕ} (wordWidth : ℕ) (real imaginary : Fin size → ℤ) :
    native (alphabet := alphabet) (publicPairs wordWidth real imaginary) = Schoenhage.cells
      (List.ofFn fun index => (Spec.SignedRingProduct.compWord wordWidth (real index)).reverse) := by
  simp only [native, publicPairs, Schoenhage.cells, Schoenhage.syms, List.ofFn_eq_map,
    List.flatMap_map, List.map_flatMap, List.map_append, List.map_map, List.map_cons,
    List.map_nil, Function.comp_def, Schoenhage.sym]

/-- The extracted cells are precisely the bits consumed by the numerically
certified recovery records; mathematical exact labels do not change the tape. -/
theorem native_recovery_records {size : ℕ} [NeZero size] (chunkWidth wordWidth : ℕ)
    (leftInput rightInput : List Bool) (real imaginary : Fin size → ℤ) :
    native (alphabet := alphabet) (publicPairs wordWidth real imaginary) = Schoenhage.cells
      ((RecoverNumericalBridge.records chunkWidth leftInput rightInput
        (fun index => (Spec.SignedRingProduct.compWord wordWidth (real index)).reverse)).map
          RecoverArray.Coefficient.bits) := by
  rw [native_public]
  simp only [RecoverNumericalBridge.records, List.map_ofFn, Function.comp_def]

/-- Extraction starts from the actual contiguous public record and writes the
native separator-terminated coefficient tape, including zero coefficients.
Imaginary components are read only for head traversal and left unchanged. -/
theorem runs_public {size : ℕ} (wordWidth : ℕ) (real imaginary : Fin size → ℤ)
    (widthPositive : 0 < wordWidth) :
    HoareTime (program (alphabet := alphabet))
      (· = bank (word (List.replicate wordWidth true))
        (word (Spec.SignedRingProduct.record wordWidth real imaginary)) (fun _ => blank) 0 0 0)
      (· = bank (word (List.replicate wordWidth true))
        (word (Spec.SignedRingProduct.record wordWidth real imaginary))
        (putWord (fun _ => blank) 0 (Schoenhage.cells
          (List.ofFn fun index => (Spec.SignedRingProduct.compWord wordWidth (real index)).reverse)))
        0 (Spec.SignedRingProduct.record wordWidth real imaginary).length
        (Schoenhage.clen (List.ofFn fun index =>
          (Spec.SignedRingProduct.compWord wordWidth (real index)).reverse)))
      ((8 * wordWidth + 21) * size) := by
  have extraction := runs_array (publicPairs wordWidth real imaginary) (List.replicate wordWidth true) []
    (fun _ => (blank : Fin (alphabet+4))) 0 (by simpa using widthPositive) (by
      intro pair member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      simp [List.length_replicate])
  simp only [List.nil_append, raw_public, native_public] at extraction
  simpa only [List.length_nil, Nat.cast_zero, zero_add, publicPairs, List.length_map,
    List.length_finRange, List.length_replicate, raw_public, native_public, Schoenhage.length_cells]
    using extraction

end
end IntegerMultBounds.Machine.RecoverRecordArray
