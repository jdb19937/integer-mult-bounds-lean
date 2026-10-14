module

public import IntegerMultBounds.Machine.RecoverRecordArray

/-! Finish the public-record handoff: rewind the native coefficient stream,
erase the consumed contiguous source, and erase the now-unused width ruler.
Only the separator-terminated native array remains, with its head at origin;
it is ready for RecoverLoad without a caller-supplied positioning premise. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverRecordReady
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverRecordArray (Pair raw native)
open RecoverRecordField (bank)
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)

def program : Program 3 32 alphabet :=
  seq (seq (seq RecoverRecordArray.program (atProgram ReturnOrigin.program (2 : Fin 3)))
    (atProgram EraseBack.program (1 : Fin 3)))
    (atProgram RecoverArrayCleanup.eraseOrigin (0 : Fin 3))

def input (pairs : List Pair) (rulerBits : List Bool) : Tapes 3 alphabet :=
  bank (word rulerBits) (word (raw pairs)) (fun _ => blank) 0 0 0

def output (pairs : List Pair) : Tapes 3 alphabet :=
  bank (fun _ => blank) (fun _ => blank) (putWord (fun _ => blank) 0 (native (alphabet := alphabet) pairs)) 0 0 0

theorem native_cells (pairs : List Pair) :
    native (alphabet := alphabet) pairs = Schoenhage.cells (pairs.map fun pair => pair.1.reverse) := by
  simp only [native, Schoenhage.cells, Schoenhage.syms, List.flatMap_map, List.map_flatMap,
    List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def, Schoenhage.sym]

private theorem native_nonblank (pairs : List Pair) :
    ∀ symbol ∈ native (alphabet := alphabet) pairs, symbol ≠ blank := by
  rw [native_cells]
  intro symbol member
  obtain ⟨sourceSymbol, _, rfl⟩ := List.mem_map.mp member
  exact Schoenhage.sym_ne_blank sourceSymbol

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol, blank, Fin.ext_iff]

/-- Full physical handoff from contiguous complex fields to the native array
at origin. Both consumed adapter work tapes are entirely blank with zero heads. -/
theorem runs_ready (pairs : List Pair) (rulerBits : List Bool)
    (widthPositive : 0 < rulerBits.length)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = rulerBits.length ∧ pair.2.length = rulerBits.length) :
    HoareTime program (· = input (alphabet := alphabet) pairs rulerBits) (· = output pairs)
      ((8 * rulerBits.length + 21) * pairs.length +
        (native (alphabet := alphabet) pairs).length + (raw pairs).length + 2 * rulerBits.length + 10) := by
  have extracted := RecoverRecordArray.runs_array (alphabet := alphabet) pairs rulerBits []
    (fun _ => blank) 0 widthPositive fieldWidths
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at extracted
  let extractedBank := bank (word (alphabet := alphabet) rulerBits) (word (raw pairs))
    (putWord (fun _ => blank) 0 (native (alphabet := alphabet) pairs)) 0 (raw pairs).length (native (alphabet := alphabet) pairs).length
  let returnedBank := RecoverWorkspace.restored extractedBank (2 : Fin 3)
  let sourceClearedBank := RecoverWorkspace.erased returnedBank (1 : Fin 3)
  have returned := RecoverWorkspace.return_at (2 : Fin 3) extractedBank (native pairs) (native_nonblank pairs) rfl rfl
  have sourceCleared := RecoverWorkspace.erase_at (1 : Fin 3) returnedBank
    ((raw pairs).map bitSymbol) (bits_nonblank _)
    (by simp [returnedBank, RecoverWorkspace.restored, setTape, extractedBank, bank, RulerCopy.cfg, Config.tapes])
    (by simp [returnedBank, RecoverWorkspace.restored, setTape, extractedBank, bank, RulerCopy.cfg, Config.tapes]; rfl)
  have rulerCleared := RecoverArrayCleanup.erase_origin_at (0 : Fin 3) sourceClearedBank
    (rulerBits.map bitSymbol) (bits_nonblank _)
    (by simp [sourceClearedBank, returnedBank, RecoverWorkspace.erased, RecoverWorkspace.restored,
      setTape, extractedBank, bank, RulerCopy.cfg, Config.tapes])
    (by simp [sourceClearedBank, returnedBank, RecoverWorkspace.erased, RecoverWorkspace.restored,
      setTape, extractedBank, bank, RulerCopy.cfg, Config.tapes]; rfl)
  have endpoint : RecoverWorkspace.erased sourceClearedBank (0 : Fin 3) = output (alphabet := alphabet) pairs := by
    unfold sourceClearedBank returnedBank extractedBank RecoverWorkspace.erased RecoverWorkspace.restored
      setTape output bank RulerCopy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program
  apply (((extracted.seq returned).seq sourceCleared).seq rulerCleared).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  simp only [List.length_map]
  omega

/-- The native array representation is exactly RecoverLoad's immutable source
format at its initial word boundary, including the empty array. -/
theorem native_source (pairs : List Pair) :
    (output (alphabet := alphabet) pairs).tape (2 : Fin 3) =
      (⟨[], pairs.map fun pair => pair.1.reverse⟩ : Schoenhage.WTape).tape := by
  change putWord (fun _ => (blank : Fin (alphabet+4))) 0 (native pairs) = _
  rw [native_cells, putWord_blank_origin]
  simp only [Schoenhage.WTape.tape, Schoenhage.WTape.words, List.reverse_nil, List.nil_append]

end
end IntegerMultBounds.Machine.RecoverRecordReady
