module

public import IntegerMultBounds.Networks.MaskDAG

/-! Compose independently checked certificate chunks without expanding their rows. -/

@[expose] public section

namespace IntegerMultBounds.Networks.MaskDAG

variable {width : ℕ}

/-- A shared predicate lets chunk count proofs compose without distinct generated matchers. -/
def Entry.isAddition (entry : Entry width) : Bool :=
  match entry.kind with
  | .input _ => false
  | .add _ _ => true

/-- Each chunk is checked at the offset following the preceding chunks. -/
def ChunksChecked (bank : ℕ → Option (BitVec width)) :
    ℕ → List (List (Entry width)) → Prop
  | _, [] => True
  | offset, chunk :: chunks =>
    checkChunk bank offset chunk = true ∧
      ChunksChecked bank (offset + chunk.length) chunks

/-- Separately checked chunks form a checked certificate. Keeping the chunks abstract
avoids comparing expanded certificate rows when composing their proofs. -/
theorem checkChunk_flatten (bank : ℕ → Option (BitVec width)) :
    ∀ (offset : ℕ) (chunks : List (List (Entry width))),
      ChunksChecked bank offset chunks → checkChunk bank offset chunks.flatten = true
  | _, [], _ => by simp [checkChunk]
  | offset, chunk :: chunks, ⟨hc, hr⟩ => by
    exact checkChunk_append_of bank offset chunk chunks.flatten hc
      (checkChunk_flatten bank _ chunks hr)

end IntegerMultBounds.Networks.MaskDAG
