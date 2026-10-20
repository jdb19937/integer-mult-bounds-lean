module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Backward

/-! The backward events in the 25 chunks of the forward trace. The eight center blocks lie in
chunk 12, events `263..470` of it; every other chunk is the dual of its forward chunk. The
symbolic action checks run chunk by chunk, so no check evaluates the events before its chunk. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

/-- Chunk 12 of the backward events: duals around the eight transposed center blocks. -/
def centerChunk (c : List Event) : List Event :=
  (c.take 263).map Event.dual ++
    (List.range 8).flatMap (fun k => centerDual ((c.drop (263 + centerLength * k)).take centerLength)) ++
    (c.drop (263 + 8 * centerLength)).map Event.dual

def backwardChunks : List (List Event) :=
  (forwardChunks.take 12).map (·.map Event.dual) ++ [centerChunk (forwardChunks.getD 12 [])] ++
    (forwardChunks.drop 13).map (·.map Event.dual)

theorem forwardEvents_split :
    forwardEvents = (forwardChunks.take 12).flatten ++
      (forwardChunks.getD 12 [] ++ (forwardChunks.drop 13).flatten) := by
  rw [forwardEvents, ← List.take_append_drop 12 forwardChunks, List.flatten_append]
  rfl

theorem forwardChunks_take_length : (forwardChunks.take 12).flatten.length = 12288 := by
  decide +kernel

theorem forwardChunk12_length : (forwardChunks.getD 12 []).length = 1024 := by
  decide +kernel

/-- The backward event formula on any list split as `A ++ (c ++ C)` at the chunk boundaries. -/
theorem dual_split {A c C : List Event} (hA : A.length = 12288) (hc : c.length = 1024) :
    ((A ++ (c ++ C)).take 12551).map Event.dual ++
        (List.range 8).flatMap (fun k => centerDual (((A ++ (c ++ C)).drop (12551 + 26 * k)).take 26)) ++
        ((A ++ (c ++ C)).drop (12551 + 8 * 26)).map Event.dual =
      A.map Event.dual ++ (centerChunk c ++ C.map Event.dual) := by
  have hblock : ∀ k ∈ List.range 8,
      centerDual (((A ++ (c ++ C)).drop (12551 + 26 * k)).take 26) =
        centerDual ((c.drop (263 + 26 * k)).take 26) := by
    intro k hk
    rw [List.mem_range] at hk
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_append,
      List.take_append_of_le_length (by simp only [List.length_drop]; omega),
      show 12551 + 26 * k - A.length = 263 + 26 * k by omega]
  rw [List.flatMap_congr hblock, List.take_append, List.take_of_length_le (by omega),
    List.take_append_of_le_length (by omega), List.drop_append, List.drop_eq_nil_of_le (by omega),
    List.nil_append, List.drop_append_of_le_length (by omega), hA]
  simp only [centerChunk, centerLength, List.map_append, List.append_assoc, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceAdd]

theorem backwardEvents_eq : backwardEvents = backwardChunks.flatten := by
  rw [backwardEvents, centerStart, centerLength, forwardEvents_split,
    dual_split forwardChunks_take_length forwardChunk12_length, backwardChunks,
    List.flatten_append, List.flatten_append, List.flatten_singleton, ← List.map_flatten,
    ← List.map_flatten, List.append_assoc]

end IntegerMultBounds.Networks.Certificates.T16.Trace
