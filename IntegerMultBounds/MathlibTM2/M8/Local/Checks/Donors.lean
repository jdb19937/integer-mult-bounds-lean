module

public import IntegerMultBounds.MathlibTM2.M8.Local.Witness

/-!
# The donor count of the PR97 side DAG

A kernel count over the node records: `38741` nodes donate a linked operand (`donors_count`).
The count runs in sixteen chunks of 4096 records, one `decide +kernel` theorem each, so the
kernel's memory is freed between chunks. `countP_chunks` splits the count over the chunks for
every predicate, so joining the chunks compares no concrete counts.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

theorem countP_split (p : ℕ → Bool) (s w n s' : ℕ) (hs : s + w = s') :
    (List.range' s (w + n)).countP p = (List.range' s w).countP p + (List.range' s' n).countP p := by
  rw [← hs, ← List.range'_append_1, List.countP_append]

/-- The count over the records, chunk by chunk. -/
theorem countP_chunks (p : ℕ → Bool) :
    (List.range 64042).countP p =
      (List.range' 0 4096).countP p + (
      (List.range' 4096 4096).countP p + (
      (List.range' 8192 4096).countP p + (
      (List.range' 12288 4096).countP p + (
      (List.range' 16384 4096).countP p + (
      (List.range' 20480 4096).countP p + (
      (List.range' 24576 4096).countP p + (
      (List.range' 28672 4096).countP p + (
      (List.range' 32768 4096).countP p + (
      (List.range' 36864 4096).countP p + (
      (List.range' 40960 4096).countP p + (
      (List.range' 45056 4096).countP p + (
      (List.range' 49152 4096).countP p + (
      (List.range' 53248 4096).countP p + (
      (List.range' 57344 4096).countP p + (
      (List.range' 61440 2602).countP p))))))))))))))) := by
  rw [List.range_eq_range']
  rw [countP_split p 0 4096 59946 4096 rfl]
  rw [countP_split p 4096 4096 55850 8192 rfl]
  rw [countP_split p 8192 4096 51754 12288 rfl]
  rw [countP_split p 12288 4096 47658 16384 rfl]
  rw [countP_split p 16384 4096 43562 20480 rfl]
  rw [countP_split p 20480 4096 39466 24576 rfl]
  rw [countP_split p 24576 4096 35370 28672 rfl]
  rw [countP_split p 28672 4096 31274 32768 rfl]
  rw [countP_split p 32768 4096 27178 36864 rfl]
  rw [countP_split p 36864 4096 23082 40960 rfl]
  rw [countP_split p 40960 4096 18986 45056 rfl]
  rw [countP_split p 45056 4096 14890 49152 rfl]
  rw [countP_split p 49152 4096 10794 53248 rfl]
  rw [countP_split p 53248 4096 6698 57344 rfl]
  rw [countP_split p 57344 4096 2602 61440 rfl]

theorem donors00 :
    ((List.range' 0 4096).countP fun n => (recAt n).link.isSome) = 2024 := by
  decide +kernel

theorem donors01 :
    ((List.range' 4096 4096).countP fun n => (recAt n).link.isSome) = 1452 := by
  decide +kernel

theorem donors02 :
    ((List.range' 8192 4096).countP fun n => (recAt n).link.isSome) = 3408 := by
  decide +kernel

theorem donors03 :
    ((List.range' 12288 4096).countP fun n => (recAt n).link.isSome) = 3622 := by
  decide +kernel

theorem donors04 :
    ((List.range' 16384 4096).countP fun n => (recAt n).link.isSome) = 3924 := by
  decide +kernel

theorem donors05 :
    ((List.range' 20480 4096).countP fun n => (recAt n).link.isSome) = 4049 := by
  decide +kernel

theorem donors06 :
    ((List.range' 24576 4096).countP fun n => (recAt n).link.isSome) = 3986 := by
  decide +kernel

theorem donors07 :
    ((List.range' 28672 4096).countP fun n => (recAt n).link.isSome) = 3758 := by
  decide +kernel

theorem donors08 :
    ((List.range' 32768 4096).countP fun n => (recAt n).link.isSome) = 3551 := by
  decide +kernel

theorem donors09 :
    ((List.range' 36864 4096).countP fun n => (recAt n).link.isSome) = 3401 := by
  decide +kernel

theorem donors10 :
    ((List.range' 40960 4096).countP fun n => (recAt n).link.isSome) = 385 := by
  decide +kernel

theorem donors11 :
    ((List.range' 45056 4096).countP fun n => (recAt n).link.isSome) = 963 := by
  decide +kernel

theorem donors12 :
    ((List.range' 49152 4096).countP fun n => (recAt n).link.isSome) = 4096 := by
  decide +kernel

theorem donors13 :
    ((List.range' 53248 4096).countP fun n => (recAt n).link.isSome) = 122 := by
  decide +kernel

theorem donors14 :
    ((List.range' 57344 4096).countP fun n => (recAt n).link.isSome) = 0 := by
  decide +kernel

theorem donors15 :
    ((List.range' 61440 2602).countP fun n => (recAt n).link.isSome) = 0 := by
  decide +kernel

theorem donors_count : ((List.range nodeCount).countP fun n => (recAt n).link.isSome) = 38741 := by
  rw [show nodeCount = 64042 from rfl, countP_chunks, donors00, donors01, donors02, donors03, donors04, donors05,
    donors06, donors07, donors08, donors09, donors10, donors11,
    donors12, donors13, donors14, donors15]

end IntegerMultBounds.MathlibTM2.M8.Local
