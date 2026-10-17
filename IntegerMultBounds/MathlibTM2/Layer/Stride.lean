module

public import Mathlib.Tactic

/-!
# Alternating blocks

A list of `2 N` blocks of length `σ` splits into its even blocks and its odd blocks; the `k`-th
entries of the two halves are partners at distance `σ` in the original list, and interleaving
the halves block by block restores the list (`interleave_evens_odds`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

variable {α : Type*}

/-- Block `n` of length `σ`. -/
def blk (l : List α) (σ n : ℕ) : List α := (l.drop (n * σ)).take σ

/-- The even blocks. -/
def evens (σ N : ℕ) (l : List α) : List α := (List.range N).flatMap fun i => blk l σ (2 * i)

/-- The odd blocks. -/
def odds (σ N : ℕ) (l : List α) : List α := (List.range N).flatMap fun i => blk l σ (2 * i + 1)

/-- Interleave two lists block by block. -/
def interleave (σ N : ℕ) (a b : List α) : List α :=
  (List.range N).flatMap fun i => blk a σ i ++ blk b σ i

lemma length_blk (l : List α) (σ n : ℕ) (h : (n + 1) * σ ≤ l.length) : (blk l σ n).length = σ := by
  simp [blk, List.length_take, List.length_drop]
  rw [Nat.add_mul] at h; omega

lemma getElem_blk (l : List α) (σ n j : ℕ) (hj : j < σ) (h : (n + 1) * σ ≤ l.length)
    (hb : j < (blk l σ n).length) :
    (blk l σ n)[j] = l[n * σ + j]'(by rw [Nat.add_mul] at h; omega) := by
  simp [blk, List.getElem_take, List.getElem_drop]

/-- A list is the concatenation of its blocks. -/
lemma blk_succ (l : List α) (σ n : ℕ) : blk l σ (n + 1) = blk (l.drop σ) σ n := by
  simp [blk, List.drop_drop, Nat.add_mul, Nat.add_comm]

lemma flatMap_blk (σ M : ℕ) (l : List α) (hl : l.length = M * σ) :
    (List.range M).flatMap (fun n => blk l σ n) = l := by
  induction M generalizing l with
  | zero => simp at hl; simp [List.length_eq_zero_iff.1 (by simpa using hl)]
  | succ M ih =>
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [blk_succ]
      rw [ih (l.drop σ) (by simp [hl, Nat.succ_mul])]
      simp [blk, List.take_append_drop]

/-- Blocks of a concatenation of equal-length blocks. -/
lemma blk_flatMap (σ N : ℕ) (g : ℕ → List α) (hg : ∀ j < N, (g j).length = σ) (i : ℕ) (hi : i < N) :
    blk ((List.range N).flatMap g) σ i = g i := by
  induction N generalizing g i with
  | zero => omega
  | succ N ih =>
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      rcases i with _ | i
      · simp only [blk, zero_mul, List.drop_zero]
        rw [List.take_append_of_le_length (by rw [hg 0 (by omega)])]
        rw [List.take_of_length_le (by rw [hg 0 (by omega)])]
      · rw [blk_succ, List.drop_append_of_le_length (by rw [hg 0 (by omega)])]
        rw [List.drop_of_length_le (by rw [hg 0 (by omega)]), List.nil_append]
        exact ih (fun j => g (j + 1)) (fun j hj => hg (j + 1) (by omega)) i (by omega)

lemma flatMap_pairs (N : ℕ) (b : ℕ → List α) :
    (List.range N).flatMap (fun i => b (2 * i) ++ b (2 * i + 1)) = (List.range (2 * N)).flatMap b := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.flatMap_append, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
        List.range_succ, List.range_succ, List.flatMap_append, List.flatMap_append]
      simp [List.append_assoc]

theorem interleave_evens_odds (σ N : ℕ) (l : List α) (hl : l.length = 2 * N * σ) :
    interleave σ N (evens σ N l) (odds σ N l) = l := by
  have hlen : ∀ n < 2 * N, (blk l σ n).length = σ := fun n hn =>
    length_blk l σ n (by rw [hl]; nlinarith)
  unfold interleave
  rw [show ((List.range N).flatMap fun i => blk (evens σ N l) σ i ++ blk (odds σ N l) σ i) =
      (List.range N).flatMap (fun i => blk l σ (2 * i) ++ blk l σ (2 * i + 1)) from ?_]
  · rw [flatMap_pairs, flatMap_blk σ (2 * N) l hl]
  · apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [evens, odds, blk_flatMap σ N _ (fun j hj => hlen _ (by omega)) i hi,
      blk_flatMap σ N _ (fun j hj => hlen _ (by omega)) i hi]

end IntegerMultBounds.MathlibTM2.Layer
