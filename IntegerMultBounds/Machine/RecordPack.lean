module

public import IntegerMultBounds.Machine.RecordCopy

/-! Packing blank-separated records into one contiguous word: a two-tape
machine that copies every nonblank source cell to the destination and skips
each separator without moving the destination head, stopping at the blank
after the last record. The destination receives the concatenation of the
records (`pack_hoare`). This is the record side of the bit arrays moved by
the address-chunk interchange. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RecordPack

open OrderedSelect (flat flat_cons)

variable {a : ℕ}

/-- State one: at a record origin; state zero: inside a record. -/
def program : Program 2 2 a where
  tapes_pos := by decide
  start := 1
  transition := fun s sy =>
    if s = 1 ∧ sy 0 = blank then none
    else if sy 0 ≠ blank then some (0, fun i => if i = 0 then (sy 0, .right) else (sy 0, .right))
    else some (1, fun i => if i = 0 then (sy 0, .right) else (sy 1, .stay))

def cfg (f g : ℤ → Fin (a + 4)) (x y : ℤ) (s : Fin 2) : Config 2 2 a :=
  ⟨s, fun i => if i = 0 then x else y, fun i => if i = 0 then f else g⟩

theorem step_sym (f g : ℤ → Fin (a + 4)) (x y : ℤ) (s : Fin 2) (hc : f x ≠ blank) :
    step program (cfg f g x y s) = some (cfg f (putWord g y [f x]) (x + 1) (y + 1) 0) := by
  have ht : (program (a := a)).transition s (fun i => (cfg f g x y s).tape i ((cfg f g x y s).head i)) =
      some (0, fun i => if i = 0 then (f x, Move.right) else (f x, Move.right)) := by
    fin_cases s <;> simp_all [program, cfg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Option.some.injEq, Config.mk.injEq, true_and]
  constructor
  · funext i; fin_cases i <;> simp [Move.offset]
  · funext i j; fin_cases i <;> simp [putWord, Function.update_apply]
    all_goals (try (intro hj; rw [hj]))

theorem step_sep (f g : ℤ → Fin (a + 4)) (x y : ℤ) (hc : f x = blank) :
    step program (cfg f g x y 0) = some (cfg f g (x + 1) y 1) := by
  have ht : (program (a := a)).transition 0 (fun i => (cfg f g x y 0).tape i ((cfg f g x y 0).head i)) =
      some (1, fun i => if i = 0 then (f x, Move.right) else (g y, Move.stay)) := by
    simp_all [program, cfg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Option.some.injEq, Config.mk.injEq, true_and]
  constructor
  · funext i; fin_cases i <;> simp [Move.offset]
  · funext i j; fin_cases i <;> simp
    all_goals (try (intro hj; rw [hj]))

/-- Copying a nonempty nonblank word. -/
theorem word_run (f : ℤ → Fin (a + 4)) (c : Fin (a + 4)) (xs : List (Fin (a + 4)))
    (hx : ∀ z ∈ c :: xs, z ≠ blank) :
    ∀ (g : ℤ → Fin (a + 4)) (x y : ℤ) (s : Fin 2),
    (∀ k : ℕ, k < (c :: xs).length → f (x + k) = (c :: xs).getD k blank) →
    run program (c :: xs).length (cfg f g x y s) =
      some (cfg f (putWord g y (c :: xs)) (x + (c :: xs).length) (y + (c :: xs).length) 0) := by
  induction xs generalizing c with
  | nil =>
    intro g x y s hf
    have hfx : f x = c := by simpa using hf 0 (by simp)
    rw [List.length_singleton, run, step_sym f g x y s (by rw [hfx]; exact hx c (by simp))]
    simp [run, hfx]
  | cons d xs ih =>
    intro g x y s hf
    have hfx : f x = c := by simpa using hf 0 (by simp)
    rw [List.length_cons, run, step_sym f g x y s (by rw [hfx]; exact hx c (by simp))]
    simp only [Option.bind_some]
    rw [ih d (fun z hz => hx z (by simp_all)) (putWord g y [f x]) (x + 1) (y + 1) 0
      (fun k hk => by
        have := hf (k + 1) (by simp at hk ⊢; omega)
        rw [show x + 1 + (k : ℤ) = x + ((k + 1 : ℕ) : ℤ) by push_cast; ring, this]
        simp), hfx, putWord_cons g y c (d :: xs)]
    congr 2
    · push_cast; ring
    · simp; ring

/-- Packing a list of records from a record origin. -/
theorem records_run (f : ℤ → Fin (a + 4)) (recs : List (List (Fin (a + 4))))
    (hne : ∀ z ∈ recs, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank) :
    ∀ (g : ℤ → Fin (a + 4)) (x y : ℤ),
    (∀ k : ℕ, k < (flat recs).length → f (x + k) = (flat recs).getD k blank) →
    run program (flat recs).length (cfg f g x y 1) =
      some (cfg f (putWord g y recs.flatten) (x + (flat recs).length) (y + recs.flatten.length) 1) := by
  induction recs with
  | nil => intro g x y _; simp [OrderedSelect.flat_nil, run, putWord]
  | cons z zs ih =>
    intro g x y hf
    obtain ⟨hz0, hzb⟩ := hne z (by simp)
    obtain ⟨c, xs, rfl⟩ := List.exists_cons_of_ne_nil hz0
    have hflat : flat ((c :: xs) :: zs) = (c :: xs) ++ (blank :: flat zs) := flat_cons _ _
    rw [hflat] at hf ⊢
    have hlen : ((c :: xs) ++ (blank :: flat zs)).length = (c :: xs).length + (1 + (flat zs).length) := by
      simp; ring
    rw [hlen, run_add]
    rw [word_run f c xs hzb g x y 1 (fun k hk => by
        rw [hf k (by simp at hk ⊢; omega), List.getD_append _ _ _ _ hk])]
    simp only [Option.bind_some]
    have hsep : f (x + (c :: xs).length) = blank := by
      rw [hf (c :: xs).length (by simp), List.getD_append_right _ _ _ _ le_rfl]; simp
    rw [run_add, run_one, step_sep f _ _ _ hsep]
    simp only [Option.bind_some]
    have := ih (fun z' hz' => hne z' (by simp [hz'])) (putWord g y (c :: xs))
      (x + (c :: xs).length + 1) (y + (c :: xs).length)
      (fun k hk => by
        rw [show x + ((c :: xs).length : ℤ) + 1 + k = x + (((c :: xs).length + 1 + k : ℕ) : ℤ) by push_cast; ring,
          hf _ (by simp at hk ⊢; omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [List.length_cons]
        rw [show xs.length + 1 + 1 + k - (xs.length + 1) = k + 1 by omega]
        simp)
    rw [this, List.flatten_cons, putWord_append_forward]
    congr 2
    · push_cast; ring
    · simp; ring

/-- The contract: from a record origin, the destination receives the records' concatenation. -/
theorem pack_hoare (f g : ℤ → Fin (a + 4)) (x y : ℤ) (recs : List (List (Fin (a + 4))))
    (hne : ∀ z ∈ recs, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank)
    (hf : ∀ k : ℕ, k < (flat recs).length → f (x + k) = (flat recs).getD k blank)
    (hend : f (x + (flat recs).length) = blank) :
    HoareTime program (fun v => v = (cfg f g x y 1).tapes)
      (fun v => v = (cfg f (putWord g y recs.flatten) (x + (flat recs).length)
        (y + recs.flatten.length) 1).tapes) (flat recs).length := by
  rintro v rfl
  refine ⟨_, _, le_rfl, records_run f recs hne g x y hf, ?_, rfl⟩
  unfold step
  simp_all [program, cfg]

end IntegerMultBounds.Machine.RecordPack
