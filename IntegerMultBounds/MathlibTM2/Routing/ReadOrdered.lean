module

public import IntegerMultBounds.MathlibTM2.Routing.ReadRows
public import IntegerMultBounds.MathlibTM2.Routing.Coordinates

/-!
# Arbitrary-order physical source reading

A list of physical source positions is represented by an ordered table of
singleton masks. The fixed `readRows` interpreter reads these positions in exactly
that order, allowing repetitions. The complete source and table are restored.
The theorem charges `n * (6 * W + 8) + 6` host steps for `n` positions in a
`W`-bit source. Descriptors are data, never descriptor-specific program syntax.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

/-- One singleton mask per requested source position, in descriptor order. -/
def sourceTable {W : ℕ} (indices : List (Fin W)) : List (List Bool) :=
  indices.map fun q => List.ofFn fun j : Fin W => decide (j = q)

private theorem gather_none {W : ℕ} (f : Fin W → Bool) :
    gatherL (List.ofFn f) (List.ofFn fun _ : Fin W => false) = [] := by
  induction W with
  | zero => rfl
  | succ W ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simpa [gatherL] using ih (fun j => f j.succ)

/-- A singleton descriptor mask selects exactly its named physical bit. -/
theorem gather_singleton {W : ℕ} (f : Fin W → Bool) (q : Fin W) :
    gatherL (List.ofFn f) (List.ofFn fun j : Fin W => decide (j = q)) = [f q] := by
  induction W with
  | zero => exact Fin.elim0 q
  | succ W ih =>
    refine Fin.cases ?_ (fun q => ?_) q
    · rw [List.ofFn_succ, List.ofFn_succ]
      simp only [decide_true, gatherL, Fin.succ_ne_zero, decide_false]
      rw [gather_none]
      simp
    · rw [List.ofFn_succ, List.ofFn_succ]
      have hz : (0 : Fin (W + 1)) ≠ q.succ := Ne.symm (Fin.succ_ne_zero q)
      simpa [gatherL, hz] using ih (fun j => f j.succ) q

theorem sourceTable_width {W : ℕ} (indices : List (Fin W)) :
    ∀ ms ∈ sourceTable indices, ms.length = W := by
  intro ms hm
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
  simp

theorem sourceTable_read {W : ℕ} (f : Fin W → Bool) (indices : List (Fin W)) :
    (sourceTable indices).flatMap (gatherL (List.ofFn f)) = indices.map f := by
  induction indices with
  | nil => rfl
  | cons q indices ih =>
    change gatherL (List.ofFn f) (List.ofFn fun j => decide (j = q)) ++
      (sourceTable indices).flatMap (gatherL (List.ofFn f)) = _
    rw [gather_singleton, ih]
    rfl

theorem sourceTable_size {W : ℕ} (indices : List (Fin W)) :
    (sourceTable indices).flatten.length = indices.length * W := by
  induction indices with
  | nil => simp [sourceTable]
  | cons q indices ih => simpa [sourceTable, Nat.add_mul, Nat.add_comm] using ih

theorem readOrdered_cost {W : ℕ} (f : Fin W → Bool) (indices : List (Fin W)) :
    readRowsCost (List.ofFn f) (sourceTable indices) = indices.length * (6 * W + 8) + 6 := by
  rw [readRowsCost, sourceTable_size, sourceTable_read]
  simp only [sourceTable, List.length_map, List.length_ofFn]
  ring

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Arbitrary ordered source reading, with all descriptor and source data restored
and three clean scratch registers. Only output gains the requested bit list. -/
theorem readOrdered_exec {src desc st saved rev out cs : Fin T}
    (h : [src, desc, st, saved, rev, out].Nodup) {W : ℕ} (hW : 0 < W)
    (f : Fin W → Bool) (indices : List (Fin W)) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = (List.ofFn f).map bitSymbol)
    (hd : S.R desc = (sourceTable indices).flatten.map bitSymbol)
    (hst : S.R st = []) (hsaved : S.R saved = []) (hrev : S.R rev = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (readRows src desc st saved rev out cs) (mk v S)
        (indices.length * (6 * W + 8) + 6)
        (mk v' { S with R := Function.update S.R out ((indices.map f).map bitSymbol ++ S.R out) }) := by
  obtain ⟨v', hu, he⟩ := readRows_exec body (cs := cs) h (List.ofFn f)
    (by simpa using hW) (sourceTable indices) (by simpa using sourceTable_width indices) v S hs hd hst hsaved hrev
  rw [readOrdered_cost, sourceTable_read] at he
  exact ⟨v', hu, he⟩

/-- The output of the fixed interpreter is the exact mathematical packed-source reader. -/
theorem ordered_read_parities {W n : ℕ} (s : Fin n → Fin W) (f : Fin W → Bool) :
    (List.ofFn s).map f = (Coordinates.read s f).map Packed.parity := by
  rw [Coordinates.read_parities, List.map_ofFn]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
