module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBAll
import IntegerMultBounds.MathlibTM2.Mult.BandSpec
public import IntegerMultBounds.Resampling.WeightTable
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-!
# Box streams of the pipeline

`rsbLineBData`: the per-axis data (source length, target width, weight tables, interchange
headers) of the `B̃₀` driver at the pipeline sizes. `rsb_mem_rsbBox`, `rsb_mem_rsbAxisL`,
`rsb_flat_mem`: the entries of box streams and of their images under line maps.

The Neumann pipeline instance (`lineBN`, `rsb_lineB_runs`) was removed with the Neumann `B̃₀`;
restore from `1cb2723b`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

/-- The axis data of `lineB n` on axis `i`: source length `s n i`, target width `Lb i`, the
weight tables `tableE`, `tableD`, the interchange headers `hs i`. -/
def rsbLineBData (n : ℕ) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) (i : Fin (Mult.Sizes.d n)) : RsbAxisData :=
  ⟨Mult.Sizes.s n i, Lb i,
    Resampling.WeightTable.tableE (Mult.Sizes.s n i) (Mult.Sizes.t n i) (Mult.Sizes.alpha n)
      (Mult.Sizes.p n),
    Resampling.WeightTable.tableD (Mult.Sizes.s n i) (Mult.Sizes.t n i) (Mult.Sizes.alpha n)
      (Mult.Sizes.p n), hs i⟩

instance rsbLineBData_neZero (n : ℕ) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) (i : Fin (Mult.Sizes.d n)) :
    NeZero (rsbLineBData n Lb hs i).s :=
  Mult.Pipeline.neZero_s n i


/-! ### Entries of box streams -/

section Entries

lemma rsb_mem_rsbBox {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ) (F : ((i : Fin d) → Fin (t i)) → α)
    {y : α}, y ∈ rsbBox d t F → ∃ a, F a = y
  | 0, _, F, y, hy => by
      simp only [rsbBox, List.mem_singleton] at hy
      exact ⟨_, hy.symm⟩
  | d + 1, t, F, y, hy => by
      simp only [rsbBox, List.mem_flatMap, List.mem_finRange, true_and] at hy
      obtain ⟨x₀, hx₀⟩ := hy
      obtain ⟨a, ha⟩ := rsb_mem_rsbBox d _ _ hx₀
      exact ⟨_, ha⟩

lemma rsb_mem_rsbLineAt {H Q : ℕ} {L : List GaussianInt} {p q : ℕ} {y : GaussianInt}
    (hy : y ∈ rsbLineAt H Q L p q) : y = 0 ∨ y ∈ L := by
  simp only [rsbLineAt, List.mem_map, List.mem_range] at hy
  obtain ⟨h, -, rfl⟩ := hy
  rw [List.getD_eq_getElem?_getD]
  cases hh : L[(p * H + h) * Q + q]? with
  | none => left; rfl
  | some a => right; exact List.mem_of_getElem? hh

lemma rsb_mem_getD {L : List GaussianInt} {k : ℕ} : L.getD k 0 = 0 ∨ L.getD k 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD]
  cases hh : L[k]? with
  | none => left; rfl
  | some a => right; exact List.mem_of_getElem? hh

/-- An entry of a line map is an entry of the image of a line, or zero. -/
lemma rsb_mem_rsbAxisL {P H Q : ℕ} {g : List GaussianInt → List GaussianInt}
    {l : List GaussianInt} {x : GaussianInt} (hx : x ∈ rsbAxisL P H Q g l) :
    x = 0 ∨ ∃ L', L'.length = H ∧ (∀ y ∈ L', y = 0 ∨ y ∈ l) ∧ x ∈ g L' := by
  simp only [rsbAxisL, rsbChunkMap, rsbChunks, List.mem_flatMap, List.mem_map,
    List.mem_range] at hx
  obtain ⟨b, ⟨c, -, rfl⟩, hxb⟩ := hx
  simp only [rsbBlockOp, List.mem_map, List.mem_range] at hxb
  obtain ⟨z, -, rfl⟩ := hxb
  rcases rsb_mem_getD (L := g ((List.range H).map fun h =>
      ((l.drop (c * (H * Q))).take (H * Q)).getD (h * Q + z % Q) 0)) (k := z / Q) with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ⟨_, by simp, fun y hy => ?_, h1⟩
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨h, -, rfl⟩ := hy
    rcases rsb_mem_getD (L := (l.drop (c * (H * Q))).take (H * Q)) (k := h * Q + z % Q) with
      e | e
    · exact Or.inl e
    · exact Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take e))

/-- A property of the entries kept by every line map is kept along all axes. -/
lemma rsb_flat_mem {d : ℕ} (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (P : GaussianInt → Prop) (h0 : P 0)
    (hg : ∀ i L, L.length = t i → (∀ y ∈ L, P y) → ∀ x ∈ g i L, P x)
    (l : List GaussianInt) (hl : ∀ x ∈ l, P x) : ∀ k, ∀ x ∈ rsbFlat d t g k l, P x := by
  intro k
  rw [rsbFlat]
  induction ((List.finRange d).drop k) with
  | nil => exact hl
  | cons j js ih =>
      intro x hx
      rw [List.foldr_cons, rsbAxisOp] at hx
      rcases rsb_mem_rsbAxisL hx with e | ⟨L', hL', hy, hx'⟩
      · rw [e]; exact h0
      · exact hg j L' hL' (fun y hyL => (hy y hyL).elim (fun e => e ▸ h0) (ih y)) x hx'

end Entries


end

end IntegerMultBounds.MathlibTM2.Fast
