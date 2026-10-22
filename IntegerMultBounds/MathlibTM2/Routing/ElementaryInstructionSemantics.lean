module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopFrame
public import IntegerMultBounds.MathlibTM2.Routing.RouterTerminal

/-!
# The executed instruction sequence realizes the terminal shear

Instructions appear in execution order. Their reversed target list is the
outer-to-inner order of the mathematical shear schedule. Only their coordinates
enter this identity; header generation and validity are separate requirements.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Node

private theorem elementaryShears_append {ι : Type*} [DecidableEq ι]
    (source : ι → ι) (a b : List ι) (x : ι → Bool) :
    elementaryShears source (a ++ b) x = elementaryShears source a (elementaryShears source b x) := by
  induction a with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.cons_append, elementaryShears, ih]

/-- The complete rank permutation agrees on all coordinates with its shear list. -/
theorem elementaryInstructionsRank_bits {n : ℕ} (rows : ℕ) (source : Fin n → Fin n)
    (ds : List (ElementaryInstruction n)) (hs : ∀ d ∈ ds, d.source = source d.target)
    (i : Fin (rows * 2 ^ n)) :
    (fun q : Fin n => (elementaryInstructionsRank rows ds i).val.testBit q.val) =
      elementaryShears source (ds.map ElementaryInstruction.target).reverse (fun q => i.val.testBit q.val) := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
    change (fun q : Fin n => (elementaryInstructionsRank rows ds (d.rank rows i)).val.testBit q.val) = _
    rw [ih (fun d hd => hs d (by simp [hd]))]
    have hd := hs d (by simp)
    have hstep : (fun q : Fin n => (d.rank rows i).val.testBit q.val) =
        shear {d.target} source (fun q => i.val.testBit q.val) := by
      funext q
      rw [ElementaryInstruction.rank, elementaryXorRank_bit]
      simp only [shear, toggle, Finset.mem_singleton]
      by_cases hq : q = d.target
      · subst q
        simp only [ite_true, hd]
      · simp only [ite_eq_right hq]
    rw [hstep]
    simp only [List.map_cons, List.reverse_cons, elementaryShears_append,
      elementaryShears]

/-- A sequence covering each target once implements the entire simultaneous shear. -/
theorem elementaryInstructionsRank_shear {n : ℕ} (rows : ℕ) (targets : Finset (Fin n))
    (source : Fin n → Fin n) (hsource : ∀ i ∈ targets, source i ∉ targets)
    (ds : List (ElementaryInstruction n)) (hs : ∀ d ∈ ds, d.source = source d.target)
    (htargets : (ds.map ElementaryInstruction.target).reverse = targets.toList)
    (i : Fin (rows * 2 ^ n)) :
    (fun q : Fin n => (elementaryInstructionsRank rows ds i).val.testBit q.val) =
      shear targets source (fun q => i.val.testBit q.val) := by
  rw [elementaryInstructionsRank_bits rows source ds hs, htargets,
    elementaryShears_eq targets source hsource]

/-- The instruction count inherits the shared geometry's logarithmic suffix bound. -/
theorem routerTerminalInstruction_count (n G : ℕ) (hG : 0 < G) (hn : 64 * G ≤ n)
    (targets : Finset (Fin (routerTargetWidth n (64 * G) G)))
    (ds : List (ElementaryInstruction (routerTargetWidth n (64 * G) G)))
    (htargets : (ds.map ElementaryInstruction.target).reverse =
      (routerTerminalTargets n (64 * G) G targets).toList) : ds.length < 131 * G := by
  have hl := congrArg List.length htargets
  simp only [List.length_reverse, List.length_map, Finset.length_toList] at hl
  rw [hl]
  exact routerTerminalTargets_spacing n G targets hG hn

end IntegerMultBounds.MathlibTM2.Routing
