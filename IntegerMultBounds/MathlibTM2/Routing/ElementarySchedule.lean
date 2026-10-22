module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryXor
public import IntegerMultBounds.MathlibTM2.Routing.TerminalShears

/-!
# Elementary rank schedules implement complete directional shears

The schedule composes the concrete rank permutations of the executed elementary
primitive. A source outside the full target set remains valid in every pass.
This is its semantic composition, not yet a uniform metadata-loading loop.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {n : ℕ}

def coordinateXorStep (t s : Fin n) (R : ℕ) : Equiv.Perm (Fin (R * 2 ^ n)) :=
  if hne : s ≠ t then elementaryXorRank t s hne R else Equiv.refl _

def elementaryRankSchedule (R : ℕ) (source : Fin n → Fin n) :
    List (Fin n) → Equiv.Perm (Fin (R * 2 ^ n))
  | [] => Equiv.refl _
  | t :: ts => (elementaryRankSchedule R source ts).trans (coordinateXorStep t (source t) R)

theorem elementaryRankSchedule_bits (R : ℕ) (source : Fin n → Fin n)
    (ts : List (Fin n)) (hs : ∀ t ∈ ts, source t ≠ t) (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (elementaryRankSchedule R source ts i).val.testBit q.val) =
      elementaryShears source ts (fun q => i.val.testBit q.val) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := hs t (by simp)
    have htail := ih (fun t ht => hs t (by simp [ht]))
    funext q
    change (coordinateXorStep t (source t) R (elementaryRankSchedule R source ts i)).val.testBit q.val = _
    rw [coordinateXorStep, dite_eq_left ht, elementaryXorRank_bit]
    have hb (q : Fin n) := congrFun htail q
    simp only [elementaryShears, shear, toggle, Finset.mem_singleton]
    by_cases hq : q = t
    · subst q
      simp only [ite_true, hb]
    · simp only [ite_eq_right hq, hb]

/-- All terminal steps together give the exact simultaneous XOR, not merely
agreement on selected coordinates. -/
theorem elementaryRankSchedule_shear (R : ℕ) (targets : Finset (Fin n))
    (source : Fin n → Fin n) (hsource : ∀ i ∈ targets, source i ∉ targets)
    (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (elementaryRankSchedule R source targets.toList i).val.testBit q.val) =
      shear targets source (fun q => i.val.testBit q.val) := by
  rw [elementaryRankSchedule_bits]
  · exact elementaryShears_eq targets source hsource _
  · intro t ht he
    have ht' : t ∈ targets := by simpa using ht
    apply hsource t ht'
    rw [he]
    exact ht'

theorem elementaryXorRank_row (t s : Fin n) (hne : s ≠ t) (R : ℕ)
    (i : Fin (R * 2 ^ n)) :
    (elementaryXorRank t s hne R i).val / 2 ^ n = i.val / 2 ^ n := by
  let spec := elementarySwapSpec t
  change blockExchangeIdx spec.a spec.b spec.w
    (lowBitXor (spec.coordinate s).val (blockExchangeIdx spec.a spec.b spec.w i.val)) / 2 ^ n = _
  rw [blockExchangeIdx_div n spec.a spec.b spec.w spec.separate spec.fits,
    lowBitXor_div_pow _ _ n (by have := t.isLt; omega),
    blockExchangeIdx_div n spec.a spec.b spec.w spec.separate spec.fits]

/-- Arbitrary outer rows are spectators of the complete elementary schedule. -/
theorem elementaryRankSchedule_row (R : ℕ) (source : Fin n → Fin n)
    (ts : List (Fin n)) (i : Fin (R * 2 ^ n)) :
    (elementaryRankSchedule R source ts i).val / 2 ^ n = i.val / 2 ^ n := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (coordinateXorStep t (source t) R (elementaryRankSchedule R source ts i)).val / 2 ^ n = _
    unfold coordinateXorStep
    split_ifs with ht
    · rw [elementaryXorRank_row]
      exact ih
    · exact ih

end IntegerMultBounds.MathlibTM2.Routing
