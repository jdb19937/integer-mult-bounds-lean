module

public import IntegerMultBounds.Compact.ActiveTargetSubsegmentValue

/-! Literal selected-bit mask on a contiguous active target, with the omitted
highest operation separated onto the first bit of the retained high field. -/

@[expose] public section

namespace IntegerMultBounds.Compact.ActiveTargetSubsegmentWords
noncomputable section
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine
open PowerTwo

def ideal (q : ℕ) (lo V hi Z : List Bool) := lo++CountedIdealToggle.word q V Z++hi

theorem width (q rho : ℕ) (lo V hi Z : List Bool) (hq : 1≤q)
    (hlo : lo.length=rho) (hV : V.length=Z.length*q) (hhi : hi.length=q-rho) (hr : rho≤q) :
    (ideal q lo V hi Z).length=(Z.length+1)*q := by
  simp only [ideal,List.length_append,CountedIdealToggle.word_length q V Z hq hV,hlo,hV,hhi]
  rw [Nat.add_mul]
  omega

theorem spectators (q : ℕ) (lo V hi Z : List Bool) (hq : 1≤q) (hV : V.length=Z.length*q) :
    (ideal q lo V hi Z).take lo.length=lo ∧
    (ideal q lo V hi Z).drop (lo.length+V.length)=hi := by
  unfold ideal
  constructor
  · simp
  · rw [List.drop_append,List.drop_append]
    rw [List.drop_eq_nil_of_le (by omega : lo.length ≤ lo.length+V.length)]
    have hw := CountedIdealToggle.word_length q V Z hq hV
    rw [← hw]
    simp

theorem xor_zero (xs : List Bool) : List.zipWith xor xs (List.replicate xs.length false)=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.replicate_succ,ih]

/-- The omitted highest selected operation changes only the first bit of hi. -/
def highest (z : Bool) : List Bool → List Bool
  | [] => []
  | a::hi => xor a z::hi

theorem highest_xor (z a : Bool) (hi : List Bool) :
    List.zipWith xor (a::hi) (z::List.replicate hi.length false)=highest z (a::hi) := by
  simp only [List.zipWith_cons_cons,highest,xor_zero]

/-- All n+1 selected positions have now been supplied: rho low zeros, n
stride-q controls, then the highest control and the remaining high zeros. -/
theorem full_selected (q : ℕ) (lo V hi Z : List Bool) (z a : Bool)
    (hq : 1≤q) (hV : V.length=Z.length*q) :
    List.zipWith xor (lo++V++(a::hi))
      (List.replicate lo.length false++toggleMask q Z++(z::List.replicate hi.length false))=
      ideal q lo V (highest z (a::hi)) Z := by
  rw [List.zipWith_append (by simp only [List.length_append,List.length_replicate,toggleMask_length q hq,hV]),
    List.zipWith_append (by simp only [List.length_replicate]),xor_zero,highest_xor]
  rfl

end
end IntegerMultBounds.Compact.ActiveTargetSubsegmentWords
