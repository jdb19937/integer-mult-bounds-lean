module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryXor

/-! Arithmetic identities needed by the live elementary coordinate compiler. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

/-- Away from the target, swapping zero with the target changes only source zero. -/
theorem elementarySwap_source {n : ℕ} (target source : Fin n) (hne : source ≠ target) :
    ((elementarySwapSpec target).coordinate source).val =
      if source.val = 0 then target.val else source.val := by
  have hs : source.val ≠ target.val := fun he => hne (Fin.ext he)
  change blockExchange 0 target.val (if target.val = 0 then 0 else 1) source.val = _
  unfold blockExchange
  split_ifs <;> omega

/-- Nonemptiness of the live unary source determines the renamed coordinate. -/
theorem elementarySwap_source_gate {n : ℕ} {α : Type*} (target source : Fin n)
    (hne : source ≠ target) (word : List α) (hword : word.length = source.val) :
    (if word.head?.isSome then source.val else target.val) =
      ((elementarySwapSpec target).coordinate source).val := by
  rw [elementarySwap_source target source hne]
  cases word with
  | nil => simp only [List.length_nil] at hword; simp [← hword]
  | cons x xs =>
    have hs : source.val ≠ 0 := by simp only [List.length_cons] at hword; omega
    simp [hs]

end IntegerMultBounds.MathlibTM2.Routing
