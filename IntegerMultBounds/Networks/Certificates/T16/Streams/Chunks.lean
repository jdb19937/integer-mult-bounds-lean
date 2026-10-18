module

/-! A list passes a Boolean test when every chunk of a fixed width does. The
stream checks are evaluated chunk by chunk so that no single kernel check holds
a whole replica. -/

@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

theorem all_of_chunks {α : Type} (p : α → Bool) (w : Nat) :
    ∀ (n : Nat) (l : List α), l.length ≤ w * n →
      (∀ k < n, ((l.drop (w * k)).take w).all p = true) → l.all p = true
  | 0, l, hl, _ => by
    cases l with
    | nil => rfl
    | cons _ _ => simp at hl
  | n + 1, l, hl, h => by
    rw [← List.take_append_drop w l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (Nat.succ_pos n), all_of_chunks p w n (l.drop w) ?_ fun k hk => ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      omega
    · rw [List.drop_drop, Nat.add_comm, ← Nat.mul_succ]
      exact h (k + 1) (by omega)

end IntegerMultBounds.Networks.Certificates.T16.Streams
