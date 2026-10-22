module

public import IntegerMultBounds.GrowingCounterData
public import IntegerMultBounds.MathlibTM2.Host.Index

/-! Every padded binary word consists of a canonical prefix and high zeros. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host

theorem binaryCanonical_split (bs : List Bool) :
    ∃ (cs : List Bool) (k : ℕ), bs = cs ++ List.replicate k false ∧
      GrowingCounterData.Canonical cs := by
  induction bs with
  | nil => exact ⟨[], 0, rfl, Or.inl rfl⟩
  | cons b bs ih =>
    obtain ⟨cs, k, he, hc⟩ := ih
    cases cs with
    | nil =>
      cases b with
      | false =>
        refine ⟨[], k + 1, ?_, Or.inl rfl⟩
        simp [he, List.replicate_succ]
      | true =>
        exact ⟨[true], k, by simp [he], Or.inr rfl⟩
    | cons c cs =>
      refine ⟨b :: c :: cs, k, by simp [he], Or.inr ?_⟩
      have hl := hc.resolve_left (by simp)
      simpa only [List.getLast?_cons_cons] using hl

theorem binaryCanonical_value_padding (bs : List Bool) (k : ℕ) :
    Counter.value (bs ++ List.replicate k false) = Counter.value bs := by
  have hz : Counter.value (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, Counter.value, ih]
  induction bs with
  | nil => exact hz
  | cons b bs ih => simp [Counter.value, ih]

/-- Padded host arithmetic values agree with the counter values of raw headers. -/
theorem binaryCanonical_value_binBits (L x : ℕ) (hx : x < 2 ^ L) :
    Counter.value (binBits L x) = x := by
  induction L generalizing x with
  | zero =>
    have hz : x = 0 := by simpa using hx
    subst x
    rfl
  | succ L ih =>
    have hdiv : x / 2 < 2 ^ L := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [pow_succ, Nat.mul_comm] using hx
    rw [binBits_succ, Counter.value, ih (x / 2) hdiv]
    have hbit : (if x.testBit 0 then 1 else 0) = x % 2 := by
      simp only [Nat.testBit_zero, decide_eq_true_eq]
      split <;> omega
    rw [hbit]
    omega

end IntegerMultBounds.MathlibTM2.Routing
