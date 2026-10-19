module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Model

@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

/-- Whether a binary trie contains the requested wire. -/
def Labels.contains : Labels → ℕ → Bool
  | .leaf _, i => i == 0
  | .fork even odd, i =>
      if i % 2 = 0 then even.contains (i / 2) else odd.contains (i / 2)

/-- Label assignments preserve the register domain. -/
theorem Labels.contains_put (labels : Labels) (i j f : ℕ) :
    (labels.put j f).contains i = labels.contains i := by
  induction labels generalizing i j with
  | leaf old => simp [Labels.put, Labels.contains]
  | fork even odd ihe iho =>
    by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0 <;>
      simp_all [Labels.put, Labels.contains]

/-- Label assignment changes precisely the addressed leaf. -/
theorem Labels.get_put_self (labels : Labels) (i f : ℕ)
    (h : labels.contains i = true) : (labels.put i f).get i = f := by
  induction labels generalizing i with
  | leaf old =>
    have hi : i = 0 := by simpa [Labels.contains] using h
    simp [Labels.put, Labels.get, hi]
  | fork even odd ihe iho =>
    by_cases hi : i % 2 = 0
    · simpa [Labels.put, Labels.get, hi] using
        ihe _ (by simpa [Labels.contains, hi] using h)
    · simpa [Labels.put, Labels.get, hi] using
        iho _ (by simpa [Labels.contains, hi] using h)

/-- All other wire labels survive an assignment. -/
theorem Labels.get_put_other (labels : Labels) (i j f : ℕ) (h : i ≠ j) :
    (labels.put j f).get i = labels.get i := by
  induction labels generalizing i j with
  | leaf old =>
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp_all [Labels.put, Labels.get]
  | fork even odd ihe iho =>
    by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0
    · simpa [Labels.put, Labels.get, hi, hj] using ihe (i / 2) (j / 2) (by omega)
    · simp [Labels.put, Labels.get, hi, hj]
    · simp [Labels.put, Labels.get, hi, hj]
    · simpa [Labels.put, Labels.get, hi, hj] using iho (i / 2) (j / 2) (by omega)

/-- A bounded register check split into shallow blocks for kernel reduction. -/
def checkRegisters (bound : ℕ) (p : ℕ → Bool) : Bool :=
  (List.range ((bound + 31) / 32)).all fun block =>
    (List.range 32).all fun offset =>
      let i := 32 * block + offset
      if i < bound then p i else true

theorem checkRegisters_sound {bound : ℕ} {p : ℕ → Bool}
    (h : checkRegisters bound p = true) (i : ℕ) (hi : i < bound) : p i = true := by
  have hb : i / 32 < (bound + 31) / 32 := by omega
  have hj : i % 32 < 32 := Nat.mod_lt _ (by decide)
  have hblock := List.all_eq_true.mp h (i / 32) (List.mem_range.mpr hb)
  have hentry := List.all_eq_true.mp hblock (i % 32) (List.mem_range.mpr hj)
  have he : 32 * (i / 32) + i % 32 = i := by omega
  simpa [he, hi] using hentry

end IntegerMultBounds.Networks.Certificates.T16.Trace
