module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy

/-! A canonical binary header is determined uniquely by its numeric value.
This identifies executed normalization with the exact header lists used by R2. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem canonical_tail (b : Bool) (bs : List Bool) (hc : GrowingCounterData.Canonical (b :: bs)) :
    GrowingCounterData.Canonical bs := by
  cases bs with
  | nil => exact Or.inl rfl
  | cons c cs =>
    apply Or.inr
    rcases hc with hn | hl
    · simp at hn
    · simpa only [List.getLast?_cons_cons] using hl

theorem canonical_value_zero (bs : List Bool) (hc : GrowingCounterData.Canonical bs)
    (hv : Counter.value bs = 0) : bs = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have ht := canonical_tail b bs hc
    have hz : Counter.value bs = 0 := by cases b <;> simp [Counter.value] at hv; omega
    have he := ih ht hz
    subst bs
    cases b <;> simp [GrowingCounterData.Canonical, Counter.value] at hc hv

theorem canonical_value_injective (xs ys : List Bool)
    (hx : GrowingCounterData.Canonical xs) (hy : GrowingCounterData.Canonical ys)
    (hv : Counter.value xs = Counter.value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact (canonical_value_zero ys hy hv.symm).symm
  | cons b xs ih =>
    cases ys with
    | nil => exact canonical_value_zero (b :: xs) hx hv
    | cons c ys =>
      have hb : b = c := by cases b <;> cases c <;> simp [Counter.value] at hv ⊢ <;> omega
      subst c
      have ht : Counter.value xs = Counter.value ys := by cases b <;> simp [Counter.value] at hv <;> omega
      exact congrArg (List.cons b) (ih ys (canonical_tail b xs hx) (canonical_tail b ys hy) ht)

theorem canonical_eq_advance (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    bs = GrowingCounterData.advance (Counter.value bs) [] := by
  apply canonical_value_injective bs _ hc (GrowingCounterData.advance_canonical _ [] (Or.inl rfl))
  simp [GrowingCounterData.advance_value, Counter.value]

theorem canonicalHeader_length_le (L x : ℕ) (hx : x < 2 ^ L) :
    (GrowingCounterData.advance x []).length ≤ L := by
  obtain ⟨cs, k, he, hc⟩ := binaryCanonical_split (binBits L x)
  have hv : Counter.value cs = x := by
    have h := binaryCanonical_value_binBits L x hx
    rw [he, binaryCanonical_value_padding] at h
    exact h
  have hl := congrArg List.length he
  have hs : cs = GrowingCounterData.advance x [] := by
    simpa only [hv] using canonical_eq_advance cs hc
  rw [hs] at hl
  simp only [length_binBits, List.length_append, List.length_replicate] at hl
  omega

theorem binaryCanonicalHeaderCopy_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src dst tmp work : Fin T)
    (hregs : [src, dst, tmp, work].Nodup) (L x : ℕ) (hx : x < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L x)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCanonicalCopyProgram src dst tmp work) (mk v S) (10 * L + 12)
        (mk v' { S with R := Function.update S.R dst ((GrowingCounterData.advance x []).map bitSymbol) }) := by
  obtain ⟨bs, v', hc, hv, _, hu, he⟩ := binaryCanonicalCopy_exec body src dst tmp work hregs L x hx v S hsrc hdst htmp hwork
  have hb : bs = GrowingCounterData.advance x [] := by simpa only [hv] using canonical_eq_advance bs hc
  rw [hb] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
