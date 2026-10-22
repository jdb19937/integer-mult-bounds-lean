module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleLayout

/-! One finite bank for placement and exact repair. Only the record stream is
shared; every other placement tape lies beyond the complete R2 bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable abbrev sharedScheduleT (N t₀ : ℕ) : ℕ := N + (swapT t₀ + 34)

noncomputable def sharedCoreEmbed {N t₀ : ℕ} (i : Fin N) : Fin (sharedScheduleT N t₀) :=
  ⟨i.val, by have := i.isLt; unfold sharedScheduleT; omega⟩

theorem sharedCoreEmbed_injective {N t₀ : ℕ} :
    Function.Injective (sharedCoreEmbed (N := N) (t₀ := t₀)) := by
  intro i j h
  have hv : i.val = j.val := congrArg (fun x : Fin (sharedScheduleT N t₀) => x.val) h
  exact Fin.ext hv

noncomputable def sharedScheduleSlot {N t₀ : ℕ} (src : Fin N) (r : BinaryScheduleReg t₀ 3) : Fin (sharedScheduleT N t₀) :=
  if r = .str then sharedCoreEmbed src
  else ⟨N + (binaryScheduleSlot r).val, by
    have h := (binaryScheduleSlot r).isLt
    unfold sharedScheduleT
    omega⟩

@[simp] theorem sharedScheduleSlot_str {N t₀ : ℕ} (src : Fin N) :
    sharedScheduleSlot (t₀ := t₀) src .str = sharedCoreEmbed src := by
  simp [sharedScheduleSlot]

theorem sharedScheduleSlot_separate {N t₀ : ℕ} (src : Fin N) (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin N) : sharedScheduleSlot src r ≠ sharedCoreEmbed i := by
  intro he
  have hv := congrArg (fun x : Fin (sharedScheduleT N t₀) => x.val) he
  simp only [sharedScheduleSlot, ite_eq_right hr, sharedCoreEmbed] at hv
  have := i.isLt
  omega

theorem sharedScheduleSlot_injective {N t₀ : ℕ} (src : Fin N) :
    Function.Injective (sharedScheduleSlot (t₀ := t₀) src) := by
  intro r s h
  by_cases hr : r = .str
  · subst r
    by_cases hs : s = .str
    · exact hs.symm
    · exact (sharedScheduleSlot_separate src s hs src (by simpa using h.symm)).elim
  · by_cases hs : s = .str
    · subst s
      exact (sharedScheduleSlot_separate src r hr src (by simpa using h)).elim
    · apply binaryScheduleSlot_injective
      apply Fin.ext
      have hv := congrArg (fun x : Fin (sharedScheduleT N t₀) => x.val) h
      simp only [sharedScheduleSlot, ite_eq_right hr, ite_eq_right hs] at hv
      omega

/-- Every R2 register other than its stream is untouched by placement metadata. -/
theorem sharedCoreEmbed_separate {N t₀ : ℕ} (src : Fin N) (i : Fin N) (hi : i ≠ src)
    (r : BinaryScheduleReg t₀ 3) : sharedCoreEmbed i ≠ sharedScheduleSlot src r := by
  by_cases hr : r = .str
  · subst r
    rw [sharedScheduleSlot_str]
    exact (sharedCoreEmbed_injective (t₀ := t₀)).ne hi
  · exact (sharedScheduleSlot_separate src r hr i).symm

end IntegerMultBounds.MathlibTM2.Routing
