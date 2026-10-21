module

public import IntegerMultBounds.Machine.CounterSteps
public import IntegerMultBounds.Machine.BinaryDescriptorAdvance

/-!
# Writing and advancing counters on any tape slot

`zeroProgram i` writes the counter `bits 0` on the blank tape `i` (`zero_hoare`).
`advProgram i c k` adds the runtime counter on tape `k` to the counter on tape `i`, with a blank
clock tape `c` (`adv_hoare`): `bits x` becomes `bits (x + y)` for `bits y` on `k`. Both change only
tape `i`. Erasing a counter is `BinaryDescriptorCleanupList.oneProgram`.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.CounterAdvance
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
noncomputable section
variable {t a : ℕ}

theorem advance_bits (x y : ℕ) : GrowingCounterData.advance y (bits x) = bits (x + y) :=
  BinaryCanonicalData.value_injective _ _
    (GrowingCounterData.advance_canonical y _ (FlatCoordinateSchedule.bits_canonical x))
    (FlatCoordinateSchedule.bits_canonical _)
    (by rw [GrowingCounterData.advance_value, FlatCoordinateSchedule.bits_value,
      FlatCoordinateSchedule.bits_value])

/-! ### Zero -/

def zeroProgram (i : Fin t) :=
  Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 0) (FiniteReturnStackAt.placement i)

theorem zero_hoare (i : Fin t) (v : Tapes t a) (hs : v.tape i = fun _ => blank) (hh : v.head i = 0) :
    HoareTime (zeroProgram (a := a) i) (fun w => w = v)
      (fun w => w = setTape v i (RadixZeroFill.encodedBinary (bits 0)) 1) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 0)
    (FiniteReturnStackAt.placement i) v (by rw [FiniteReturnStackAt.active_bank, hs, hh])
  apply h.consequence (fun _ h => h) ?_ (le_of_eq rfl)
  rintro w ⟨y, rfl, rfl⟩
  rw [FiniteReturnStackAt.replace_bank, CounterSteps.bits_eq,
    BinaryDescriptorStackRoundtrip.descriptor_encoded]

/-! ### Advance -/

/-- The three slots of the advance: the counter, the clock and the count. -/
def slots (i c k : Fin t) : Fin 3 → Fin t := ![i, c, k]

theorem slots_injective {i c k : Fin t} (hic : i ≠ c) (hik : i ≠ k) (hck : c ≠ k) :
    Function.Injective (slots i c k) := CounterSteps.slots_injective hic hik hck

theorem three_le {i c k : Fin t} (hic : i ≠ c) (hik : i ≠ k) (hck : c ≠ k) : 3 + (t - 3) = t :=
  CounterSteps.three_le hic hik hck

def advProgram (i c k : Fin t) (hic : i ≠ c) (hik : i ≠ k) (hck : c ≠ k) :=
  Placement.placed (BinaryDescriptorAdvance.program (q := a))
    (InjectivePlacement.placement (slots i c k) (slots_injective hic hik hck) (three_le hic hik hck))

theorem addCases_val {m n : ℕ} {α : Sort*} (f : Fin m → α) (g : Fin n → α) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => α) f g i =
      if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [j.isLt]
  · simp

theorem binary_encoded (xs : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) xs = RadixZeroFill.encodedBinary xs :=
  (CountedLoopReuseAlphabet.encoding_binary xs).symm

/-- Replacement through an injective placement: the selected tapes take the small bank, the
others keep the large one. -/
theorem replace_eq {s : ℕ} (sl : Fin s → Fin t) (hinj : Function.Injective sl) (hsize : s + (t - s) = t)
    (v u : Tapes t a) (w : Tapes s a)
    (hin : ∀ i, u.head (sl i) = w.head i ∧ u.tape (sl i) = w.tape i)
    (hout : ∀ j, (∀ i, sl i ≠ j) → u.head j = v.head j ∧ u.tape j = v.tape j) :
    Placement.replace (InjectivePlacement.placement sl hinj hsize) v w = u := by
  set e := InjectivePlacement.placement sl hinj hsize
  have hext (k : Fin (t - s)) : ∀ i, sl i ≠ e (Fin.natAdd s k) := by
    intro i he
    rw [← InjectivePlacement.active_slot sl hinj hsize i] at he
    have := congrArg Fin.val (e.injective he)
    simp at this
    omega
  apply congrArg₂ Tapes.mk <;> funext j <;> obtain ⟨x, rfl⟩ := e.surjective j <;>
    refine Fin.addCases (fun i => ?_) (fun k => ?_) x
  · change (Placement.combine e w (Placement.extra e v)).head _ = _
    rw [Placement.combine_head_active, InjectivePlacement.active_slot]
    exact (hin i).1.symm
  · change (Placement.combine e w (Placement.extra e v)).head _ = _
    rw [Placement.combine_head_extra]
    exact ((hout _ (hext k)).1).symm
  · change (Placement.combine e w (Placement.extra e v)).tape _ = _
    rw [Placement.combine_tape_active, InjectivePlacement.active_slot]
    exact (hin i).2.symm
  · change (Placement.combine e w (Placement.extra e v)).tape _ = _
    rw [Placement.combine_tape_extra]
    exact ((hout _ (hext k)).2).symm

theorem adv_hoare {i c k : Fin t} (hic : i ≠ c) (hik : i ≠ k) (hck : c ≠ k) (v : Tapes t a) (x y : ℕ)
    (hs : v.tape i = RadixZeroFill.encodedBinary (bits x)) (hh : v.head i = 1)
    (hc : v.tape c = fun _ => blank) (hch : v.head c = 0)
    (hk : v.tape k = RadixZeroFill.encodedBinary (bits y)) (hkh : v.head k = 1) :
    HoareTime (advProgram (a := a) i c k hic hik hck) (fun w => w = v)
      (fun w => w = setTape v i (RadixZeroFill.encodedBinary (bits (x + y))) 1)
      (10*y+2*(bits x).length+7*(bits y).length+28) := by
  have hd := BinaryDescriptorAdvance.advances_hoare (q := a) (bits x) (bits y) y
    (FlatCoordinateSchedule.bits_value y)
  have h := Placement.hoare_at hd
    (InjectivePlacement.placement (slots i c k) (slots_injective hic hik hck) (three_le hic hik hck))
    v (by
      rw [InjectivePlacement.active_bank]
      simp only [BinaryDescriptorAdvance.input, BinaryDescriptorAdvance.bank,
        CountedLoopReuseAlphabet.bank, CountedLoopReuseAlphabet.controls, BinaryDescriptorIncrement.bank]
      apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j
      · simp [slots, addCases_val, hh]
      · simp [slots, addCases_val, hch]
      · simp [slots, addCases_val, hkh]
      · simp [slots, addCases_val, hs, BinaryDescriptorStackRoundtrip.descriptor_encoded]
      · simp [slots, addCases_val, hc]
      · simp [slots, addCases_val, hk, binary_encoded])
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z, rfl, rfl⟩
  rw [advance_bits]
  apply replace_eq
  · intro j
    fin_cases j
    · simp [slots, setTape, BinaryDescriptorAdvance.input, BinaryDescriptorAdvance.bank,
        CountedLoopReuseAlphabet.bank, Tapes.append, addCases_val, BinaryDescriptorIncrement.bank,
        BinaryDescriptorStackRoundtrip.descriptor_encoded]
    · simp [slots, setTape, BinaryDescriptorAdvance.input, BinaryDescriptorAdvance.bank,
        CountedLoopReuseAlphabet.bank, CountedLoopReuseAlphabet.controls, Tapes.append, addCases_val,
        Function.update_of_ne (Ne.symm hic), hc, hch]
    · simp [slots, setTape, BinaryDescriptorAdvance.input, BinaryDescriptorAdvance.bank,
        CountedLoopReuseAlphabet.bank, CountedLoopReuseAlphabet.controls, Tapes.append, addCases_val,
        Function.update_of_ne (Ne.symm hik), hk, hkh, binary_encoded]
  · intro j hj
    have hj0 : j ≠ i := fun h => hj 0 (by simp [slots, h])
    simp [setTape, Function.update_of_ne hj0]

end
end IntegerMultBounds.Machine.CounterAdvance
