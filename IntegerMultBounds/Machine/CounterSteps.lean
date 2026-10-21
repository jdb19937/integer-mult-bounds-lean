module

public import IntegerMultBounds.Machine.BinaryDescriptorIncrement
public import IntegerMultBounds.Machine.BinaryDescriptorDifference
public import IntegerMultBounds.Machine.BinaryDescriptorInstall
public import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
public import IntegerMultBounds.Machine.FlatCoordinateSchedule

/-!
# Counter steps on any tape slot

A counter is a canonical descriptor `bits n` at head one. `incProgram i` adds one to the counter
on tape `i` in place (`inc_hoare`). `decProgram i o z` subtracts one, with two blank scratch
tapes `o` and `z`: it writes the constant one on `o`, the difference on `z`, moves it to `i`,
and erases the scratch (`dec_hoare`). Both change only the counter's tape, and both cost at most
linearly in the counter's value.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.CounterSteps
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
noncomputable section
variable {t a : ℕ}

theorem increment_advance (n : ℕ) (ts : List Bool) :
    GrowingCounterData.increment (GrowingCounterData.advance n ts) =
      GrowingCounterData.advance (n+1) ts := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih => exact ih (GrowingCounterData.increment ts)

theorem bits_succ (n : ℕ) : GrowingCounterData.increment (bits n) = bits (n+1) :=
  increment_advance n []

theorem bits_eq (n : ℕ) : RecursiveChildQuotientsConstant.bits n = bits n :=
  RecursiveChildQuotientsConstant.bits_eq_advance n

theorem bits_length (n : ℕ) : (bits n).length ≤ n + 1 := by
  have hw := GrowingCounterData.canonical_width _ (FlatCoordinateSchedule.bits_canonical n)
  have hl := Nat.log2_le_self n
  rw [FlatCoordinateSchedule.bits_value] at hw
  omega

/-! ### Increment -/

def incProgram (i : Fin t) :=
  Placement.placed (BinaryDescriptorIncrement.program (q := a)) (FiniteReturnStackAt.placement i)

theorem inc_hoare (i : Fin t) (v : Tapes t a) (n : ℕ)
    (hs : v.tape i = RadixZeroFill.encodedBinary (bits n)) (hh : v.head i = 1) :
    HoareTime (incProgram i) (fun w => w = v)
      (fun w => w = setTape v i (RadixZeroFill.encodedBinary (bits (n+1))) 1) (2*n+4) := by
  have h := Placement.hoare_at (BinaryDescriptorIncrement.increment_hoare (q := a) (bits n))
    (FiniteReturnStackAt.placement i) v (by
      rw [FiniteReturnStackAt.active_bank, hs, hh, ← BinaryDescriptorStackRoundtrip.descriptor_encoded]
      rfl)
  apply h.consequence (fun _ h => h) ?_ ?_
  · rintro w ⟨z, rfl, rfl⟩
    rw [show BinaryDescriptorIncrement.bank (q := a) (GrowingCounterData.increment (bits n)) =
      FiniteReturnStack.bank (BinaryDescriptorStack.descriptor (GrowingCounterData.increment (bits n))) 1
      from rfl, FiniteReturnStackAt.replace_bank, bits_succ, BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · have hc := (GrowingCounterData.carrySteps_bounds (bits n)).2
    have hl := bits_length n
    omega

/-! ### Decrement -/

/-- The three slots of the difference: the counter, the constant one and the result. -/
def slots (i o z : Fin t) : Fin 3 → Fin t := ![i, o, z]

theorem slots_injective {i o z : Fin t} (hio : i ≠ o) (hiz : i ≠ z) (hoz : o ≠ z) :
    Function.Injective (slots i o z) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> first | rfl | (simp only [slots] at h; simp at h; first
    | exact absurd h hio | exact absurd h.symm hio | exact absurd h hiz | exact absurd h.symm hiz
    | exact absurd h hoz | exact absurd h.symm hoz)

theorem three_le {i o z : Fin t} (hio : i ≠ o) (hiz : i ≠ z) (hoz : o ≠ z) : 3 + (t - 3) = t := by
  have h := Fintype.card_le_of_injective _ (slots_injective hio hiz hoz)
  simp only [Fintype.card_fin] at h
  omega

def decProgram (i o z : Fin t) (hio : i ≠ o) (hiz : i ≠ z) (hoz : o ≠ z) :=
  seq (seq (seq (seq (seq
    (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1) (FiniteReturnStackAt.placement o))
    (Placement.placed (BinaryDescriptorDifference.program (a := a))
      (InjectivePlacement.placement (slots i o z) (slots_injective hio hiz hoz) (three_le hio hiz hoz))))
    (BinaryDescriptorCleanupList.oneProgram (a := a) i))
    (BinaryDescriptorInstall.program a z i (Ne.symm hiz)))
    (BinaryDescriptorCleanupList.oneProgram (a := a) z))
    (BinaryDescriptorCleanupList.oneProgram (a := a) o)

private theorem binary_descriptor (xs : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) xs = BinaryDescriptorStack.descriptor xs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact (CountedLoopReuseAlphabet.encoding_binary xs).symm

/-- Replacing the three difference slots by a bank that agrees on the first two. -/
private theorem replace_slots {i o z : Fin t} (hio : i ≠ o) (hiz : i ≠ z) (hoz : o ≠ z)
    (v : Tapes t a) (w : Tapes 3 a) (h0 : w.head 0 = v.head i) (h0' : w.tape 0 = v.tape i)
    (h1 : w.head 1 = v.head o) (h1' : w.tape 1 = v.tape o) :
    Placement.replace (InjectivePlacement.placement (slots i o z) (slots_injective hio hiz hoz)
      (three_le hio hiz hoz)) v w = setTape v z (w.tape 2) (w.head 2) := by
  set e := InjectivePlacement.placement (slots i o z) (slots_injective hio hiz hoz) (three_le hio hiz hoz)
  have hslot (k : Fin 3) : e (Fin.castAdd (t-3) k) = slots i o z k := InjectivePlacement.active_slot _ _ _ k
  have hext (m : Fin (t-3)) (k : Fin 3) : e (Fin.natAdd 3 m) ≠ slots i o z k := by
    intro he
    rw [← hslot k] at he
    have := congrArg Fin.val (e.injective he)
    simp at this; omega
  apply congrArg₂ Tapes.mk <;> funext j <;> obtain ⟨j, rfl⟩ := e.surjective j <;>
    refine Fin.addCases (fun k => ?_) (fun m => ?_) j
  · change (Placement.combine e w (Placement.extra e v)).head _ = _
    rw [Placement.combine_head_active, hslot]
    fin_cases k
    · simp [slots, Function.update_of_ne hiz, h0]
    · simp [slots, Function.update_of_ne hoz, h1]
    · simp [slots]
  · change (Placement.combine e w (Placement.extra e v)).head _ = _
    rw [Placement.combine_head_extra]
    simp only [Placement.extra]
    rw [Function.update_of_ne (by simpa [slots] using hext m 2)]
  · change (Placement.combine e w (Placement.extra e v)).tape _ = _
    rw [Placement.combine_tape_active, hslot]
    fin_cases k
    · simp [slots, Function.update_of_ne hiz, h0']
    · simp [slots, Function.update_of_ne hoz, h1']
    · simp [slots]
  · change (Placement.combine e w (Placement.extra e v)).tape _ = _
    rw [Placement.combine_tape_extra]
    simp only [Placement.extra]
    rw [Function.update_of_ne (by simpa [slots] using hext m 2)]

theorem dec_hoare {i o z : Fin t} (hio : i ≠ o) (hiz : i ≠ z) (hoz : o ≠ z) (v : Tapes t a) (n : ℕ)
    (hn : 1 ≤ n) (hs : v.tape i = RadixZeroFill.encodedBinary (bits n)) (hh : v.head i = 1)
    (ho : v.tape o = fun _ => blank) (hoh : v.head o = 0)
    (hz : v.tape z = fun _ => blank) (hzh : v.head z = 0) :
    HoareTime (decProgram i o z hio hiz hoz) (fun w => w = v)
      (fun w => w = setTape v i (RadixZeroFill.encodedBinary (bits (n-1))) 1) (20*n+80) := by
  have hl := bits_length n
  have hl' := bits_length (n-1)
  have hl1 : (bits 1).length = 1 := rfl
  -- the constant one on `o`
  set v1 := setTape v o (BinaryDescriptorStack.descriptor (bits 1)) 1
  have s1 : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
      (FiniteReturnStackAt.placement o)) (fun w => w = v) (fun w => w = v1)
      (RecursiveChildQuotientsConstant.cost 1) := by
    have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
      (FiniteReturnStackAt.placement o) v (by rw [FiniteReturnStackAt.active_bank, ho, hoh])
    apply h.consequence (fun _ h => h) ?_ le_rfl
    rintro w ⟨y, rfl, rfl⟩
    rw [FiniteReturnStackAt.replace_bank, bits_eq]
  -- the difference on `z`
  set v2 := setTape v1 z (BinaryDescriptorStack.descriptor (bits (n-1))) 1
  have s2 : HoareTime (Placement.placed (BinaryDescriptorDifference.program (a := a))
      (InjectivePlacement.placement (slots i o z) (slots_injective hio hiz hoz) (three_le hio hiz hoz)))
      (fun w => w = v1) (fun w => w = v2) (6*max (bits n).length (bits 1).length+21) := by
    have hd := BinaryDescriptorDifference.difference_hoare (a := a) (bits n) (bits 1) (by simp; omega)
    simp only [FlatCoordinateSchedule.bits_value, bits_eq] at hd
    have h := Placement.hoare_at hd
      (InjectivePlacement.placement (slots i o z) (slots_injective hio hiz hoz) (three_le hio hiz hoz))
      v1 (by
      rw [InjectivePlacement.active_bank]
      simp only [BinaryDescriptorDifference.input, BinaryDescriptorDifference.bank]
      apply congrArg₂ Tapes.mk <;> funext k <;> fin_cases k
      · simp [slots, v1, setTape, Function.update_of_ne hio, hh]
      · simp [slots, v1, setTape]
      · simp [slots, v1, setTape, Function.update_of_ne (Ne.symm hoz), hzh]
      · simp [slots, v1, setTape, Function.update_of_ne hio, hs, binary_descriptor,
          BinaryDescriptorStackRoundtrip.descriptor_encoded]
      · simp [slots, v1, setTape, binary_descriptor]
      · simp [slots, v1, setTape, Function.update_of_ne (Ne.symm hoz), hz])
    apply h.consequence (fun _ h => h) ?_ le_rfl
    rintro w ⟨y, rfl, rfl⟩
    rw [replace_slots hio hiz hoz]
    · rfl
    · simp [BinaryDescriptorDifference.output, BinaryDescriptorDifference.bank, v1, setTape,
        Function.update_of_ne hio, hh]
    · simp [BinaryDescriptorDifference.output, BinaryDescriptorDifference.bank, v1, setTape,
        Function.update_of_ne hio, hs, binary_descriptor, BinaryDescriptorStackRoundtrip.descriptor_encoded]
    · simp [BinaryDescriptorDifference.output, BinaryDescriptorDifference.bank, v1, setTape]
    · simp [BinaryDescriptorDifference.output, BinaryDescriptorDifference.bank, v1, setTape,
        binary_descriptor]
  -- erase `i`
  set v3 := setTape v2 i (fun _ => blank) 0
  have s3 : HoareTime (BinaryDescriptorCleanupList.oneProgram (a := a) i) (fun w => w = v2)
      (fun w => w = v3) (2*(bits n).length+4) :=
    BinaryDescriptorCleanupList.one_hoare i v2 (bits n)
      (by simp [v2, v1, setTape, Function.update_of_ne hiz, Function.update_of_ne hio, hs,
        BinaryDescriptorStackRoundtrip.descriptor_encoded])
      (by simp [v2, v1, setTape, Function.update_of_ne hiz, Function.update_of_ne hio, hh])
  -- move the difference to `i`
  set v4 := setTape v3 i (RadixZeroFill.encodedBinary (bits (n-1))) 1
  have s4 : HoareTime (BinaryDescriptorInstall.program a z i (Ne.symm hiz)) (fun w => w = v3)
      (fun w => w = v4) (2*(bits (n-1)).length+5) :=
    BinaryDescriptorInstall.install_hoare z i (Ne.symm hiz) v3 (bits (n-1))
      (by simp [v3, v2, setTape, Function.update_of_ne (Ne.symm hiz),
        BinaryDescriptorStackRoundtrip.descriptor_encoded])
      (by simp [v3, v2, setTape, Function.update_of_ne (Ne.symm hiz)])
      (by simp [v3, setTape]) (by simp [v3, setTape])
  -- erase `z`, then `o`
  set v5 := setTape v4 z (fun _ => blank) 0
  have s5 : HoareTime (BinaryDescriptorCleanupList.oneProgram (a := a) z) (fun w => w = v4)
      (fun w => w = v5) (2*(bits (n-1)).length+4) :=
    BinaryDescriptorCleanupList.one_hoare z v4 (bits (n-1))
      (by simp [v4, v3, v2, setTape, Function.update_of_ne (Ne.symm hiz)])
      (by simp [v4, v3, v2, setTape, Function.update_of_ne (Ne.symm hiz)])
  set v6 := setTape v5 o (fun _ => blank) 0
  have s6 : HoareTime (BinaryDescriptorCleanupList.oneProgram (a := a) o) (fun w => w = v5)
      (fun w => w = v6) (2*(bits 1).length+4) :=
    BinaryDescriptorCleanupList.one_hoare o v5 (bits 1)
      (by simp [v5, v4, v3, v2, v1, setTape, Function.update_of_ne hoz, Function.update_of_ne (Ne.symm hio)])
      (by simp [v5, v4, v3, v2, v1, setTape, Function.update_of_ne hoz, Function.update_of_ne (Ne.symm hio)])
  have he : v6 = setTape v i (RadixZeroFill.encodedBinary (bits (n-1))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext j <;> simp only [v5, v4, v3, v2, v1, setTape] <;>
      by_cases hj : j = o <;> by_cases hj' : j = z <;> by_cases hj'' : j = i <;> subst_vars <;>
      simp_all
  have hc : RecursiveChildQuotientsConstant.cost 1 = 9 := rfl
  rw [he] at s6
  apply (((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).consequence (fun _ h => h) (fun _ h => h)
  rw [hc, hl1]
  have : max (bits n).length 1 ≤ n + 1 := max_le hl (by omega)
  omega

end
end IntegerMultBounds.Machine.CounterSteps
