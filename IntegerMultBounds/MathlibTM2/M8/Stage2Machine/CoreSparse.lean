module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBody
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding

/-!
# The core's own bank as fifteen descriptors

With a blank payload, node tape and stacks, the core's own bank (`CoreShared.privateBank`) holds
exactly fifteen descriptors and is blank elsewhere (`private_sparse`): the six headers of the view,
the memo of its width, and the eight counters of `Prepare.rest w 529` that are present. So the
padded core's own bank is the sparse bank of the four padding headers and these fifteen words
(`padded_sparse`), which stage 1's sparse copies fill and erase.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSparse

noncomputable section
open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.CounterDimensions (descriptorHead descriptorTape)
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open FixedHeaderSparseBankCopy (headerBank headerBank_eq headerBank_target headerBank_blank)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersCore (blankTape emptyOne emptyTwo)
open RevMachine

/-! ### On the common bank -/

variable {t : ℕ}

/-- The fifteen present descriptors of the common bank. -/
def slots₀ : Fin 15 → Fin (CommonBank.count t) :=
  ![CommonBank.headerSlot 0, CommonBank.headerSlot 1, CommonBank.headerSlot 2, CommonBank.headerSlot 3,
    CommonBank.headerSlot 4, CommonBank.headerSlot 5, Place.scalarSlot, CommonBank.auxSlot 0,
    CommonBank.auxSlot 1, CommonBank.auxSlot 2, CommonBank.auxSlot 3, CommonBank.auxSlot 4,
    CommonBank.auxSlot 7, CommonBank.auxSlot 10, CommonBank.auxSlot 15]

/-- Their offsets past the role tapes. -/
def offset : Fin 15 → ℕ := ![1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 15, 16, 19, 22, 27]

theorem slots₀_val (i : Fin 15) : (slots₀ (t := t) i).val = t + offset i := by
  fin_cases i <;> simp [slots₀, offset, CommonBank.headerSlot_val, CommonBank.auxSlot_val, Place.scalarSlot_val,
    CommonBank.K]

theorem offset_injective : Function.Injective offset := by decide

theorem slots₀_injective : Function.Injective (slots₀ (t := t)) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [slots₀_val, slots₀_val] at hv
  exact offset_injective (by omega)

/-- The fifteen words: the headers of `v`, its width and the present counters. -/
def words (w : ℕ) (v : Descriptor) : Fin 15 → List Bool :=
  ![Routines.hdr v 0, Routines.hdr v 1, Routines.hdr v 2, Routines.hdr v 3, Routines.hdr v 4, Routines.hdr v 5,
    bits v.width, bits w, bits 0, bits 0, bits 0, bits 0, bits 0, bits 529, bits 1]

theorem childRoles_blank : NodePark.childRoles rev97m blankTape = SharedBank.empty (NodeBank.tapes rev97m) prime := by
  unfold NodePark.childRoles
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [SharedPlacementAlphabet.setTape, SharedBank.empty, Function.update_apply]

/-- **The common bank of the core** holds the fifteen descriptors. -/
theorem common_sparse (w : ℕ) (v : Descriptor) :
    CommonBank.bank (NodePark.childRoles rev97m blankTape) (Routines.hdr v) blankTape 0 emptyOne
        (Place.memo v.width) (Prepare.rest w 529) emptyTwo =
      headerBank (a := prime) slots₀ (words w v) := by
  apply headerBank_eq _ slots₀_injective
  · intro i
    fin_cases i <;>
      simp [slots₀, words, CommonBank.bank_header, CommonBank.bank_aux, Place.bank_memo, Prepare.rest,
        CommonBank.word, descriptorHead, descriptorTape]
  · intro j hj
    rw [childRoles_blank]
    revert hj
    simp only [CommonBank.bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common]
    induction j using Fin.addCases with
    | left j => intro _; simp [Tapes.append, SharedBank.empty]
    | right j =>
      induction j using Fin.addCases with
      | left j =>
        change Fin (1+6) at j
        induction j using Fin.addCases with
        | left j => intro _; simp [Tapes.append, SharedBank.empty]
        | right j =>
          intro hj
          fin_cases j
          · exact absurd rfl (hj 0)
          · exact absurd rfl (hj 1)
          · exact absurd rfl (hj 2)
          · exact absurd rfl (hj 3)
          · exact absurd rfl (hj 4)
          · exact absurd rfl (hj 5)
      | right j =>
        induction j using Fin.addCases with
        | left j =>
          induction j using Fin.addCases with
          | left j =>
            intro _
            fin_cases j <;> simp [Tapes.append, RecursiveCallBank.work]
          | right j =>
            induction j using Fin.addCases with
            | left j => intro _; fin_cases j; simp [Tapes.append, SharedBank.empty]
            | right j =>
              induction j using Fin.addCases with
              | left j => intro hj; fin_cases j; exact absurd rfl (hj 6)
              | right j =>
                intro hj
                have h := CommonBank.bank_aux (SharedBank.empty (NodeBank.tapes rev97m) prime) (Routines.hdr v)
                  blankTape 0 emptyOne (Place.memo v.width) (Prepare.rest w 529) emptyTwo j
                have hn : CommonBank.word (Prepare.rest w 529 j) = none := by
                  fin_cases j
                  all_goals first
                    | exact absurd rfl (hj 7) | exact absurd rfl (hj 8) | exact absurd rfl (hj 9)
                    | exact absurd rfl (hj 10) | exact absurd rfl (hj 11) | exact absurd rfl (hj 12)
                    | exact absurd rfl (hj 13) | exact absurd rfl (hj 14) | rfl
                rw [hn] at h
                exact h
        | right j => intro _; fin_cases j <;> simp [Tapes.append, SharedBank.empty]

/-! ### Padding to more tapes -/

theorem raw_sparse {n u T : ℕ} (d : Fin n → Fin u) (hd : Function.Injective d) (bs : Fin n → List Bool)
    (h : u ≤ T) :
    raw (headerBank (a := prime) d bs) T = headerBank (fun i => Fin.castLE h (d i)) bs := by
  apply headerBank_eq _ (fun i j hij => hd (Fin.castLE_injective h hij))
  · intro i
    have hl : (Fin.castLE h (d i)).val < u := (d i).isLt
    have := headerBank_target (a := prime) d hd bs i
    simp only [raw, hl, dite_true]
    exact this
  · intro j hj
    by_cases hl : j.val < u
    · simp only [raw, hl, dite_true]
      exact headerBank_blank d bs ⟨j.val, hl⟩ fun i hi => hj i (Fin.ext (by rw [Fin.val_castLE, hi]))
    · simp [raw, hl]

/-! ### The core's own bank -/

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

theorem count_le : CommonBank.count (NodeBank.tapes rev97m) ≤ Assembly.tW capacity :=
  (Assembly.count_le capacity).trans (Assembly.tF_le capacity)

/-- The fifteen descriptors among the core's tapes. -/
def slots : Fin 15 → Fin (Assembly.tW capacity) := fun i => Fin.castLE (count_le capacity) (slots₀ i)

theorem slots_injective : Function.Injective (slots capacity) :=
  fun _ _ h => slots₀_injective (Fin.castLE_injective _ h)

/-- **The core's own bank** holds the fifteen descriptors. -/
theorem private_sparse (w : ℕ) (v : Descriptor) :
    CoreShared.privateBank capacity blankTape 0 emptyOne emptyTwo w v = headerBank (slots capacity) (words w v) := by
  unfold CoreShared.privateBank CoreShared.bankWith
  rw [common_sparse]
  exact raw_sparse _ slots₀_injective _ _

/-- The padded core's slots: the padding headers, then the core's. -/
def paddedSlots : Fin (4+15) → Fin (HighBody.padCount capacity) :=
  ArbitraryWidthExecutionPrivateHeadersAppend.slots M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding.rowSlots
    (slots capacity)

theorem paddedSlots_injective : Function.Injective (paddedSlots capacity) :=
  ArbitraryWidthExecutionPrivateHeadersAppend.slots_injective _ _
    M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding.row_injective (slots_injective capacity)

/-- The padded core's words. -/
def paddedWords (ph : Fin 4 → List Bool) (w : ℕ) (u : Descriptor) : Fin (4+15) → List Bool :=
  Fin.addCases ph (words w u)

/-- **The padded core's own bank** is sparse. -/
theorem padded_sparse (K : ℕ) (ph : Fin 4 → List Bool) (u : Descriptor) :
    HighBody.privateBank capacity K ph u blankTape 0 emptyOne emptyTwo =
      headerBank (paddedSlots capacity) (paddedWords ph (Assembly.wOf K u) u) := by
  unfold HighBody.privateBank HighBody.bankWith HighBody.corePrivate
  rw [M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding.row_sparse, private_sparse]
  exact ArbitraryWidthExecutionPrivateHeadersAppend.append _ _
    M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding.row_injective (slots_injective capacity) _ _

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSparse
