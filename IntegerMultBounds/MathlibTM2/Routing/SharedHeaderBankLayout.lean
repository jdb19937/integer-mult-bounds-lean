module

public import IntegerMultBounds.MathlibTM2.Routing.SharedHeaderRoles

/-! A concrete shared header workspace extends any suitable core by fifteen
tapes: thirteen generator roles and two binary inputs, shared by both swaps. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev sharedHeaderT (N : ℕ) := N + Fintype.card HeaderWorkRole

theorem headerWorkRole_card : Fintype.card HeaderWorkRole = 15 := by decide +kernel

def sharedHeaderCore {N : ℕ} (i : Fin N) : Fin (sharedHeaderT N) := ⟨i.val, by have := i.isLt; unfold sharedHeaderT; omega⟩

def sharedHeaderWork {N : ℕ} (r : HeaderWorkRole) : Fin (sharedHeaderT N) :=
  ⟨N + (Fintype.equivFin HeaderWorkRole r).val, by have := (Fintype.equivFin HeaderWorkRole r).isLt; unfold sharedHeaderT; omega⟩

theorem sharedHeaderCore_injective {N : ℕ} : Function.Injective (sharedHeaderCore (N := N)) := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin (sharedHeaderT N) => x.val) he)

theorem sharedHeaderWork_injective {N : ℕ} : Function.Injective (sharedHeaderWork (N := N)) := by
  intro r s he
  apply (Fintype.equivFin HeaderWorkRole).injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [sharedHeaderWork] at hv
  omega

theorem sharedHeaderCore_work {N : ℕ} (i : Fin N) (r : HeaderWorkRole) : sharedHeaderCore i ≠ sharedHeaderWork r := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [sharedHeaderCore, sharedHeaderWork] at hv
  omega

def sharedHeaderSlot {N : ℕ} (core : HeaderCoreRole → Fin N) : HeaderCoreRole ⊕ HeaderWorkRole → Fin (sharedHeaderT N)
  | .inl r => sharedHeaderCore (core r)
  | .inr r => sharedHeaderWork r

theorem sharedHeaderSlot_injective {N : ℕ} (core : HeaderCoreRole → Fin N) (hcore : Function.Injective core) :
    Function.Injective (sharedHeaderSlot core) := by
  intro r s he
  cases r with
  | inl r =>
    cases s with
    | inl s => exact congrArg Sum.inl (hcore (sharedHeaderCore_injective he))
    | inr s => exact (sharedHeaderCore_work (core r) s he).elim
  | inr r =>
    cases s with
    | inl s => exact (sharedHeaderCore_work (core s) r he.symm).elim
    | inr s => exact congrArg Sum.inr (sharedHeaderWork_injective he)

def sharedHeaderBank {N : ℕ} (core : HeaderCoreRole → Fin N) (c : Fin 2) : RepairHeaderReg → Fin (sharedHeaderT N) :=
  sharedHeaderSlot core ∘ sharedHeaderRole c

def sharedHeaderBinary {N : ℕ} (i : Fin 2) : Fin (sharedHeaderT N) := sharedHeaderWork (.binary i)

theorem sharedHeaderBank_injective {N : ℕ} (core : HeaderCoreRole → Fin N) (hcore : Function.Injective core) (c : Fin 2) :
    Function.Injective (sharedHeaderBank core c) :=
  (sharedHeaderSlot_injective core hcore).comp (sharedHeaderRole_injective c)

theorem sharedHeaderBank_cross {N : ℕ} (core : HeaderCoreRole → Fin N) (hcore : Function.Injective core)
    (r : RepairHeaderReg) (i : Fin 5) :
    sharedHeaderBank core 1 r ≠ sharedHeaderBank core 0 (.exchange (.base (.header i))) :=
  (sharedHeaderSlot_injective core hcore).ne (sharedHeaderRole_cross r i)

theorem sharedHeaderBinary_separate {N : ℕ} (core : HeaderCoreRole → Fin N) (hcore : Function.Injective core)
    (c : Fin 2) (i : Fin 2) (r : RepairHeaderReg) : sharedHeaderBinary i ≠ sharedHeaderBank core c r :=
  (sharedHeaderSlot_injective core hcore).ne (sharedHeaderRole_binary c r i)

end
end IntegerMultBounds.MathlibTM2.Routing
