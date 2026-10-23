module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderSources

/-! Generated canonical row/width sources preserve all other generator inputs.
Source writes commute with header writes, allowing sources to be erased last. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

theorem repairHeaderSourceBank_keep {T A : ℕ} (bank : RepairHeaderReg → Fin T)
    (R w : ℕ) (tapes : Fin T → List (Fin (A + 4))) (i : Fin T)
    (hrows : i ≠ bank (.exchange (.base .rows))) (htarget : i ≠ bank (.exchange (.base .target))) :
    repairHeaderSourceBank bank R w tapes i = tapes i := by
  simp [repairHeaderSourceBank, hrows, htarget]

theorem repairHeaderSourceBank_commute {T A : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (R w : ℕ) (tapes : Fin T → List (Fin (A + 4)))
    (words : Fin 5 → List Bool) :
    repairHeaderSourceBank bank R w (elementaryHeaderBank tapes (fun r => bank (.exchange (.base r))) words) =
      elementaryHeaderBank (repairHeaderSourceBank bank R w tapes) (fun r => bank (.exchange (.base r))) words := by
  funext i
  by_cases hr : i = bank (.exchange (.base .rows))
  · subst i; simp [repairHeaderSourceBank, elementaryHeaderBank, hbank.eq_iff]
  · by_cases hw : i = bank (.exchange (.base .target))
    · subst i; simp [repairHeaderSourceBank, elementaryHeaderBank, hbank.eq_iff]
    · simp only [repairHeaderSourceBank, elementaryHeaderBank, Function.update_apply]
      simp [hr, hw]

end IntegerMultBounds.MathlibTM2.Routing
