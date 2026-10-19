module
public import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationRun
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement
import IntegerMultBounds.Machine.SharedBankRawCompose
import Mathlib.Tactic.Positivity.Finset


/-! Concrete compact conjugations on arbitrary seventeen-port caller banks.
All sixteen supplied original/prepared descriptors survive; only the full
array changes and every native private tape returns blank. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationPlaced
noncomputable section
open ActivePrefixDirtyControlConjugationData
open ActivePrefixDirtyControlConjugationSwap (count bank)
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def ports (i : Fin 17) : Fin count := ⟨i.val,by have := i.isLt; unfold count; omega⟩
theorem ports_injective : Function.Injective ports := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin count => k.val) h)
def result {m : ℕ} (caller : Tapes t prime) (focus : Fin 17 → Fin t) (x : Fin m → Bool) :=
  setTape caller (focus 16) (ActiveTargetRotation.word x) 0

theorem bank_raw (v : Tapes 17 prime) : bank v=SharedBankStageInput.raw v count := by
  change (CleanSubbank.bank (s := swapCount) v).append (SharedBank.empty 65 prime)=_
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankFamily.raw_append v (by omega)]
  rfl

theorem native_payload (v : Tapes 17 prime) : SharedBank.payload (bank v) ports=v := by
  rw [bank_raw]
  exact SharedBankRawCompose.payload_raw v ports (fun _ => rfl)
theorem native_clean (v : Tapes 17 prime) : SharedBank.strip (bank v) ports=SharedBank.empty count prime := by
  rw [bank_raw]
  exact SharedBankRawCompose.strip_raw v ports (fun _ => rfl)

theorem native_output {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool)
    (rs bs : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    bank (base gs bw hs rs bs y)=setTape (bank (base gs bw hs rs bs x)) (ports 16) (ActiveTargetRotation.word y) 0 := by
  change ((base gs bw hs rs bs y).append (SharedBank.empty swapCount prime)).append
    (SharedBank.empty 65 prime)=setTape
    (((base gs bw hs rs bs x).append (SharedBank.empty swapCount prime)).append (SharedBank.empty 65 prime))
    (Fin.castAdd 65 (Fin.castAdd swapCount (16 : Fin 17))) _ 0
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,base_set]

theorem realizes {c budget m n : ℕ} (M : Program count c prime)
    (caller : Tapes t prime) (focus : Fin 17 → Fin t) (hf : Function.Injective focus)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Fin m → Bool) (y : Fin n → Bool) (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x)
    (h : HoareTime M (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs y)) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus y)) budget := by
  refine CleanSubbank.realizes M ports focus ports_injective hf caller (result caller focus y)
    _ _ _ ?_ ?_ (native_clean _) (native_clean _) ?_ h
  · exact (native_payload (base gs bw hs rs bs x)).trans hsrc.symm
  · refine (native_payload (base gs bw hs rs bs y)).trans ?_
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,base_set]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationPlaced
