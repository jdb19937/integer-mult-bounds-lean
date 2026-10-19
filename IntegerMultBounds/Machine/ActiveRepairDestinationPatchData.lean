module
import Mathlib.Tactic.Positivity.Finset
import IntegerMultBounds.Compact.PowerTwoDigits
public import IntegerMultBounds.Machine.Gather
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init


/-! Fixed-width address patches retain all bits outside their runtime interval.
The word definition is identified with the actual physical tape overwrite. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchData
noncomputable section
variable {a : ℕ}

def patch (xs : List Bool) (start : ℕ) (ys : List Bool) : List Bool :=
  (List.range xs.length).map fun j =>
    if start≤j ∧ j<start+ys.length then ys.getD (j-start) false else xs.getD j false

@[simp] theorem patch_length (xs : List Bool) (start : ℕ) (ys : List Bool) :
    (patch xs start ys).length=xs.length := by simp [patch]

theorem patch_bit (xs : List Bool) (start : ℕ) (ys : List Bool) (j : ℕ) (hj : j<xs.length) :
    (patch xs start ys).getD j false=
      if start≤j ∧ j<start+ys.length then ys.getD (j-start) false else xs.getD j false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hj)]
  simp [patch]

theorem outside (xs : List Bool) (start : ℕ) (ys : List Bool) (j : ℕ)
    (hj : j<xs.length) (hout : j<start ∨ start+ys.length≤j) :
    (patch xs start ys).getD j false=xs.getD j false := by
  rw [patch_bit xs start ys j hj,ite_eq_right (by omega)]

theorem inside (xs : List Bool) (start : ℕ) (ys : List Bool)
    (hfit : start+ys.length≤xs.length) (j : ℕ) (hj : j<ys.length) :
    (patch xs start ys).getD (start+j) false=ys.getD j false := by
  rw [patch_bit xs start ys (start+j) (by omega),ite_eq_left (by omega),Nat.add_sub_cancel_left]

theorem tape (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) (start : ℕ) (ys : List Bool)
    (hfit : start+ys.length≤xs.length) :
    putWord (putWord f p (xs.map bitSymbol)) (p+start) (ys.map bitSymbol)=
      putWord f p ((patch xs start ys).map bitSymbol) := by
  funext z
  by_cases hlow : z<p
  · rw [putWord_outside _ _ _ _ (Or.inl (by omega)),
        putWord_outside _ _ _ _ (Or.inl hlow),putWord_outside _ _ _ _ (Or.inl hlow)]
  by_cases hhigh : p+xs.length≤z
  · rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega)),
        putWord_outside _ _ _ _ (Or.inr (by simpa using hhigh)),
        putWord_outside _ _ _ _ (Or.inr (by simpa using hhigh))]
  let j := (z-p).toNat
  have hz : z=p+j := by dsimp [j]; omega
  have hj : j<xs.length := by omega
  rw [hz,Gather.putWord_getD f p (patch xs start ys) j (by simpa using hj),patch_bit xs start ys j hj]
  by_cases hin : start≤j ∧ j<start+ys.length
  · rw [ite_eq_left hin]
    have he : p+(j : ℤ)=(p+start)+((j-start : ℕ) : ℤ) := by omega
    rw [he,Gather.putWord_getD _ _ ys (j-start) (by omega)]
  · rw [ite_eq_right hin,putWord_outside _ _ _ _ (by simp only [List.length_map]; omega),
        Gather.putWord_getD f p xs j hj]

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchData
