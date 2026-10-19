module

import IntegerMultBounds.Machine.CountedPackedParityValue
import IntegerMultBounds.Machine.CountedPackedControlLoadValue
import IntegerMultBounds.Machine.CountedPackedGuarded
public import IntegerMultBounds.Machine.CountedPackedControlLoadRun
public import IntegerMultBounds.Machine.CountedPackedParityRun
public import IntegerMultBounds.Compact.ToggleValue

/-! Exact word specification for the two early gadgets and the physical dirty
load/unload used by the later-source gadget. These are data semantics; the
actual sequential tape assembly is proved separately. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CountedPackedLateData
noncomputable section
open Compact Compact.PowerTwo Compact.Radix
open ColumnTransducer (addRule subRule)
open CountedPackedControlLoadRun (word word_length load_value unload_value)
open CountedPackedParityRun (parities parities_length)

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (V W U X : List Bool)
def firstV := PackedArith.v2 q b hb hbq V W (parities b U X.length)
def firstW := PackedArith.w2 q b hb hbq V W (parities b U X.length)
def loaded := word addRule b hb U X

def target := PackedArith.v2 q b hb hbq (firstV q b hb hbq V W U X)
  (firstW q b hb hbq V W U X) (parities b (loaded b hb U X) X.length)
def temp := PackedArith.w2 q b hb hbq (firstV q b hb hbq V W U X)
  (firstW q b hb hbq V W U X) (parities b (loaded b hb U X) X.length)
def restored := word subRule b hb (loaded b hb U X) X

/-- Every stage has the literal original width; no target erasure is assumed
when physically replacing an equal-width word. -/
theorem lengths (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    (firstV q b hb hbq V W U X).length=V.length ∧
    (firstW q b hb hbq V W U X).length=W.length ∧
    (loaded b hb U X).length=U.length ∧
    (target q b hb hbq V W U X).length=V.length ∧
    (temp q b hb hbq V W U X).length=W.length ∧
    (restored b hb U X).length=U.length := by
  have hpV : V.length=(parities b U X.length).length*q := by simpa using hV
  have hpW : W.length=(parities b U X.length).length*b := by simpa using hW
  obtain ⟨_,_,_,_,_,_,_,hv,_,hw⟩ := PackedArith.lengths q b hb hbq V W
    (parities b U X.length) hpV hpW
  have hv' : (firstV q b hb hbq V W U X).length=V.length := by
    exact hv.trans hpV.symm
  have hw' : (firstW q b hb hbq V W U X).length=W.length := by
    exact hw.trans hpW.symm
  have hu' : (loaded b hb U X).length=U.length := word_length addRule b hb U X hU
  have hfv : (firstV q b hb hbq V W U X).length=
      (parities b (loaded b hb U X) X.length).length*q := by simpa [hv'] using hV
  have hfw : (firstW q b hb hbq V W U X).length=
      (parities b (loaded b hb U X) X.length).length*b := by simpa [hw'] using hW
  obtain ⟨_,_,_,_,_,_,_,hvv,_,hww⟩ := PackedArith.lengths q b hb hbq
    (firstV q b hb hbq V W U X) (firstW q b hb hbq V W U X)
    (parities b (loaded b hb U X) X.length) hfv hfw
  refine ⟨hv',hw',hu',hvv.trans ?_,hww.trans ?_,?_⟩
  · simp only [parities_length]; exact hV.symm
  · simp only [parities_length]; exact hW.symm
  · exact (word_length subRule b hb (loaded b hb U X) X (hu'.trans hU)).trans hu'

/-- The literal data produced by the eight real stages has precisely the
packedLate integer specification, even outside the guarded set. -/
theorem value_spec (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    ((Counter.value (target q b hb hbq V W U X) : ℤ),
      (Counter.value (temp q b hb hbq V W U X) : ℤ),
      (Counter.value (restored b hb U X) : ℤ)) =
      packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (X.map ctrl)
        (Counter.value V) (Counter.value W) (Counter.value U) := by
  obtain ⟨hfv,hfw,hlu,_,_,_⟩ := lengths q b hb hbq V W U X hV hW hU
  have hc₀ := CountedPackedParityValue.controls_eq_digit_parities b hb U X.length hU
  have hc₁ := CountedPackedParityValue.controls_eq_digit_parities b hb
    (loaded b hb U X) X.length (hlu.trans hU)
  have he₀ := forward_value q b hb hbq V W (parities b U X.length)
    (by simpa using hV) (by simpa using hW)
  rw [hc₀] at he₀
  change ((Counter.value (firstV q b hb hbq V W U X) : ℤ),
    (Counter.value (firstW q b hb hbq V W U X) : ℤ)) = _ at he₀
  have he₁ := forward_value q b hb hbq (firstV q b hb hbq V W U X)
    (firstW q b hb hbq V W U X) (parities b (loaded b hb U X) X.length)
    (by simpa only [parities_length,hfv] using hV)
    (by simpa only [parities_length,hfw] using hW)
  rw [hc₁] at he₁
  change ((Counter.value (target q b hb hbq V W U X) : ℤ),
    (Counter.value (temp q b hb hbq V W U X) : ℤ)) = _ at he₁
  have hl := load_value b hb U X hU
  change (Counter.value (loaded b hb U X) : ℤ) = _ at hl
  have hr := unload_value b hb (loaded b hb U X) X (hlu.trans hU)
  change (Counter.value (restored b hb U X) : ℤ) = _ at hr
  unfold packedLate
  simp only [List.length_map,← he₀,← hl,← he₁,← hr]


/-- Actual literal blocks supplying the later-source guard. -/
def states (q b : ℕ) (V W U X : List Bool) : List LateDigitState :=
  (List.range X.length).map fun i =>
    ⟨Counter.value (Gather.field V (i*q) q), Counter.value (Gather.field W (i*b) b),
      Counter.value (Gather.field U (i*b) b), ctrl (X.getD i false)⟩

end
end IntegerMultBounds.Machine.CountedPackedLateData
