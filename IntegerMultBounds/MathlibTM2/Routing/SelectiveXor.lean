module

public import IntegerMultBounds.MathlibTM2.Routing.SlotSources
public import IntegerMultBounds.MathlibTM2.Layer.CompactKey

/-!
# Physical XOR endpoint of the complete masked schedule

The final target is its original word XOR an explicitly sparse word of actual
source bits. Hence every unselected bit, complete spectators and all borrowed
fields are preserved by the full instruction schedule.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par}

/-- Segmentwise Boolean toggles are XOR with their sparse physical bit word. -/
theorem togY_placeVal (hK : 0 < p.K) (b : ℕ → Bool) (y : ℕ) :
    togY p (fun c => (b c).toNat) y = y ^^^ placeVal p.n (posS p) b := by
  let x := placeVal p.n (posS p) b
  have hpar : ∀ c < p.n, par p c x = (b c).toNat := by
    intro c hc
    rw [par_eq hK]
    simp [x, testBit_placeVal (posS_mono hK), (posS_mono (p := p) hK).injective.eq_iff, hc]
  have hmask : x &&& maskVal p.n (posS p) = x := by
    apply Nat.eq_of_testBit_eq
    intro q
    simp only [x, Nat.testBit_and, testBit_placeVal (posS_mono hK),
      testBit_maskVal (posS_mono hK)]
    by_cases hb : ∃ c < p.n, posS p c = q ∧ b c = true
    · have hex := hb
      obtain ⟨c, hc, hpos, _⟩ := hex
      simp [hb, show ∃ c < p.n, posS p c = q from ⟨c, hc, hpos⟩]
    · simp [hb]
  have htoggle : togY p (fun c => (b c).toNat) y = togY p (fun c => par p c x) y := by
    unfold togY
    apply asm_congr
    intro c hc
    simp only [hpar c hc]
  rw [htoggle, togY_xor hK, hmask]

/-- The precise sparse target mask loaded with the actual ordered source bits. -/
def targetWord (p : Par) {X : ℕ} (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (y x : ℕ) : ℕ :=
  placeVal p.n (posS p) fun c => if hc : c < p.n then
    active ⟨c, hc⟩ && (s ⟨c, hc⟩).physical y x else false

theorem targetWord_bit {X : ℕ} (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (y x : ℕ) (c : Fin p.n) :
    (targetWord p active s y x).testBit (posS p c.val) =
      (active c && (s c).physical y x) := by
  simp [targetWord, testBit_placeVal (posS_mono hK),
    (posS_mono (p := p) hK).injective.eq_iff, c.isLt]

theorem targetWord_other_bit {X : ℕ} (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (y x q : ℕ)
    (hq : ∀ c : Fin p.n, active c = true → q ≠ posS p c.val) :
    (targetWord p active s y x).testBit q = false := by
  rw [targetWord, testBit_placeVal (posS_mono hK), decide_eq_false_iff_not]
  rintro ⟨c, hc, hpos, hb⟩
  simp only [dite_eq_left hc, Bool.and_eq_true] at hb
  exact hq ⟨c, hc⟩ hb.1 hpos.symm

/-- The whole actual-source schedule is the requested physical XOR on the good
set; equality of the full record preserves every borrowed and spectator field. -/
theorem selectiveRun_physical_xor {X : ℕ} (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (hs : ∀ c, (s c).Allowed active)
    {v : V} (hv : Fits p v) (hgood : Good p v) (hG : 0 < p.G) (hK : 1 ≤ p.K) :
    selectiveRun p active (slotRead p active (slotSourcesRead active s)) prog v =
      { v with y := v.y ^^^ targetWord p active s v.y v.x } := by
  rw [selectiveRun_sources_good active s hs hv hgood hG hK]
  have heq : activeSource p active (slotPhysicalRead s v.y v.x) =
      (fun c => (if hc : c < p.n then
        active ⟨c, hc⟩ && (s ⟨c, hc⟩).physical v.y v.x else false).toNat) := by
    funext c
    by_cases hc : c < p.n
    · by_cases ha : active ⟨c, hc⟩ = true <;>
        simp [activeSource, slotPhysicalRead, hc, ha]
    · simp [activeSource, hc]
  rw [heq, togY_placeVal (by omega)]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
