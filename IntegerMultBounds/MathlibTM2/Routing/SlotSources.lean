module

public import IntegerMultBounds.MathlibTM2.Routing.MaskedDynamic

/-!
# Physical sources for the complete selective schedule

Sources may be prefix bits, any preserved segment bit (including inactive low
bits), suffix bits, or bits of an arbitrary unchanged spectator word. The typed
source list is arbitrary in order and may repeat positions.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

inductive SlotSource (p : Par) (X : ℕ) where
  | low (r : Fin p.ρ)
  | digit (c : Fin p.n) (r : Fin p.K)
  | high (r : Fin p.m)
  | spectator (r : Fin X)
  deriving DecidableEq

variable {p : Par} {X : ℕ}

/-- Exactly active target low bits are forbidden as sources. -/
def SlotSource.Allowed (active : Fin p.n → Bool) : SlotSource p X → Prop
  | .digit c r => active c = true → 0 < r.val
  | _ => True

def SlotSource.physical (y x : ℕ) : SlotSource p X → Bool
  | .low r => y.testBit r.val
  | .digit c r => y.testBit (p.ρ + c.val * p.K + r.val)
  | .high r => y.testBit (p.ρ + p.n * p.K + r.val)
  | .spectator r => x.testBit r.val

def SlotSource.observed (active : Fin p.n → Bool)
    (obs : ℕ × (Fin p.n → ℕ) × ℕ) (x : ℕ) : SlotSource p X → Bool
  | .low r => obs.1.testBit r.val
  | .digit c r => (obs.2.1 c).testBit (if active c then r.val - 1 else r.val)
  | .high r => obs.2.2.testBit r.val
  | .spectator r => x.testBit r.val

private theorem observed_bit (a : Bool) (x r : ℕ) (hr : a = true → 0 < r) :
    (if a then x / 2 else x).testBit (if a then r - 1 else r) = x.testBit r := by
  cases a with
  | false => rfl
  | true =>
    change (x / 2 ^ 1).testBit (r - 1) = x.testBit r
    rw [Nat.testBit_div_two_pow]
    congr 1
    have := hr rfl
    omega

/-- The source observation decodes the actual physical bit, including inactive
low bits and complete prefix/suffix/outer spectators. -/
theorem SlotSource.observed_physical (active : Fin p.n → Bool) (s : SlotSource p X)
    (hs : s.Allowed active) (y x : ℕ) :
    s.observed active (slotView p active y) x = s.physical y x := by
  cases s with
  | low r => simp [observed, physical, slotView, r.isLt]
  | digit c r =>
    change (if active c then seg p.ρ p.K c.val y / 2 else seg p.ρ p.K c.val y).testBit
      (if active c then r.val - 1 else r.val) = _
    rw [observed_bit _ _ _ hs]
    simp [physical, seg, window, Nat.testBit_mod_two_pow, r.isLt,
      Nat.testBit_div_two_pow, Nat.add_comm]
  | high r => simp [observed, physical, slotView, Nat.testBit_div_two_pow, Nat.add_comm]
  | spectator r => rfl

/-- A total digit reader whose first `n` entries follow the ordered source list. -/
def slotSourcesRead (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (obs : ℕ × (Fin p.n → ℕ) × ℕ) (x c : ℕ) : ℕ :=
  if hc : c < p.n then ((s ⟨c, hc⟩).observed active obs x).toNat else 0

theorem slotSourcesRead_bits (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (obs : ℕ × (Fin p.n → ℕ) × ℕ) (x c : ℕ) :
    slotSourcesRead active s obs x c = 0 ∨ slotSourcesRead active s obs x c = 1 := by
  unfold slotSourcesRead
  split
  · cases (s _).observed active obs x <;> simp
  · simp

theorem slotSourcesRead_physical (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hs : ∀ c, (s c).Allowed active) (y x : ℕ) (c : Fin p.n) :
    slotRead p active (slotSourcesRead active s) y x c.val = ((s c).physical y x).toNat := by
  simp only [slotRead, slotSourcesRead, dite_eq_left c.isLt]
  rw [SlotSource.observed_physical active (s c) (hs c)]

/-- Actual source bits as a total digit list. -/
def slotPhysicalRead (s : Fin p.n → SlotSource p X) (y x c : ℕ) : ℕ :=
  if hc : c < p.n then ((s ⟨c, hc⟩).physical y x).toNat else 0

theorem slotRead_eq_physical (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hs : ∀ c, (s c).Allowed active) (y x : ℕ) :
    slotRead p active (slotSourcesRead active s) y x = slotPhysicalRead s y x := by
  funext c
  by_cases hc : c < p.n
  · simpa only [slotPhysicalRead, dite_eq_left hc] using
      slotSourcesRead_physical active s hs y x ⟨c, hc⟩
  · simp [slotRead, slotSourcesRead, slotPhysicalRead, hc]

/-- Complete schedule correctness for explicit physical sources in arbitrary order. -/
theorem selectiveRun_sources_good (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hs : ∀ c, (s c).Allowed active)
    {v : V} (hv : Fits p v) (hgood : Good p v) (hG : 0 < p.G) (hK : 1 ≤ p.K) :
    selectiveRun p active (slotRead p active (slotSourcesRead active s)) prog v =
      { v with y := togY p (activeSource p active (slotPhysicalRead s v.y v.x)) v.y } := by
  rw [selectiveRun_dynamic_good p active (slotSourcesRead active s)
    (slotSourcesRead_bits active s) hv hgood hG hK, slotRead_eq_physical active s hs]

end IntegerMultBounds.MathlibTM2.Routing
