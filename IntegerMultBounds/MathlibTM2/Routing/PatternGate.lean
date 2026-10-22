module

public import IntegerMultBounds.MathlibTM2.Routing.ReadPattern
public import IntegerMultBounds.MathlibTM2.Layer.CompactCodes

/-!
# Boolean gates on source patterns

Two optional source patterns supply each offset bit. A fixed Boolean gate combines
them; AND handles temporary-times-control bits and XOR handles masked parity bits.
The rule is stateless, so descriptor data determines gaps and repeated controls.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-- The low `L` bits of a Boolean gate applied to two words. -/
def gateWord (gate : Bool → Bool → Bool) (L u v : ℕ) : ℕ :=
  placeVal L id (fun q => gate (u.testBit q) (v.testBit q))

theorem gateWord_lt (gate : Bool → Bool → Bool) (L u v : ℕ) :
    gateWord gate L u v < 2 ^ L := placeVal_lt strictMono_id _ L

theorem gateWord_bit (gate : Bool → Bool → Bool) (L u v q : ℕ) :
    (gateWord gate L u v).testBit q =
      (decide (q < L) && gate (u.testBit q) (v.testBit q)) := by
  rw [gateWord, testBit_placeVal strictMono_id]
  by_cases hq : q < L <;> simp [hq]

/-- A constant-state offset rule over `(target, pattern zero, pattern one)`. -/
def rGate (gate : Bool → Bool → Bool) : ORule 3 :=
  ⟨fun a col => (gate (col 1) (col 2), a)⟩

/-- The existing carry/borrow automata compute this exact gate word as their offset. -/
theorem offv_gate (gate : Bool → Bool → Bool) (L a u v : ℕ) :
    offv (rGate gate) L false ![a, u, v] = gateWord gate L u v := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_offv, gateWord_bit]
  rfl

/-- Gate output at the current source word, with source selectors supplied as data. -/
def patternGateValue {W L : ℕ} (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) (x : ℕ) : ℕ :=
  gateWord gate L (patternValue (s 0) x) (patternValue (s 1) x)

theorem patternGateValue_lt {W L : ℕ} (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) (x : ℕ) : patternGateValue gate s x < 2 ^ L :=
  gateWord_lt _ _ _ _

end IntegerMultBounds.MathlibTM2.Routing
