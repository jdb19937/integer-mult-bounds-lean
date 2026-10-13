module

public import IntegerMultBounds.Schoenhage.CertifiedSequence
public import IntegerMultBounds.Schoenhage.TapeBank

/-! Lift single-output contracts without re-proving each complementary tape.
The local theorem must preserve its full bank except the named output. -/

@[expose] public section
namespace IntegerMultBounds.Schoenhage.CertifiedSequence
open Machine

theorem placed_update {alphabet small large : ℕ} {command : Cmd alphabet small}
    (slots : Fin small → Fin large) (slotsInjective : Function.Injective slots)
    (bank : Fin large → WTape) {localInput : Fin small → WTape}
    (ready : bank ∘ slots = localInput) (outputSlot : Fin small) (value : WTape) {bound : ℕ}
    (localRun : Runs command localInput (· = Function.update localInput outputSlot value) bound) :
    Runs (command.map slots slotsInjective) bank
      (· = Function.update bank (slots outputSlot) value) bound := by
  rw [← ready] at localRun
  have lifted := TapeBank.runs_place slots slotsInjective localRun
  simpa only [TapeBank.place_update slotsInjective, TapeBank.place_self slotsInjective] using lifted

end IntegerMultBounds.Schoenhage.CertifiedSequence
