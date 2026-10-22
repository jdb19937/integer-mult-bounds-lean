module

public import IntegerMultBounds.MathlibTM2.Routing.MaskedSlot

/-!
# The complete selective instruction schedule

The source-load instruction reads the current target and unchanged spectator
word. All other instructions use the checked masked offsets. This retains the
actual twelve-rotation, twelve-interchange gadget schedule.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par)

/-- Arbitrary ordered source bits replace only the source-load offset. -/
def selectiveOp (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ) : Op → V → V
  | .rotB neg .X, v => { v with b := rotv p.wc neg (casm p.G p.n (read v.y v.x)) v.b }
  | op, v => maskedOp p active op v

def selectiveRun (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (os : List Op) (v : V) : V := os.foldl (fun v op => selectiveOp p active read op v) v

theorem selectiveRun_append (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (os os' : List Op) (v : V) :
    selectiveRun p active read (os ++ os') v =
      selectiveRun p active read os' (selectiveRun p active read os v) := by
  simp [selectiveRun, List.foldl_append]

/-- The early schedule uses no source-load instruction. -/
theorem selectiveRun_E (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ) (v : V) :
    selectiveRun p active read E v = maskedRun p active E v := rfl

/-- Swaps make the source rotation act on the actual borrowed control, then
restore the field order. This is equality of the complete instruction sequence. -/
theorem selectiveRun_load (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (neg : Bool) (v : V) :
    selectiveRun p active read [.swapU, .rotB neg .X, .swapU] v =
      { v with u := rotv p.wc neg (casm p.G p.n (read v.y v.x)) v.u } := rfl

/-- The complete concrete schedule is early, actual-source load, early, unload. -/
theorem selectiveRun_prog (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ) (v : V) :
    selectiveRun p active read prog v =
      let v₁ := maskedRun p active E v
      let v₂ := { v₁ with u := rotv p.wc false (casm p.G p.n (read v₁.y v₁.x)) v₁.u }
      let v₃ := maskedRun p active E v₂
      { v₃ with u := rotv p.wc true (casm p.G p.n (read v₃.y v₃.x)) v₃.u } := by
  rw [prog, selectiveRun_append, selectiveRun_append, selectiveRun_append,
    selectiveRun_E, selectiveRun_load, selectiveRun_E, selectiveRun_load]

/-- Requested source toggles with inactive target coordinates suppressed. -/
def activeSource (active : Fin p.n → Bool) (src : ℕ → ℕ) (c : ℕ) : ℕ :=
  if hc : c < p.n then if active ⟨c, hc⟩ then src c else 0 else 0

end IntegerMultBounds.MathlibTM2.Routing
