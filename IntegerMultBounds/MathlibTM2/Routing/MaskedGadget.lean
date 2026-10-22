module

public import IntegerMultBounds.MathlibTM2.Routing.CompactPatterns

/-!
# The masked compact instruction schedule

Only offset evaluation sees masked control parities. All physical borrowed fields
remain arbitrary. The early schedule is the existing gadget schedule, and its
correctness follows by projecting to the existing `run_E` theorem rather than
reproving its scalar updates.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par)

/-- A proof projection, never an initialization of the actual borrowed field. -/
def maskedView (active : Fin p.n → Bool) (v : V) : V :=
  { v with u := maskedControls p active v.u }

/-- The actual instruction uses masked offsets and keeps its physical operands. -/
def maskedOp (active : Fin p.n → Bool) : Op → V → V
  | .rotY neg o, v =>
    { v with y := rotv p.wy neg (o.eval p (maskedView p active v)) v.y }
  | .rotB neg o, v =>
    { v with b := rotv p.wc neg (o.eval p (maskedView p active v)) v.b }
  | .swapT, v => { v with b := v.t, t := v.b }
  | .swapU, v => { v with b := v.u, u := v.b }

def maskedRun (active : Fin p.n → Bool) (os : List Op) (v : V) : V :=
  os.foldl (fun v op => maskedOp p active op v) v

/-- The unchanged actual control is masked only when read by an early offset. -/
theorem maskedView_op (active : Fin p.n → Bool) (op : Op) (hop : op ≠ .swapU) (v : V) :
    maskedView p active (maskedOp p active op v) = op.pure p (maskedView p active v) := by
  cases op <;> first | rfl | exact (hop rfl).elim

theorem maskedView_run (active : Fin p.n → Bool) (os : List Op)
    (hos : ∀ op ∈ os, op ≠ .swapU) (v : V) :
    maskedView p active (maskedRun p active os v) = run p os (maskedView p active v) := by
  induction os generalizing v with
  | nil => rfl
  | cons op os ih =>
    change maskedView p active (maskedRun p active os (maskedOp p active op v)) = _
    rw [ih (fun op hop => hos op (by simp [hop])), maskedView_op p active op (hos op (by simp))]
    rfl

theorem maskedRun_u (active : Fin p.n → Bool) (os : List Op)
    (hos : ∀ op ∈ os, op ≠ .swapU) (v : V) :
    (maskedRun p active os v).u = v.u := by
  induction os generalizing v with
  | nil => rfl
  | cons op os ih =>
    change (maskedRun p active os (maskedOp p active op v)).u = _
    rw [ih (fun op hop => hos op (by simp [hop]))]
    have hop := hos op (by simp)
    cases op <;> simp_all [maskedOp]

theorem maskedControls_lt (hG : 0 < p.G) (active : Fin p.n → Bool) (u : ℕ) :
    maskedControls p active u < 2 ^ p.wc := by
  unfold maskedControls
  simpa [posC, Par.wc] using placeVal_lt (posC_mono (p := p) hG)
    (fun c => if hc : c < p.n then active ⟨c, hc⟩ && u.testBit (posC p c) else false) p.n

/-- The checked early schedule restores every borrowed field and only toggles
active target parities. No restriction on the actual control parities is imposed. -/
theorem maskedRun_E (active : Fin p.n → Bool) {v : V} (hv : Fits p v)
    (hG : 0 < p.G)
    (ht : ∀ c < p.n, cdig p.G c v.t + 1 < 2 ^ p.G)
    (hg : ∀ c < p.n, seg p.ρ p.K c v.y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)) (hK : 1 ≤ p.K) :
    maskedRun p active E v =
      { v with y := togY p (fun c => zc p c (maskedView p active v)) v.y } := by
  have hE : ∀ op ∈ E, op ≠ .swapU := by simp [E]
  have hvm : Fits p (maskedView p active v) :=
    ⟨hv.b, hv.t, maskedControls_lt p hG active v.u, hv.y⟩
  have hp := maskedView_run p active E hE v
  rw [run_E hvm ht hg hK] at hp
  have hb := congrArg V.b hp
  have ht' := congrArg V.t hp
  have hy := congrArg V.y hp
  have hx := congrArg V.x hp
  have hu := maskedRun_u p active E hE v
  generalize maskedRun p active E v = w at hb ht' hy hx hu ⊢
  cases v
  cases w
  simp_all [maskedView]

/-- Active-control semantics at every used digit. -/
theorem zc_maskedView (hG : 0 < p.G) (active : Fin p.n → Bool) (v : V) (c : Fin p.n) :
    zc p c.val (maskedView p active v) = if active c then zc p c.val v else 0 := by
  rw [zc_eq hG, zc_eq hG]
  change ((maskedControls p active v.u).testBit (posC p c.val)).toNat = _
  rw [maskedControls_bit p hG active v.u c]
  cases active c <;> simp

end IntegerMultBounds.MathlibTM2.Routing
