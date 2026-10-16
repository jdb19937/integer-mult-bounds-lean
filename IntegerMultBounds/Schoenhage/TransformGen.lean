module

public import IntegerMultBounds.Schoenhage.TransformWrap
public import IntegerMultBounds.Schoenhage.TransformParams

/-! The header generators of the transform programs (§6): the interface. The ring product's bank
sits in the word bank with its header tape on paper tape 0 and every other tape on drivers' tapes
`50 + x` (`gslot`). After the header decoder (`TransformParams.runs_decodeParams`) the word bank is
`decState`: the decoded parameters `p`, `D = d - 1`, `ℓ`, `K`, `w` in unary, the axis ticks and the
long-axis flags. The round-script and layout-script writers are hypotheses here (`ScriptGen`,
`LayoutGen`): from `decState` each writes its script on named tape 6 or 7 and changes nothing else. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Spec.SignedRingProduct Resampling AxisDriver LayoutMachines TwistDescriptors

variable {A tL nL : ℕ}

/-- The ring product's bank inside the word bank: the header tape on paper tape 0, tape `x` on
drivers' tape `50 + x`. -/
def gslot (tL nL : ℕ) (x : Fin 𝕌) : Fin (4 + DB tL nL) :=
  if x = zH then pt tL nL 0 else drv tL nL ⟨50 + x.val, by have := x.isLt; change x.val < 91 at this; unfold DB; omega⟩

theorem gslot_injective : Function.Injective (gslot tL nL) := by
  intro x y e
  have e' := congrArg Fin.val e
  have hx := x.isLt; have hy := y.isLt
  change x.val < 91 at hx; change y.val < 91 at hy
  unfold gslot at e'
  split_ifs at e' with h1 h2 h2 <;> simp [pt, drv] at e' <;> first | (subst_vars; rfl) | omega

/-- The decoder's start: the header on its header tape, every other tape empty. -/
def decStart (hdr : List Bool) : Fin 𝕌 → WTape := fun x => if x = zH then reg hdr else emp

/-- The decoder's result. -/
def decoded (p d l K w : ℕ) (ts : List ℕ) : Fin 𝕌 → WTape :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (decStart (transformHeader p d (2 ^ l) K w ts)) iP (reg (ones p)))
    kN (reg (ones (d - 1)))) iL (reg (ones l))) kI (reg (ones K))) iW (reg (ones w)))
    xB ⟨List.replicate ts.length [] ++ [], []⟩) xA ⟨((TransformParams.lengthFlags l ts).map fun b => [b]).reverse, []⟩

/-- The word bank after decoding the header, input `F` on paper tape 1. -/
noncomputable def decState (p d l K w : ℕ) (ts : List ℕ) (F : List Bool) : Fin (4 + DB tL nL) → WTape :=
  upd (wst ![reg (transformHeader p d (2 ^ l) K w ts), reg F, emp, emp] (fun _ => emp)) (gslot tL nL)
    (decoded p d l K w ts)

/-- A round-script writer: from the decoded parameters it writes the forward (`fwd = true`) or
opposite round script on named tape 6 within `B` steps and changes nothing else. -/
def ScriptGen (fwd : Bool) (sg : Cmd A (4 + DB tL nL)) {ℓ K : ℕ} {ts : List ℕ}
    (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (p d w B : ℕ) : Prop :=
  ∀ F : List Bool, Runs sg (decState p d ℓ K w ts F)
    (· = Function.update (decState p d ℓ K w ts F) (drv tL nL (nm tL nL 6))
      ⟨[], if fwd then fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K else oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K⟩) B

/-- A layout-script writer: from the decoded parameters, whatever is on named tape 6, it writes the
layout (`fwd = true`) or undo script on named tape 7 within `B` steps and changes nothing else. -/
def LayoutGen (fwd : Bool) (lg : Cmd A (4 + DB tL nL)) (ℓ K : ℕ) (ts : List ℕ) (p d w B : ℕ) : Prop :=
  ∀ (F : List Bool) (S6 : WTape), Runs lg (Function.update (decState p d ℓ K w ts F) (drv tL nL (nm tL nL 6)) S6)
    (· = Function.update (Function.update (decState p d ℓ K w ts F) (drv tL nL (nm tL nL 6)) S6)
      (drv tL nL (nm tL nL 7))
      ⟨[], if fwd then layoutWords (2 ^ ℓ) w ts ℓ K else undoWords (2 ^ ℓ) w ts ℓ K⟩) B

end IntegerMultBounds.Schoenhage
