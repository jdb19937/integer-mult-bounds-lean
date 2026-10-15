module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre

/-! Forward layout followed by the concrete hybrid scan, with original transform semantics. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

/-- Scratch blankness is a consequence of the synthetic invariant. -/
lemma compactSynUniformView_scratch {K ℓ W l : ℕ} {es : List ℕ}
    {v : SynW → List (Fin (prime+Ka+4))}
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    {R : Fin compactMnT → List (Fin (prime+Ka+4))} {io park : List (Fin (prime+Ka+4))}
    (hR : compactSynView R=synG (synIdle io park) v) :
    ∀ i : Fin 32,R (compactMnSyn (.s i))=[] := by
  intro i
  rw [compactMnSyn_dispatch,compactSynView_wire hR]
  exact hv.hs i

end
end IntegerMultBounds.MathlibTM2.Fast.Main
