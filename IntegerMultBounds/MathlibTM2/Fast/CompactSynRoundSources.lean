module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced
public import IntegerMultBounds.MathlibTM2.Fast.SynRecB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Actual chunk-round sourcing of the stride, remainder and current selected
offset. Global original depth/guard must be initialized separately and retained;
this stage never identifies the current word width with original precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Compute `kh`, `rh` and the current offset from the existing round counters,
then put that offset in the original-input constructor's source register. -/
def compactSynChunkSource : Pr P (nT SXReg) Q A U :=
  .seq synChunkA (moveR (sreg (.s 6)) (sreg (.s 7)) id)

def compactSynChunkSourceOut (v : SynW → List (Fin (A+4))) (h b K D : ℕ) :=
  Function.update (Function.update (Function.update v (.p .kh) (List.replicate K tick))
    (.p .rh) (List.replicate ((h-b)%K) tick)) (.s 7) (List.replicate (K*((h-b)/K*D)) tick)

def compactSynChunkSourceCost (h b K D : ℕ) :=
  synChunkACost h b K D+(2*(K*((h-b)/K*D))+2)

theorem sg_compactSynChunkSource (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D : ℕ) (hKpos : 1≤K) (hs : ∀ i,v (.s i)=[])
    (hkh : v (.p .kh)=[]) (hrh : v (.p .rh)=[])
    (hh : (v (.p .h)).length=h) (hb : (v (.p .b)).length=b)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) :
    LayRuns body compactSynChunkSource (synG R v)
      (synG R (compactSynChunkSourceOut v h b K D)) (compactSynChunkSourceCost h b K D) := by
  have e₁ := sg_synChunkA body (R := R) v h b K D hKpos
    (hs 2) (hs 3) (hs 4) (hs 6) (hs 8) (hs 9) (hs 10) (hs 11) hkh hrh hh hb hK hD
  let v₁ := Function.update (Function.update (Function.update v (.p .kh)
    (List.replicate K tick)) (.p .rh) (List.replicate ((h-b)%K) tick)) (.s 6)
      (List.replicate (K*((h-b)/K*D)) tick)
  have e₂ := sg_moveR body (R := R) (v := v₁) (a := .s 6) (b := .s 7) (by decide)
  refine lr_weaken body (e₁.seq e₂) ?_ ?_
  · apply congrArg (synG R)
    funext x
    by_cases hx : x=.s 6
    · subst x
      simp [v₁,compactSynChunkSourceOut,hs]
    · simp [v₁,compactSynChunkSourceOut,Function.update_apply,hx,hs]
  · simp [v₁,compactSynChunkSourceCost]

/-- The same call-free computation on the union host preserves the complete
compact private bank, including initialized original depth and guard sources. -/
def compactSynChunkSourcePlaced : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim) (compactSynChunkSource (P := Empty))

theorem compactSynChunkSourcePlaced_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D : ℕ) (hKpos : 1≤K) (hs : ∀ i,v (.s i)=[])
    (hkh : v (.p .kh)=[]) (hrh : v (.p .rh)=[])
    (hh : (v (.p .h)).length=h) (hb : (v (.p .b)).length=b)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) :
    CompactPlacedRuns body compactSynChunkSourcePlaced (synG R v)
      (synG R (compactSynChunkSourceOut v h b K D)) (compactSynChunkSourceCost h b K D) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_compactSynChunkSource (fun f : Empty => f.elim) R v h b K D hKpos hs hkh hrh hh hb hK hD)
    vbig S hL hR

end
end IntegerMultBounds.MathlibTM2.Fast
