module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupFrame
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupCounts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Actual persistent compact bank setup, with original source words and all scratch restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactBasisCountsOutput_small
    (v : SynW → List (Fin (A+4))) (d g K D q o r : ℕ) :
    compactBasisCountsOutput v d g K D q o r=
      compactSetupUpdate7 v compactBasisOutputWire ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g] := by
  rfl

lemma compactBasisCountsOutput_file (R : Fin (nT SXReg) → List (Fin (A+4)))
    (v : SynW → List (Fin (A+4))) (d g K D q o r : ℕ) :
    synG R (compactBasisCountsOutput v d g K D q o r)=
      compactSetupUpdate7 (synG R v) (sreg ∘ compactBasisOutputWire)
        ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g] :=
  (congrArg (synG R) (compactBasisCountsOutput_small v d g K D q o r)).trans
    (compactSetupUpdate7_map (synG R) sreg (fun v x l => (synG_update (R:=R) (v:=v) x l).symm)
      v compactBasisOutputWire _)

end
end IntegerMultBounds.MathlibTM2.LayerMachine
