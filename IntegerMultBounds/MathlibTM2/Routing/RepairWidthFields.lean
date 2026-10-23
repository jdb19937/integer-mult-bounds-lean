module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFieldPair
public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBank

/-! Generate the actual raw row and full-key-mask configuration registers of
R2. The remaining R2 bank is preserved, and six auxiliary tapes suffice. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

noncomputable section

def repairWidthFields (Lr Lm rb wy : ℕ) : List (BinaryFieldJob (repairT + 6)) :=
  fieldPairJobs (repairSetupSource (.inr .row)) (repairSetupSource (.inr .keyMask)) Lr Lm rb wy

theorem repairWidthFields_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P (repairT + 6) Q A U) (Lr Lm rb wy : ℕ)
    (hr : rb < 2 ^ Lr) (hm : wy < 2 ^ Lm)
    (v : HS (repairT + 6) Q A U) (S : Stacks (repairT + 6) A)
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairSetupSource (.inr .row))) = [])
    (hmask : S.R (fieldCore (repairSetupSource (.inr .keyMask))) = []) :
    ∃ (v' : HS (repairT + 6) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * wy + 11) + 2 * wy + 6) + 1 ∧
      Exec body (binaryFieldBatch (repairWidthFields Lr Lm rb wy)) (mk v S) m
        (mk v' { S with R := Function.update (Function.update S.R (fieldCore (repairSetupSource (.inr .row))) (binSyms rb 0)) (fieldCore (repairSetupSource (.inr .keyMask))) (binSyms wy (maskVal wy id)) }) := by
  exact fieldPair_exec body _ _ (by simp [repairSetupSource]) Lr Lm rb wy hr hm v S
    hrowWidth hmaskWidth hscratch hrow hmask

end
end IntegerMultBounds.MathlibTM2.Routing
