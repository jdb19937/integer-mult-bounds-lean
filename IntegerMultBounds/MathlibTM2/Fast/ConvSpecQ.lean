module

public import IntegerMultBounds.MathlibTM2.Fast.ConvSpec
public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRoundsQ
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The synthetic transform contracts with computed rounds

`Fast/ConvSpec` with the computed rounds of `Mult/SynthErrRoundsQ` in place of `Q_p` after each
exact round: for forward rounds `F` and opposite rounds `O` (`RoundOp`), the forward output
`cvFwdOutQ` holds the numerators of `fwdRoundsQ F (nRounds a)` of the grid records in the order
`π`, the opposite output `cvOppOutQ` those of `oppRoundsQ O (nRounds a)` in natural order.
`SynFwdSpecQ`, `SynOppSpecQ` are `SynFwdSpec`, `SynOppSpec` with these outputs.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr

noncomputable section

section Spec

variable {T Q A : ℕ} {U P : Type} {d : ℕ}

/-- The forward output with computed rounds `F`. -/
def cvFwdOutQ (p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ) {η : ℝ}
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) η)
    (Z : ℕ → Fin (2 ^ l) → GaussianInt) : ℕ → Fin (2 ^ l) → GaussianInt :=
  fun n => cvNum p (fwdRoundsQ F (nRounds a) (rpGrid p Z)) (π n)

/-- The opposite output with computed rounds `O`, in natural order. -/
def cvOppOutQ (p l : ℕ) (a : Fin d → ℕ) {η : ℝ}
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) η)
    (V : ℕ → Fin (2 ^ l) → GaussianInt) : ℕ → Fin (2 ^ l) → GaussianInt :=
  cvNum p (oppRoundsQ O (nRounds a) (rpGrid p V))

/-- `SynFwdSpec` with the computed forward rounds `F`. -/
def SynFwdSpecQ (body : P → Pr P T Q A U) (fwdP : Pr P T Q A U) (io : Fin T)
    (Pre : Stacks T A → Prop) (w p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ) {η : ℝ}
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2 ^ l) (List.ofFn a)) η) (cF : ℕ) : Prop :=
  ∀ (Z : ℕ → Fin (2 ^ l) → GaussianInt) (v : HS T Q A U) (S : Stacks T A), Pre S →
    SupLe (List.ofFn a).sum (rpGrid p Z) 1 → S.R io = cstream A w (rpStream (cvM a) Z) →
    ∃ v' n, v'.user = v.user ∧ n ≤ cF ∧
      Exec body fwdP (mk v S) n (mk v' { S with
        R := Function.update S.R io (cstream A w (rpStream (cvM a) (cvFwdOutQ p l a π F Z))) })

/-- `SynOppSpec` with the computed opposite rounds `O`. -/
def SynOppSpecQ (body : P → Pr P T Q A U) (oppP : Pr P T Q A U) (io : Fin T)
    (Pre : Stacks T A → Prop) (w p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ) {η : ℝ}
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2 ^ l) (List.ofFn a)) η) (cO : ℕ) : Prop :=
  ∀ (V : ℕ → Fin (2 ^ l) → GaussianInt) (v : HS T Q A U) (S : Stacks T A), Pre S →
    SupLe (List.ofFn a).sum (rpGrid p V) 1 →
    S.R io = cstream A w (rpStream (cvM a) fun n => V (π n)) →
    ∃ v' n, v'.user = v.user ∧ n ≤ cO ∧
      Exec body oppP (mk v S) n (mk v' { S with
        R := Function.update S.R io (cstream A w (rpStream (cvM a) (cvOppOutQ p l a O V))) })

end Spec

end

end IntegerMultBounds.MathlibTM2.Fast
