module

public import IntegerMultBounds.MathlibTM2.Fast.RingProd

/-!
# The contract of the synthetic transforms

The complex convolution stage (`Fast/ConvSynth`, `Fast/ConvBox`) runs the forward and the
opposite synthetic transforms of `lem:synthetic-transform-cost` as black boxes. This file fixes
what it needs from them.

**Format.** A record array is held on one host register `io` as
`cstream A w (rpStream M Z)` (`Fast/RingProd`): the numerators `Z n c : GaussianInt` at scale
`2^p` of the records `n = 0, …, M - 1`, `M = 2^{Σ aᵢ}` (`cvM a`), each record `r = 2^l`
coefficients `c = 0, …, r - 1`, each coefficient `w` pair symbols, least significant first, the
first coefficient on top. The grid records are `rpGrid p Z`; `cvNum p u` are the numerators of a
record array `u`.

**Forward** (`SynFwdSpec`). For every numerator array `Z` of disk records
(`SupLe (Σ aᵢ) (rpGrid p Z) 1`) and all stacks `S` meeting the parameter precondition `Pre`,
the program `fwdP` turns `io = cstream A w (rpStream M Z)` into
`io = cstream A w (rpStream M Z')` with
`Z' n = cvNum p (fwdRoundsC p (List.ofFn a) A (rpGrid p Z)) (π n)` (`cvFwdOut`): record `n` of
the output is record `π n` of the computed forward rounds `Mult/SynthErrRounds.fwdRoundsC`
(`A = nRounds a`), whose own record order is the bit reversal `B`; `π` is the record
permutation of the machine's layout. Every other stack, the left stacks, the input and output
stacks are restored, the `user` component is kept, within `cF` steps.

**Opposite** (`SynOppSpec`). For every numerator array `V` (natural order) of disk records, from
`io = cstream A w (rpStream M (V ∘ π))` (the order the forward program produces) the program
`oppP` leaves `io = cstream A w (rpStream M (cvOppOut p l a V))`, the numerators of
`oppRoundsC p (List.ofFn a) A (rpGrid p V)` in natural order; everything else as for the
forward program, within `cO` steps.

Both contracts quantify over whole arrays `Z`, `V`; the stream determines only the records
below `M`, and the computed rounds map the first `M` records to themselves (the butterflies act
on address bits below `Σ aᵢ`), so a machine meets the contract when it computes the first `M`
output records.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr

noncomputable section

section Spec

variable {T Q A : ℕ} {U P : Type} {d : ℕ}

/-- The record count `M = 2^{Σ aᵢ}` of the box `∏ᵢ ℤ/2^{aᵢ}`. -/
abbrev cvM (a : Fin d → ℕ) : ℕ := 2 ^ (List.ofFn a).sum

/-- The numerators at scale `2^p` of a record array. -/
def cvNum (p : ℕ) {r : ℕ} (u : Recs r) : ℕ → Fin r → GaussianInt := fun n c => numer p (u n c)

/-- The forward output: record `n` holds the numerators of record `π n` of the computed forward
rounds of the grid records of `Z`. -/
def cvFwdOut (p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ) (Z : ℕ → Fin (2 ^ l) → GaussianInt) :
    ℕ → Fin (2 ^ l) → GaussianInt :=
  fun n => cvNum p (fwdRoundsC p (List.ofFn a) (nRounds a) (rpGrid p Z)) (π n)

/-- The opposite output: the numerators of the computed opposite rounds of the grid records of
`V`, in natural order. -/
def cvOppOut (p l : ℕ) (a : Fin d → ℕ) (V : ℕ → Fin (2 ^ l) → GaussianInt) :
    ℕ → Fin (2 ^ l) → GaussianInt :=
  cvNum p (oppRoundsC p (List.ofFn a) (nRounds a) (rpGrid p V))

/-- **The forward transform contract.** From `io = cstream A w (rpStream M Z)` (disk records,
`Pre`), `fwdP` leaves `io = cstream A w (rpStream M (cvFwdOut p l a π Z))` and every other part
of the stacks unchanged, keeps `user`, within `cF` steps. -/
def SynFwdSpec (body : P → Pr P T Q A U) (fwdP : Pr P T Q A U) (io : Fin T)
    (Pre : Stacks T A → Prop) (w p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ) (cF : ℕ) : Prop :=
  ∀ (Z : ℕ → Fin (2 ^ l) → GaussianInt) (v : HS T Q A U) (S : Stacks T A), Pre S →
    SupLe (List.ofFn a).sum (rpGrid p Z) 1 → S.R io = cstream A w (rpStream (cvM a) Z) →
    ∃ v' n, v'.user = v.user ∧ n ≤ cF ∧
      Exec body fwdP (mk v S) n (mk v' { S with
        R := Function.update S.R io (cstream A w (rpStream (cvM a) (cvFwdOut p l a π Z))) })

/-- **The opposite transform contract.** For a natural-order array `V` of disk records, from
`io = cstream A w (rpStream M (V ∘ π))` (`Pre`), `oppP` leaves
`io = cstream A w (rpStream M (cvOppOut p l a V))` and every other part of the stacks unchanged,
keeps `user`, within `cO` steps. -/
def SynOppSpec (body : P → Pr P T Q A U) (oppP : Pr P T Q A U) (io : Fin T)
    (Pre : Stacks T A → Prop) (w p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ) (cO : ℕ) : Prop :=
  ∀ (V : ℕ → Fin (2 ^ l) → GaussianInt) (v : HS T Q A U) (S : Stacks T A), Pre S →
    SupLe (List.ofFn a).sum (rpGrid p V) 1 →
    S.R io = cstream A w (rpStream (cvM a) fun n => V (π n)) →
    ∃ v' n, v'.user = v.user ∧ n ≤ cO ∧
      Exec body oppP (mk v S) n (mk v' { S with
        R := Function.update S.R io (cstream A w (rpStream (cvM a) (cvOppOut p l a V))) })

end Spec

end

end IntegerMultBounds.MathlibTM2.Fast
