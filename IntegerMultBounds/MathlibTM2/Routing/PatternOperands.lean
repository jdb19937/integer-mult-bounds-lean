module

public import IntegerMultBounds.MathlibTM2.Routing.PatternCode

/-!
# Pattern callbacks on explicit operand words

The two-field index below is only a proof adapter for the existing execution
lemma. It does not change the physical record fields: a caller can map the source
register to a priced metadata header and the target to its actual live counter.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

private theorem operand_digits (W L x y : ℕ) (hx : x < 2 ^ W) (hy : y < 2 ^ L) :
    digit ![W, L] 0 (x + y * 2 ^ W) = x ∧
      digit ![W, L] 1 (x + y * 2 ^ W) = y := by
  have h0 : fieldOff ![W, L] 0 = 0 := fieldOff_zero _ _ rfl
  have h1 : fieldOff ![W, L] 1 = W := by
    simpa [h0] using fieldOff_succ ![W, L] 0 (by decide)
  simp [digit, h0, h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx,
    Nat.add_mul_div_right, Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hy]

variable {T Q A W L : ℕ} {P U : Type}

/-- Execute the existing concrete callback using a source word and target word,
without asserting that either belongs to any particular physical field bank. -/
theorem patternOperands_exec (body : P → Pr P T Q A U)
    (ι : PatternReg 2 → Fin T) (hι : Function.Injective ι)
    (s : Fin 2 → Fin L → Option (Fin W)) {nd : ℕ} (C : CAuto A 3 nd)
    (x y : ℕ) (hx : x < 2 ^ W) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (ι (.fld 0)) = binSyms W x)
    (htgt : S.R (ι (.fld 1)) = binSyms L y)
    (hscratch : ∀ r : PatternReg 2, (∀ f, r ≠ .fld f) → r ≠ .st →
      S.R (ι r) = patternStatic A s r) :
    ∃ v' m, v'.user = v.user ∧ m ≤ patternCodeCost L W ∧
      codeSel C (v'.scan (ι .st)).val =
        C.eval L ![y, patternValue (s 0) x, patternValue (s 1) x] ∧
      Exec body (patternCode ι 0 1 C) (mk v S) m (mk v' S) := by
  have hd := operand_digits W L x y hx hy
  have hI : PatternInv ![W, L] ι s S.R (x + y * 2 ^ W) := by
    intro r hr
    cases r with
    | fld f =>
      fin_cases f
      · simpa [hd.1] using hsrc
      · simpa [hd.2] using htgt
    | st => exact (hr rfl).elim
    | _ => exact hscratch _ (by simp) hr
  have hspec := patternCode_spec body (len := ![W, L]) hι 0 1 rfl rfl s C
  simpa [hd.1, hd.2] using hspec.runs (x + y * 2 ^ W) v S hI

end IntegerMultBounds.MathlibTM2.Routing
