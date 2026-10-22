module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob
public import IntegerMultBounds.GrowingCounterData

/-!
# Executed multiplication by a tape-supplied power of two

Copy a binary input and prepend one low zero per exponent-tape symbol. All input
and scratch tapes are restored. This constructs shifted row-count headers without
unrolling dimensions or numerical values into the program.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

theorem binaryScale_value (e : ℕ) (bs : List Bool) :
    Counter.value (List.replicate e false ++ bs) = 2 ^ e * Counter.value bs := by
  induction e with
  | zero => simp
  | succ e ih => simp only [List.replicate_succ, List.cons_append, Counter.value, Bool.false_eq_true, reduceIte, Nat.zero_add, ih, pow_succ]
                 ring

/-- Low zeros preserve the highest true bit of a nonzero canonical input. -/
theorem binaryScale_canonical (e : ℕ) (bs : List Bool)
    (hc : GrowingCounterData.Canonical bs) (hne : bs ≠ []) :
    GrowingCounterData.Canonical (List.replicate e false ++ bs) := by
  obtain ⟨initial, he⟩ := List.getLast?_eq_some_iff.mp (hc.resolve_left hne)
  right
  rw [he, ← List.append_assoc]
  simp


def binaryScaleProgram (exponent src dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (bcopy src dst tmp work) (.seq (bzero exponent tmp work) (moveR tmp dst id))

/-- Construct a shifted copy with a complete frame and exact linear cost. -/
theorem binaryScale_exec (body : P → Pr P T Q A U) (exponent src dst tmp work : Fin T)
    (hreg : [exponent, src, dst, tmp, work].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryScaleProgram exponent src dst tmp work) (mk v S)
        (6 * ((S.R src).length + (S.R exponent).length) + 12)
        (mk v' { S with R := Function.update S.R dst (List.replicate (S.R exponent).length (bitSymbol false) ++ S.R src) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body (a := src) (c := dst) (t₁ := tmp) (t₂ := work)
    (by regs_nodup) v S htmp hwork
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (S.R src ++ S.R dst) }
  have hexp : S₁.R exponent = S.R exponent := by simp [S₁, ‹exponent ≠ dst›]
  obtain ⟨v₂, hu₂, he₂⟩ := bzero_exec body (wR := exponent) (c := tmp) (t := work)
    (by regs_nodup) v₁ S₁ (by simp [S₁, hwork, Ne.symm ‹dst ≠ work›])
  let S₂ : Stacks T A :=
    { S₁ with R := Function.update S₁.R tmp (binSyms (S₁.R exponent).length 0 ++ S₁.R tmp) }
  have htmp₂ : S₂.R tmp = binSyms (S.R exponent).length 0 := by
    simp [S₂, S₁, htmp, Ne.symm ‹dst ≠ tmp›, ‹exponent ≠ dst›]
  have hdst₂ : S₂.R dst = S.R src := by simp [S₂, S₁, ‹dst ≠ tmp›, hdst]
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body tmp dst (Ne.symm ‹dst ≠ tmp›) id v₂ S₂
  have hfinal : movedR S₂.R tmp dst id (S₂.R tmp) =
      Function.update S.R dst (List.replicate (S.R exponent).length (bitSymbol false) ++ S.R src) := by
    funext j
    by_cases hj : j = dst
    · subst j
      simp [movedR, htmp₂, hdst₂, binSyms]
    · by_cases hk : j = tmp
      · subst j
        simp [movedR, Ne.symm ‹dst ≠ tmp›, htmp]
      · simp [movedR, S₂, S₁, hj, hk]
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  refine Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_
  · rw [hexp, htmp₂]
    simp
    omega
  · simp only [hfinal]
    rfl

end IntegerMultBounds.MathlibTM2.Routing
