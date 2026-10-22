module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob
public import IntegerMultBounds.MathlibTM2.Host.BinArithBits
public import IntegerMultBounds.GrowingCounterData

/-!
# Uniform generation of power-of-two header words

The exponent is the length of an input tape, not part of the program. Scanning
that tape creates low zeros; moving them onto a single true bit produces the
canonical word for a power of two, restoring the exponent and both scratch tapes.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryPowerBits (e : ℕ) : List Bool := List.replicate e false ++ [true]

theorem binaryPowerBits_value (e : ℕ) : Counter.value (binaryPowerBits e) = 2 ^ e := by
  induction e with
  | zero => rfl
  | succ e ih => simpa [binaryPowerBits, List.replicate_succ, Counter.value, pow_succ, Nat.mul_comm]
      using ih

theorem binaryPowerBits_canonical (e : ℕ) : GrowingCounterData.Canonical (binaryPowerBits e) := by
  right
  simp [binaryPowerBits]

def binaryPowerProgram (exponent dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => bitSymbol true) .done))
    (.seq (bzero exponent tmp work) (moveR tmp dst id))

/-- Generate a canonical power-of-two header with every scratch stack restored. -/
theorem binaryPower_exec (body : P → Pr P T Q A U) (exponent dst tmp work : Fin T)
    (hreg : [exponent, dst, tmp, work].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryPowerProgram exponent dst tmp work) (mk v S)
        (6 * (S.R exponent).length + 7)
        (mk v' { S with R := Function.update S.R dst ((binaryPowerBits (S.R exponent).length).map bitSymbol) }) := by
  have hn := hreg
  regs_ne hn
  let S₁ : Stacks T A := { S with R := Function.update S.R dst [bitSymbol true] }
  have hpush : (Action.push (.rt dst) (fun _ => bitSymbol true) .done : Act T Q A U).run (mk v S) =
      mk v S₁ := by simp [Action.run, update_rt, hdst, S₁]
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec body (wR := exponent) (c := tmp) (t := work)
    (by regs_nodup) v S₁ (by simp [S₁, hwork, Ne.symm ‹dst ≠ work›])
  let S₂ : Stacks T A :=
    { S₁ with R := Function.update S₁.R tmp (binSyms (S₁.R exponent).length 0 ++ S₁.R tmp) }
  have hexp : S₁.R exponent = S.R exponent := by simp [S₁, ‹exponent ≠ dst›]
  have htmp₂ : S₂.R tmp = binSyms (S.R exponent).length 0 := by
    simp [S₂, S₁, htmp, Ne.symm ‹dst ≠ tmp›, ‹exponent ≠ dst›]
  have hdst₂ : S₂.R dst = [bitSymbol true] := by simp [S₂, S₁, ‹dst ≠ tmp›]
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp dst (Ne.symm ‹dst ≠ tmp›) id v₁ S₂
  have hfinal : movedR S₂.R tmp dst id (S₂.R tmp) =
      Function.update S.R dst ((binaryPowerBits (S.R exponent).length).map bitSymbol) := by
    funext j
    by_cases hj : j = dst
    · subst j
      simp [movedR, htmp₂, hdst₂, binaryPowerBits, binSyms]
    · by_cases hk : j = tmp
      · subst j
        simp [movedR, Ne.symm ‹dst ≠ tmp›, htmp]
      · simp [movedR, S₂, S₁, hj, hk]
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  refine Exec.cast (Exec.seq (hpush ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq he₁ he₂)) ?_ ?_
  · rw [hexp, htmp₂]
    simp
    omega
  · simp only [hfinal]
    rfl

end IntegerMultBounds.MathlibTM2.Routing
