module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPower

/-!
# Executed padded one-hot source masks

Generate a power word from the live source-coordinate tape, then append high
zeros from a second tape. Both inputs and all scratch are restored. The program
is independent of the coordinate and address width.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

/-- Binary counter words are the host representation of their own values. -/
theorem binaryBits_value_repr (bs : List Bool) : binBits bs.length (Counter.value bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, binBits_succ]
    cases b <;> simp [Counter.value, Nat.testBit_zero, Nat.add_mul_div_left, ih]

/-- Identify the generated power word with a host arithmetic register. -/
theorem binaryPowerBits_binSyms (s : ℕ) :
    ((binaryPowerBits s).map bitSymbol : List (Fin (A + 4))) = binSyms (s + 1) (2 ^ s) := by
  have h := binaryBits_value_repr (binaryPowerBits s)
  rw [binaryPowerBits_value] at h
  have hl : (binaryPowerBits s).length = s + 1 := by simp [binaryPowerBits]
  rw [hl] at h
  rw [binSyms_eq, h]

def sourceMaskProgram (source high dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (binaryPowerProgram source dst tmp work) (bpad dst high tmp work)

/-- Construct the actual full-width mask with exact cost and complete frame. -/
theorem sourceMask_exec (body : P → Pr P T Q A U) (source high dst tmp work : Fin T)
    (hreg : [source, high, dst, tmp, work].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sourceMaskProgram source high dst tmp work) (mk v S)
        (10 * (S.R source).length + 6 * (S.R high).length + 19)
        (mk v' { S with R := Function.update S.R dst (binSyms
          ((S.R source).length + 1 + (S.R high).length) (2 ^ (S.R source).length)) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := binaryPower_exec body source dst tmp work (by regs_nodup) v S hdst htmp hwork
  let S₁ : Stacks T A :=
    { S with R := Function.update S.R dst ((binaryPowerBits (S.R source).length).map bitSymbol) }
  have hhigh : S₁.R high = S.R high := by simp [S₁, ‹high ≠ dst›]
  have hdst₁ : S₁.R dst = binSyms ((S.R source).length + 1) (2 ^ (S.R source).length) := by
    simp only [S₁, Function.update_self, binaryPowerBits_binSyms]
  have hfit : 2 ^ (S.R source).length < 2 ^ ((S.R source).length + 1) := by
    have hp := Nat.two_pow_pos (S.R source).length
    rw [pow_succ]
    omega
  obtain ⟨v₂, hu₂, he₂⟩ := bpad_exec body (a := dst) (eR := high) (t₁ := tmp) (t₂ := work)
    (by regs_nodup) hfit v₁ S₁ hdst₁
    (by simp [S₁, Ne.symm ‹dst ≠ tmp›, htmp])
    (by simp [S₁, Ne.symm ‹dst ≠ work›, hwork])
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  refine Exec.cast (Exec.seq he₁ he₂) ?_ ?_
  · rw [hhigh]
    omega
  · simp only [S₁, Function.update_of_ne ‹high ≠ dst›, Function.update_idem]

end IntegerMultBounds.MathlibTM2.Routing
