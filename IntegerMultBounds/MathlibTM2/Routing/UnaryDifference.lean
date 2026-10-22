module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-!
# Executed unary differences of live binary dimensions

Subtract two live binary dimensions, build the unary difference, and clear the
binary intermediate. All original inputs and scratch tapes are restored. This
supplies coordinate and padding tapes to the instruction compiler.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

variable {T Q A : ℕ} {P U : Type}

def unaryDifferenceProgram (a b bin dst work tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bsub a b bin tx ty tz cy)
    (.seq (toUnary bin dst work tx ty) (bclear bin))

private theorem unaryDifference_mod (L x y : ℕ) (hx : x < 2 ^ L) (hyx : y ≤ x) :
    (x + 2 ^ L - y) % 2 ^ L = x - y := by
  have he : x + 2 ^ L - y = (x - y) + 2 ^ L := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Construct a unary difference with restored operands and complete cleanup. -/
theorem unaryDifference_exec (body : P → Pr P T Q A U) (a b bin dst work tx ty tz cy : Fin T)
    (hreg : [a, b, bin, dst, work, tx, ty, tz].Nodup) (hca : cy ≠ a) (hcb : cy ≠ b)
    (L x y : ℕ) (hx : x < 2 ^ L) (hyx : y ≤ x)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y)
    (hbin : S.R bin = []) (hdst : S.R dst = []) (hwork : S.R work = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * (x - y) + 21) + 2 * (x - y) + 16 ∧
      Exec body (unaryDifferenceProgram a b bin dst work tx ty tz cy) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (List.replicate (x - y) tick) }) := by
  have hn := hreg
  regs_ne hn
  have hy : y < 2 ^ L := by omega
  have hd : x - y < 2 ^ L := by omega
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := bsub_exec body (a := a) (b := b) (c := bin)
    (tx := tx) (ty := ty) (tz := tz) (cy := cy) (by regs_nodup) hca hcb hx hy v S ha hb htx hty htz
  rw [unaryDifference_mod L x y hx hyx, hbin, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R bin (binSyms L (x - y)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toUnary_exec body (a := bin) (z := dst) (w := work)
    (t := tx) (t₂ := ty) (by regs_nodup) hd v₁ S₁ (by simp [S₁])
    (by simp [S₁, Ne.symm ‹bin ≠ work›, hwork])
    (by simp [S₁, Ne.symm ‹bin ≠ tx›, htx])
    (by simp [S₁, Ne.symm ‹bin ≠ ty›, hty])
  have hdst₁ : S₁.R dst = [] := by simp [S₁, Ne.symm ‹bin ≠ dst›, hdst]
  rw [hdst₁, List.append_nil] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (List.replicate (x - y) tick) }
  have hbin₂ : S₂.R bin = binSyms L (x - y) := by simp [S₂, S₁, ‹bin ≠ dst›]
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body bin v₂ S₂
  have hfinal : Function.update S₂.R bin [] = Function.update S.R dst (List.replicate (x - y) tick) := by
    funext j
    by_cases hj : j = bin
    · subst j; simp [‹bin ≠ dst›, hbin]
    · by_cases hk : j = dst
      · subst j; simp [S₂, Ne.symm ‹bin ≠ dst›]
      · simp [S₂, S₁, hj, hk]
  refine ⟨v₃, (8 * L + 8) + (m₂ + (2 * (S₂.R bin).length + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hbin₂, length_binSyms]
    have he : L * (4 * (x - y) + 21) = 8 * L + L * (4 * (x - y) + 11) + 2 * L := by ring
    rw [he]
    omega
  · refine Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_
    simp only [hfinal]
    rfl

end IntegerMultBounds.MathlibTM2.Routing
