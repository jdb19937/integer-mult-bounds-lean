module

public import IntegerMultBounds.MathlibTM2.Host.BinArithMul

/-! Generate a sparse slot position offset + index * stride from live binary
operands. Multiplication scratch is reused for addition; the product is erased.
Only the position output changes, and arithmetic cost is fully charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryAffinePositionProgram (index stride product offset dst muls mult tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bmul index stride product muls mult tx ty tz cy)
    (.seq (badd product offset dst tx ty tz cy) (bclear product))

theorem binaryAffinePosition_exec (body : P → Pr P T Q A U)
    (index stride product offset dst muls mult tx ty tz cy : Fin T)
    (hregs : [index, stride, product, offset, dst, muls, mult, tx, ty, tz].Nodup)
    (hcyProduct : cy ≠ product) (hcyMuls : cy ≠ muls) (hcyOffset : cy ≠ offset)
    (Li Lk i k o : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R index = binSyms Li i) (hstride : S.R stride = binSyms Lk k)
    (hoffset : S.R offset = binSyms (Li + Lk) o)
    (hproduct : S.R product = []) (hdst : S.R dst = [])
    (hmuls : S.R muls = []) (hmult : S.R mult = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ Li * (12 * (Li + Lk) + 20) + 26 * (Li + Lk) + 34 ∧
      Exec body (binaryAffinePositionProgram index stride product offset dst muls mult tx ty tz cy)
        (mk v S) steps (mk v' { S with R := Function.update S.R dst (binSyms (Li + Lk) (i * k + o)) }) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := bmul_exec body (a := index) (b := stride) (c := product)
    (s := muls) (t := mult) (tx := tx) (ty := ty) (tz := tz) (cy := cy)
    (by regs_nodup) hcyProduct hcyMuls hi hk v S hindex hstride hproduct hmuls hmult htx hty htz
  let S₁ : Stacks T A := { S with R := Function.update S.R product (binSyms (Li + Lk) (i * k)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec body (a := product) (b := offset) (c := dst)
    (tx := tx) (ty := ty) (tz := tz) (cy := cy) (by regs_nodup) hcyProduct hcyOffset
    (by omega : i * k < 2 ^ (Li + Lk)) (by omega : o < 2 ^ (Li + Lk)) v₁ S₁
    (by simp [S₁]) (by simp [S₁, Ne.symm ‹product ≠ offset›, hoffset])
    (by simp [S₁, Ne.symm ‹product ≠ tx›, htx])
    (by simp [S₁, Ne.symm ‹product ≠ ty›, hty]) (by simp [S₁, Ne.symm ‹product ≠ tz›, htz])
  have hd : S₁.R dst = [] := by simp [S₁, Ne.symm ‹product ≠ dst›, hdst]
  rw [Nat.mod_eq_of_lt hfit, hd, List.append_nil] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (binSyms (Li + Lk) (i * k + o)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body product v₂ S₂
  have hp : S₂.R product = binSyms (Li + Lk) (i * k) := by simp [S₂, S₁, ‹product ≠ dst›]
  have hf : Function.update S₂.R product [] = Function.update S.R dst (binSyms (Li + Lk) (i * k + o)) := by
    funext j
    by_cases hp : j = product
    · subst j; simp [‹product ≠ dst›, hproduct]
    · by_cases hd : j = dst
      · subst j; simp [S₂, S₁, hp]
      · simp [S₂, S₁, hp, hd]
  rw [hf, hp, length_binSyms] at he₃
  exact ⟨v₃, n₁ + ((8 * (Li + Lk) + 8) + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
