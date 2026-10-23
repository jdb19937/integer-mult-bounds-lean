module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryAffinePosition
public import IntegerMultBounds.MathlibTM2.Routing.SparseSourceCoordinateEmit

/-! Generate and emit a mirrored source coordinate from live affine slot
parameters. The position operand is generated and erased within this execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineSourceCoordinateProgram (index stride product offset pos muls mult last wire one selector gap dst tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (binaryAffinePositionProgram index stride product offset pos muls mult tx ty tz cy)
    (.seq (sparseSourceCoordinateProgram last pos wire one selector gap dst tx ty tz cy) (bclear pos))

theorem affineSourceCoordinate_exec (body : P → Pr P T Q A U)
    (index stride product offset pos muls mult last wire one selector gap dst tx ty tz cy : Fin T)
    (hregs : [index, stride, product, offset, pos, muls, mult, last, wire, one, selector, gap, dst, tx, ty, tz].Nodup)
    (hcyProduct : cy ≠ product) (hcyMuls : cy ≠ muls) (hcyOffset : cy ≠ offset)
    (hcyWire : cy ≠ wire) (hcyOne : cy ≠ one) (hcyLast : cy ≠ last) (hcyPos : cy ≠ pos)
    (Li Lk Ls i k o N q : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hN : N < 2 ^ (Li + Lk)) (hpos : i * k + o < N) (hq : q + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R index = binSyms Li i) (hstride : S.R stride = binSyms Lk k)
    (hoffset : S.R offset = binSyms (Li + Lk) o) (hlast : S.R last = binSyms (Li + Lk) (N - 1))
    (hwire : S.R wire = binSyms Ls q) (hone : S.R one = binSyms Ls 1)
    (hproduct : S.R product = []) (hposition : S.R pos = []) (hmuls : S.R muls = []) (hmult : S.R mult = [])
    (hselector : S.R selector = []) (hgap : S.R gap = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ Li * (12 * (Li + Lk) + 20) + 44 * (Li + Lk) + 16 * Ls + 71 ∧
      Exec body (affineSourceCoordinateProgram index stride product offset pos muls mult last wire one selector gap dst tx ty tz cy)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (binSyms (Li + Lk) (N - 1 - (i * k + o)) ++ separator :: (binSyms Ls (q + 1) ++ separator :: S.R dst)) }) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := binaryAffinePosition_exec body index stride product offset pos muls mult tx ty tz cy
    (by regs_nodup) hcyProduct hcyMuls hcyOffset Li Lk i k o hi hk (by omega) v S
    hindex hstride hoffset hproduct hposition hmuls hmult htx hty htz
  let S₁ : Stacks T A := { S with R := Function.update S.R pos (binSyms (Li + Lk) (i * k + o)) }
  have hkeep (j : Fin T) (hj : j ≠ pos) : S₁.R j = S.R j := Function.update_of_ne hj _ _
  obtain ⟨v₂, hu₂, he₂⟩ := sparseSourceCoordinate_exec body last pos wire one selector gap dst tx ty tz cy
    (by regs_nodup) hcyWire hcyOne hcyLast hcyPos (Li + Lk) Ls N (i * k + o) q hN hpos hq v₁ S₁
    ((hkeep last (Ne.symm ‹pos ≠ last›)).trans hlast) (by simp [S₁])
    ((hkeep wire (Ne.symm ‹pos ≠ wire›)).trans hwire) ((hkeep one (Ne.symm ‹pos ≠ one›)).trans hone)
    ((hkeep selector (Ne.symm ‹pos ≠ selector›)).trans hselector) ((hkeep gap (Ne.symm ‹pos ≠ gap›)).trans hgap)
    ((hkeep tx (Ne.symm ‹pos ≠ tx›)).trans htx)
    ((hkeep ty (Ne.symm ‹pos ≠ ty›)).trans hty) ((hkeep tz (Ne.symm ‹pos ≠ tz›)).trans htz)
  rw [hkeep dst (Ne.symm ‹pos ≠ dst›)] at he₂
  let out := binSyms (Li + Lk) (N - 1 - (i * k + o)) ++ separator :: (binSyms Ls (q + 1) ++ separator :: S.R dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body pos v₂ S₂
  have hp : S₂.R pos = binSyms (Li + Lk) (i * k + o) := by simp [S₂, S₁, ‹pos ≠ dst›]
  have hf : Function.update S₂.R pos [] = Function.update S.R dst out := by
    funext j
    by_cases hp : j = pos
    · subst j; simp [‹pos ≠ dst›, hposition]
    · by_cases hd : j = dst
      · subst j; simp [S₂, S₁, hp]
      · simp [S₂, S₁, hp, hd]
  rw [hf, hp, length_binSyms] at he₃
  exact ⟨v₃, n₁ + ((16 * (Li + Lk) + 16 * Ls + 35) + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
