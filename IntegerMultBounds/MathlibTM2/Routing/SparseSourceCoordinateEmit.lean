module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateEmit

/-! Generate a mirrored target/source coordinate frame from live binary values.
Present wire q is encoded as selector q+1; no prepared selector word is supplied.
Both arithmetic temporaries are erased and every input tape restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseSourceCoordinateProgram (last pos wire one selector gap dst tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (badd wire one selector tx ty tz cy)
    (.seq (sparseCoordinateEmitProgram last pos gap selector dst tx ty tz cy) (bclear selector))

theorem sparseSourceCoordinate_exec (body : P → Pr P T Q A U)
    (last pos wire one selector gap dst tx ty tz cy : Fin T)
    (hregs : [last, pos, wire, one, selector, gap, dst, tx, ty, tz].Nodup)
    (hcyWire : cy ≠ wire) (hcyOne : cy ≠ one) (hcyLast : cy ≠ last) (hcyPos : cy ≠ pos)
    (L Ls N position q : ℕ) (hN : N < 2 ^ L) (hpos : position < N) (hq : q + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hlast : S.R last = binSyms L (N - 1)) (hposition : S.R pos = binSyms L position)
    (hwire : S.R wire = binSyms Ls q) (hone : S.R one = binSyms Ls 1)
    (hselector : S.R selector = []) (hgap : S.R gap = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseSourceCoordinateProgram last pos wire one selector gap dst tx ty tz cy)
        (mk v S) (16 * L + 16 * Ls + 35)
        (mk v' { S with R := Function.update S.R dst (binSyms L (N - 1 - position) ++ separator :: (binSyms Ls (q + 1) ++ separator :: S.R dst)) }) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := badd_exec body (a := wire) (b := one) (c := selector)
    (tx := tx) (ty := ty) (tz := tz) (cy := cy) (by regs_nodup) hcyWire hcyOne
    (by omega : q < 2 ^ Ls) (by omega : 1 < 2 ^ Ls) v S hwire hone htx hty htz
  rw [Nat.mod_eq_of_lt hq, hselector, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R selector (binSyms Ls (q + 1)) }
  obtain ⟨v₂, hu₂, he₂⟩ := sparseCoordinateEmit_exec body last pos gap selector dst tx ty tz cy
    (by regs_nodup) hcyLast hcyPos L Ls (N - 1) position (q + 1) (by omega) (by omega) v₁ S₁
    (by simp [S₁, ‹last ≠ selector›, hlast]) (by simp [S₁, ‹pos ≠ selector›, hposition])
    (by simp [S₁]) (by simp [S₁, Ne.symm ‹selector ≠ gap›, hgap])
    (by simp [S₁, Ne.symm ‹selector ≠ tx›, htx])
    (by simp [S₁, Ne.symm ‹selector ≠ ty›, hty]) (by simp [S₁, Ne.symm ‹selector ≠ tz›, htz])
  have hd : S₁.R dst = S.R dst := by simp [S₁, Ne.symm ‹selector ≠ dst›]
  rw [hd] at he₂
  let out := binSyms L (N - 1 - position) ++ separator :: (binSyms Ls (q + 1) ++ separator :: S.R dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body selector v₂ S₂
  have hs : S₂.R selector = binSyms Ls (q + 1) := by simp [S₂, S₁, ‹selector ≠ dst›]
  have hf : Function.update S₂.R selector [] = Function.update S.R dst out := by
    funext j
    by_cases hs : j = selector
    · subst j; simp [‹selector ≠ dst›, hselector]
    · by_cases hd : j = dst
      · subst j; simp [S₂, S₁, hs]
      · simp [S₂, S₁, hs, hd]
  rw [hf, hs, length_binSyms] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
