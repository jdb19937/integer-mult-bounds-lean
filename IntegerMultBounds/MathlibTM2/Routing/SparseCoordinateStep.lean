module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateEmit
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorAdvance

/-! One sparse-coordinate iteration emits the compact gap/selector pair and
advances the live cursor. Every other tape is restored and both phases charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCoordinateStepProgram (target cursor gap entry one dst tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (sparseCoordinateEmitProgram target cursor gap entry dst tx ty tz cy)
    (sparseCursorAdvanceProgram target one cursor tx ty tz cy)

theorem sparseCoordinateStep_exec (body : P → Pr P T Q A U)
    (target cursor gap entry one dst tx ty tz cy : Fin T)
    (hregs : [target, cursor, gap, entry, one, dst, tx, ty, tz].Nodup)
    (hcyTarget : cy ≠ target) (hcyCursor : cy ≠ cursor) (hcyOne : cy ≠ one)
    (L Ls x y q : ℕ) (hx : x + 1 < 2 ^ L) (hyx : y ≤ x)
    (v : HS T Q A U) (S : Stacks T A)
    (htarget : S.R target = binSyms L x) (hcursor : S.R cursor = binSyms L y)
    (hentry : S.R entry = binSyms Ls q) (hone : S.R one = binSyms L 1)
    (hgap : S.R gap = []) (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCoordinateStepProgram target cursor gap entry one dst tx ty tz cy)
        (mk v S) (26 * L + 6 * Ls + 35)
        (mk v' { S with R := Function.update (Function.update S.R dst (binSyms L (x - y) ++ separator :: (binSyms Ls q ++ separator :: S.R dst))) cursor (binSyms L (x + 1)) }) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := sparseCoordinateEmit_exec body target cursor gap entry dst tx ty tz cy
    (by regs_nodup) hcyTarget hcyCursor L Ls x y q (by omega) hyx v S htarget hcursor hentry hgap htx hty htz
  let out := binSyms L (x - y) ++ separator :: (binSyms Ls q ++ separator :: S.R dst)
  let S₁ : Stacks T A := { S with R := Function.update S.R dst out }
  have hk (j : Fin T) (hj : j ≠ dst) : S₁.R j = S.R j := Function.update_of_ne hj _ _
  obtain ⟨v₂, hu₂, he₂⟩ := sparseCursorAdvance_exec body target one cursor tx ty tz cy
    (by regs_nodup) hcyTarget hcyOne L x hx v₁ S₁
    ((hk target ‹target ≠ dst›).trans htarget) ((hk one ‹one ≠ dst›).trans hone)
    (by rw [hk cursor ‹cursor ≠ dst›, hcursor, length_binSyms])
    ((hk tx (Ne.symm ‹dst ≠ tx›)).trans htx)
    ((hk ty (Ne.symm ‹dst ≠ ty›)).trans hty) ((hk tz (Ne.symm ‹dst ≠ tz›)).trans htz)
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  have he := Exec.seq he₁ he₂
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
