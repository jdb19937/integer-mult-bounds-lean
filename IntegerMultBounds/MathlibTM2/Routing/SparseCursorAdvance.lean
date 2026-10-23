module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Set the next sparse cursor to the live target plus one. The old cursor is
erased; target, reusable binary one and arithmetic scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCursorAdvanceProgram (target one cursor tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bclear cursor) (badd target one cursor tx ty tz cy)

theorem sparseCursorAdvance_exec (body : P → Pr P T Q A U)
    (target one cursor tx ty tz cy : Fin T)
    (hreg : [target, one, cursor, tx, ty, tz].Nodup) (hcyTarget : cy ≠ target) (hcyOne : cy ≠ one)
    (L x : ℕ) (hx : x + 1 < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (htarget : S.R target = binSyms L x) (hone : S.R one = binSyms L 1)
    (hcursor : (S.R cursor).length = L)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCursorAdvanceProgram target one cursor tx ty tz cy) (mk v S) (10 * L + 10)
        (mk v' { S with R := Function.update S.R cursor (binSyms L (x + 1)) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, _, he₁⟩ := bclear_exec body cursor v S
  rw [hcursor] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R cursor [] }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec body (a := target) (b := one) (c := cursor)
    (tx := tx) (ty := ty) (tz := tz) (cy := cy) hreg hcyTarget hcyOne
    (by omega : x < 2 ^ L) (by omega : 1 < 2 ^ L) v₁ S₁
    (by simp [S₁, ‹target ≠ cursor›, htarget]) (by simp [S₁, ‹one ≠ cursor›, hone])
    (by simp [S₁, Ne.symm ‹cursor ≠ tx›, htx])
    (by simp [S₁, Ne.symm ‹cursor ≠ ty›, hty]) (by simp [S₁, Ne.symm ‹cursor ≠ tz›, htz])
  have hf : Function.update S₁.R cursor (binSyms L ((x + 1) % 2 ^ L) ++ S₁.R cursor) =
      Function.update S.R cursor (binSyms L (x + 1)) := by simp [S₁, Nat.mod_eq_of_lt hx]
  rw [hf] at he₂
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  have he := Exec.seq he₁ he₂
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
