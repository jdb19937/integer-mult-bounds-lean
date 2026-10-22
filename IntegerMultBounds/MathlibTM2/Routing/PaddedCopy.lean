module

public import IntegerMultBounds.MathlibTM2.Host.BinArithBits
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Executed binary-word copying with one high zero for the repair classifier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def paddedCopy (src dst tmp ctmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => bitSymbol false) .done)) (bcopy src dst tmp ctmp)

theorem paddedCopy_exec (body : P → Pr P T Q A U) {src dst tmp ctmp : Fin T}
    (hregs : [src, dst, tmp, ctmp].Nodup) (w value : ℕ) (hv : value < 2 ^ w)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms w value)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (paddedCopy src dst tmp ctmp) (mk v S) (1 + (6 * w + 6))
        (mk v' { S with R := Function.update S.R dst (binSyms (w + 1) value) }) := by
  have hn := hregs
  regs_ne hn
  let R₁ := Function.update S.R dst [bitSymbol false]
  have hp : (.push (.rt dst) (fun _ => bitSymbol false) .done : Act T Q A U).run (mk v S) =
      mk v { S with R := R₁ } := by simp [Action.run, update_rt, R₁, hdst]
  obtain ⟨v', hu, he⟩ := bcopy_exec body hregs v { S with R := R₁ }
    (by simp [R₁, ne_comm, *]) (by simp [R₁, ne_comm, *])
  have hs : R₁ src = binSyms w value := by simp [R₁, *]
  have hd : R₁ dst = [bitSymbol false] := by simp [R₁]
  dsimp only at he
  rw [hs, hd, length_binSyms] at he
  have hf : Function.update R₁ dst (binSyms w value ++ [bitSymbol false]) =
      Function.update S.R dst (binSyms (w + 1) value) := by
    rw [binSyms_pad w 1 value hv]
    simp [R₁]
  rw [hf] at he
  exact ⟨v', hu, Exec.seq (hp ▸ Exec.act (body := body) _ _) he⟩

end IntegerMultBounds.MathlibTM2.Routing
