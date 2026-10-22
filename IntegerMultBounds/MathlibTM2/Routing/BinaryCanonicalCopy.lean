module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalExec
public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-! Canonical binary copies with a restored padded source and scratch bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def binaryCanonicalCopyProgram {T Q A : ℕ} {P U : Type}
    (src dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (bcopy src dst tmp work) (binaryCanonicalProgram dst tmp)

theorem binaryCanonicalCopy_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src dst tmp work : Fin T)
    (hregs : [src, dst, tmp, work].Nodup) (L x : ℕ) (hx : x < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L x)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (bs : List Bool) (v' : HS T Q A U), GrowingCounterData.Canonical bs ∧
      Counter.value bs = x ∧ bs.length ≤ L ∧ v'.user = v.user ∧
      Exec body (binaryCanonicalCopyProgram src dst tmp work) (mk v S) (10 * L + 12)
        (mk v' { S with R := Function.update S.R dst (bs.map bitSymbol) }) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hregs v S htmp hwork
  rw [hdst, List.append_nil, hsrc, length_binSyms] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (binSyms L x) }
  obtain ⟨bs, v₂, hc, hv, hl, hu₂, he₂⟩ := binaryCanonical_exec body dst tmp ‹dst ≠ tmp› L x hx v₁ S₁
    (by simp [S₁]) (by simp [S₁, Ne.symm ‹dst ≠ tmp›, htmp])
  have hfinal : Function.update S₁.R dst (bs.map bitSymbol) = Function.update S.R dst (bs.map bitSymbol) := by
    simp only [S₁, Function.update_idem]
  rw [hfinal] at he₂
  refine ⟨bs, v₂, hc, hv, hl, hu₂.trans hu₁, ?_⟩
  have hex := Exec.seq he₁ he₂
  have htime : (6 * L + 6) + (4 * L + 6) = 10 * L + 12 := by omega
  rw [htime] at hex
  exact hex

end IntegerMultBounds.MathlibTM2.Routing
