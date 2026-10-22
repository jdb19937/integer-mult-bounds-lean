module

public import IntegerMultBounds.MathlibTM2.Routing.SourceMask
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupBank
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryXor

/-! Generate the exact sixth instruction word from live unary coordinate tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

/-- The source mask is computed, rather than supplied as a raw bit word. Unary
coordinate construction is a separate compiler obligation. -/
theorem elementarySourceMask_exec {T Q A n : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (target source : Fin n)
    (coord high dst tmp work : Fin T) (hreg : [coord, high, dst, tmp, work].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hcoord : (S.R coord).length = ((elementarySwapSpec target).coordinate source).val)
    (hhigh : (S.R high).length = n - (((elementarySwapSpec target).coordinate source).val + 1))
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 10 * n + 9 ∧
      Exec body (sourceMaskProgram coord high dst tmp work) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (binSyms n (2 ^ ((elementarySwapSpec target).coordinate source).val)) }) := by
  have hbound := ((elementarySwapSpec target).coordinate source).isLt
  have hn : (S.R coord).length + 1 + (S.R high).length = n := by rw [hcoord, hhigh]; omega
  obtain ⟨v', hu, he⟩ := sourceMask_exec body coord high dst tmp work hreg v S hdst htmp hwork
  refine ⟨v', 10 * (S.R coord).length + 6 * (S.R high).length + 19, hu, by omega, ?_⟩
  rw [hn] at he
  simpa only [hcoord] using he

end IntegerMultBounds.MathlibTM2.Routing
