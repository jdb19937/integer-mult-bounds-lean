module

public import IntegerMultBounds.MathlibTM2.Routing.SourceMask
public import IntegerMultBounds.MathlibTM2.Routing.RepeatedPhaseMask

/-! Construct one three-mark phase block from live unary low/high counts.
The generated power receives two low one bits; every input and scratch survives. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem binSyms_prefix_two_ones {A : ℕ} (W x : ℕ) :
    binSyms (A := A) (W + 2) (4 * x + 3) = bitSymbol true :: bitSymbol true :: binSyms W x := by
  have hd : (4 * x + 3) / 2 = 2 * x + 1 := by omega
  have hd' : (2 * x + 1) / 2 = x := by omega
  have hm : (4 * x + 3) % 2 = 1 := by omega
  have hm' : (2 * x + 1) % 2 = 1 := by omega
  rw [show W + 2 = (W + 1) + 1 by omega, binSyms_succ, hd, binSyms_succ, hd']
  simp [Nat.testBit_zero, hm, hm']

def phaseBlockFinish {T Q A : ℕ} {U : Type} (dst : Fin T) : Act T Q A U :=
  .push (.rt dst) (fun _ => bitSymbol true) (.push (.rt dst) (fun _ => bitSymbol true) .done)

def phaseBlockProgram {T Q A : ℕ} {P U : Type} (low high dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (sourceMaskProgram low high dst tmp work) (.act (phaseBlockFinish dst))

theorem phaseBlock_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (low high dst tmp work : Fin T)
    (hreg : [low, high, dst, tmp, work].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (phaseBlockProgram low high dst tmp work) (mk v S)
        (10 * (S.R low).length + 6 * (S.R high).length + 20)
        (mk v' { S with R := Function.update S.R dst (binSyms
          ((S.R low).length + (S.R high).length + 3) (phaseBlockValue ((S.R low).length + 1))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := sourceMask_exec body low high dst tmp work hreg v S hdst htmp hwork
  let W := (S.R low).length + 1 + (S.R high).length
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (binSyms W (2 ^ (S.R low).length)) }
  have hv : phaseBlockValue ((S.R low).length + 1) = 4 * 2 ^ (S.R low).length + 3 := by
    simp only [phaseBlockValue, pow_succ]
    ring
  have hw : (S.R low).length + (S.R high).length + 3 = W + 2 := by dsimp [W]; omega
  have hp : (phaseBlockFinish dst : Act T Q A U).run (mk v₁ S₁) =
      mk v₁ { S with R := Function.update S.R dst (binSyms
        ((S.R low).length + (S.R high).length + 3) (phaseBlockValue ((S.R low).length + 1))) } := by
    rw [hv, hw, binSyms_prefix_two_ones]
    simp [phaseBlockFinish, Action.run, update_rt, S₁]
  exact ⟨v₁, hu₁, Exec.cast (Exec.seq he₁ (hp ▸ Exec.act (body := body) _ (mk v₁ S₁))) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
