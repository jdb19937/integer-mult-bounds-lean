module

public import IntegerMultBounds.MathlibTM2.Routing.UnaryComplement
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryXor

/-! Executed outer-row exponent construction, including the zero-target case. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

variable {T Q A : ℕ} {P U : Type}

def elementaryRowExponentProgram (gate width target next bin dst work tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR gate)) (.cond (·.flag)
    (unaryComplementProgram width target next bin dst work tx ty tz cy)
    (toUnary width dst work tx ty))

/-- Read the live target gate and construct precisely the outer-row exponent.
All binary inputs, the unary gate and every temporary tape are restored. -/
theorem elementaryRowExponent_exec {n : ℕ} (body : P → Pr P T Q A U) (target : Fin n)
    (gate width targetBin next bin dst work tx ty tz cy : Fin T)
    (hreg : [width, targetBin, next, bin, dst, work, tx, ty, tz].Nodup)
    (hcw : cy ≠ width) (hcn : cy ≠ next)
    (L : ℕ) (hn : n < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hgate : (S.R gate).length = target.val)
    (hwidth : S.R width = binSyms L n) (htarget : S.R targetBin = binSyms L target.val)
    (hnext : S.R next = []) (hbin : S.R bin = []) (hdst : S.R dst = [])
    (hwork : S.R work = []) (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ L * (4 * n + 33) + 2 * n + 31 ∧
      Exec body (elementaryRowExponentProgram gate width targetBin next bin dst work tx ty tz cy) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (List.replicate (n - (target.val + (elementarySwapSpec target).w)) tick) }) := by
  have hregs := hreg
  regs_ne hregs
  let v₀ := { v with flag := (S.R gate).head?.isSome }
  have hp : (peekR gate : Act T Q A U).run (mk v S) = mk v₀ S := rfl
  cases hg : (S.R gate).head?.isSome with
  | false =>
    have hz : S.R gate = [] := by simpa using hg
    have ht : target.val = 0 := by rw [hz] at hgate; simpa using hgate.symm
    obtain ⟨v', m, hu, hm, he⟩ := toUnary_exec body (a := width) (z := dst) (w := work)
      (t := tx) (t₂ := ty) (by regs_nodup) hn v₀ S hwidth hwork htx hty
    rw [hdst, List.append_nil] at he
    have hbound := Nat.mul_le_mul_left L (by omega : 4 * n + 11 ≤ 4 * n + 33)
    refine ⟨v', 1 + (m + 1), hu, by omega, ?_⟩
    have hex := Exec.seq (hp ▸ Exec.act (body := body) (peekR gate) (mk v S))
      (Exec.cond_false (f := (·.flag))
        (p := unaryComplementProgram width targetBin next bin dst work tx ty tz cy) hg he)
    simpa only [elementaryRowExponentProgram, elementarySwapSpec, ht, reduceIte, Nat.zero_add, Nat.sub_zero] using hex
  | true =>
    have hne : S.R gate ≠ [] := by simpa using hg
    have ht : target.val ≠ 0 := by
      intro hz
      have hl : (S.R gate).length = 0 := hgate.trans hz
      exact hne (by simpa using hl)
    obtain ⟨v', m, hu, hm, he⟩ := unaryComplement_exec body width targetBin next bin dst work tx ty tz cy
      hreg hcw hcn L n target.val hn target.isLt v₀ S hwidth htarget hnext hbin hdst hwork htx hty htz
    have hd : n - (target.val + 1) ≤ n := Nat.sub_le _ _
    have hbound := Nat.mul_le_mul_left L (by omega : 4 * (n - (target.val + 1)) + 33 ≤ 4 * n + 33)
    refine ⟨v', 1 + (m + 1), hu, by omega, ?_⟩
    have hex := Exec.seq (hp ▸ Exec.act (body := body) (peekR gate) (mk v S))
      (Exec.cond_true (f := (·.flag)) (q := toUnary width dst work tx ty) hg he)
    simpa only [elementaryRowExponentProgram, elementarySwapSpec, ite_eq_right ht] using hex

end IntegerMultBounds.MathlibTM2.Routing
