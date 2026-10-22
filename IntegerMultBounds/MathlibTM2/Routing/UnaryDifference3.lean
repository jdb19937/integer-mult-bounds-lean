module

public import IntegerMultBounds.MathlibTM2.Routing.UnaryDifference

/-! Generate an interval exponent x-y-z from three restored binary operands. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive Difference3Reg where
  | x | y | z | next | bin | dst | work | tx | ty | tz | cy
  deriving DecidableEq

def unaryDifference3Program {T Q A : ℕ} {P U : Type} (rg : Difference3Reg → Fin T) : Pr P T Q A U :=
  .seq (bsub (rg .x) (rg .y) (rg .next) (rg .tx) (rg .ty) (rg .tz) (rg .cy))
    (.seq (unaryDifferenceProgram (rg .next) (rg .z) (rg .bin) (rg .dst) (rg .work)
      (rg .tx) (rg .ty) (rg .tz) (rg .cy)) (bclear (rg .next)))

/-- Both subtractions, unary conversion and intermediate cleanup execute.
Only the unary destination changes; all three binary inputs are restored. -/
theorem unaryDifference3_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : Difference3Reg → Fin T) (hrg : Function.Injective rg)
    (L x y z : ℕ) (hx : x < 2 ^ L) (hyx : y ≤ x) (hzy : z ≤ x - y)
    (v : HS T Q A U) (S : Stacks T A)
    (hxs : S.R (rg .x) = binSyms L x) (hys : S.R (rg .y) = binSyms L y)
    (hzs : S.R (rg .z) = binSyms L z)
    (hnext : S.R (rg .next) = []) (hbin : S.R (rg .bin) = []) (hdst : S.R (rg .dst) = [])
    (hwork : S.R (rg .work) = []) (htx : S.R (rg .tx) = [])
    (hty : S.R (rg .ty) = []) (htz : S.R (rg .tz) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * (x - y - z) + 31) + 2 * (x - y - z) + 26 ∧
      Exec body (unaryDifference3Program rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .dst) (List.replicate (x - y - z) tick) }) := by
  have hy : y < 2 ^ L := by omega
  have hd : x - y < 2 ^ L := by omega
  have hmod : (x + 2 ^ L - y) % 2 ^ L = x - y := by
    rw [show x + 2 ^ L - y = (x - y) + 2 ^ L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := bsub_exec body (a := rg .x) (b := rg .y) (c := rg .next)
    (tx := rg .tx) (ty := rg .ty) (tz := rg .tz) (cy := rg .cy)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    hx hy v S hxs hys htx hty htz
  rw [hmod, hnext, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .next) (binSyms L (x - y)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryDifference_exec body
    (rg .next) (rg .z) (rg .bin) (rg .dst) (rg .work) (rg .tx) (rg .ty) (rg .tz) (rg .cy)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L (x - y) z hd hzy v₁ S₁ (by simp [S₁]) (by simp [S₁, hrg.eq_iff, hzs])
    (by simp [S₁, hrg.eq_iff, hbin]) (by simp [S₁, hrg.eq_iff, hdst])
    (by simp [S₁, hrg.eq_iff, hwork]) (by simp [S₁, hrg.eq_iff, htx])
    (by simp [S₁, hrg.eq_iff, hty]) (by simp [S₁, hrg.eq_iff, htz])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) (List.replicate (x - y - z) tick) }
  have hnext₂ : S₂.R (rg .next) = binSyms L (x - y) := by simp [S₂, S₁, hrg.eq_iff]
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .next) v₂ S₂
  have hfinal : Function.update S₂.R (rg .next) [] =
      Function.update S.R (rg .dst) (List.replicate (x - y - z) tick) := by
    funext j
    by_cases hj : j = rg .next
    · subst j; simp [hrg.eq_iff, hnext]
    · by_cases hk : j = rg .dst
      · subst j; simp [S₂, hj]
      · simp [S₂, S₁, hj, hk]
  rw [hnext₂, length_binSyms, hfinal] at he₃
  refine ⟨v₃, (8 * L + 8) + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have he : L * (4 * (x - y - z) + 31) = 10 * L + L * (4 * (x - y - z) + 21) := by ring
  rw [he]
  omega

end IntegerMultBounds.MathlibTM2.Routing
