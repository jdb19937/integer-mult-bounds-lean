module

public import IntegerMultBounds.MathlibTM2.Routing.UnaryDifference3
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! All three interval-exchange exponent words from binary coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive ExchangeExponentReg where
  | width | lower | upper | span | rowExp | gapExp | lowerExp | scratch (i : Fin 7)
  deriving DecidableEq

def exchangeExponentDifference (row : Bool) : Difference3Reg → ExchangeExponentReg
  | .x => if row then .width else .upper
  | .y => if row then .upper else .lower
  | .z => .span
  | .next => .scratch 0
  | .bin => .scratch 1
  | .dst => if row then .rowExp else .gapExp
  | .work => .scratch 2
  | .tx => .scratch 3
  | .ty => .scratch 4
  | .tz => .scratch 5
  | .cy => .scratch 6

theorem exchangeExponentDifference_injective (row : Bool) : Function.Injective (exchangeExponentDifference row) := by
  cases row <;> intro i j h <;> cases i <;> cases j <;> simp_all [exchangeExponentDifference]

def exchangeExponentBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (n a b w : ℕ) :=
  Function.update (Function.update (Function.update R (rg .lowerExp) (List.replicate a tick))
    (rg .rowExp) (List.replicate (n - b - w) tick)) (rg .gapExp) (List.replicate (b - a - w) tick)

def exchangeExponentProgram {T Q A : ℕ} {P U : Type} (rg : ExchangeExponentReg → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg .lower) (rg .lowerExp) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)))
    (.seq (unaryDifference3Program (rg ∘ exchangeExponentDifference true))
      (unaryDifference3Program (rg ∘ exchangeExponentDifference false)))

def exchangeExponentPrivate {T : ℕ} (rg : ExchangeExponentReg → Fin T) : List (Fin T) :=
  [rg .lowerExp, rg .rowExp, rg .gapExp]

theorem exchangeExponentBank_keep {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (n a b w : ℕ) (j : Fin T)
    (hj : j ∉ exchangeExponentPrivate rg) : exchangeExponentBank R rg n a b w j = R j := by
  simp only [exchangeExponentPrivate, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [exchangeExponentBank, hj.1, hj.2.1, hj.2.2]

theorem exchangeExponentBank_restore {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (n a b w : ℕ)
    (hlower : R (rg .lowerExp) = []) (hrow : R (rg .rowExp) = []) (hgap : R (rg .gapExp) = []) :
    metadataCleared (exchangeExponentBank R rg n a b w) (exchangeExponentPrivate rg) = R := by
  funext j
  by_cases hj : j ∈ exchangeExponentPrivate rg
  · rw [metadataCleared_at _ _ j hj]
    simp only [exchangeExponentPrivate, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [hlower, hrow, hgap]
  · rw [metadataCleared_keep _ _ j hj, exchangeExponentBank_keep R rg n a b w j hj]

theorem exchangeExponent_cleanCost {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (hrg : Function.Injective rg)
    (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n) :
    metadataCleanCost (exchangeExponentBank R rg n a b w) (exchangeExponentPrivate rg) =
      2 * (n - 2 * w) + 7 := by
  simp [exchangeExponentBank, exchangeExponentPrivate, metadataCleanCost, hrg.eq_iff]
  omega

theorem exchangeExponents_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : ExchangeExponentReg → Fin T) (hrg : Function.Injective rg)
    (L n a b w : ℕ) (hn : n < 2 ^ L) (hab : a + w ≤ b) (hb : b + w ≤ n)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L n) (hlower : S.R (rg .lower) = binSyms L a)
    (hupper : S.R (rg .upper) = binSyms L b) (hspan : S.R (rg .span) = binSyms L w)
    (hlower0 : S.R (rg .lowerExp) = []) (hrow0 : S.R (rg .rowExp) = []) (hgap0 : S.R (rg .gapExp) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 3 * (L * (4 * n + 31) + 2 * n + 26) ∧
      Exec body (exchangeExponentProgram rg) (mk v S) m
        (mk v' { S with R := exchangeExponentBank S.R rg n a b w }) := by
  have ha : a < 2 ^ L := by omega
  have hbf : b < 2 ^ L := by omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := rg .lower) (z := rg .lowerExp)
    (w := rg (.scratch 2)) (t := rg (.scratch 3)) (t₂ := rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff]) ha v S hlower (hscratch 2) (hscratch 3) (hscratch 4)
  rw [hlower0, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .lowerExp) (List.replicate a tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryDifference3_exec body (rg ∘ exchangeExponentDifference true)
    (hrg.comp (exchangeExponentDifference_injective true)) L n b w hn (by omega) (by omega) v₁ S₁
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hwidth])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hupper])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hspan])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hrow0])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₁, hrg.eq_iff, hscratch])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .rowExp) (List.replicate (n - b - w) tick) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := unaryDifference3_exec body (rg ∘ exchangeExponentDifference false)
    (hrg.comp (exchangeExponentDifference_injective false)) L b a w hbf (by omega) (by omega) v₂ S₂
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hupper])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hlower])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hspan])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hgap0])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [exchangeExponentDifference, S₂, S₁, hrg.eq_iff, hscratch])
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have h₁ := Nat.mul_le_mul_left L (by omega : 4 * a + 11 ≤ 4 * n + 31)
  have h₂ := Nat.mul_le_mul_left L (by omega : 4 * (n - b - w) + 31 ≤ 4 * n + 31)
  have h₃ := Nat.mul_le_mul_left L (by omega : 4 * (b - a - w) + 31 ≤ 4 * n + 31)
  omega

end IntegerMultBounds.MathlibTM2.Routing
