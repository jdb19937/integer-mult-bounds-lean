module

public import IntegerMultBounds.MathlibTM2.Routing.ExchangeExponents
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy

/-! Binary-only coordinate setup for general interval exchanges. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def exchangeBinarySetupProgram {T Q A : ℕ} {P U : Type}
    (rg : ExchangeExponentReg → Fin T) (canonical : Fin T) : Pr P T Q A U :=
  .seq (exchangeExponentProgram rg)
    (binaryCanonicalCopyProgram (rg .span) canonical (rg (.scratch 3)) (rg (.scratch 4)))

/-- Prepare all unary exponents and the canonical width from padded binary
coordinates. Original inputs and every scratch tape are restored. -/
theorem exchangeBinarySetup_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : ExchangeExponentReg → Fin T) (hrg : Function.Injective rg)
    (canonical : Fin T) (hcanonical : ∀ r, canonical ≠ rg r)
    (L n a b w : ℕ) (hn : n < 2 ^ L) (hab : a + w ≤ b) (hb : b + w ≤ n)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L n) (hlower : S.R (rg .lower) = binSyms L a)
    (hupper : S.R (rg .upper) = binSyms L b) (hspan : S.R (rg .span) = binSyms L w)
    (hlower0 : S.R (rg .lowerExp) = []) (hrow0 : S.R (rg .rowExp) = []) (hgap0 : S.R (rg .gapExp) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) (hcanonical0 : S.R canonical = []) :
    ∃ (bits : List Bool) (v' : HS T Q A U) (m : ℕ), GrowingCounterData.Canonical bits ∧
      Counter.value bits = w ∧ bits.length ≤ L ∧ v'.user = v.user ∧
      m ≤ 3 * (L * (4 * n + 31) + 2 * n + 26) + 10 * L + 12 ∧
      Exec body (exchangeBinarySetupProgram rg canonical) (mk v S) m
        (mk v' { S with R := Function.update (exchangeExponentBank S.R rg n a b w) canonical (bits.map bitSymbol) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := exchangeExponents_exec body rg hrg L n a b w hn hab hb
    v S hwidth hlower hupper hspan hlower0 hrow0 hgap0 hscratch
  let S₁ : Stacks T A := { S with R := exchangeExponentBank S.R rg n a b w }
  obtain ⟨bits, v₂, hc, hv, hl, hu₂, he₂⟩ := binaryCanonicalCopy_exec body
    (rg .span) canonical (rg (.scratch 3)) (rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff, hcanonical, Ne.symm (hcanonical _)])
    L w (by omega) v₁ S₁
    (by simp [S₁, exchangeExponentBank, hrg.eq_iff, hspan])
    (by simp [S₁, exchangeExponentBank, hcanonical, hcanonical0])
    (by simp [S₁, exchangeExponentBank, hrg.eq_iff, hscratch])
    (by simp [S₁, exchangeExponentBank, hrg.eq_iff, hscratch])
  exact ⟨bits, v₂, m₁ + (10 * L + 12), hc, hv, hl, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

def exchangeBinarySetupPrivate {T : ℕ} (rg : ExchangeExponentReg → Fin T) (canonical : Fin T) : List (Fin T) :=
  canonical :: exchangeExponentPrivate rg

theorem exchangeBinarySetup_keep {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (canonical : Fin T) (bits : List Bool) (n a b w : ℕ)
    (j : Fin T) (hj : j ∉ exchangeBinarySetupPrivate rg canonical) :
    Function.update (exchangeExponentBank R rg n a b w) canonical (bits.map bitSymbol) j = R j := by
  have hne : j ≠ canonical := by intro he; exact hj (by simp [exchangeBinarySetupPrivate, he])
  rw [Function.update_of_ne hne]
  exact exchangeExponentBank_keep R rg n a b w j (fun h => hj (List.mem_cons_of_mem _ h))

theorem exchangeBinarySetup_cleanCost {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (hrg : Function.Injective rg)
    (canonical : Fin T) (hcanonical : ∀ r, canonical ≠ rg r)
    (bits : List Bool) (L n a b w : ℕ) (hlength : bits.length ≤ L)
    (hab : a + w ≤ b) (hb : b + w ≤ n) :
    metadataCleanCost (Function.update (exchangeExponentBank R rg n a b w) canonical (bits.map bitSymbol))
      (exchangeBinarySetupPrivate rg canonical) ≤ 2 * n + 2 * L + 9 := by
  have hc : metadataCleanCost
      (Function.update (exchangeExponentBank R rg n a b w) canonical (bits.map bitSymbol))
      (exchangeExponentPrivate rg) = metadataCleanCost (exchangeExponentBank R rg n a b w) (exchangeExponentPrivate rg) := by
    apply metadataCleanCost_congr
    intro j hj
    have hne : j ≠ canonical := by
      simp only [exchangeExponentPrivate, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact (hcanonical _).symm
    exact Function.update_of_ne hne _ _
  simp only [exchangeBinarySetupPrivate, metadataCleanCost, Function.update_self, List.length_map]
  rw [hc, exchangeExponent_cleanCost R rg hrg n a b w hab hb]
  omega

theorem exchangeBinarySetup_restore {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeExponentReg → Fin T) (canonical : Fin T) (bits : List Bool) (n a b w : ℕ)
    (hcanonical : R canonical = []) (hlower : R (rg .lowerExp) = [])
    (hrow : R (rg .rowExp) = []) (hgap : R (rg .gapExp) = []) :
    metadataCleared (Function.update (exchangeExponentBank R rg n a b w) canonical (bits.map bitSymbol))
      (exchangeBinarySetupPrivate rg canonical) = R := by
  have hclear : metadataCleared (Function.update (exchangeExponentBank R rg n a b w) canonical (bits.map bitSymbol))
      (exchangeExponentPrivate rg) = Function.update
        (metadataCleared (exchangeExponentBank R rg n a b w) (exchangeExponentPrivate rg)) canonical
        (if canonical ∈ exchangeExponentPrivate rg then [] else bits.map bitSymbol) := by
    funext j
    by_cases hj : j ∈ exchangeExponentPrivate rg
    · rw [metadataCleared_at _ _ j hj]
      by_cases he : j = canonical
      · subst j; simp [hj]
      · simp [Function.update_of_ne he, metadataCleared_at _ _ j hj]
    · rw [metadataCleared_keep _ _ j hj]
      by_cases he : j = canonical
      · subst j; simp [hj]
      · simp [Function.update_of_ne he, metadataCleared_keep _ _ j hj]
  simp only [exchangeBinarySetupPrivate, metadataCleared]
  rw [hclear, exchangeExponentBank_restore R rg n a b w hlower hrow hgap, Function.update_idem]
  simpa only [hcanonical] using Function.update_eq_self canonical R

end IntegerMultBounds.MathlibTM2.Routing
