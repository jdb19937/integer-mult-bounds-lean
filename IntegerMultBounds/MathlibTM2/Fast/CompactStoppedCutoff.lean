module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedDigitsSpec

/-!
# Executed cutoff provisioning from a supplied threshold

Copy the threshold length into s29, count its nonzero base-m quotients into
s22, then pop once. The caller chooses the source wire; its entire contents
are preserved. No existing metadata wire is assigned a new meaning here.
Computing the threshold from the global precision/leaf budget, and absorbing
this explicit unary preparation cost, remain separate obligations.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

noncomputable def compactStoppedCutoff (source : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg source) (sreg (.s 29)) (sreg (.s 2))) <|
  .seq (synCntLoop m (.s 29) (.s 22) source) (synPop (sreg (.s 22)))

def compactStoppedCutoffCost (T : ℕ) : ℕ := (4*T+4)+(synCntCost m T T+1)

/-- A positive threshold produces its floor base-m logarithm on s22. The work
wire s29 returns empty and every other wire, including the source, is restored. -/
theorem sg_compactStoppedCutoff (source : SynW) (v : SynW → List (Fin (A+4)))
    (T : ℕ) (hTpos : 0 < T) (hT : (v source).length = T)
    (hsource2 : source ≠ .s 2) (hsource17 : source ≠ .s 17)
    (hsource22 : source ≠ .s 22) (hsource23 : source ≠ .s 23)
    (hsource29 : source ≠ .s 29)
    (h2 : v (.s 2)=[]) (h17 : v (.s 17)=[]) (h22 : v (.s 22)=[])
    (h23 : v (.s 23)=[]) (h29 : v (.s 29)=[]) :
    LayRuns body (compactStoppedCutoff source) (synG R v)
      (synG R (Function.update v (.s 22) (List.replicate (Nat.log m T) tick)))
      (compactStoppedCutoffCost T) := by
  have hcount : synJk m T T - 1 = Nat.log m T := by
    change synJ T T - 1 = Nat.log m T
    rw [synJ_self_eq (Nat.ne_of_gt hTpos), Nat.add_sub_cancel]
  refine lr_weaken body
    ((sgU_copy body (a:=source) (b:=.s 29) (t:=.s 2) (x:=T) (y:=0)
      hsource29 hsource2 (by decide) h2 hT (by simpa using h29)).seq <|
    (sg_synCntLoop body m m_pos (x:=.s 29) (cnt:=.s 22) (ctr:=source) _ T T
      (by decide) hsource29.symm hsource22.symm (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hsource17 hsource2 hsource23
      (by simp) (by simp [h22]) (by simp [hsource29,hT])
      (by simp [h17]) (by simp [h2]) (by simp [h23])).seq <|
    sgU_pop body (a:=.s 22) (y:=synJk m T T) (by simp)) ?_ le_rfl
  apply congrArg (synG R)
  funext z
  by_cases hz29 : z = .s 29
  · subst z
    simp [div_pow_self, h29]
  by_cases hz22 : z = .s 22
  · subst z
    simp [hcount]
  simp [hz29, hz22]

/-- The runtime-computed cutoff is the largest base-m power not exceeding the
positive supplied threshold. This does not assert that every nonzero digit's
rebased leaf count is itself below that threshold. -/
theorem compactStoppedCutoff_power_bounds (T : ℕ) (hTpos : 0 < T) :
    m^(Nat.log m T) ≤ T ∧ T < m^(Nat.log m T+1) := by
  exact ⟨Nat.pow_log_le_self m (Nat.ne_of_gt hTpos),
    Nat.lt_pow_succ_log_self (by norm_num [m]) T⟩

end IntegerMultBounds.MathlibTM2.Fast
