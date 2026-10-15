module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest

/-! Clear the persistent compact counters, restoring the initially blank bank exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {T Q A : ℕ} {U P : Type}

def compactClear7 (e : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (uclear (e 0)) <| .seq (uclear (e 1)) <| .seq (uclear (e 2)) <|
  .seq (uclear (e 3)) <| .seq (uclear (e 4)) <| .seq (uclear (e 5)) (uclear (e 6))

def compactClear7Cost (values : Fin 7 → ℕ) :=
  (2*values 0+2)+(2*values 1+2)+(2*values 2+2)+(2*values 3+2)+
    (2*values 4+2)+(2*values 5+2)+(2*values 6+2)

theorem compactClear7_runs (body : P → Pr P T Q A U)
    (e : Fin 7 → Fin T) (he : Function.Injective e) (R : Fin T → List (Fin (A+4)))
    (values : Fin 7 → ℕ) (hz : ∀ i,R (e i)=[]) :
    LayRuns body (compactClear7 e) (compactSetupUpdate7 R e values) R (compactClear7Cost values) := by
  refine lr_weaken body
    ((lr_uclear body (R:=compactSetupUpdate7 R e values) (e 0)).seq <|
    (lr_uclear body (e 1)).seq <| (lr_uclear body (e 2)).seq <|
    (lr_uclear body (e 3)).seq <| (lr_uclear body (e 4)).seq <|
    (lr_uclear body (e 5)).seq <| lr_uclear body (e 6)) ?_ ?_
  · funext z
    by_cases h0 : z=e 0
    · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
    by_cases h1 : z=e 1
    · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
    by_cases h2 : z=e 2
    · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
    by_cases h3 : z=e 3
    · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
    by_cases h4 : z=e 4
    · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
    by_cases h5 : z=e 5
    · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
    by_cases h6 : z=e 6
    · subst z; simp [compactSetupUpdate7,hz]
    simp [compactSetupUpdate7,Function.update_of_ne,h0,h1,h2,h3,h4,h5,h6]
  · simp [compactSetupUpdate7,he.eq_iff,compactClear7Cost,Nat.add_assoc]

/-- Cleanup has no input-data dependency beyond the seven persistent lengths. -/
def compactBasisCleanup : Pr P (nT CompactHostBReg) Q A U := compactClear7 compactBasisPersistent

theorem compactBasisCleanup_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (values : Fin 7 → ℕ)
    (hz : ∀ i,R (compactBasisPersistent i)=[]) :
    LayRuns body compactBasisCleanup (compactSetupUpdate7 R compactBasisPersistent values) R
      (compactClear7Cost values) :=
  compactClear7_runs body compactBasisPersistent compactBasisPersistent_injective R values hz

end
end IntegerMultBounds.MathlibTM2.LayerMachine
