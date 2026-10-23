module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderLayout

/-! Execute both header generators on the concrete shared repair bank.
Only the ten existing raw header destinations change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem repairCompactSharedHeaders_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairCompactHeaderT Q A U) (p : Par) (X rb R B L Lr Lw : ℕ)
    (hR : R < 2 ^ Lr) (hR0 : 0 < R) (hw : p.wc < 2 ^ Lw)
    (hB : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ L)
    (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (v : HS repairCompactHeaderT Q A U) (S : Stacks repairCompactHeaderT A)
    (hdim : ∀ f, (S.R (sharedHeaderCore (classifierCore (repairCompactConfigurationCore (repairRoutingConfig (.field f)))))).length = selectiveLen p X f)
    (hrowInput : S.R (sharedHeaderBinary 0) = binSyms Lr R)
    (hwidthInput : S.R (sharedHeaderBinary 1) = binSyms Lw p.wc)
    (hblock : S.R (sharedHeaderCore (classifierCore (repairCompactConfigurationCore (repairRoutingConfig .block)))) =
      binSyms L (fieldsLen (selectiveKeyLen p X rb) + B))
    (hheaders : ∀ c i, S.R (repairCompactSharedHeaderBank c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (sharedHeaderWork r) = []) :
    ∃ (v' : HS repairCompactHeaderT Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * (14 * (p.wc + p.wy + X) + 18 * Lr + 24 * Lw + 52 * L + 280) ∧
      Exec body (binaryRepairHeaderPairProgram sharedHeaderBinary repairCompactSharedHeaderBank) (mk v S) m
        (mk v' { S with R := repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank S.R }) := by
  apply binaryRepairHeaderPair_exec body sharedHeaderBinary repairCompactSharedHeaderBank
    repairCompactSharedHeaderBank_injective repairCompactSharedHeaderBinary_separate repairCompactSharedHeaderBank_cross
    p X rb R B L Lr Lw hR hR0 hw hB hB0 v S
  · intro c f
    simpa only [repairCompactSharedHeaderBank_dimension] using hdim f
  · exact hrowInput
  · exact hwidthInput
  · intro c
    simpa only [repairCompactSharedHeaderBank_block] using hblock
  · intro c r hr
    cases r with
    | lowerExp => exact hwork .lower (by intro i; simp)
    | triple => exact hwork .triple (by intro i; simp)
    | base r =>
      cases r with
      | block => exact (hr rfl).elim
      | header i => exact hheaders c i
      | rowExp => exact hwork .rowExp (by intro i; simp)
      | gapExp => exact hwork .gapExp (by intro i; simp)
      | target => exact hwork .target (by intro i; simp)
      | rows => exact hwork .rows (by intro i; simp)
      | scratch i => exact hwork (.scratch i) (by intro j; simp)

end
end IntegerMultBounds.MathlibTM2.Routing
