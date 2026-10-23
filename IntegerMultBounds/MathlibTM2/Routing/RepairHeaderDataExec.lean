module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderData

/-! Executed header generation establishes repair readiness from the reduced
initial-data contract. Width and block hypotheses are derived from that data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem repairHeaderData_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairHeaderT Q A U) (p : Par) (X rb R B wb wm wp wk Lr Lw : ℕ)
    (hR : R < 2 ^ Lr) (hR0 : 0 < R) (hw : p.wc < 2 ^ Lw) (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (v : HS repairHeaderT Q A U) (S : Stacks repairHeaderT A)
    (data : RepairPendingHeaderData p X rb wb wm wp wk R B (fun i => S.R (repairHeaderRawCore i)))
    (hrowInput : S.R (sharedHeaderBinary 0) = binSyms Lr R)
    (hwidthInput : S.R (sharedHeaderBinary 1) = binSyms Lw p.wc)
    (hheaders : ∀ c i, S.R (repairSharedHeaderBank c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (sharedHeaderWork r) = []) :
    let generated := repairHeaderPairBank p X rb R B repairSharedHeaderBank S.R
    ∃ (v' : HS repairHeaderT Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * (14 * (p.wc + p.wy + X) + 18 * Lr + 24 * Lw + 52 * wb + 280) ∧
      Exec body (binaryRepairHeaderPairProgram sharedHeaderBinary repairSharedHeaderBank) (mk v S) m
        (mk v' { S with R := generated }) ∧
      RepairPendingMaskData p X rb wb wm wp wk R B (repairCanonicalHeaders p X rb R B)
        (fun i => generated (repairHeaderRawCore i)) := by
  obtain ⟨v', m, hu, hm, he⟩ := repairSharedHeaders_exec body p X rb R B wb Lr Lw hR hR0 hw data.block_lt hB0
    v S data.widths hrowInput hwidthInput data.block hheaders hwork
  exact ⟨v', m, hu, hm, he, data.generated p X rb⟩

end
end IntegerMultBounds.MathlibTM2.Routing
