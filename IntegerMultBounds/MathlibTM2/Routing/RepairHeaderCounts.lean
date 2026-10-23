module

public import IntegerMultBounds.MathlibTM2.Routing.RepairExchangeHeaders
public import IntegerMultBounds.MathlibTM2.Routing.SourceHeader

/-! Construct both R2 header shift counts by copying live dimension tapes.
The fixed lists depend only on the interchange bank, never on numeric widths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

inductive HeaderCountReg where
  | field (i : Fin 5) | row | gap | tmp | work
  deriving DecidableEq

def repairHeaderRowFields (c : Fin 2) : List (Fin 5) := if c = 0 then [0, 4] else [4]
def repairHeaderGapFields (c : Fin 2) : List (Fin 5) := if c = 0 then [1] else [1, 0]

def repairHeaderCountProgram {T Q A : ℕ} {P U : Type} (rg : HeaderCountReg → Fin T) (c : Fin 2) : Pr P T Q A U :=
  .seq (sourceHeader ((repairHeaderRowFields c).map (fun f => rg (.field f))) (rg .row) (rg .tmp) (rg .work))
    (sourceHeader ((repairHeaderGapFields c).map (fun f => rg (.field f))) (rg .gap) (rg .tmp) (rg .work))

def repairHeaderCountBank {T A : ℕ} (rg : HeaderCountReg → Fin T) (c : Fin 2)
    (bank : Fin T → List (Fin (A + 4))) :=
  Function.update (Function.update bank (rg .row) ((repairHeaderRowFields c).flatMap (fun f => bank (rg (.field f)))))
    (rg .gap) ((repairHeaderGapFields c).flatMap (fun f => bank (rg (.field f))))

theorem repairHeaderCounts_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : HeaderCountReg → Fin T) (hrg : Function.Injective rg) (c : Fin 2)
    (v : HS T Q A U) (S : Stacks T A)
    (hrow : S.R (rg .row) = []) (hgap : S.R (rg .gap) = [])
    (htmp : S.R (rg .tmp) = []) (hwork : S.R (rg .work) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (repairHeaderCountProgram rg c) (mk v S)
        (sourceHeaderCost S.R ((repairHeaderRowFields c).map (fun f => rg (.field f))) +
          sourceHeaderCost S.R ((repairHeaderGapFields c).map (fun f => rg (.field f))))
        (mk v' { S with R := repairHeaderCountBank rg c S.R }) := by
  have hf (f : Fin 5) : rg (.field f) ≠ rg .row ∧ rg (.field f) ≠ rg .gap ∧
      rg (.field f) ≠ rg .tmp ∧ rg (.field f) ≠ rg .work := by simp [hrg.eq_iff]
  obtain ⟨v₁, hu₁, he₁⟩ := sourceHeader_exec body ((repairHeaderRowFields c).map (fun f => rg (.field f)))
    (rg .row) (rg .tmp) (rg .work)
    (by intro f hm; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm; exact ⟨(hf i).1, (hf i).2.2⟩)
    (by simp [List.nodup_cons, hrg.eq_iff]) v S htmp hwork
  rw [hrow, List.append_nil, List.flatMap_map] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .row) ((repairHeaderRowFields c).flatMap (fun f => S.R (rg (.field f)))) }
  obtain ⟨v₂, hu₂, he₂⟩ := sourceHeader_exec body ((repairHeaderGapFields c).map (fun f => rg (.field f)))
    (rg .gap) (rg .tmp) (rg .work)
    (by intro f hm; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm; exact (hf i).2)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ S₁
    (by simp [S₁, hrg.eq_iff, htmp]) (by simp [S₁, hrg.eq_iff, hwork])
  have hgap₁ : S₁.R (rg .gap) = [] := by simp [S₁, hrg.eq_iff, hgap]
  rw [hgap₁, List.append_nil, List.flatMap_map] at he₂
  have hg : (repairHeaderGapFields c).flatMap (fun f => S₁.R (rg (.field f))) =
      (repairHeaderGapFields c).flatMap (fun f => S.R (rg (.field f))) := by
    simp [S₁, hrg.eq_iff]
  have hc : sourceHeaderCost S₁.R ((repairHeaderGapFields c).map (fun f => rg (.field f))) =
      sourceHeaderCost S.R ((repairHeaderGapFields c).map (fun f => rg (.field f))) := by
    fin_cases c <;> simp [repairHeaderGapFields, sourceHeaderCost, S₁, hrg.eq_iff]
  rw [hg, hc] at he₂
  exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂⟩

theorem repairHeaderCounts_lengths {T A : ℕ} (p : Par) (X : ℕ) (rg : HeaderCountReg → Fin T)
    (bank : Fin T → List (Fin (A + 4))) (c : Fin 2)
    (hwidth : ∀ f, (bank (rg (.field f))).length = selectiveLen p X f) :
    ((repairHeaderRowFields c).flatMap (fun f => bank (rg (.field f)))).length =
      fieldsLen (selectiveLen p X) - (repairHeaderUpper p X c + p.wc) ∧
    ((repairHeaderGapFields c).flatMap (fun f => bank (rg (.field f)))).length = repairHeaderUpper p X c - p.wc := by
  rw [repairHeaderRowExp_eq, repairHeaderGapExp_eq]
  fin_cases c <;> simp [repairHeaderRowFields, repairHeaderGapFields, hwidth, selectiveLen]

theorem repairHeaderCounts_cost {T A : ℕ} (p : Par) (X : ℕ) (rg : HeaderCountReg → Fin T)
    (bank : Fin T → List (Fin (A + 4))) (c : Fin 2)
    (hwidth : ∀ f, (bank (rg (.field f))).length = selectiveLen p X f) :
    sourceHeaderCost bank ((repairHeaderRowFields c).map (fun f => rg (.field f))) +
      sourceHeaderCost bank ((repairHeaderGapFields c).map (fun f => rg (.field f))) =
      6 * (p.wc + p.wy + X) + 20 := by
  fin_cases c <;> simp [repairHeaderRowFields, repairHeaderGapFields, sourceHeaderCost, hwidth, selectiveLen] <;> omega

end IntegerMultBounds.MathlibTM2.Routing
