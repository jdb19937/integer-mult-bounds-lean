module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryRepairHeaders

/-! Generate both R2 header banks with one pair of binary row/width inputs.
The generators may share all non-output scratch and dimension tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def binaryRepairHeaderPairProgram {T Q A : ℕ} {P U : Type}
    (src : Fin 2 → Fin T) (bank : Fin 2 → RepairHeaderReg → Fin T) : Pr P T Q A U :=
  .seq (binaryRepairHeadersProgram src (bank 0) 0) (binaryRepairHeadersProgram src (bank 1) 1)

def repairHeaderPairBank {T A : ℕ} (p : Par) (X rb R B : ℕ)
    (bank : Fin 2 → RepairHeaderReg → Fin T) (tapes : Fin T → List (Fin (A + 4))) :=
  elementaryHeaderBank (elementaryHeaderBank tapes (fun r => bank 0 (.exchange (.base r)))
    (repairCanonicalHeaders p X rb R B 0)) (fun r => bank 1 (.exchange (.base r))) (repairCanonicalHeaders p X rb R B 1)

theorem repairHeaderPairBank_contents {T A : ℕ} (p : Par) (X rb R B : ℕ)
    (bank : Fin 2 → RepairHeaderReg → Fin T) (hbank : ∀ c, Function.Injective (bank c))
    (hcross : ∀ r i, bank 1 r ≠ bank 0 (.exchange (.base (.header i))))
    (tapes : Fin T → List (Fin (A + 4))) (c : Fin 2) (k : Fin 5) :
    repairHeaderPairBank p X rb R B bank tapes (bank c (.exchange (.base (.header k)))) =
      (repairCanonicalHeaders p X rb R B c k).map bitSymbol := by
  fin_cases c <;> fin_cases k <;>
    simp [repairHeaderPairBank, elementaryHeaderBank, (hbank 0).eq_iff, (hbank 1).eq_iff, hcross, Ne.symm]

theorem repairHeaderPairBank_keep {T A : ℕ} (p : Par) (X rb R B : ℕ)
    (bank : Fin 2 → RepairHeaderReg → Fin T) (tapes : Fin T → List (Fin (A + 4)))
    (i : Fin T) (hi : ∀ c k, i ≠ bank c (.exchange (.base (.header k)))) :
    repairHeaderPairBank p X rb R B bank tapes i = tapes i := by
  simp [repairHeaderPairBank, elementaryHeaderBank, hi]

theorem binaryRepairHeaderPair_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src : Fin 2 → Fin T) (bank : Fin 2 → RepairHeaderReg → Fin T)
    (hbank : ∀ c, Function.Injective (bank c)) (hsep : ∀ c i r, src i ≠ bank c r)
    (hcross : ∀ r i, bank 1 r ≠ bank 0 (.exchange (.base (.header i))))
    (p : Par) (X rb R B L Lr Lw : ℕ)
    (hR : R < 2 ^ Lr) (hR0 : 0 < R) (hw : p.wc < 2 ^ Lw)
    (hB : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ L)
    (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (v : HS T Q A U) (S : Stacks T A)
    (hdim : ∀ c f, (S.R (bank c (.dimension f))).length = selectiveLen p X f)
    (hrowInput : S.R (src 0) = binSyms Lr R) (hwidthInput : S.R (src 1) = binSyms Lw p.wc)
    (hblock : ∀ c, S.R (bank c (.exchange (.base .block))) = binSyms L (fieldsLen (selectiveKeyLen p X rb) + B))
    (hblank : ∀ c (r : ExchangeHeaderReg), r ≠ .base .block → S.R (bank c (.exchange r)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * (14 * (p.wc + p.wy + X) + 18 * Lr + 24 * Lw + 52 * L + 280) ∧
      Exec body (binaryRepairHeaderPairProgram src bank) (mk v S) m
        (mk v' { S with R := repairHeaderPairBank p X rb R B bank S.R }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryRepairHeaders_exec body src (bank 0) (hbank 0) (hsep 0)
    p X rb R B L Lr Lw 0 hR hR0 hw hB hB0 v S (hdim 0) hrowInput hwidthInput (hblock 0) (hblank 0)
  let S₁ : Stacks T A := { S with R := elementaryHeaderBank S.R (fun r => bank 0 (.exchange (.base r))) (repairCanonicalHeaders p X rb R B 0) }
  have hk (i : Fin T) (hi : ∀ k, i ≠ bank 0 (.exchange (.base (.header k)))) : S₁.R i = S.R i := by
    simp [S₁, elementaryHeaderBank, hi]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryRepairHeaders_exec body src (bank 1) (hbank 1) (hsep 1)
    p X rb R B L Lr Lw 1 hR hR0 hw hB hB0 v₁ S₁
    (by intro f; rw [hk _ (hcross (.dimension f))]; exact hdim 1 f)
    (by rw [hk _ (fun k => hsep 0 0 _)]; exact hrowInput)
    (by rw [hk _ (fun k => hsep 0 1 _)]; exact hwidthInput)
    (by rw [hk _ (hcross (.exchange (.base .block)))]; exact hblock 1)
    (by intro r hr; rw [hk _ (hcross (.exchange r))]; exact hblank 1 r hr)
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
