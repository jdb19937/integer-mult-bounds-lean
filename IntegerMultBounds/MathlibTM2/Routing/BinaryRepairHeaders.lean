module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderSourcesClean

/-! Generate one complete five-word R2 header bank from live padded binary
inputs and dimension tapes, restoring every intermediate and non-output tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def binaryRepairHeadersProgram {T Q A : ℕ} {P U : Type}
    (src : Fin 2 → Fin T) (bank : RepairHeaderReg → Fin T) (c : Fin 2) : Pr P T Q A U :=
  .seq (repairHeaderSourceProgram src bank)
    (.seq (repairHeaderGenerateProgram bank c)
      (metadataClean [bank (.exchange (.base .rows)), bank (.exchange (.base .target))]))

theorem binaryRepairHeaders_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src : Fin 2 → Fin T) (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (hsep : ∀ i r, src i ≠ bank r)
    (p : Par) (X rb R B L Lr Lw : ℕ) (c : Fin 2)
    (hR : R < 2 ^ Lr) (hR0 : 0 < R) (hw : p.wc < 2 ^ Lw)
    (hB : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ L)
    (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (v : HS T Q A U) (S : Stacks T A)
    (hdim : ∀ f, (S.R (bank (.dimension f))).length = selectiveLen p X f)
    (hrowInput : S.R (src 0) = binSyms Lr R) (hwidthInput : S.R (src 1) = binSyms Lw p.wc)
    (hblock : S.R (bank (.exchange (.base .block))) = binSyms L (fieldsLen (selectiveKeyLen p X rb) + B))
    (hblank : ∀ r : ExchangeHeaderReg, r ≠ .base .block → S.R (bank (.exchange r)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 14 * (p.wc + p.wy + X) + 18 * Lr + 24 * Lw + 52 * L + 280 ∧
      Exec body (binaryRepairHeadersProgram src bank c) (mk v S) m
        (mk v' { S with R := elementaryHeaderBank S.R (fun r => bank (.exchange (.base r))) (repairCanonicalHeaders p X rb R B c) }) := by
  have hb (r : ExchangeHeaderReg) (hr : r ≠ .base .block) : S.R (bank (.exchange r)) = [] := hblank r hr
  obtain ⟨v₁, hu₁, he₁⟩ := repairHeaderSources_exec body src bank hbank hsep Lr Lw R p.wc hR hw v S
    hrowInput hwidthInput (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))
  let S₁ : Stacks T A := { S with R := repairHeaderSourceBank bank R p.wc S.R }
  have hk (r : ExchangeHeaderReg) (hr : r ≠ .base .rows) (ht : r ≠ .base .target) :
      S₁.R (bank (.exchange r)) = S.R (bank (.exchange r)) :=
    repairHeaderSourceBank_keep bank R p.wc S.R _ (hbank.ne (by simpa using hr)) (hbank.ne (by simpa using ht))
  have hcR : GrowingCounterData.Canonical (GrowingCounterData.advance R []) :=
    GrowingCounterData.advance_canonical R [] (Or.inl rfl)
  have hcW : GrowingCounterData.Canonical (GrowingCounterData.advance p.wc []) :=
    GrowingCounterData.advance_canonical p.wc [] (Or.inl rfl)
  have hvR : Counter.value (GrowingCounterData.advance R []) = R := by simp [GrowingCounterData.advance_value, Counter.value]
  have hvW : Counter.value (GrowingCounterData.advance p.wc []) = p.wc := by simp [GrowingCounterData.advance_value, Counter.value]
  have hnR : GrowingCounterData.advance R [] ≠ [] := by
    intro he
    rw [he] at hvR
    simp [Counter.value] at hvR
    omega
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := repairHeaderGenerate_exec body bank hbank p X rb R B L c hB hB0
    (GrowingCounterData.advance R []) (GrowingCounterData.advance p.wc []) hcR hnR hvR hcW hvW v₁ S₁
    (by intro f; simpa [S₁, repairHeaderSourceBank, hbank.eq_iff] using hdim f)
    (by simp [S₁, repairHeaderSourceBank, hbank.eq_iff])
    (by rw [hk _ (by simp) (by simp)]; exact hblock)
    (by simp [S₁, repairHeaderSourceBank])
    (by intro r hr hbl ht; rw [hk r hr ht]; exact hb r hbl)
  let S₂ : Stacks T A := { S with R := elementaryHeaderBank S.R (fun r => bank (.exchange (.base r))) (repairCanonicalHeaders p X rb R B c) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := repairHeaderSourcesClean_exec body bank hbank Lr Lw R p.wc hR hw v₂ S₂
    (by simpa [S₂, elementaryHeaderBank, hbank.eq_iff] using hb (.base .rows) (by simp))
    (by simpa [S₂, elementaryHeaderBank, hbank.eq_iff] using hb (.base .target) (by simp))
  dsimp only [S₂] at he₃
  rw [repairHeaderSourceBank_commute bank hbank R p.wc S.R] at he₃
  have hlR := canonicalHeader_length_le Lr R hR
  have hlW := canonicalHeader_length_le Lw p.wc hw
  exact ⟨v₃, ((10 * Lr + 12) + (10 * Lw + 12)) + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
