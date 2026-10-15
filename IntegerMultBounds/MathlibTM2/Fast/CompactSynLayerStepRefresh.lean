module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRecords
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshInput

/-! Refresh actual per-round counters from the original constructor's preserved sources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- A general full-host refresh contract, with its projection obligation derived
from the legacy view and blank destination bank. -/
theorem compactSynLayerRefresh_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (Rbig : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d g K D o r : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hr : (v (.p .r)).length=r)
    (hs : ∀ i : Fin 32,i≠0 → i≠1 → i≠7 → v (.s i)=[])
    (hlegacy : Rbig ∘ compactLegacyReg=synG Ro v)
    (hblank : ∀ i,Rbig (compactBasisRefreshDst i)=[]) :
    LayRuns body compactBasisRefresh Rbig
      (compactSetupUpdate7 Rbig compactBasisRefreshDst
        (compactZeroTail (compactBasisSetupValues d g K D o r)))
      (compactBasisRefreshCost d g K D o r) := by
  have hwire (i : Fin 7) : v (compactBasisOutputWire i)=[] := by
    fin_cases i <;> apply hs <;> decide
  have hinput := compactBasisRefresh_input Rbig Ro v hlegacy hblank hwire
  intro vbig S hL hR
  obtain ⟨v',c,hu,hc,he⟩ := compactBasisRefresh_exec body Ro v d g K D o r
    hdpos hk hd hg hK hD ho hr hs vbig S hL (by rw [hR]; exact hinput)
  rw [hR] at he
  exact ⟨v',c,hu,hc,he⟩

/-- Refresh changes no legacy register, including every source copy and record. -/
lemma compactSynLayerRefresh_legacy
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (values : Fin 7 → ℕ)
    (i : Fin (nT SXReg)) :
    compactSetupUpdate7 R compactBasisRefreshDst values (compactLegacyReg i)=R (compactLegacyReg i) := by
  apply compactSetupUpdate7_off
  intro j
  exact compactLegacyReg_ne_compact_bc i (.work (compactBasisRefreshWork j))

lemma compactSynLayerRefresh_projection
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (values : Fin 7 → ℕ) :
    compactSetupUpdate7 R compactBasisRefreshDst values ∘ compactLegacyReg=R ∘ compactLegacyReg := by
  funext i
  exact compactSynLayerRefresh_legacy R values i

end
end IntegerMultBounds.MathlibTM2.Fast
