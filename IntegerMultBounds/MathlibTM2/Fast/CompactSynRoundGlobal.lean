module
public import IntegerMultBounds.MathlibTM2.Node.CompactRegisterEmbedding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat


/-! Read initialized original depth and guard from persistent compact registers
into empty constructor scratch. This is a read bridge, not their bootstrap. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Synthetic scratch addressed directly on the common host. -/
def compactSynScratch (i : Fin 32) : Fin (nT CompactHostBReg) :=
  reg (BReg := CompactHostBReg) (.wire (synWire (.s i)))

lemma compactSynScratch_ne {i j : Fin 32} (h : i≠j) : compactSynScratch i≠compactSynScratch j := by
  intro he
  have hh := synWire_inj (LReg.wire.inj (reg_injective he))
  exact h (SynW.s.inj hh)

lemma compactSynScratch_legacy (i : Fin 32) : compactLegacyReg (sreg (.s i))=compactSynScratch i := by
  simp only [sreg_eq,compactLegacyReg,compactMapReg_reg,compactMapRegName,compactSynScratch]

/-- Original depth/guard copies. All source registers stay unchanged. -/
def compactSynGlobalRead : Pr P (nT CompactHostBReg) Q A U :=
  .seq (ucopy (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))) (compactSynScratch 0) (compactSynScratch 2))
    (ucopy (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))) (compactSynScratch 1) (compactSynScratch 2))

theorem compactSynGlobalRead_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (d g : ℕ)
    (hd : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
    (hg : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
    (h0 : R (compactSynScratch 0)=[]) (h1 : R (compactSynScratch 1)=[])
    (h2 : R (compactSynScratch 2)=[]) :
    LayRuns body compactSynGlobalRead R
      (Function.update (Function.update R (compactSynScratch 0) (List.replicate d tick))
        (compactSynScratch 1) (List.replicate g tick)) ((4*d+4)+(4*g+4)) := by
  have hd0 : reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))≠compactSynScratch 0 :=
    reg_ne (by simp)
  have hd2 : reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))≠compactSynScratch 2 :=
    reg_ne (by simp)
  have hg1 : reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))≠compactSynScratch 1 :=
    reg_ne (by simp)
  have hg2 : reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))≠compactSynScratch 2 :=
    reg_ne (by simp)
  have hg0 : reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))≠compactSynScratch 0 :=
    reg_ne (by simp)
  have e₁ := lr_ucopy body hd0 hd2 (compactSynScratch_ne (by decide : (0:Fin 32)≠2)) h2
  rw [hd,h0,List.append_nil] at e₁
  have e₂ := lr_ucopy body (R := Function.update R (compactSynScratch 0) (List.replicate d tick))
    hg1 hg2 (compactSynScratch_ne (by decide : (1:Fin 32)≠2))
    (by rw [Function.update_of_ne (compactSynScratch_ne (by decide : (2:Fin 32)≠0))]; exact h2)
  rw [Function.update_of_ne hg0, hg,
    Function.update_of_ne (compactSynScratch_ne (by decide : (1:Fin 32)≠0)),h1,List.append_nil] at e₂
  exact e₁.seq e₂

end
end IntegerMultBounds.MathlibTM2.Fast
