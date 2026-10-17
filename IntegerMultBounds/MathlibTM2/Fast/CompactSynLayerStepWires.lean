module
public import IntegerMultBounds.MathlibTM2.Fast.SynRound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat


/-! Wire identities needed to park and restore one concretely prepared round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

def compactSynPreparedW (v : SynW → List (Fin (A+4))) (K ρ working : ℕ)
    (pr cf : List (Fin (A+4))) :=
  Function.update (Function.update (Function.update (Function.update (Function.update v
    (.p .kh) (List.replicate K tick)) (.p .rh) (List.replicate ρ tick)) (.p .pr) pr)
    (.p .cf) cf) (.p .w2) (List.replicate working tick)

def compactSynRaisedW (v : SynW → List (Fin (A+4))) :=
  Function.update (Function.update (Function.update (Function.update v (.p .kh) [])
    (.p .rh) []) (.p .pr) []) (.p .w2) []

lemma compactSynRaised_prepared
    (v : SynW → List (Fin (A+4))) (K ρ working : ℕ) (pr cf : List (Fin (A+4)))
    (hkh : v (.p .kh)=[]) (hrh : v (.p .rh)=[]) (hpr : v (.p .pr)=[]) (hw2 : v (.p .w2)=[]) :
    compactSynRaisedW (compactSynPreparedW v K ρ working pr cf)=Function.update v (.p .cf) cf := by
  funext x
  by_cases h1 : x=.p .kh
  · subst x; simp [compactSynRaisedW,hkh]
  by_cases h2 : x=.p .rh
  · subst x; simp [compactSynRaisedW,hrh]
  by_cases h3 : x=.p .pr
  · subst x; simp [compactSynRaisedW,hpr]
  by_cases h4 : x=.p .w2
  · subst x; simp [compactSynRaisedW,hw2]
  simp [compactSynRaisedW,compactSynPreparedW,Function.update_apply,h1,h2,h3,h4]

lemma compactSynRaised_prepared_synXS
    (v : SynW → List (Fin (A+4))) (K ρ working : ℕ) (pr cf : List (Fin (A+4)))
    (x : SynW) (hx : x∈synXS) :
    compactSynRaisedW (compactSynPreparedW v K ρ working pr cf) x=v x := by
  simp only [synXS,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [compactSynRaisedW,compactSynPreparedW]

lemma compactSynParkedW_empty
    (v : SynW → List (Fin (A+4))) (es : List ℕ) (ℓ K W l h : ℕ)
    (L : Equiv.Perm (Fin es.sum)) (hv : SynV v es ℓ K W l h L)
    (cf : List (Fin (A+4))) :
    ∀ x,Function.update (synClrW (Function.update v (.p .cf) cf) synXS) (.p .cf) [] x=[] := by
  intro x
  by_cases hx : x∈synXS
  · simp [synClrW,hx,Function.update_apply]
  · simp only [synClrW,hx,ite_false,Function.update_apply]
    split_ifs with hcf
    · rfl
    · rcases x with tw | i | param | i
      · have hpz : tw≠.pz := by intro he; subst he; simp [synXS] at hx
        exact hv.htw tw hpz
      · exact hv.hly i
      · cases param <;> simp_all [synXS,hv.hw2,hv.hkh,hv.hrh,hv.hpr]
      · exact hv.hs i

lemma compactSynRaised_restore
    (v : SynW → List (Fin (A+4))) (K ρ working : ℕ) (pr cf : List (Fin (A+4)))
    (hkh : v (.p .kh)=[]) (hrh : v (.p .rh)=[]) (hpr : v (.p .pr)=[])
    (hw2 : v (.p .w2)=[]) (hcf : v (.p .cf)=[]) :
    Function.update (compactSynRaisedW (compactSynPreparedW v K ρ working pr cf)) (.p .cf) []=v := by
  rw [compactSynRaised_prepared v K ρ working pr cf hkh hrh hpr hw2,Function.update_idem]
  funext x
  by_cases hx : x=.p .cf
  · subst x; simp [hcf]
  · simp [Function.update_of_ne,hx]

end
end IntegerMultBounds.MathlibTM2.Fast
