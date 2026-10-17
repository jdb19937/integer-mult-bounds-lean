module

public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Consistent compact chunk-dependent wires: chunk, block width and permutation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter


noncomputable section

def compactDsyV₀ (n : ℕ) : SynW → List (Fin (bdA + 4))
  | .p .K => List.replicate (CompactSizes.K n) tick
  | .p .ℓ => List.replicate (ℓ n) tick
  | .p .b => List.replicate (layB (ℓ n) (CompactSizes.K n)) tick
  | .p .D => List.replicate (dsyEs n).length tick
  | .p .Lg => List.replicate (layLongs (dsyEs n) (ℓ n)).length tick
  | .p .N => List.replicate (dsyEs n).sum tick
  | .p .w => List.replicate (dsW n) tick
  | .p .r => List.replicate (r n) tick
  | .p .lr => List.replicate (ℓ n) tick
  | .p .es => topRec (dsyEs n)
  | .p .c => List.replicate (nRounds (cvAx (t n))) tick
  | .tw .pz => twPosReg bdA (dsyEs n).sum (twPosL (layPerm (dsyEs n) (ℓ n) (CompactSizes.K n)))
  | _ => []

theorem compactDsyV₀_wires : ∀ᶠ n in atTop,
    SynV (compactDsyV₀ n) (dsyEs n) (ℓ n) (CompactSizes.K n) (dsW n) (ℓ n) 0 (layPerm (dsyEs n) (ℓ n) (CompactSizes.K n)) ∧
      compactDsyV₀ n (.p .h) = [] ∧ compactDsyV₀ n (.p .t) = [] ∧
      (compactDsyV₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧ blank ∉ compactDsyV₀ n (.p .c) := by
  refine Eventually.of_forall fun n => ⟨?_, rfl, rfl, by simp [compactDsyV₀], ?_⟩
  · refine
      { hh := rfl
        hK := by simp [compactDsyV₀]
        hℓ := by simp [compactDsyV₀]
        hb := by simp [compactDsyV₀]
        hD := by simp [compactDsyV₀]
        hLg := by simp [compactDsyV₀, synLg]
        hN := by simp [compactDsyV₀]
        hw := by simp [compactDsyV₀]
        hr := by simp [compactDsyV₀, r]
        hlr := by simp [compactDsyV₀]
        hes := rfl
        hpz := rfl
        htw := fun w hw => by cases w <;> first | rfl | exact absurd rfl hw
        hs := fun _ => rfl
        hly := fun _ => rfl
        hw2 := rfl
        hcf := rfl
        hkh := rfl
        hrh := rfl
        hpr := rfl
        hblank := ?_ }
    intro x hx
    simp only [synXS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact dsy_blank_not_mem (dsy_mem_replicate_tick _)
      | exact dsy_blank_not_mem (dsy_mem_topRec _)
      | exact dsy_blank_not_mem (dsy_mem_twPosReg _ _)
      | simp [compactDsyV₀]
  · exact dsy_blank_not_mem (dsy_mem_replicate_tick _)


theorem compactDs_layHyp {n : ℕ} (h : Big n) :
    LayHyp (dsyEs n) (ℓ n) (CompactSizes.K n) := by
  have hlegacy := ds_layHyp h
  exact ⟨hlegacy.1,CompactSizes.one_le_K h.1,by
    have hk : CompactSizes.K n+1≤ℓ n := CompactSizes.K_succ_le_ℓ h
    omega⟩

/-- Distribution output consumed by the wire builder; only the chunk differs. -/
def compactBdO (n : ℕ) : DsX → List (Fin (bdA+4))
  | .lK => List.replicate (CompactSizes.K n) tick
  | x => bdO n x

/-- Precisely the parking and empty-layout premises used by the wire builder. -/
structure CompactBdWiresPre (R : Regs mnT bdA) (n : ℕ) : Prop where
  io : ∀ x,R (bdIo x)=compactBdO n x
  lay : ∀ x,(∀ y,bdLayX y≠x) → R (mnLay x)=[]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
