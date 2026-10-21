module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStep
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCore

/-!
# The core's leaf

The leaf of the core is the stage-1 interchange on the low view: the family's leaf core
`LeafCore.core io` transposes the array on the I/O role of any positive view (`leaf_phase`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open Stage2Wrapper (Moves)
open FamilyRoot (ext rolesOf)
open FamilyStep (rolesAt)
open Core (Phase)
open RevMachine

/-- Moves depend on the arrays only within the volume. -/
theorem moves_congr {v : Descriptor} {g : ℕ × ℕ → ℕ × ℕ} {X X' Y : ℕ → ZMod 2}
    (hX : ∀ i < volume prime v, X i = X' i)
    (h : Moves prime v g X Y) : Moves prime v g X' Y := by
  intro a ha row hrow before hb h' hh mid hm d hd after haf
  rw [h a ha row hrow before hb h' hh mid hm d hd after haf]
  have e := Transpose.addr_val (v := v) ⟨a, ha⟩ ⟨row, hrow⟩ ⟨before, hb⟩ ⟨h', hh⟩ ⟨mid, hm⟩ ⟨d, hd⟩
    ⟨after, haf⟩
  exact hX _ (e ▸ (Transpose.addr _ _ _ _ _ _ _).isLt)

variable [M8.Machine.Net] (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
  (c : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)

/-- The bank of the leaf core. -/
def leafBank (u : Descriptor) (X : ℕ → ZMod 2) :=
  CommonBank.bank (rolesAt u X) (Routines.hdr u) f p node scalar c st

/-- **The leaf**: on a positive view the leaf core interchanges the array. -/
theorem leaf_phase {u : Descriptor} (hpos : u.Positive) :
    Phase (LeafCore.core (NodeBank.io rev97m)).program
      (fun u X => raw (leafBank f p node scalar c st u X) (LeafCore.core (NodeBank.io rev97m)).tapes) u u
      (Moves prime u Prod.swap) (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u)) := by
  intro X
  set x : Fin (volume prime u) → ZMod 2 := fun i => X i
  have hio : (rolesAt u X).head (NodeBank.io rev97m) = 0 ∧
      (rolesAt u X).tape (NodeBank.io rev97m) = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x := by
    simp [rolesAt, rolesOf, NodePark.childRoles, M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord, x,
      setTape]
  have h := LeafCore.core_runs (NodeBank.io rev97m) (roles := rolesAt u X) (f := f) (p := p) (node := node)
    (scalar := scalar) (c := c) (st := st) hpos x hio.1 hio.2
  refine h.consequence (fun _ h => h) (fun z hz => ⟨ext (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) x),
    moves_congr (fun i hi => by simp [x, ext, hi]) (Transpose.transpose_moves x), ?_⟩) le_rfl
  have hr : setTape (rolesAt u X) (NodeBank.io rev97m)
      (M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) x)) 0 =
      rolesAt u (ext (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) x)) := by
    rw [FamilyStep.rolesAt_ext]
    unfold rolesAt rolesOf NodePark.childRoles
    rw [SharedPlacementAlphabet.setTape_setTape]
    rfl
  rw [hz, hr]
  rfl

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
