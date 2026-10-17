module
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Absolute serialized coordinates and relative compact-layer coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

def compactRelativePc (o : ℕ) (pc : TopPc) : TopPc := {pc with a₀:=pc.a₀-o}

theorem compactRelativePc_rebase (o R : ℕ) (pc : TopPc) :
    compactRelativePc o (compactRebasePc R pc) = compactRebasePc R (compactRelativePc o pc) := by
  cases pc
  rfl

theorem compactRelativePc_synPc (o K X D offset J j : ℕ) (ho : o≤offset) :
    compactRelativePc o (synPc K X D offset J j) = synPc K X D (offset-o) J j := by
  have h : offset+K*(D%m^j)-o=offset-o+K*(D%m^j) := by omega
  exact congrArg (fun z => (⟨j,synDg D j,rowsAt (2^X) (J-j),z⟩ : TopPc)) h

theorem compactRelativePc_synPcs (o K X D offset J t : ℕ) (ho : o≤offset) :
    (synPcs K X D offset J t).map (compactRelativePc o) = synPcs K X D (offset-o) J t := by
  unfold synPcs
  rw [List.map_filterMap]
  congr 1
  funext j
  by_cases hz : synDg D j=0
  · simp only [hz,↓reduceIte,Option.map_none]
  · simp only [hz,↓reduceIte,Option.map_some]
    exact congrArg some (compactRelativePc_synPc o K X D offset J j ho)

theorem compactRelativePc_reserved (o K X offset B activeOffset J D : ℕ)
    (ho : o≤activeOffset) :
    (compactReservedPcs K X offset B activeOffset J D).map (compactRelativePc o) =
      compactReservedPcs K X (offset-o) B (activeOffset-o) J D := by
  unfold compactReservedPcs
  rw [List.map_append,compactRelativePc_synPcs o K X D activeOffset J D ho]
  by_cases hb : B=0
  · simp only [hb,↓reduceIte,List.map_nil,List.nil_append]
  · simp only [hb,↓reduceIte,List.map_cons,List.map_nil,compactRelativePc]

theorem compactRelativePc_ok (ds : ComplexFramedExecution.Directions)
    {o K n w R : ℕ} {pc : TopPc} (ho : o≤pc.a₀) (h : pc.Ok ds K n w R) :
    (compactRelativePc o pc).Ok ds K (n-o) w R := by
  refine ⟨h.hu,h.hR₀,h.hR,h.hTw,?_⟩
  have hfit := h.hfit
  change pc.a₀-o+K*bits pc.u pc.j≤n-o
  omega

/-- The volume exponent remains the absolute address width. -/
theorem compactRelative_volume (R n o r w : ℕ) (ho : o≤n) :
    R*2^(o+(n-o))*(r*w)=R*2^n*(r*w) := by
  rw [Nat.add_sub_of_le ho]

end
end IntegerMultBounds.MathlibTM2.Cost
