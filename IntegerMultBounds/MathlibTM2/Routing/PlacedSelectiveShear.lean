module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedSelectiveCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.Shear

/-! The actual conjugated exact permutation is the simultaneous physical shear.
Source coordinates remain outside active targets; dirty controls need no zeroing. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def placedSelectiveTargets (p : Par) (X : ℕ) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X)))) : Finset (Fin (fieldsLen (selectiveLen p X))) :=
  (Finset.univ.filter (fun c => active c = true)).image (fun c => e (selectiveTargetPosition p X hK c))

noncomputable def placedSelectiveSource (p : Par) (X : ℕ) (hK : 0 < p.K)
    (s : Fin p.n → SlotSource p X) (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X)))) :
    Fin (fieldsLen (selectiveLen p X)) → Fin (fieldsLen (selectiveLen p X)) :=
  Function.extend (fun c => e (selectiveTargetPosition p X hK c))
    (fun c => e (selectiveSourcePosition p X (s c))) id

variable {p : Par} {X R : ℕ} (hK : 0 < p.K) (active : Fin p.n → Bool)
  (s : Fin p.n → SlotSource p X) (hs : ∀ c, (s c).Allowed active)
  (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))

theorem mem_placedSelectiveTargets (q : Fin (fieldsLen (selectiveLen p X))) :
    q ∈ placedSelectiveTargets p X hK active e ↔
      ∃ c, active c = true ∧ e (selectiveTargetPosition p X hK c) = q := by
  simp [placedSelectiveTargets]

theorem placedSelectiveSource_at (c : Fin p.n) :
    placedSelectiveSource p X hK s e (e (selectiveTargetPosition p X hK c)) =
      e (selectiveSourcePosition p X (s c)) :=
  (e.injective.comp (selectiveTargetPosition_injective p X hK)).extend_apply _ _ c

include hs in
theorem placedSelectiveSource_avoids (q : Fin (fieldsLen (selectiveLen p X)))
    (hq : q ∈ placedSelectiveTargets p X hK active e) :
    placedSelectiveSource p X hK s e q ∉ placedSelectiveTargets p X hK active e := by
  obtain ⟨c, hc, rfl⟩ := (mem_placedSelectiveTargets hK active e q).mp hq
  rw [placedSelectiveSource_at]
  intro hm
  obtain ⟨d, hd, he⟩ := (mem_placedSelectiveTargets hK active e _).mp hm
  exact placedSelectiveSource_allowed hK active s hs e c d hd he.symm

theorem placedSelectivePerm_shear
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (fun q => (placedSelectivePerm hK active s hs f i).val.testBit q.val) =
      shear (placedSelectiveTargets p X hK active e) (placedSelectiveSource p X hK s e)
        (fun q => i.val.testBit q.val) := by
  funext q
  by_cases hq : q ∈ placedSelectiveTargets p X hK active e
  · obtain ⟨c, hc, rfl⟩ := (mem_placedSelectiveTargets hK active e q).mp hq
    rw [placedSelectivePerm_physical_target hK active s hs f e hf]
    simp [shear, toggle, hq, placedSelectiveSource_at, hc]
  · rw [placedSelectivePerm_physical_other hK active s hs f e hf i q]
    · simp [shear, toggle, hq]
    · intro c hc he
      apply hq
      exact (mem_placedSelectiveTargets hK active e q).mpr ⟨c, hc, he.symm⟩

theorem reservoirPlacedSelective_shear (H : ℕ) (hfit : 9 * H ≤ fieldsLen (selectiveLen p X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (fun q => (placedSelectivePerm hK active s hs
      (reservoirExchangeRank (fieldsLen (selectiveLen p X)) H hfit w hw reservoir R) i).val.testBit q.val) =
      shear (placedSelectiveTargets p X hK active
          (reservoirPlacement (fieldsLen (selectiveLen p X)) H hfit w hw reservoir))
        (placedSelectiveSource p X hK s
          (reservoirPlacement (fieldsLen (selectiveLen p X)) H hfit w hw reservoir))
        (fun q => i.val.testBit q.val) :=
  placedSelectivePerm_shear hK active s hs
    (reservoirPlacement (fieldsLen (selectiveLen p X)) H hfit w hw reservoir)
    (reservoirExchangeRank (fieldsLen (selectiveLen p X)) H hfit w hw reservoir R)
    (reservoirExchangeRank_bit (fieldsLen (selectiveLen p X)) H hfit w hw reservoir R) i

end IntegerMultBounds.MathlibTM2.Routing
