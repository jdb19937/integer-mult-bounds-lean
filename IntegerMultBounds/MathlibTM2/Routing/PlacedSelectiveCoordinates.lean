module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedSelectiveBits
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveCoordinates

/-! The placed exact primitive reads the original physical source coordinate,
not a pre-placement source name or an abstract observation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {X R : ℕ} (hK : 0 < p.K) (active : Fin p.n → Bool)
  (s : Fin p.n → SlotSource p X) (hs : ∀ c, (s c).Allowed active)

theorem placedSelectivePerm_physical_target
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) (c : Fin p.n) :
    (placedSelectivePerm hK active s hs f i).val.testBit (e (selectiveTargetPosition p X hK c)).val =
      Bool.xor (i.val.testBit (e (selectiveTargetPosition p X hK c)).val)
        (active c && i.val.testBit (e (selectiveSourcePosition p X (s c))).val) := by
  have h := placedSelectivePerm_target_bit hK active s hs f e hf i
    (e (selectiveTargetPosition p X hK c)) c (by simp [selectiveTargetPosition])
  rw [← selectiveSourcePosition_bit (s c) (f i).val, hf] at h
  exact h

theorem placedSelectivePerm_physical_other
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) (q : Fin (fieldsLen (selectiveLen p X)))
    (hq : ∀ c : Fin p.n, active c = true → q ≠ e (selectiveTargetPosition p X hK c)) :
    (placedSelectivePerm hK active s hs f i).val.testBit q.val = i.val.testBit q.val := by
  apply placedSelectivePerm_other_bit hK active s hs f e hf i q
  intro c hc he
  apply hq c hc
  have he' : e.symm q = selectiveTargetPosition p X hK c := Fin.ext he
  rw [← e.apply_symm_apply q, he']

include hs in
theorem placedSelectiveSource_allowed
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X)))) (c d : Fin p.n) (hd : active d = true) :
    e (selectiveSourcePosition p X (s c)) ≠ e (selectiveTargetPosition p X hK d) :=
  e.injective.ne (selectiveSourcePosition_allowed hK active (s c) (hs c) d hd)

end IntegerMultBounds.MathlibTM2.Routing
