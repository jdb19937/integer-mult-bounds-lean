module

public import IntegerMultBounds.MathlibTM2.M8.Local.SequenceCheckB

/-! Constant-depth key membership checks reuse checked inverse positions and sequences. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local

/-- An inverse position and indexed value jointly test key membership. -/
def keyMember (index get : Nat → Nat) (size s : Nat) : Bool :=
  Nat.blt (index s) size && Nat.beq (get (index s)) s

/-- Both positive and negative membership answers follow from the same checked key. -/
theorem keyMember_spec (index get : Nat → Nat) (xs : List Nat) (size : Nat)
    (hi : indexCheck index 0 xs = true) (hg : sequenceCheck get 0 xs = true)
    (hlen : xs.length = size) (s : Nat) :
    keyMember index get size s = true ↔ s ∈ xs := by
  constructor
  · intro h
    obtain ⟨hb, he⟩ := Bool.and_eq_true_iff.mp h
    have hb : index s < xs.length := by simpa only [hlen] using Nat.blt_eq.mp hb
    have hv := sequenceCheck_get get 0 xs hg (index s) hb
    have he : get (index s) = s := Nat.beq_eq.mp he
    have hm := List.getElem_mem hb
    rw [← hv, Nat.zero_add, he] at hm
    exact hm
  · intro hs
    have hb : xs.idxOf s < xs.length := List.idxOf_lt_length_iff.mpr hs
    have hv : xs[xs.idxOf s] = s := List.getElem_idxOf hb
    have he : index s = xs.idxOf s := by
      simpa only [hv, Nat.zero_add] using indexCheck_get index 0 xs hi (xs.idxOf s) hb
    unfold keyMember
    rw [he]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Nat.blt_eq.mpr (by simpa only [← hlen] using hb), Nat.beq_eq.mpr ?_⟩
    simpa only [Nat.zero_add, hv] using sequenceCheck_get get 0 xs hg (xs.idxOf s) hb

end IntegerMultBounds.MathlibTM2.M8.Local
