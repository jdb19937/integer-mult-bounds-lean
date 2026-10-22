module

public import IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFrames

/-! Every ordered pair in an existing checked chain supplies an incoming
frame edge. Repetitions use idempotence; no geometric residual is recomputed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup

open IntegerMultBounds Matrix

theorem edgeCheck_nested (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i, i < size → (bank i).check = true) (chain : List Signed.Frame)
    (hchain : Signed.chainCheck bank size chain = true) (a b : Signed.Frame)
    (ha : a.validCheck size = true) (hedge : edgeCheck a b chain = true) :
    Nested (a.eval bank) (b.eval bank) := by
  rcases Bool.or_eq_true_iff.mp hedge with he | hs
  · have he : a = b := of_decide_eq_true he
    subst b
    exact ⟨a.idem bank size hbank ha, a.idem bank size hbank ha⟩
  · have hsub := (sublistCheck_sound [a, b] chain hs).map (Signed.Frame.eval bank)
    have hp := (Signed.chainCheck_pairwise bank size hbank chain hchain).sublist hsub
    simpa using hp

theorem pathCheck_chain (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i, i < size → (bank i).check = true) (chain : List Signed.Frame)
    (hchain : Signed.chainCheck bank size chain = true) :
    ∀ frames, pathCheck size chain frames = true →
      List.IsChain Nested (frames.map (Signed.Frame.eval bank))
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: frames, h => by
    change (a.validCheck size && (edgeCheck a b chain && pathCheck size chain (b :: frames))) = true at h
    simp only [Bool.and_eq_true] at h
    apply List.isChain_cons_cons.mpr
    refine ⟨edgeCheck_nested bank size hbank chain hchain a b h.1 h.2.1, ?_⟩
    exact pathCheck_chain bank size hbank chain hchain (b :: frames) h.2.2

end IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup
