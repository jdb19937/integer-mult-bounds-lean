module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
public import IntegerMultBounds.MathlibTM2.Fast.SynSel

/-! The actual compact chunk selection implements the original synthetic butterfly round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds
open CompactGadgetReservationCapacity
noncomputable section

theorem compactSynSelection_physical {es : List ℕ} {ℓ K h N : ℕ}
    (H : LayHyp es ℓ K) (hc : synChunk ℓ K h) (sel : List (Fin N))
    (hsel : (sel.map Fin.val).Perm ((List.range es.length).map
      fun i => (h-layB ℓ K)%K+K*((h-layB ℓ K)/K*es.length)+K*i)) :
    (sel.map Fin.val).Perm ((selBits es h).map (twPosL (layPerm es ℓ K))) := by
  apply hsel.trans
  have hp := (synSel_chunk H hc).symm
  have hb : ¬h<layB ℓ K := Nat.not_lt.mpr hc.2
  simpa only [synRh,synOS,hc,ite_true,hc.1,hb,ite_false] using hp

theorem compactSynSelection_stream {es : List ℕ} {ℓ K h N r A W : ℕ}
    (H : LayHyp es ℓ K) (hc : synChunk ℓ K h) (hK : 0<K)
    (sel : List (Fin N)) (Y : ℕ → Fin r → GaussianInt)
    (hsel : (sel.map Fin.val).Perm ((List.range es.length).map
      fun i => (h-layB ℓ K)%K+K*((h-layB ℓ K)/K*es.length)+K*i)) :
    encZ A W (fun z => (⟨truncR (Hl _ sel (toC (synZ N Y)) z).re,
      truncR (Hl _ sel (toC (synZ N Y)) z).im⟩ : GaussianInt)) =
    cstream A W (rpStream (2^N) (synTrunc
      (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
        (fun x c => GaussianInt.toComplex (Y x c))))) := by
  have hphys := compactSynSelection_physical H hc sel hsel
  have hnd : (sel.map Fin.val).Nodup := by
    apply hsel.nodup_iff.2
    refine List.nodup_range.map fun i j hij => ?_
    exact Nat.eq_of_mul_eq_mul_left hK (Nat.add_left_cancel hij)
  have he : (fun z => (⟨truncR (Hl _ sel (toC (synZ N Y)) z).re,
      truncR (Hl _ sel (toC (synZ N Y)) z).im⟩ : GaussianInt)) =
      synZ N (synTrunc (bflyL (sel.map Fin.val)
        (fun x c => GaussianInt.toComplex (Y x c)))) := by
    funext z
    rw [Hl_synZ]
    rfl
  rw [he,encZ_synZ,bflyL_perm hphys hnd]

end
end IntegerMultBounds.MathlibTM2.Fast
