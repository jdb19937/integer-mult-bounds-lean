module

public import IntegerMultBounds.MathlibTM2.M8.Global.GaugedSinks
public import IntegerMultBounds.MathlibTM2.M8.Global.MoveMoments

/-! Exact move moments of terminal alignment and whole-projector gauge closure. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {ι : Type} [DecidableEq ι] {d : Nat} {M : Type} [AddCommMonoid M]

/-- Each role pays its terminal alignment and one whole-projector exit. -/
theorem edgeMoment_closeGauges (φ : Nat → M) (A C : ι → Mat d) :
    ∀ (ws : List ι) (fr : ι → Mat d), ws.Nodup →
      edgeMoment φ (closeGauges A C fr ws) =
        (ws.map fun i => stepMoment φ (fr i) (A i) + φ (1 - (A i - C i)).rank).sum
  | [], _, _ => rfl
  | i :: ws, fr, hn => by
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hn
    rw [closeGauges, edgeMoment_append, edgeMoment_move]
    change stepMoment φ (fr i) (A i) + (φ (1 - (A i - C i)).rank +
      edgeMoment φ (closeGauges A C (Function.update fr i (1 - C i)) ws)) = _
    rw [edgeMoment_closeGauges φ A C ws _ hn, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    have hne : j ≠ i := fun h => hnot (h ▸ hj)
    rw [Function.update_of_ne hne]

/-- Terminal alignment is exactly the final edge of the padded frame path. -/
theorem chainMoment_append_last (φ : Nat → M) : ∀ (fs : List (Mat d)) (A B : Mat d),
    chainMoment φ (A :: fs ++ [B]) =
      chainMoment φ (A :: fs) + stepMoment φ (fs.getLast?.getD A) B
  | [], A, B => by simp [chainMoment]
  | F :: fs, A, B => by
    change stepMoment φ A F + chainMoment φ (F :: fs ++ [B]) =
      (stepMoment φ A F + chainMoment φ (F :: fs)) +
        stepMoment φ ((F :: fs).getLast?.getD A) B
    rw [chainMoment_append_last φ fs F B, List.getLast?_cons]
    simp only [Option.getD_some, add_assoc]

/-- The actual aligned body and its side closure are priced by their complete wire paths. -/
theorem moment_closeGauges [Fintype ι] (φ : Nat → M) (L : List (FGate ι d))
    (cur A C : ι → Mat d) (hg : GatesOk L) (hc : ChainOk cur L)
    (ws : List ι) (hn : ws.Nodup) [DecidablePred (· ∈ ws)] :
    edgeMoment φ (autoSteps cur L ++ closeGauges A C (finalFrames (autoSteps cur L) cur) ws) =
      ∑ w, (chainMoment φ (cur w :: fseq w L) +
        if w ∈ ws then stepMoment φ ((fseq w L).getLast?.getD (cur w)) (A w) +
          φ (1 - (A w - C w)).rank else 0) := by
  rw [edgeMoment_append,
    edgeMoment_autoSteps φ Finset.univ L cur hg (fun _ _ _ _ => Finset.mem_univ _),
    edgeMoment_closeGauges φ A C ws _ hn,
    (valid_autoSteps L cur (fun _ => False) hg hc).2,
    Finset.sum_add_distrib, ← List.sum_toFinset _ hn, ← Finset.sum_filter]
  congr 2
  ext w
  simp

end
end IntegerMultBounds.MathlibTM2.M8.Global
