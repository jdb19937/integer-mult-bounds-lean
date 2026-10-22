module

public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.Kernel
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootFacts

/-! A passed target check bounds the exact readout chain by its output hyperplane. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
noncomputable section
open IntegerMultBounds Matrix Local

theorem targetOk_chain (t endpoint : Nat) (h : targetOk t endpoint = true) :
    List.IsChain Nested
      (0 :: (readoutLabels t).map (Signed.Frame.eval SignedFull.bankEntry) ++
        [rootFrame (SignedFull.bankEntry endpoint).basis]) := by
  unfold targetOk at h
  have hp := GeometryB.chainAt_path (28866 + t) _ (Bool.and_eq_true_iff.mp h).1
  simpa only [List.map_cons, List.map_append, List.map_singleton, List.map_nil, Signed.Frame.eval,
    RootBank.Record.frame] using hp

theorem targetOk_endpoint (t endpoint : Nat) (ht : t < leafCount)
    (h : targetOk t endpoint = true) :
    Nested (rootFrame (SignedFull.bankEntry endpoint).basis) (hyperFrame (leafTriple t)) := by
  unfold targetOk at h
  have hmem := (Bool.and_eq_true_iff.mp h).2
  have hspan : rvec (GeometryB.rootCode (3 * t)) ∈ rspan (SignedFull.bankEntry endpoint).basis :=
    Submodule.subset_span (List.mem_map_of_mem (List.contains_iff_mem.mp hmem))
  rw [rootCode_output (3 * t) (by omega)] at hspan
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 3)] at hspan
  exact rootFrame_le_hyper_of_unit
    (RootBank.Record.check_spec (SignedFull.bankEntry_checked endpoint)).2.1 hspan

/-- Replacing the last endpoint by a larger frame preserves the chain. -/
theorem pairwise_replace_last {α : Type*} {R : α → α → Prop} {xs : List α} {a b : α}
    (h : (xs ++ [a]).Pairwise R) (hab : R a b)
    (htrans : ∀ x y z, R x y → R y z → R x z) : (xs ++ [b]).Pairwise R := by
  obtain ⟨hx, _, ha⟩ := List.pairwise_append.mp h
  apply List.pairwise_append.mpr
  refine ⟨hx, by simp, ?_⟩
  intro x hx y hy
  have hy : y = b := List.mem_singleton.mp hy
  subst y
  exact htrans x a b (ha x hx a (by simp)) hab

theorem targetOk_readout_chain (t endpoint : Nat) (ht : t < leafCount)
    (h : targetOk t endpoint = true) :
    (0 :: (readoutLabels t).map (Signed.Frame.eval SignedFull.bankEntry) ++
      [hyperFrame (leafTriple t)]).Pairwise Nested := by
  let : IsTrans _ Nested := ⟨fun _ _ _ h h' => h.trans h'⟩
  have hp := List.isChain_iff_pairwise.mp (targetOk_chain t endpoint h)
  exact pairwise_replace_last hp (targetOk_endpoint t endpoint ht h)
    (fun _ _ _ h h' => h.trans h')

end
end IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
