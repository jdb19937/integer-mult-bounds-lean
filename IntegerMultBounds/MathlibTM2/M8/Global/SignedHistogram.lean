module

public import IntegerMultBounds.MathlibTM2.M8.Global.LocalSteps
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedMoves

/-! A checked signed chain contributes its exact rank-step histogram. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.MathlibTM2.M8.Frames Local

private theorem bump_addH : ∀ (e : Nat) (a b : List Nat), a.length = b.length →
    bump e (addH a b) = addH (bump e a) b
  | e, [], [], _ => by cases e <;> rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | 0, x :: a, y :: b, _ => by
    simp only [bump, addH]
    congr 1
    change x + y + 1 = (x + 1) + y
    omega
  | e + 1, x :: a, y :: b, h => by
    simp only [bump, addH]
    rw [bump_addH e a b (by simpa using h)]

private theorem addH_zero_left : ∀ b : List Nat, addH (List.replicate b.length 0) b = b
  | [] => rfl
  | x :: b => by
    simp only [List.length_cons, List.replicate_succ, addH]
    rw [addH_zero_left b]
    change (0 + x) :: b = x :: b
    rw [Nat.zero_add]

/-- Histograms preserve concatenation; no step codes are inspected again. -/
theorem histOf_append (xs ys : List Nat) : histOf (xs ++ ys) = addH (histOf xs) (histOf ys) := by
  induction xs with
  | nil =>
    have hz : zeros = List.replicate (histOf ys).length 0 := by rw [length_histOf]; rfl
    simp only [List.nil_append, histOf]
    rw [hz, addH_zero_left]
  | cons x xs ih =>
    rw [List.cons_append, histOf, histOf, ih,
      bump_addH x _ _ ((length_histOf xs).trans (length_histOf ys).symm)]

/-- Zero padding past a checked finite table does not change its sum. -/
theorem sum_range_padded (f : Nat → ℝ) (n k : Nat) (hn : n ≤ k) :
    (∑ i ∈ Finset.range k, if i < n then f i else 0) = ∑ i ∈ Finset.range n, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Convert a consecutive index list to the corresponding finite sum. -/
theorem sum_map_range' (f : Nat → ℝ) (s n : Nat) :
    ((List.range' s n).map f).sum = ∑ i ∈ Finset.range n, f (s + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_concat, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Certified signed frames have ranks at most their ambient dimension. -/
theorem signed_rankValue_le (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (f : Signed.Frame)
    (hf : f.validCheck size = true) : f.rankValue bank ≤ 23 := by
  rw [← f.rank_eval bank size hbank hf]
  simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (f.eval bank)

/-- Every nonzero step code in a checked 23-dimensional chain is below 24. -/
theorem signed_rankSteps_lt (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) :
    ∀ fs, (∀ f ∈ fs, f.validCheck size = true) →
      ∀ r ∈ Signed.rankSteps bank fs, r < 24
  | [], _, _, h => by simp [Signed.rankSteps] at h
  | [_], _, _, h => by simp [Signed.rankSteps] at h
  | a :: b :: fs, hv, r, hr => by
    have ht := signed_rankSteps_lt bank size hbank (b :: fs)
      (fun f hf => hv f (List.mem_cons_of_mem a hf))
    have hb := signed_rankValue_le bank size hbank b (hv b (by simp))
    simp only [Signed.rankSteps] at hr
    split_ifs at hr with hz
    · exact ht r hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · omega
      · exact ht r hr

/-- Positive move codes evaluate directly under the requested cost function. -/
theorem evalL_eq_sum (φ : Nat → ℝ) (fs : List Nat) (hf : ∀ r ∈ fs, r < 24) :
    evalL φ fs = (fs.map φ).sum := by
  unfold evalL
  congr 1
  apply List.map_congr_left
  intro r hr
  exact ite_eq_left (hf r hr)

/-- The finite histogram of a signed chain is its actual matrix move moment. -/
theorem signed_chainMoment_eq_hist (φ : Nat → ℝ) (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (fs : List Signed.Frame)
    (hf : Signed.chainCheck bank size fs = true) :
    chainMoment φ (fs.map (Signed.Frame.eval bank)) = evalH φ (histOf (Signed.rankSteps bank fs)) := by
  have hb := signed_rankSteps_lt bank size hbank fs (Signed.chainCheck_valid bank size fs hf)
  rw [Signed.chainMoment_rankSteps φ bank size hbank fs hf,
    evalH_histOf φ _ (fun r hr => (hb r hr).trans (by decide)), evalL_eq_sum φ _ hb]

/-- A finite list of chain indices is aggregated without assumptions about their ordering. -/
theorem signed_chains_hist_eq (φ : Nat → ℝ) (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (chain : Nat → List Signed.Frame)
    (hc : ∀ i, Signed.chainCheck bank size (chain i) = true) (ids : List Nat) :
    evalH φ (histOf (ids.flatMap (fun i => Signed.rankSteps bank (chain i)))) =
      (ids.map (fun i => chainMoment φ ((chain i).map (Signed.Frame.eval bank)))).sum := by
  have hb : ∀ r ∈ ids.flatMap (fun i => Signed.rankSteps bank (chain i)), r < 24 := by
    intro r hr
    obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
    exact signed_rankSteps_lt bank size hbank _ (Signed.chainCheck_valid bank size _ (hc i)) r hr
  rw [evalH_histOf φ _ (fun r hr => (hb r hr).trans (by decide)), evalL_eq_sum φ _ hb]
  clear hb
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [ih, Signed.chainMoment_rankSteps φ bank size hbank _ (hc i)]

/-- The tree histogram counts actual chain moments at its physical-slot indices. -/
theorem signed_tree_hist_eq {α : Type} (φ : Nat → ℝ) (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (chain : Nat → List Signed.Frame)
    (hc : ∀ i, Signed.chainCheck bank size (chain i) = true) (index : Nat → α → Nat)
    (bound : Nat) (t : Local.Tree α) (w n : Nat) (ht : t.Perfect w) :
    evalH φ (Local.Tree.hist (fun n x => Signed.rankSteps bank (chain (index n x))) bound t n w) =
      ∑ i ∈ Finset.range w, if n + i < bound then
        chainMoment φ ((chain (index (n + i) (t.get w i))).map (Signed.Frame.eval bank)) else 0 := by
  have hb (i : Nat) : ∀ r ∈ Signed.rankSteps bank (chain i), r < 24 :=
    signed_rankSteps_lt bank size hbank _ (Signed.chainCheck_valid bank size _ (hc i))
  rw [(hist_spec φ _ bound t w n ht (fun i _ _ r hr => (hb _ r hr).trans (by decide))).2]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [evalL_eq_sum φ _ (hb _)]
    exact (Signed.chainMoment_rankSteps φ bank size hbank _ (hc _)).symm
  · rfl

end
end IntegerMultBounds.MathlibTM2.M8.Global
