module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeRun
public import IntegerMultBounds.MathlibTM2.M8.Global.FrameMoments
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotCount
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Donors

/-!
# The interchange count of the PR97 node

The node's interchanges are the sums of the move costs along each wire (`edgeRanks_autoSteps`).
Along a contract role the frames increase, so its cost is its rise in rank: `528` for `X S T`
(from `P_S ⊗ Q_T`, of rank one, to `1`) and for `Y S T` (from `0` to `1 − P_S ⊗ Q_T`), and `529`
for a side slot (from `0` to `1`). Each centre temporary makes one move of the rank of its star
frame, at most `22` (`rank_starFrame_le`), and each correction temporary one move of rank one.
With `28866` side slots per invocation (`slot_count`), the node makes at most
`s₀ = 57403754177` interchanges (`calls_node_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-! ### The slot count -/

theorem countP_range (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((Finset.range n).filter p).card = (List.range n).countP fun k => decide (p k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append, ← ih]
    by_cases h : p n
    · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp)]; simp [h]
    · rw [ite_eq_right h]; simp [h]

theorem dag_donors : dag.donors.card = 38741 := by
  rw [Dag.donors, countP_range, ← donors_count]
  congr 1
  funext n
  simp [dag, Option.isSome_map]

/-- **The slot count**: `28866` side slots per invocation. -/
theorem slot_count : dag.compile.next = 28866 := by
  have h := dag.compile_next dag_valid
  rw [dag_donors] at h
  have h1 : dag.N = 64042 := rfl
  have h2 : dag.v = 1771 := rfl
  have h3 : dag.rootCount = 5336 := rfl
  rw [h1, h2, h3] at h
  clear h1 h2 h3
  generalize dag.compile.next = x at h ⊢
  omega

/-! ### Ranks of the frames -/

theorem tvec_ne_zero {T : Finset ℕ} (hT : IsTriple T) : tvec T ≠ 0 := by
  obtain ⟨c, hc⟩ : T.Nonempty := Finset.card_pos.mp (by rw [hT.1]; norm_num)
  intro h
  have := congrFun h ⟨c, hT.2 c hc⟩
  simp [tvec, hc] at this

theorem rank_lineFrame {T : Finset ℕ} (hT : IsTriple T) : (lineFrame T).rank = 1 := by
  obtain ⟨c, hc⟩ : T.Nonempty := Finset.card_pos.mp (by rw [hT.1]; norm_num)
  rw [lineFrame, frameOf_rank (instar_single hT hc)]
  have hsub := basisOf_sub ({T} : Finset (Finset ℕ))
  have hle : (basisOf ({T} : Finset (Finset ℕ))).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp [vecs])
  have hne : (basisOf ({T} : Finset (Finset ℕ))).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hspan := basisOf_span ({T} : Finset (Finset ℕ))
    rw [he, Finset.coe_empty, Submodule.span_empty] at hspan
    have : tvec T ∈ Submodule.span ℚ ((vecs {T} : Finset _) : Set (Fin 23 → ℚ)) :=
      Submodule.subset_span (by simp [vecs])
    rw [← hspan, Submodule.mem_bot] at this
    exact tvec_ne_zero hT this
  have := hne.card_pos
  omega

theorem rank_lineOf (k : V) : (lineOf k).rank = 1 := rank_lineFrame (leafTriple_isTriple k.2)

theorem rank_starFrame_le {c : ℕ} (hc : c < 23) : (starFrame c).rank ≤ 22 := by
  rw [starFrame, frameOf_rank (starSet_mem hc)]
  have hind := basisOf_ind (starSet c)
  have hfin := finrank_span_eq_card hind
  rw [Subtype.range_coe_subtype, Fintype.card_coe] at hfin
  have hspan : Submodule.span ℚ {x | x ∈ basisOf (starSet c)} ≤ starSpace c := by
    rw [show {x | x ∈ basisOf (starSet c)} = ((basisOf (starSet c) : Finset _) : Set (Fin 23 → ℚ))
      from rfl, basisOf_span, Submodule.span_le]
    intro w hw
    exact vecs_star (starSet_mem hc) w hw
  have hlt : starSpace c < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hmem : (Pi.single ⟨c, hc⟩ 1 : Fin 23 → ℚ) ∈ starSpace c := htop ▸ Submodule.mem_top
    have := sum_eq_of_mem_star hc hmem
    simp at this
  have h1 := Submodule.finrank_mono hspan
  have h2 := Submodule.finrank_lt hlt.ne
  rw [Module.finrank_fin_fun] at h2
  omega

theorem rank_one529 : (1 : Mat 529).rank = 529 := by
  rw [rank_one, Fintype.card_fin]

theorem rank_uFrame (S T : V) : (uFrame S T).rank = 1 := by
  rw [uFrame, kron_rank (lineOf_idem S) (lineOf_idem T), rank_lineOf, rank_lineOf]

theorem rank_one_sub_uFrame (S T : V) : (1 - uFrame S T).rank = 528 := by
  have hU : IsFrame (uFrame S T) := lframe_lift1 T (lframe_lineOf S)
  have := rank_sub_of_le hU.idem (isFrame_one (d := 529)).idem (le_one _)
  rw [rank_uFrame, rank_one529] at this
  omega

/-! ### Costs along the wires -/

theorem moveRank_le_rank {d : ℕ} (A B : Mat d) : moveRank A B ≤ (A - B).rank := by
  unfold moveRank
  split_ifs
  · exact Nat.zero_le _
  · rw [← neg_sub, rank_neg]
  · exact le_rfl

theorem chainCost_const {d : ℕ} (a : Mat d) (l : List ℕ) :
    chainCost (a :: l.map fun _ => a) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, chainCost_cons_cons, ih]
    simp [moveRank]

theorem chainCost_temp {d : ℕ} (a b : Mat d) (l : List ℕ) :
    chainCost (a :: a :: l.map fun _ => b) ≤ (a - b).rank := by
  rw [chainCost_cons_cons, show moveRank a a = 0 by simp [moveRank], zero_add]
  cases l with
  | nil => exact Nat.zero_le _
  | cons x l =>
    rw [List.map_cons, chainCost_cons_cons, chainCost_const, add_zero]
    exact moveRank_le_rank a b

theorem chainCost_append_single {d : ℕ} : ∀ (l : List (Mat d)) (a x : Mat d),
    chainCost ((a :: l) ++ [x]) = chainCost (a :: l) + moveRank ((a :: l).getLast (by simp)) x
  | [], a, x => by simp [chainCost]
  | b :: l, a, x => by
    rw [List.cons_append, List.cons_append, chainCost_cons_cons, ← List.cons_append,
      chainCost_append_single l b x, chainCost_cons_cons, List.getLast_cons_cons]
    ring

theorem fseq_frames {ι : Type} [DecidableEq ι] {d : ℕ} {w : ι} {L : List (FGate ι d)} {f : Mat d}
    (hf : f ∈ fseq w L) : ∃ v ∈ L, v.frame = f := by
  simp only [fseq, List.mem_map, List.mem_filter] at hf
  obtain ⟨v, ⟨hv, -⟩, rfl⟩ := hf
  exact ⟨v, hv, rfl⟩

theorem node_idem (w : Wire) : ∀ f ∈ gInit w :: fseq w allGates, f * f = f := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact (isFrame_gInit w).idem
  · obtain ⟨v, hv, rfl⟩ := fseq_frames hf
    exact (gatesOk_node v hv).1.idem

/-- The last frame of a wire. -/
def lastFrame (w : Wire) : Mat 529 := (fseq w allGates).getLast?.getD (gInit w)

theorem getD_getLast? {α : Type*} (a : α) (l : List α) :
    l.getLast?.getD a = (a :: l).getLast (by simp) := by
  cases l with
  | nil => rfl
  | cons b l => simp [List.getLast?_eq_some_getLast]

theorem lastFrame_eq (w : Wire) :
    lastFrame w = (gInit w :: fseq w allGates).getLast (by simp) := by
  rw [lastFrame]
  exact getD_getLast? _ _

/-- The cost along a wire, with its sink. -/
def wireCost (w : Wire) : ℕ :=
  chainCost (gInit w :: fseq w allGates) + if w ∈ sideWires then moveRank (lastFrame w) 1 else 0

/-- **Interchanges of an aligned list with sinks**, as a sum over the wires. Generic, so that the
node's sums match it syntactically and the kernel never compares closed sums over the node's
wires. -/
theorem calls_sinks {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (L : List (FGate ι d))
    (cur : ι → Mat d) (hg : GatesOk L) (hc : ChainOk cur L) {ws : List ι} (hnd : ws.Nodup)
    [DecidablePred (· ∈ ws)] :
    calls (physOf (autoSteps cur L ++ alignMoves (finalFrames (autoSteps cur L) cur) ws 1)) =
      ∑ w, (chainCost (cur w :: fseq w L) +
        if w ∈ ws then moveRank ((fseq w L).getLast?.getD (cur w)) 1 else 0) := by
  rw [calls_physOf, edgeRanks_append,
    edgeRanks_autoSteps Finset.univ L cur hg (fun _ _ _ _ => Finset.mem_univ _),
    edgeRanks_alignMoves _ _ _ hnd, (valid_autoSteps L cur (fun _ => False) hg hc).2,
    Finset.sum_add_distrib, ← List.sum_toFinset _ hnd, ← Finset.sum_filter]
  congr 2
  ext w
  simp

theorem calls_node_eq : calls (physOf framedNode) = ∑ w, wireCost w := by
  rw [framedNode, sinks]
  exact calls_sinks allGates gInit gatesOk_node chainOk_node sideWires_nodup

/-- A bound on each wire's cost, by its kind: data `X`, data `Y`, side slot, centre temporary,
correction temporary, unused wire. Generic over the six kinds, so that its sum is computed with
the kinds as variables (`sum_costBoundOf`). -/
def costBoundOf {A B C D E F : Type} : (A ⊕ B ⊕ C) ⊕ (D ⊕ E ⊕ F) → ℕ
  | .inl (.inl _) => 528
  | .inl (.inr (.inl _)) => 528
  | .inl (.inr (.inr _)) => 529
  | .inr (.inl _) => 22
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr _)) => 0

abbrev costBound : Wire → ℕ := costBoundOf

theorem sum_costBoundOf {A B C D E F : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] :
    ∑ w : (A ⊕ B ⊕ C) ⊕ (D ⊕ E ⊕ F), costBoundOf w = 528 * Fintype.card A +
      528 * Fintype.card B + 529 * Fintype.card C + 22 * Fintype.card D + Fintype.card E := by
  simp only [Fintype.sum_sum_type, costBoundOf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

theorem getLast_snoc {α : Type*} (a x : α) (l : List α) (h : a :: (l ++ [x]) ≠ []) :
    (a :: (l ++ [x])).getLast h = x := by
  simp

theorem wireCost_le (w : Wire) : wireCost w ≤ costBound w := by
  rcases w with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · -- `X S T`
    have hnot : (wX S T) ∉ sideWires := fun h => by
      obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wX, wSide] at h
    have hc := chainCost_mono _ _ (pairwise_wX S T).isChain (node_idem (wX S T))
    rw [fseq_wX, getLast_snoc, rank_one529, show gInit (wX S T) = uFrame S T from rfl,
      rank_uFrame] at hc
    show chainCost (gInit (wX S T) :: fseq (wX S T) allGates) +
      (if wX S T ∈ sideWires then moveRank (lastFrame (wX S T)) 1 else 0) ≤ 528
    rw [ite_eq_right hnot, add_zero, fseq_wX, show gInit (wX S T) = uFrame S T from rfl]
    omega
  · -- `Y S T`
    have hnot : (wY S T) ∉ sideWires := fun h => by
      obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wY, wSide] at h
    have hc := chainCost_mono _ _ (pairwise_wY S T).isChain (node_idem (wY S T))
    rw [fseq_wY, getLast_snoc, rank_one_sub_uFrame, show gInit (wY S T) = 0 from rfl,
      rank_zero] at hc
    show chainCost (gInit (wY S T) :: fseq (wY S T) allGates) +
      (if wY S T ∈ sideWires then moveRank (lastFrame (wY S T)) 1 else 0) ≤ 528
    rw [ite_eq_right hnot, add_zero, fseq_wY, show gInit (wY S T) = 0 from rfl]
    omega
  · -- a side slot
    have hin : wSide b k s ∈ sideWires := mem_sideWires.mpr ⟨b, k, s, rfl⟩
    have hpw : (gInit (wSide b k s) :: (fseq (wSide b k s) allGates ++ [1])).Pairwise Le := by
      rw [← List.cons_append]
      refine pw_app ?_ (List.pairwise_singleton _ _) fun a _ x hx => by
        rw [List.mem_singleton.mp hx]; exact le_one a
      cases b
      · exact pairwise_side1 k s
      · exact pairwise_side2 k s
    have hid : ∀ f ∈ gInit (wSide b k s) :: (fseq (wSide b k s) allGates ++ [1]), f * f = f := by
      intro f hf
      rw [← List.cons_append] at hf
      rcases List.mem_append.mp hf with hf | hf
      · exact node_idem _ f hf
      · rw [List.mem_singleton.mp hf]; simp
    have hc := chainCost_mono _ _ hpw.isChain hid
    have h0 : (gInit (wSide b k s)).rank = 0 := by
      rw [show gInit (wSide b k s) = 0 from rfl, rank_zero]
    rw [getLast_snoc, rank_one529, h0] at hc
    show chainCost (gInit (wSide b k s) :: fseq (wSide b k s) allGates) +
      (if wSide b k s ∈ sideWires then moveRank (lastFrame (wSide b k s)) 1 else 0) ≤ 529
    rw [ite_eq_left hin, lastFrame_eq, ← chainCost_append_single, List.cons_append]
    omega
  · -- a centre temporary
    cases b
    · show chainCost (gInit (wCentre false k c) :: fseq (wCentre false k c) allGates) +
        (if wCentre false k c ∈ sideWires then _ else 0) ≤ 22
      rw [ite_eq_right (fun h => by obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wCentre, wSide] at h),
        add_zero, fseq_centre1, fseq1_tmp, show gInit (wCentre false k c) = lift1 (lineOf k) (starFrame c)
        from rfl, List.map_cons, List.map_map]
      refine (chainCost_temp _ (lift1 (lineOf k) 0) _).trans ?_
      rw [lift1_zero, sub_zero, lift1, kron_rank (smallFrame_star c.2).idem (lineOf_idem k),
        rank_lineOf, mul_one]
      exact rank_starFrame_le c.2
    · show chainCost (gInit (wCentre true k c) :: fseq (wCentre true k c) allGates) +
        (if wCentre true k c ∈ sideWires then _ else 0) ≤ 22
      rw [ite_eq_right (fun h => by obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wCentre, wSide] at h),
        add_zero, fseq_centre2, fseq2_tmp, show gInit (wCentre true k c) = lift2 (lineOf k) (1 - starFrame c)
        from rfl, List.map_cons, List.map_map]
      refine (chainCost_temp _ (lift2 (lineOf k) 1) _).trans ?_
      rw [← neg_sub, rank_neg, rank_lift2_sub (lineOf_idem k) (smallFrame_star c.2).compl.idem
        (by simp) (le_one _), rank_lineOf, one_mul, sub_sub_cancel]
      exact rank_starFrame_le c.2
  · -- a correction temporary
    show chainCost (gInit (wCorr S T) :: fseq (wCorr S T) allGates) +
      (if wCorr S T ∈ sideWires then _ else 0) ≤ 1
    rw [ite_eq_right (fun h => by obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wCorr, wSide] at h),
      add_zero, fseq_wCorr, show gInit (wCorr S T) = 1 from rfl]
    have := chainCost_temp (1 : Mat 529) (1 - uFrame S T) [0]
    rw [sub_sub_cancel, rank_uFrame] at this
    exact this
  · show chainCost (gInit wJunk :: fseq wJunk allGates) + (if wJunk ∈ sideWires then _ else 0) ≤ 0
    rw [ite_eq_right (fun h => by obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wJunk, wSide] at h),
      fseq_wJunk]
    rfl

/-! The counts of wires are rewritten with lemmas stated on `V` and `Slot` themselves: a
rewrite whose instance differs from the goal by unfolding `V` or `Slot` leaves the kernel a closed
arithmetic comparison, which it settles by evaluating `Fintype.card Slot`, so by running the
compiler. -/

theorem card_V : Fintype.card V = leafCount := Fintype.card_fin _

theorem card_Slot : Fintype.card Slot = dag.compile.next := Fintype.card_fin _

theorem card_pairs : Fintype.card (V × V) = 1771 * 1771 := by
  rw [Fintype.card_prod V V, card_V]
  rfl

theorem card_sides : Fintype.card (Bool × V × Slot) = 2 * (1771 * 28866) := by
  rw [Fintype.card_prod Bool (V × Slot), Fintype.card_prod V Slot, Fintype.card_bool, card_V,
    card_Slot, slot_count]
  rfl

theorem card_centres : Fintype.card (Bool × V × Fin 23) = 2 * (1771 * 23) := by
  rw [Fintype.card_prod Bool (V × Fin 23), Fintype.card_prod V (Fin 23), Fintype.card_bool,
    card_V, Fintype.card_fin 23]
  rfl

/-- **The interchange count of the node** is at most `s₀ = 57403754177`. -/
theorem calls_node_le : calls (physOf framedNode) ≤ 57403754177 := by
  rw [calls_node_eq]
  refine (Finset.sum_le_sum fun w _ => wireCost_le w).trans (le_of_eq ?_)
  rw [sum_costBoundOf, card_centres, card_sides, card_pairs]

end

end IntegerMultBounds.MathlibTM2.M8.Global
