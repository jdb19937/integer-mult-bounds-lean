module

public import IntegerMultBounds.MathlibTM2.M8.Global.LocalMoments
public import IntegerMultBounds.MathlibTM2.M8.Global.LocalRanks
public import IntegerMultBounds.MathlibTM2.M8.Global.NodeCost
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.StepsAll

/-!
# The local steps of the side slots

For `φ` with `φ 0 = 0`, the local moments of the side slots are the moment of the local-step
histogram `localSteps` (`sum_localMoment_eq`), the table of `scripts/pr97/stage2hist.py`.

Every move along a slot is between nested frames, so its moment is `φ` at the difference of
their ranks (`stepMoment_rank`), and the ranks are the table `dims` (`nodeFrame_rank`). By
`sum_localMoment` and `Dag.slotSum_uses`, the slot moves are a sum over the additions, the free
uses and the roots; each node's and each root's share is its formal list of moves (`nodeFS`,
`rootFS`, `node_share`, `root_share`), and the checks of `Checks/Steps*` count those lists.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames

noncomputable section

/-! ### Counting moves -/

section Hist

variable (ψ : ℕ → ℝ)

/-- The weight of a move code: `r` counts `ψ r`, `24 + r` counts `- ψ r`. -/
def wt (e : ℕ) : ℝ := if e < 24 then ψ e else -ψ (e - 24)

/-- The weight of a list of moves. -/
def evalL (fs : List ℕ) : ℝ := (fs.map (wt ψ)).sum

/-- The weight of a count by code. -/
def evalH (h : List ℕ) : ℝ := ∑ i ∈ Finset.range 48, (h.getD i 0 : ℝ) * wt ψ i

theorem length_bump : ∀ (e : ℕ) (h : List ℕ), (bump e h).length = h.length
  | e, [] => by cases e <;> rfl
  | 0, _ :: _ => rfl
  | e + 1, _ :: h => by simp [bump, length_bump e h]

theorem getD_bump : ∀ (e : ℕ) (h : List ℕ) (i : ℕ),
    (bump e h).getD i 0 = h.getD i 0 + if i = e ∧ e < h.length then 1 else 0
  | e, [], i => by cases e <;> simp [bump]
  | 0, _ :: _, 0 => by simp [bump]
  | 0, _ :: _, i + 1 => by simp [bump]
  | e + 1, _ :: _, 0 => by simp [bump]
  | e + 1, x :: h, i + 1 => by
    rw [show bump (e + 1) (x :: h) = x :: bump e h from rfl, List.getD_cons_succ,
      List.getD_cons_succ, getD_bump e h i]
    simp

theorem zeros_eq : zeros = List.replicate 48 0 := rfl

theorem evalH_zeros : evalH ψ zeros = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [zeros_eq, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

theorem evalH_bump {e : ℕ} (he : e < 48) {h : List ℕ} (hl : h.length = 48) :
    evalH ψ (bump e h) = evalH ψ h + wt ψ e := by
  simp only [evalH, getD_bump, hl, he, and_true, Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range 48) e, ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_range.mpr he) h)]

theorem length_histOf : ∀ fs : List ℕ, (histOf fs).length = 48
  | [] => rfl
  | e :: fs => by rw [histOf, length_bump, length_histOf fs]

theorem evalH_histOf : ∀ fs : List ℕ, (∀ e ∈ fs, e < 48) → evalH ψ (histOf fs) = evalL ψ fs
  | [], _ => by rw [histOf, evalH_zeros]; rfl
  | e :: fs, h => by
    rw [histOf, evalH_bump ψ (h e (List.mem_cons_self ..)) (length_histOf fs),
      evalH_histOf fs fun x hx => h x (List.mem_cons_of_mem _ hx), evalL, evalL, List.map_cons,
      List.sum_cons, add_comm]

theorem length_addH : ∀ a b : List ℕ, a.length = b.length → (addH a b).length = a.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: a, _ :: b, h => by simp [addH, length_addH a b (by simpa using h)]

theorem getD_addH : ∀ a b : List ℕ, a.length = b.length → ∀ i,
    (addH a b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], [], _, i => by simp [addH]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: a, _ :: b, h, 0 => by simp [addH]
  | x :: a, y :: b, h, i + 1 => by
    rw [show addH (x :: a) (y :: b) = Nat.add x y :: addH a b from rfl, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ, getD_addH a b (by simpa using h) i]

theorem evalH_addH {a b : List ℕ} (h : a.length = b.length) :
    evalH ψ (addH a b) = evalH ψ a + evalH ψ b := by
  simp only [evalH, getD_addH a b h, Nat.cast_add, add_mul, Finset.sum_add_distrib]

/-- **The count of a subtree** weighs the moves of its entries below the bound. -/
theorem hist_spec {α : Type} (f : ℕ → α → List ℕ) (bound : ℕ) :
    ∀ (t : Local.Tree α) (w n : ℕ), t.Perfect w →
      (∀ i < w, n + i < bound → ∀ e ∈ f (n + i) (t.get w i), e < 48) →
      (Tree.hist f bound t n w).length = 48 ∧
        evalH ψ (Tree.hist f bound t n w) =
          ∑ i ∈ Finset.range w, if n + i < bound then evalL ψ (f (n + i) (t.get w i)) else 0
  | .leaf v, w, n, hp, hf => by
    simp only [Tree.Perfect] at hp
    subst hp
    have hf0 := hf 0 (by norm_num)
    simp only [Tree.hist, cond_ite, blt_iff, Finset.sum_range_one, Nat.add_zero, Tree.get_leaf] at hf0 ⊢
    split_ifs with hn
    · exact ⟨length_histOf _, evalH_histOf ψ _ (hf0 hn)⟩
    · exact ⟨rfl, evalH_zeros ψ⟩
  | .node l r, w, n, hp, hf => by
    obtain ⟨hw, hev, hl, hr⟩ := hp
    have hw2 : w = w / 2 + w / 2 := by omega
    have hfl : ∀ i < w / 2, n + i < bound → ∀ e ∈ f (n + i) (l.get (w / 2) i), e < 48 := by
      intro i hi hb e he
      refine hf i (by omega) hb e ?_
      rwa [Tree.get_node, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    have hfr : ∀ i < w / 2, n + w / 2 + i < bound → ∀ e ∈ f (n + w / 2 + i) (r.get (w / 2) i),
        e < 48 := by
      intro i hi hb e he
      have := hf (w / 2 + i) (by omega) (by omega) e
      rw [Tree.get_node, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show w / 2 + i - w / 2 = i by omega,
        show n + (w / 2 + i) = n + w / 2 + i by omega] at this
      exact this he
    obtain ⟨hl1, hl2⟩ := hist_spec f bound l (w / 2) n hl hfl
    obtain ⟨hr1, hr2⟩ := hist_spec f bound r (w / 2) (n + w / 2) hr hfr
    rw [Local.Tree.hist_node, length_addH _ _ (hl1.trans hr1.symm), evalH_addH ψ (hl1.trans hr1.symm),
      hl2, hr2, hl1]
    refine ⟨rfl, ?_⟩
    have hsplit := Finset.sum_range_add
      (fun i => if n + i < bound then evalL ψ (f (n + i) ((Local.Tree.node l r).get w i)) else 0)
      (w / 2) (w / 2)
    rw [← hw2] at hsplit
    rw [hsplit]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      simp only [Local.Tree.get_node, hi', ↓reduceIte]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hi' : ¬ w / 2 + i < w / 2 := by omega
      simp only [Local.Tree.get_node, hi', ↓reduceIte, Nat.add_sub_cancel_left,
        show n + (w / 2 + i) = n + w / 2 + i by omega]

theorem evalL_append (a b : List ℕ) : evalL ψ (a ++ b) = evalL ψ a + evalL ψ b := by
  simp [evalL]

theorem evalL_nil : evalL ψ [] = 0 := rfl

theorem wt_lt {e : ℕ} (h : e < 24) : wt ψ e = ψ e := ite_eq_left_of_eq_true _ _ (eq_true h)

theorem wt_neg {x : ℕ} (h : x < 24) : wt ψ (neg x) = -ψ x := by
  rw [wt, neg, Nat.add_eq, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]

theorem evalL_freeFS {d : ℕ} (hd : d ≤ 23) : evalL ψ (freeFS d) = ψ d + ψ (23 - d) - ψ 23 := by
  simp only [freeFS, evalL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.sub_eq]
  simp only [wt, neg, Nat.add_eq, Nat.add_sub_cancel_left, show d < 24 by omega,
    show 23 - d < 24 by omega, show ¬ 24 + 23 < 24 by omega, ↓reduceIte]
  ring

theorem evalL_addFS {dk da db : ℕ} (hk : dk ≤ 23) (ha : da ≤ 23) (hb : db ≤ 23) :
    evalL ψ (addFS dk da db) = ψ (dk - da) + ψ (23 - dk) - ψ (23 - da) + ψ (dk - db) +
      ψ (23 - dk) - ψ (23 - db) - ψ dk - ψ (23 - dk) + ψ 23 := by
  simp only [addFS, evalL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.sub_eq]
  simp only [wt, neg, Nat.add_eq, Nat.add_sub_cancel_left, show dk - da < 24 by omega,
    show dk - db < 24 by omega, show 23 - dk < 24 by omega, show (23 : ℕ) < 24 by omega,
    show ¬ 24 + (23 - da) < 24 by omega, show ¬ 24 + (23 - db) < 24 by omega,
    show ¬ 24 + dk < 24 by omega, show ¬ 24 + (23 - dk) < 24 by omega, ↓reduceIte]
  ring

end Hist

/-! ### Moves between nested frames -/

section Shares

variable (φ : ℕ → ℝ) (h0 : φ 0 = 0)

theorem rank_one23 : (1 : LMat).rank = 23 := by
  rw [Matrix.rank_one, Fintype.card_fin]

include h0 in
/-- **A move between nested frames** weighs `φ` at their difference of ranks. -/
theorem stepMoment_rank {A B : LMat} (hA : A * A = A) (hB : B * B = B) (h : Le A B) :
    stepMoment φ A B = φ (B.rank - A.rank) := by
  unfold stepMoment
  split_ifs with hab
  · subst hab; rw [Nat.sub_self, h0]
  · have := moveRank_le hA hB h
    congr 1
    omega

include h0 in
theorem endM_rank {A : LMat} (hA : A * A = A) : endM φ A = φ (23 - A.rank) := by
  rw [endM, stepMoment_rank φ h0 hA (mul_one 1) (le_one A), rank_one23]

include h0 in
theorem cMove_some {m k : ℕ} (hm : m < nodeCount) (hk : k < nodeCount)
    (h : Le (nodeFrame m) (nodeFrame k)) :
    cMove φ (some m) k = φ (dims.get width k - dims.get width m) := by
  change stepMoment φ (nodeFrame m) (nodeFrame k) = _
  rw [stepMoment_rank φ h0 (nodeFrame_idem hm) (nodeFrame_idem hk) h, nodeFrame_rank hm,
    nodeFrame_rank hk]

include h0 in
theorem cMove_none {k : ℕ} (hk : k < nodeCount) : cMove φ none k = φ (dims.get width k) := by
  change stepMoment φ 0 (nodeFrame k) = _
  rw [stepMoment_rank φ h0 (mul_zero 0) (nodeFrame_idem hk) (zero_le _), Matrix.rank_zero,
    nodeFrame_rank hk, Nat.sub_zero]

include h0 in
theorem cEnd_some {m k : ℕ} (hm : m < nodeCount) (hk : k < nodeCount) :
    cEnd φ (some m) k = φ (23 - dims.get width k) - φ (23 - dims.get width m) := by
  change endM φ (nodeFrame k) - endM φ (nodeFrame m) = _
  rw [endM_rank φ h0 (nodeFrame_idem hk), endM_rank φ h0 (nodeFrame_idem hm), nodeFrame_rank hm,
    nodeFrame_rank hk]

include h0 in
theorem cEnd_none {k : ℕ} (hk : k < nodeCount) :
    cEnd φ none k = φ (23 - dims.get width k) - φ 23 := by
  change endM φ (nodeFrame k) - endM φ 0 = _
  rw [endM_rank φ h0 (nodeFrame_idem hk), endM_rank φ h0 (mul_zero 0), Matrix.rank_zero,
    nodeFrame_rank hk, Nat.sub_zero]

end Shares

/-! ### Sources of the arguments -/

theorem donorOk_some {k : ℕ} {pos : Bool} {m : ℕ} (h : donorOk records k pos (some m) = true) :
    m < nodeCount ∧ ∃ L, (recAt m).link = some L ∧ L.user = k ∧ L.pos = pos := by
  simp only [donorOk, Bool.and_eq_true, blt_iff] at h
  obtain ⟨hm, hl⟩ := h
  refine ⟨hm, ?_⟩
  split at hl
  · next L hL =>
    simp only [Bool.and_eq_true, beq_iff, beq_iff_eq] at hl
    exact ⟨L, hL, hl.1, hl.2⟩
  · cases hl

theorem donor_ok_at {k : ℕ} (hk : k < nodeCount) (pos : Bool) :
    donorOk records k pos ((recAt k).donor pos) = true := by
  have := allOk_parts (allOk_at k hk)
  cases pos
  · exact this.2.2.1
  · exact this.2.2.2.1

/-- The source of an argument is its donor, if any, and the argument is a free use exactly when
it has none. -/
theorem src_eq {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    dag.srcNode (.gate k pos) = ((recAt k).donor pos).getD ((recAt k).arg pos) ∧
      (dag.linkedB (.gate k pos) = false ↔ (recAt k).donor pos = none) := by
  cases hd : (recAt k).donor pos with
  | some m =>
    have hok := donor_ok_at hkN pos
    rw [hd] at hok
    obtain ⟨hm, L, hL, hu, hp⟩ := donorOk_some hok
    have hlink : dag.link m = some (L.operand, k, pos) := by simp [dag, hL, hu, hp]
    have hlu : dag.linkUse m = some (.gate k pos) := dag.linkUse_eq.mpr ⟨_, _, _, hlink, rfl⟩
    refine ⟨dag.srcNode_linked dag_valid hm hlu, ?_⟩
    rw [(dag.linkedB_iff _).mpr ⟨m, hm, hlu⟩]
    simp
  | none =>
    have hl : dag.linkedB (.gate k pos) = false := by
      rcases h : dag.linkedB (.gate k pos) with _ | _
      · rfl
      · obtain ⟨n, hn, hlu⟩ := (dag.linkedB_iff _).mp h
        obtain ⟨o, t, p, hlink, he⟩ := dag.linkUse_eq.mp hlu
        cases he
        obtain ⟨L, hL, -, hu, hp⟩ := dag_link hlink
        have := (linkOk_donor hL).2.2.2.2.2.1
        rw [hu, hp, hd] at this
        cases this
    refine ⟨?_, by simp [hl]⟩
    rw [dag.srcNode_free (y := dag.arg k pos)
      (dag.mem_freeUses.mpr ⟨(dag.mem_uses_gate _ k pos).mpr ⟨hkN, hk, rfl⟩, hl⟩)]
    rfl

theorem src_lt {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    ((recAt k).donor pos).getD ((recAt k).arg pos) < nodeCount := by
  cases hd : (recAt k).donor pos with
  | some m =>
    have hok := donor_ok_at hkN pos
    rw [hd] at hok
    exact (donorOk_some hok).1
  | none =>
    have h := nodeOk_add (allOk_parts (allOk_at k hkN)).1 (by omega)
    cases pos
    · exact h.2.1.trans hkN
    · exact h.2.2.1.trans hkN

theorem src_le {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    Le (nodeFrame (((recAt k).donor pos).getD ((recAt k).arg pos))) (nodeFrame k) := by
  have := dag.srcNode_arg_le dag_valid nodeLe_order hk hkN pos
  rw [(src_eq hk hkN pos).1] at this
  exact this (src_lt hk hkN pos) hkN

/-! ### Each node's and each root's share -/

section Share

variable (φ : ℕ → ℝ) (h0 : φ 0 = 0)

include h0 in
/-- **A node's share** of the slot moves is the weight of its formal moves: an addition moves its
argument slots from their sources, and each argument without a donor is a free use. -/
theorem node_share {k : ℕ} (hk : k < dag.N) :
    evalL φ (nodeFS dims k (recAt k)) =
      (if dag.v ≤ k then cMove φ (some (dag.srcNode (.gate k false))) k +
          cMove φ (some (dag.srcNode (.gate k true))) k - cMove φ none k else 0) +
        (if dag.v ≤ k then cEnd φ (some (dag.srcNode (.gate k false))) k +
          cEnd φ (some (dag.srcNode (.gate k true))) k - cEnd φ none k else 0) +
        (if dag.v ≤ k then
          ((if dag.linkedB (.gate k true) = false then cMove φ none (dag.arg k true) else 0) +
            if dag.linkedB (.gate k false) = false then cMove φ none (dag.arg k false) else 0)
          else 0) +
        (if dag.v ≤ k then
          ((if dag.linkedB (.gate k true) = false then cEnd φ none (dag.arg k true) else 0) +
            if dag.linkedB (.gate k false) = false then cEnd φ none (dag.arg k false) else 0)
          else 0) := by
  replace hk : k < nodeCount := hk
  by_cases hv : leafCount ≤ k
  · have hv' : dag.v ≤ k := hv
    obtain ⟨hA, ha, hb, -⟩ := nodeOk_add (allOk_parts (allOk_at k hk)).1 (by omega)
    have s0 := src_eq hv hk false
    have s1 := src_eq hv hk true
    have l0 := src_lt hv hk false
    have l1 := src_lt hv hk true
    have e0 := src_le hv hk false
    have e1 := src_le hv hk true
    simp only [NodeRec.donor, NodeRec.arg, Bool.cond_false, Bool.cond_true] at s0 s1 l0 l1 e0 e1
    have hak : (recAt k).a < nodeCount := ha.trans hk
    have hbk : (recAt k).b < nodeCount := hb.trans hk
    rw [s0.1, s1.1, cMove_some φ h0 l0 hk e0, cMove_some φ h0 l1 hk e1, cMove_none φ h0 hk,
      cEnd_some φ h0 l0 hk, cEnd_some φ h0 l1 hk, cEnd_none φ h0 hk,
      show dag.arg k false = (recAt k).a from rfl, show dag.arg k true = (recAt k).b from rfl,
      cMove_none φ h0 hak, cMove_none φ h0 hbk, cEnd_none φ h0 hak, cEnd_none φ h0 hbk]
    simp only [hv', ↓reduceIte, s0.2, s1.2]
    rw [nodeFS, hA, Bool.cond_true, evalL_append, evalL_append,
      evalL_addFS φ (dims_le hk) (dims_le l0) (dims_le l1)]
    have hda := dims_le hak
    have hdb := dims_le hbk
    cases hn0 : (recAt k).donor0 <;> cases hn1 : (recAt k).donor1 <;>
      simp [evalL_freeFS φ hda, evalL_freeFS φ hdb, evalL_nil] <;> ring
  · have hv' : ¬ dag.v ≤ k := hv
    have hA := (nodeOk_leaf (allOk_parts (allOk_at k hk)).1 (by omega)).1
    simp only [hv', ↓reduceIte, add_zero]
    rw [nodeFS, hA, Bool.cond_false]
    rfl

include h0 in
/-- **A root's share**: its free use, and its read frame on the way to `1`. -/
theorem root_share {j : ℕ} (hj : j < dag.rootCount) :
    evalL φ (rootFS dims j (rootAt j)) =
      cMove φ none (dag.rootNode j) + cEnd φ none (dag.rootNode j) + rootCorr φ j := by
  replace hj : j < rootCount := hj
  have hq : dag.rootNode j < nodeCount := root_node hj
  have hdq := dims_le hq
  rw [cMove_none φ h0 hq, cEnd_none φ h0 hq, rootCorr]
  change _ = _ + _ + (stepMoment φ (nodeFrame (dag.rootNode j)) (readFrame j) +
    stepMoment φ (readFrame j) 1 - endM φ (nodeFrame (dag.rootNode j)))
  rw [endM_rank φ h0 (nodeFrame_idem hq), nodeFrame_rank hq]
  have hnode : (rootAt j).node = dag.rootNode j := rfl
  rw [rootFS, hnode, evalL_append, evalL_freeFS φ hdq]
  by_cases hjo : j < 3 * leafCount
  · have ht : j / 3 < leafCount := by have : j < 3 * 1771 := hjo; show j / 3 < 1771; omega
    have hT := leafTriple_isTriple ht
    have hr : readFrame j = hyperFrame (leafTriple (j / 3)) := ite_eq_left_of_eq_true _ _ (eq_true hjo)
    have hrank : (hyperFrame (leafTriple (j / 3))).rank = 22 := by
      have := rank_sub_of_le (lineFrame_idem hT) (mul_one (1 : LMat)) (le_one (lineFrame (leafTriple (j / 3))))
      rw [rank_one23, rank_lineFrame hT] at this
      rw [hyperFrame]; omega
    rw [hr, stepMoment_rank φ h0 (nodeFrame_idem hq) (hyperFrame_idem hT) (rootNode_out hjo),
      stepMoment_rank φ h0 (hyperFrame_idem hT) (mul_one 1) (le_one _), rank_one23, hrank,
      nodeFrame_rank hq]
    simp only [cond_ite, blt_iff, Nat.mul_eq, hjo, ↓reduceIte, evalL, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, wt, neg, Nat.add_eq, Nat.sub_eq, Nat.add_sub_cancel_left,
      show 22 - dims.get width (dag.rootNode j) < 24 by omega, show (23 - 22 : ℕ) < 24 by omega,
      show ¬ 24 + (23 - dims.get width (dag.rootNode j)) < 24 by omega]
    ring
  · have hc : j - 3 * leafCount < 23 := by
      have h1 : j < rootCount := hj
      have h2 : rootCount = 3 * leafCount + 23 := rfl
      omega
    have hr : readFrame j = nodeFrame (dag.rootNode j) := by
      rw [readFrame, ite_eq_right_of_eq_false _ _ (eq_false hjo)]
      have := rootNode_centre ⟨j - 3 * leafCount, hc⟩
      rw [show 3 * leafCount + (⟨j - 3 * leafCount, hc⟩ : Fin 23).val = j by
        simp only; omega] at this
      exact this.symm
    have hs : stepMoment φ (nodeFrame (dag.rootNode j)) (nodeFrame (dag.rootNode j)) = 0 := by
      simp [stepMoment]
    rw [hr, hs]
    rw [show stepMoment φ (nodeFrame (dag.rootNode j)) 1 = endM φ (nodeFrame (dag.rootNode j)) from rfl,
      endM_rank φ h0 (nodeFrame_idem hq), nodeFrame_rank hq]
    simp only [cond_ite, blt_iff, Nat.mul_eq, hjo, ↓reduceIte, evalL, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, wt, neg, Nat.add_eq, Nat.sub_eq, Nat.add_sub_cancel_left,
      Nat.sub_self, h0, show (0 : ℕ) < 24 by omega,
      show 23 - dims.get width (dag.rootNode j) < 24 by omega,
      show ¬ 24 + (23 - dims.get width (dag.rootNode j)) < 24 by omega]
    ring

end Share

/-! ### The codes stay below 48 -/

theorem freeFS_lt {d : ℕ} (hd : d ≤ 23) : ∀ e ∈ freeFS d, e < 48 := by
  intro e he
  simp only [freeFS, neg, Nat.add_eq, Nat.sub_eq, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> omega

theorem addFS_lt {dk da db : ℕ} (hk : dk ≤ 23) : ∀ e ∈ addFS dk da db, e < 48 := by
  intro e he
  simp only [addFS, neg, Nat.add_eq, Nat.sub_eq, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem nodeFS_lt {k : ℕ} (hk : k < nodeCount) : ∀ e ∈ nodeFS dims k (recAt k), e < 48 := by
  cases hA : (recAt k).isAdd
  · rw [nodeFS, hA, Bool.cond_false]; simp
  · obtain ⟨hv, -⟩ := isAdd_lt hA
    obtain ⟨-, ha, hb, -⟩ := nodeOk_add (allOk_parts (allOk_at k hk)).1 (by omega)
    rw [nodeFS, hA, Bool.cond_true]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact addFS_lt (dims_le hk) e he
    · rcases List.mem_append.mp he with he | he
      · cases h : (recAt k).donor0.isNone <;> rw [h] at he
        · simp at he
        · exact freeFS_lt (dims_le (ha.trans hk)) e he
      · cases h : (recAt k).donor1.isNone <;> rw [h] at he
        · simp at he
        · exact freeFS_lt (dims_le (hb.trans hk)) e he

theorem tail_lt {d rk : ℕ} (hd : d ≤ 23) (hrk : rk ≤ 23) :
    ∀ e ∈ [Nat.sub rk d, Nat.sub 23 rk, neg (Nat.sub 23 d)], e < 48 := by
  intro e he
  simp only [neg, Nat.add_eq, Nat.sub_eq, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> omega

theorem cond_le {d : ℕ} (hd : d ≤ 23) (b : Bool) : (bif b then 22 else d) ≤ 23 := by
  cases b
  · exact hd
  · exact (by norm_num : (22 : ℕ) ≤ 23)

theorem rootFS_lt {j : ℕ} (hj : j < rootCount) : ∀ e ∈ rootFS dims j (rootAt j), e < 48 := by
  have hdq := dims_le (root_node hj)
  intro e he
  rw [rootFS] at he
  rcases List.mem_append.mp he with he | he
  · exact freeFS_lt hdq e he
  · exact tail_lt hdq (cond_le hdq _) e he

/-! ### Free uses -/

/-- The free uses are the arguments without a donor and the roots. -/
theorem sum_freeUses (g : ℕ → ℝ) :
    ∑ u ∈ dag.allUses.filter (fun u => dag.linkedB u = false), g (dag.useNode u) =
      ∑ k ∈ Finset.range dag.N, (if dag.v ≤ k then
          ((if dag.linkedB (.gate k true) = false then g (dag.arg k true) else 0) +
            if dag.linkedB (.gate k false) = false then g (dag.arg k false) else 0) else 0) +
        ∑ j ∈ Finset.range dag.rootCount, g (dag.rootNode j) := by
  have hdisj : Disjoint (((Finset.range dag.N).filter (dag.v ≤ ·) ×ˢ (Finset.univ : Finset Bool)).image
      (fun p => Use.gate p.1 p.2)) ((Finset.range dag.rootCount).image Use.root) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image]
    rintro _ ⟨p, -, rfl⟩ ⟨r, -, h⟩
    cases h
  rw [Dag.allUses, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj),
    Finset.filter_image, Finset.sum_image (fun p _ q _ h => by
      obtain ⟨a, b⟩ := p; obtain ⟨c, e⟩ := q; simp only [Use.gate.injEq] at h; rw [h.1, h.2]),
    Finset.filter_image, Finset.sum_image (fun a _ b _ h => by simpa using h)]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hv : dag.v ≤ k
    · rw [ite_eq_left_iff.mpr (fun h => absurd hv h), ite_eq_left_iff.mpr (fun h => absurd hv h),
        Fintype.sum_bool]
      simp only [Dag.useNode]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hv), ite_eq_right_iff.mpr (fun h => absurd h hv)]
  · rw [Finset.filter_true_of_mem]
    · rfl
    · intro j _
      rcases h : dag.linkedB (.root j) with _ | _
      · rfl
      · obtain ⟨n, -, hlu⟩ := (dag.linkedB_iff _).mp h
        obtain ⟨o, t, p, -, he⟩ := dag.linkUse_eq.mp hlu
        cases he

/-! ### The slot moves by nodes and roots -/

section Main

variable (φ : ℕ → ℝ) (h0 : φ 0 = 0)

include h0 in
/-- **The local moments by nodes and roots.** -/
theorem sum_localMoment_shares :
    ∑ s : Slot, localMoment φ s =
      ∑ k ∈ Finset.range nodeCount, evalL φ (nodeFS dims k (recAt k)) +
        ∑ j ∈ Finset.range rootCount, evalL φ (rootFS dims j (rootAt j)) + 28866 * φ 23 := by
  rw [sum_localMoment, dag.slotSum_uses dag_valid (cMove φ) (cMove_self φ),
    dag.slotSum_uses dag_valid (cEnd φ) (cEnd_self φ), sum_freeUses, sum_freeUses, slot_count,
    endM_rank φ h0 (mul_zero 0), Matrix.rank_zero, Nat.sub_zero, nsmul_eq_mul]
  rw [show nodeCount = dag.N from rfl, show rootCount = dag.rootCount from rfl,
    Finset.sum_congr rfl fun k hk => node_share φ h0 (Finset.mem_range.mp hk),
    Finset.sum_congr rfl fun j hj => root_share φ h0 (Finset.mem_range.mp hj)]
  simp only [Finset.sum_add_distrib]
  push_cast
  ring

theorem sum_range_ite_lt (g : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Finset.range b, (if i < a then g i else 0) = ∑ i ∈ Finset.range a, g i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem nodes_eq : ∑ k ∈ Finset.range nodeCount, evalL φ (nodeFS dims k (recAt k)) =
    evalH φ nodeHist := by
  have := (hist_spec φ (nodeFS dims) nodeCount records 65536 0 records_perfect
    fun i _ hb => by rw [zero_add] at hb ⊢; exact nodeFS_lt hb).2
  rw [nodeSteps] at this
  simp only [zero_add] at this
  rw [this]
  exact (sum_range_ite_lt (fun i => evalL φ (nodeFS dims i (recAt i)))
    (show 64042 ≤ 65536 by norm_num)).symm

theorem roots_eq : ∑ j ∈ Finset.range rootCount, evalL φ (rootFS dims j (rootAt j)) =
    evalH φ rootHist := by
  have := (hist_spec φ (rootFS dims) rootCount roots 8192 0 roots_perfect
    fun i _ hb => by rw [zero_add] at hb ⊢; exact rootFS_lt hb).2
  rw [show Tree.hist (rootFS dims) rootCount roots 0 8192 = rootHist from rootSteps] at this
  simp only [zero_add] at this
  rw [this]
  exact (sum_range_ite_lt (fun j => evalL φ (rootFS dims j (rootAt j)))
    (show 5336 ≤ 8192 by norm_num)).symm

theorem evalH_split (h : List ℕ) : evalH φ h =
    ∑ r ∈ Finset.range 24, ((h.getD r 0 : ℝ) - h.getD (24 + r) 0) * φ r := by
  rw [evalH, show (48 : ℕ) = 24 + 24 from rfl, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  rw [wt, wt, ite_eq_left_of_eq_true _ _ (eq_true hr'), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]
  ring

include h0 in
/-- **The local steps.** For `φ 0 = 0`, the local moments of the side slots are the moment of the
local-step histogram. -/
theorem sum_localMoment_eq :
    ∑ s : Slot, localMoment φ s = ∑ r ∈ Finset.range 24, (localSteps.getD r 0 : ℝ) * φ r := by
  rw [sum_localMoment_shares φ h0, nodes_eq, roots_eq, evalH_split, evalH_split,
    ← Finset.sum_add_distrib]
  have hc := List.all_eq_true.mp localSteps_eq
  have h23 : (28866 : ℝ) * φ 23 =
      ∑ r ∈ Finset.range 24, (if r = 23 then (28866 : ℝ) else 0) * φ r := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]; norm_num
  rw [h23, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have := hc r (List.mem_range.mpr (Finset.mem_range.mp hr))
  rw [beq_iff_eq] at this
  have hb : (bif Nat.beq r 23 then (28866 : ℤ) else 0) = if r = 23 then 28866 else 0 := by
    by_cases h : r = 23
    · subst h; rfl
    · have e : Nat.beq r 23 = false := by
        cases e : Nat.beq r 23
        · rfl
        · exact absurd ((beq_iff _ _).mp e) h
      rw [e]; simp [h]
  rw [hb] at this
  rw [← this]
  push_cast
  split_ifs <;> ring

end Main

end

end IntegerMultBounds.MathlibTM2.M8.Global
