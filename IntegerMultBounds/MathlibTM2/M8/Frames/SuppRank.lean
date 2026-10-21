module

public import IntegerMultBounds.MathlibTM2.M8.Frames.Plain
public import IntegerMultBounds.MathlibTM2.M8.Frames.PairRank

/-!
# The ranks of the support frames

A support's frame projects onto the span of its triples, all through one point `c`, so its rank
is the dimension of that span (`frameOf_rank_finrank`). Dropping the coordinate `c` is injective
on the star of `c` (`dropC_injOn`), and sends the triple `{c, u, w}` to the pair vector
`e_u + e_w`; so the rank is that of the support's pair graph relative to `c`
(`suppFrame_rank_pairs`), whose rank `PairRank.pair_rank` counts by a parity forest.

The forest is computed by a breadth-first search on the pair mask (`certOf`) and checked by
`okB`; when the check passes, the rank is `dimOf c M`, the number of vertices on edges less the
number of bipartite components (`dim_eq`). Nothing about the search is trusted.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Module Submodule PairRank IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

theorem frameOf_rank_finrank {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    (frameOf 𝒮).rank = finrank ℚ (span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ))) := by
  rw [frameOf_rank h, ← basisOf_span, finrank_span_finset_eq_card]
  exact basisOf_ind 𝒮

/-- Zero the coordinate `c`. -/
def dropC (c : Fin 23) : (Fin 23 → ℚ) →ₗ[ℚ] (Fin 23 → ℚ) where
  toFun v i := if i = c then 0 else v i
  map_add' v w := by funext i; by_cases h : i = c <;> simp [h]
  map_smul' a v := by funext i; by_cases h : i = c <;> simp [h]

theorem dropC_injOn {c : ℕ} (hc : c < 23) {v : Fin 23 → ℚ} (hv : v ∈ starSpace c)
    (h0 : dropC ⟨c, hc⟩ v = 0) : v = 0 := by
  have hz : ∀ i, i ≠ (⟨c, hc⟩ : Fin 23) → v i = 0 := fun i hi => by
    have := congrFun h0 i
    simpa [dropC, hi] using this
  have hsum := sum_eq_of_mem_star hc hv
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨c, hc⟩),
    Finset.sum_eq_zero fun i hi => hz i (Finset.ne_of_mem_erase hi), add_zero] at hsum
  have hvc : v ⟨c, hc⟩ = 0 := by linarith
  funext i
  by_cases hi : i = ⟨c, hc⟩
  · rw [hi, hvc]; rfl
  · exact hz i hi

theorem finrank_dropC {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    finrank ℚ (span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ))) =
      finrank ℚ (span ℚ (dropC ⟨c, h.1⟩ '' (vecs 𝒮 : Set (Fin 23 → ℚ)))) := by
  set S := span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ))
  have hS : S ≤ starSpace c := span_le.mpr fun w hw => vecs_star h w hw
  have hinj : Function.Injective ((dropC ⟨c, h.1⟩).comp S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (dropC_injOn h.1 (hS x.2) hx)
  rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, range_subtype, map_span]

/-! ### Pair graphs of masks -/

/-- `u` and `w` are joined in the pair mask `M` relative to `c`. -/
def adj (c M : ℕ) (u w : Fin 23) : Bool :=
  !(u.val == w.val) && !(u.val == c) && !(w.val == c) && M.testBit (pb u.val w.val)

theorem adj_comm (c M : ℕ) (u w : Fin 23) : adj c M u w = adj c M w u := by
  unfold adj
  have e : (w.val == u.val) = (u.val == w.val) := by
    by_cases h : u.val = w.val
    · simp [h]
    · simp [h, Ne.symm h]
  rw [pb_comm u.val w.val, e]
  cases (u.val == w.val) <;> cases (u.val == c) <;> cases (w.val == c) <;> simp

/-- The edges of a pair mask, each once. -/
def edges (c M : ℕ) : Finset (Fin 23 × Fin 23) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ adj c M e.1 e.2 = true

theorem dropC_tvec {c u w : ℕ} (hc : c < 23) (hu : u < 23) (hw : w < 23) (huw : u ≠ w)
    (hcu : u ≠ c) (hcw : w ≠ c) :
    dropC ⟨c, hc⟩ (tvec {c, u, w}) = pv ⟨u, hu⟩ ⟨w, hw⟩ := by
  funext i
  simp only [dropC, LinearMap.coe_mk, AddHom.coe_mk, tvec, pv, Pi.add_apply, Pi.single_apply,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  split_ifs <;> simp_all

theorem image_dropC {s : Supp} (hs : s.Ok) {M : ℕ} (hM : relP s.point s = some M) :
    dropC ⟨s.point, (instar hs).1⟩ '' (vecs (suppSet s) : Set (Fin 23 → ℚ)) =
      (fun e : Fin 23 × Fin 23 => pv e.1 e.2) '' (edges s.point M : Set (Fin 23 × Fin 23)) := by
  have hc := (instar hs).1
  have hspec := relP_spec hs hc hM
  ext y
  simp only [vecs, Finset.coe_image, Set.mem_image, Finset.mem_coe, edges, Finset.coe_filter,
    Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    obtain ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩ := (hspec S).mp ((mem_suppSet hs).mp hS)
    refine ⟨(⟨u, by omega⟩, ⟨w, hw⟩), ⟨huw, ?_⟩, ?_⟩
    · simp [adj, hb, show u ≠ w by omega, hcu, hcw]
    · exact (dropC_tvec hc (by omega) hw (by omega) hcu hcw).symm
  · rintro ⟨⟨u, w⟩, ⟨huw, ha⟩, rfl⟩
    simp only [adj, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at ha
    obtain ⟨⟨⟨_, hcu⟩, hcw⟩, hb⟩ := ha
    refine ⟨tvec {s.point, u.val, w.val}, ⟨{s.point, u.val, w.val}, ?_, rfl⟩, ?_⟩
    · exact (mem_suppSet hs).mpr ((hspec _).mpr ⟨u.val, w.val, huw, w.isLt, hcu, hcw, rfl, hb⟩)
    · exact dropC_tvec hc u.isLt w.isLt (by omega) hcu hcw

/-- **The rank of a support frame** is the rank of its pair graph. -/
theorem suppFrame_rank_pairs {s : Supp} (hs : s.Ok) {M : ℕ} (hM : relP s.point s = some M) :
    (suppFrame s).rank = finrank ℚ (pairSpan (edges s.point M)) := by
  rw [suppFrame, frameOf_rank_finrank (instar hs), finrank_dropC (instar hs), image_dropC hs hM,
    pairSpan]

end

/-! ### The parity forest of a mask -/

/-- A vertex label: root, parent, sign and depth. -/
structure Lab where
  root : Fin 23
  parent : Fin 23
  sign : Bool
  depth : ℕ

/-- The neighbours of `u`, as a mask. -/
def adjMask (c M : ℕ) (u : Fin 23) : ℕ :=
  (List.finRange 23).foldl (fun acc w => if adj c M u w then acc ||| (1 <<< w.val) else acc) 0

/-- One layer of the search: the unvisited neighbours of the frontier, labelled. -/
def expand (A : Fin 23 → ℕ) (frontier vis : ℕ) (r : Fin 23) (dep : ℕ) (lab : Fin 23 → Lab) :
    ℕ × (Fin 23 → Lab) :=
  (List.finRange 23).foldl (fun acc w =>
    if vis.testBit w.val || acc.1.testBit w.val then acc
    else match (List.finRange 23).find? (fun u => frontier.testBit u.val && (A u).testBit w.val) with
      | some u => (acc.1 ||| (1 <<< w.val), Function.update acc.2 w ⟨r, u, !(acc.2 u).sign, dep + 1⟩)
      | none => acc) (0, lab)

/-- The search from `r`, layer by layer. -/
def bfs (A : Fin 23 → ℕ) (r : Fin 23) : ℕ → ℕ → ℕ → ℕ → (Fin 23 → Lab) → ℕ × (Fin 23 → Lab)
  | 0, _, vis, _, lab => (vis, lab)
  | n + 1, F, vis, dep, lab =>
    let e := expand A F vis r dep lab
    if e.1 = 0 then (vis, e.2) else bfs A r n e.1 (vis ||| e.1) (dep + 1) e.2

/-- The parity forest: a search from each unvisited vertex on an edge. -/
def certOf (c M : ℕ) : Fin 23 → Lab :=
  let A := adjMask c M
  ((List.finRange 23).foldl (fun (acc : ℕ × (Fin 23 → Lab)) r =>
    if A r ≠ 0 ∧ ¬ acc.1.testBit r.val then
      bfs A r 23 (1 <<< r.val) (acc.1 ||| (1 <<< r.val)) 0
        (Function.update acc.2 r ⟨r, r, false, 0⟩)
    else acc) (0, fun v => ⟨v, v, false, 0⟩)).2

/-- The checks of a parity forest. -/
def okB (c M : ℕ) : Bool :=
  let lab := certOf c M
  (List.finRange 23).all (fun u => (List.finRange 23).all (fun w =>
    !adj c M u w || (lab u).root == (lab w).root)) &&
  (List.finRange 23).all (fun v => (adjMask c M v == 0) ||
    (let r := (lab v).root
     !(adjMask c M r == 0) && (lab r).root == r &&
       (r == v || (adj c M v (lab v).parent && (lab v).sign != (lab (lab v).parent).sign &&
         (lab (lab v).parent).root == r && Nat.blt (lab (lab v).parent).depth (lab v).depth))))

/-- The root `r` has an odd component. -/
def oddB (c M : ℕ) (r : Fin 23) : Bool :=
  let lab := certOf c M
  (List.finRange 23).any fun u => (List.finRange 23).any fun w =>
    decide (u < w) && adj c M u w && (lab u).root == r && (lab u).sign == (lab w).sign

/-- The rank of the pair graph: vertices on edges less bipartite components. -/
def dimOf (c M : ℕ) : ℕ :=
  ((List.finRange 23).filter fun v => !(adjMask c M v == 0)).length -
    ((List.finRange 23).filter fun v =>
      !(adjMask c M v == 0) && (certOf c M v).root == v && !oddB c M v).length

/-! ### Soundness of the checks -/

theorem testBit_adjMask (c M : ℕ) (u w : Fin 23) :
    (adjMask c M u).testBit w.val = adj c M u w := by
  have h : ∀ (l : List (Fin 23)) (acc : ℕ), l.Nodup →
      (l.foldl (fun acc w => if adj c M u w then acc ||| (1 <<< w.val) else acc) acc).testBit w.val =
        (acc.testBit w.val || (w ∈ l && adj c M u w)) := by
    intro l
    induction l with
    | nil => intro acc _; simp
    | cons x l ih =>
      intro acc hnd
      rw [List.nodup_cons] at hnd
      rw [List.foldl_cons, ih _ hnd.2]
      by_cases hx : adj c M u x
      · simp only [hx, ite_true, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
          List.mem_cons]
        by_cases hxw : x = w
        · subst hxw; simp [hx]
        · have : x.val ≠ w.val := fun h => hxw (Fin.ext h)
          simp [this, Ne.symm hxw]
      · simp only [hx, Bool.false_eq_true, ite_false, List.mem_cons]
        by_cases hxw : x = w
        · subst hxw; simp [hx, hnd.1]
        · simp [Ne.symm hxw]
  rw [adjMask, h _ 0 (List.nodup_finRange 23)]
  simp

theorem adjMask_ne_zero {c M : ℕ} {u w : Fin 23} (h : adj c M u w = true) : adjMask c M u ≠ 0 := by
  intro h0
  have := testBit_adjMask c M u w
  rw [h0, Nat.zero_testBit, h] at this
  cases this

theorem adj_ne {c M : ℕ} {u w : Fin 23} (h : adj c M u w = true) : u ≠ w := by
  intro he; subst he; simp [adj] at h

/-- The parity forest as a certificate. -/
def certFor (c M : ℕ) : PairRank.Cert (Fin 23) where
  V := Finset.univ.filter fun v => adjMask c M v ≠ 0
  root v := (certOf c M v).root
  parent v := (certOf c M v).parent
  sign v := (certOf c M v).sign
  depth v := (certOf c M v).depth

theorem certFor_ok {c M : ℕ} (h : okB c M = true) : (certFor c M).Ok (edges c M) := by
  simp only [okB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨hedge, hvert⟩ := h
  refine ⟨fun e he => ?_, fun v hv => ?_, fun v hv hr => ?_⟩
  · simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    refine ⟨?_, ?_, ?_⟩
    · simp only [certFor, Finset.mem_filter, Finset.mem_univ, true_and]
      exact adjMask_ne_zero he.2
    · simp only [certFor, Finset.mem_filter, Finset.mem_univ, true_and]
      exact adjMask_ne_zero (w := e.1) (by rw [adj_comm]; exact he.2)
    · rcases hedge e.1 e.2 with h1 | h1
      · rw [he.2] at h1; cases h1
      · exact h1
  · simp only [certFor, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rcases hvert v with h1 | h1
    · exact absurd h1 hv
    · simp only [beq_eq_false_iff_ne] at h1
      exact ⟨h1.1.1, h1.1.2⟩
  · simp only [certFor, Finset.mem_filter, Finset.mem_univ, true_and] at hv hr ⊢
    rcases hvert v with h1 | h1
    · exact absurd h1 hv
    · simp only [bne_iff_ne, ne_eq, Nat.blt_eq] at h1
      rcases h1.2 with h2 | h2
      · exact absurd h2 hr
      · obtain ⟨⟨⟨ha, hs⟩, hroot⟩, hd⟩ := h2
        refine ⟨?_, hs, hroot, hd⟩
        rcases lt_or_gt_of_ne (adj_ne ha) with hlt | hlt
        · left
          simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hlt, ha⟩
        · right
          simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hlt, by rw [adj_comm]; exact ha⟩

theorem card_filter_finRange (p : Fin 23 → Bool) :
    (Finset.univ.filter fun v => p v = true).card = ((List.finRange 23).filter p).length := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 23).filter p)]
  congr 1
  ext v
  simp

theorem odd_iff {c M : ℕ} (r : Fin 23) :
    (certFor c M).Odd (edges c M) r ↔ oddB c M r = true := by
  simp only [PairRank.Cert.Odd, oddB, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, edges, Finset.mem_filter, Finset.mem_univ,
    certFor, Prod.exists]
  constructor
  · rintro ⟨u, w, ⟨hlt, ha⟩, hr, hs⟩; exact ⟨u, w, ⟨⟨⟨hlt, ha⟩, hr⟩, hs⟩⟩
  · rintro ⟨u, w, ⟨⟨⟨hlt, ha⟩, hr⟩, hs⟩⟩; exact ⟨u, w, ⟨hlt, ha⟩, hr, hs⟩

/-- **The rank of a mask's pair graph**, when its parity forest checks. -/
theorem dim_eq {c M : ℕ} (h : okB c M = true) : finrank ℚ (pairSpan (edges c M)) = dimOf c M := by
  rw [pair_rank (certFor_ok h), dimOf]
  congr 1
  · rw [← card_filter_finRange]
    congr 1
    ext v
    simp [certFor]
  · rw [← card_filter_finRange]
    congr 1
    ext v
    simp only [PairRank.Cert.bipRoots, PairRank.Cert.roots, Finset.mem_filter, odd_iff]
    simp only [certFor, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq, ne_eq, Bool.not_eq_true]

/-- **The rank of a support frame**, by its checked parity forest. -/
theorem suppFrame_rank {s : Supp} (hs : s.Ok) {M : ℕ} (hM : relP s.point s = some M)
    (h : okB s.point M = true) : (suppFrame s).rank = dimOf s.point M := by
  rw [suppFrame_rank_pairs hs hM, dim_eq h]

end IntegerMultBounds.MathlibTM2.M8.Frames
