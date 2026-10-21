module

public import IntegerMultBounds.MathlibTM2.M8.Frames.Plain
public import IntegerMultBounds.MathlibTM2.M8.Frames.PairRank
public import IntegerMultBounds.MathlibTM2.M8.Frames.MaskRank

/-!
# The ranks of the support frames

A support's frame projects onto the span of its triples, all through one point `c`, so its rank
is the dimension of that span (`frameOf_rank_finrank`). Dropping the coordinate `c` is injective
on the star of `c` (`dropC_injOn`), and sends the triple `{c, u, w}` to the pair vector
`e_u + e_w`; so the rank is that of the support's pair graph relative to `c`
(`suppFrame_rank_pairs`), whose rank `PairRank.pair_rank` counts by a parity forest.

The forest is the breadth-first layers of the pair mask, checked by `okC`; when the check
passes, the rank is `dimC c M`, the number of points on edges less the number of bipartite
components (`MaskRank.dim_eq`, `suppFrame_rank`).
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

/-- The edges of a pair mask, each once. -/
abbrev edges (c M : ℕ) : Finset (Fin 23 × Fin 23) := edgesU (upsOf c M)

theorem mem_edges {c M : ℕ} {u w : Fin 23} : (u, w) ∈ edges c M ↔
    u.val < w.val ∧ u.val ≠ c ∧ w.val ≠ c ∧ M.testBit (pb u w) = true := by
  rw [edges, edgesU, Finset.mem_filter, upsOf, getD_ups, ite_eq_left_of_eq_true _ _ (eq_true u.isLt), Nat.zero_add, testBit_upper]
  constructor
  · rintro ⟨-, h1, h2, -, h3, h4⟩; exact ⟨h2, h1, h3, by rwa [pb_of_lt h2]⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨Finset.mem_univ _, h2, h1, w.isLt, h3, by rwa [pb_of_lt h1] at h4⟩

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
  simp only [vecs, Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    obtain ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩ := (hspec S).mp ((mem_suppSet hs).mp hS)
    refine ⟨(⟨u, by omega⟩, ⟨w, hw⟩), mem_edges.mpr ⟨huw, hcu, hcw, hb⟩, ?_⟩
    exact (dropC_tvec hc (by omega) hw (by omega) hcu hcw).symm
  · rintro ⟨⟨u, w⟩, ha, rfl⟩
    obtain ⟨huw, hcu, hcw, hb⟩ := mem_edges.mp ha
    refine ⟨tvec {s.point, u.val, w.val}, ⟨{s.point, u.val, w.val}, ?_, rfl⟩, ?_⟩
    · exact (mem_suppSet hs).mpr ((hspec _).mpr ⟨u.val, w.val, huw, w.isLt, hcu, hcw, rfl, hb⟩)
    · exact dropC_tvec hc u.isLt w.isLt (by omega) hcu hcw

/-- **The rank of a support frame** is the rank of its pair graph. -/
theorem suppFrame_rank_pairs {s : Supp} (hs : s.Ok) {M : ℕ} (hM : relP s.point s = some M) :
    (suppFrame s).rank = finrank ℚ (pairSpan (edges s.point M)) := by
  rw [suppFrame, frameOf_rank_finrank (instar hs), finrank_dropC (instar hs), image_dropC hs hM,
    pairSpan]

end

/-- **The rank of a support frame**, by its checked parity forest. -/
theorem suppFrame_rank {s : Supp} (hs : s.Ok) {M : ℕ} (hM : relP s.point s = some M)
    (h : okC s.point M = true) : (suppFrame s).rank = dimC s.point M := by
  rw [suppFrame_rank_pairs hs hM, dim_eq h]

end IntegerMultBounds.MathlibTM2.M8.Frames
