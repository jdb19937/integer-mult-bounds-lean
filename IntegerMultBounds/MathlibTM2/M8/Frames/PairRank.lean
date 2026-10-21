module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The rank of a pair graph

The unsigned incidence vectors `e_u + e_w` of the edges of a finite graph span a space of
dimension `|V| − b` over `ℚ`, where `V` is the set of vertices on edges and `b` the number of
bipartite components. A *parity forest* certifies the components (`Cert`, `Cert.Ok`): every
vertex has a root, and every non-root vertex a parent along an edge, of the other sign and at
smaller depth. A component is odd when one of its edges joins two vertices of the same sign.

* Along the forest, `e_v ≡ ε_v e_r` modulo the forest edges, with `ε_v = ±1` the sign of `v`
  relative to its root `r` (`path_mem`); so the forest edges and one odd edge per odd component
  span (`finrank_le`).
* A vector orthogonal to every edge vector satisfies `x_v = ε_v x_r`, and vanishes on odd
  components; so the orthogonal space is spanned by the coordinates off `V` and one signed
  indicator per bipartite component (`ker_le`), and rank–nullity gives the other inequality.

`pair_rank`: `finrank (pairSpan E) = |V| − |bipartite roots|`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.PairRank

open Module Submodule

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The vector of a pair: `e_u + e_w`. -/
def pv (u w : α) : α → ℚ := Pi.single u 1 + Pi.single w 1

omit [Fintype α] in
theorem pv_comm (u w : α) : pv u w = pv w u := add_comm _ _

/-- The span of the edge vectors. -/
def pairSpan (E : Finset (α × α)) : Submodule ℚ (α → ℚ) :=
  span ℚ ((fun e : α × α => pv e.1 e.2) '' (E : Set (α × α)))

/-- A parity forest. -/
structure Cert (α : Type*) where
  V : Finset α
  root : α → α
  parent : α → α
  sign : α → Bool
  depth : α → ℕ

namespace Cert

variable (c : Cert α) (E : Finset (α × α))

/-- A parity forest of `E`: vertices on edges, roots, and parents along edges of the other sign
at smaller depth. -/
structure Ok : Prop where
  edge : ∀ e ∈ E, e.1 ∈ c.V ∧ e.2 ∈ c.V ∧ c.root e.1 = c.root e.2
  root_mem : ∀ v ∈ c.V, c.root v ∈ c.V ∧ c.root (c.root v) = c.root v
  tree : ∀ v ∈ c.V, c.root v ≠ v →
    ((v, c.parent v) ∈ E ∨ (c.parent v, v) ∈ E) ∧ c.sign v ≠ c.sign (c.parent v) ∧
      c.root (c.parent v) = c.root v ∧ c.depth (c.parent v) < c.depth v

/-- The component of root `r` is odd: an edge joins two vertices of the same sign. -/
def Odd (r : α) : Prop := ∃ e ∈ E, c.root e.1 = r ∧ c.sign e.1 = c.sign e.2

instance (r : α) : Decidable (c.Odd E r) := by unfold Odd; infer_instance

/-- The roots. -/
def roots : Finset α := c.V.filter fun v => c.root v = v

/-- The roots of bipartite components. -/
def bipRoots : Finset α := (c.roots).filter fun r => ¬ c.Odd E r

/-- The sign of `v` relative to its root. -/
def ε (v : α) : ℚ := if c.sign v = c.sign (c.root v) then 1 else -1

end Cert

variable {E : Finset (α × α)} {c : Cert α}

omit [Fintype α] [DecidableEq α] in
theorem ε_parent (h : c.Ok E) {v : α} (hv : v ∈ c.V) (hr : c.root v ≠ v) :
    c.ε (c.parent v) = - c.ε v := by
  obtain ⟨-, hs, hroot, -⟩ := h.tree v hv hr
  unfold Cert.ε
  rw [hroot]
  cases h1 : c.sign v <;> cases h2 : c.sign (c.parent v) <;> cases h3 : c.sign (c.root v) <;>
    simp_all

omit [Fintype α] [DecidableEq α] in
theorem ε_sq (v : α) : c.ε v * c.ε v = 1 := by
  unfold Cert.ε; split_ifs <;> norm_num

omit [Fintype α] [DecidableEq α] in
theorem ε_add_of_ne {u w : α} (hr : c.root u = c.root w) (hs : c.sign u ≠ c.sign w) :
    c.ε u + c.ε w = 0 := by
  unfold Cert.ε
  rw [hr]
  cases h1 : c.sign u <;> cases h2 : c.sign w <;> cases h3 : c.sign (c.root w) <;> simp_all

omit [Fintype α] [DecidableEq α] in
theorem ε_eq_of_eq {u w : α} (hr : c.root u = c.root w) (hs : c.sign u = c.sign w) :
    c.ε u = c.ε w := by
  unfold Cert.ε; rw [hr, hs]

/-! ### The forest edges span -/

/-- The forest edges. -/
def forest (c : Cert α) : Finset (α → ℚ) :=
  (c.V.filter fun v => c.root v ≠ v).image fun v => pv v (c.parent v)

theorem path_mem (h : c.Ok E) : ∀ n, ∀ v ∈ c.V, c.depth v = n →
    Pi.single v 1 - c.ε v • Pi.single (c.root v) 1 ∈ span ℚ (forest c : Set (α → ℚ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hn
    by_cases hr : c.root v = v
    · have : c.ε v = 1 := by simp [Cert.ε, hr]
      rw [this, hr, one_smul, sub_self]
      exact zero_mem _
    · obtain ⟨hedge, -, hroot, hdepth⟩ := h.tree v hv hr
      have hp : c.parent v ∈ c.V := by
        rcases hedge with he | he
        · exact (h.edge _ he).2.1
        · exact (h.edge _ he).1
      have hih := ih _ (hn ▸ hdepth) _ hp rfl
      rw [hroot, ε_parent h hv hr] at hih
      have hf : pv v (c.parent v) ∈ span ℚ (forest c : Set (α → ℚ)) :=
        subset_span (by
          simp only [forest, Finset.coe_image, Finset.coe_filter, Set.mem_image]
          exact ⟨v, ⟨hv, hr⟩, rfl⟩)
      have : Pi.single v 1 - c.ε v • Pi.single (c.root v) 1 =
          pv v (c.parent v) - (Pi.single (c.parent v) 1 - -c.ε v • Pi.single (c.root v) 1) := by
        simp only [pv, neg_smul]; abel
      rw [this]
      exact sub_mem hf hih

theorem path_mem' (h : c.Ok E) {v : α} (hv : v ∈ c.V) :
    Pi.single v 1 - c.ε v • Pi.single (c.root v) 1 ∈ span ℚ (forest c : Set (α → ℚ)) :=
  path_mem h _ v hv rfl

open Classical in
/-- One odd edge of each odd root. -/
noncomputable def Cert.oddEdge (c : Cert α) (E : Finset (α × α)) (r : α) : α × α :=
  if h : c.Odd E r then Classical.choose h else (r, r)

omit [Fintype α] in
theorem oddEdge_spec {r : α} (h : c.Odd E r) :
    c.oddEdge E r ∈ E ∧ c.root (c.oddEdge E r).1 = r ∧
      c.sign (c.oddEdge E r).1 = c.sign (c.oddEdge E r).2 := by
  unfold Cert.oddEdge
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hm, h1, h2⟩ := Classical.choose_spec h
  exact ⟨hm, h1, h2⟩

/-- The odd roots. -/
def oddRoots (c : Cert α) (E : Finset (α × α)) : Finset α := (c.roots).filter fun r => c.Odd E r

/-- The spanning family: the forest edges and one odd edge per odd root. -/
noncomputable def family (c : Cert α) (E : Finset (α × α)) : Finset (α → ℚ) :=
  forest c ∪ (oddRoots c E).image fun r => pv (c.oddEdge E r).1 (c.oddEdge E r).2

theorem edge_mem_family (h : c.Ok E) {e : α × α} (he : e ∈ E) :
    pv e.1 e.2 ∈ span ℚ (family c E : Set (α → ℚ)) := by
  obtain ⟨hu, hw, hr⟩ := h.edge e he
  set r := c.root e.1
  have hF : span ℚ (forest c : Set (α → ℚ)) ≤ span ℚ (family c E : Set (α → ℚ)) :=
    span_mono (by simp [family])
  have hpu := hF (path_mem' h hu)
  have hpw := hF (path_mem' h hw)
  rw [← hr] at hpw
  have hsplit : pv e.1 e.2 = (Pi.single e.1 1 - c.ε e.1 • Pi.single r 1) +
      (Pi.single e.2 1 - c.ε e.2 • Pi.single r 1) + (c.ε e.1 + c.ε e.2) • Pi.single r 1 := by
    simp only [pv, add_smul]; abel
  rw [hsplit]
  refine add_mem (add_mem hpu hpw) ?_
  by_cases hs : c.sign e.1 = c.sign e.2
  · -- an odd component: `e_r` itself is in the span
    have hodd : c.Odd E r := ⟨e, he, rfl, hs⟩
    obtain ⟨hm, h1, h2⟩ := oddEdge_spec hodd
    set o := c.oddEdge E r
    obtain ⟨hu0, hw0, hr0⟩ := h.edge o hm
    have hrV : r ∈ c.V := (h.root_mem _ hu).1
    have hrr : c.root r = r := (h.root_mem _ hu).2
    have hro : r ∈ oddRoots c E := by
      simp only [oddRoots, Cert.roots, Finset.mem_filter]; exact ⟨⟨hrV, hrr⟩, hodd⟩
    have ho : pv o.1 o.2 ∈ span ℚ (family c E : Set (α → ℚ)) :=
      subset_span (by simp only [family, Finset.coe_union, Finset.coe_image, Set.mem_union,
        Set.mem_image]; exact Or.inr ⟨r, hro, rfl⟩)
    have hp0 := hF (path_mem' h hu0)
    have hq0 := hF (path_mem' h hw0)
    rw [h1] at hp0
    rw [← hr0, h1] at hq0
    have heq : c.ε o.1 = c.ε o.2 := ε_eq_of_eq hr0 h2
    have hsq := ε_sq (c := c) o.1
    have her : Pi.single r 1 = ((2 : ℚ) * c.ε o.1)⁻¹ •
        (pv o.1 o.2 - (Pi.single o.1 1 - c.ε o.1 • Pi.single r 1) -
          (Pi.single o.2 1 - c.ε o.2 • Pi.single r 1)) := by
      rw [← heq]
      have hne : (2 : ℚ) * c.ε o.1 ≠ 0 := by
        intro h0; have : c.ε o.1 = 0 := by linarith
        rw [this] at hsq; norm_num at hsq
      simp only [pv]
      rw [show Pi.single o.1 1 + Pi.single o.2 1 - (Pi.single o.1 1 - c.ε o.1 • Pi.single r (1 : ℚ)) -
          (Pi.single o.2 1 - c.ε o.1 • Pi.single r 1) = ((2 : ℚ) * c.ε o.1) • Pi.single r (1 : ℚ) by
        rw [mul_smul, two_smul]; abel]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [her, smul_smul]
    exact smul_mem _ _ (sub_mem (sub_mem ho hp0) hq0)
  · rw [ε_add_of_ne hr hs, zero_smul]
    exact zero_mem _

theorem pairSpan_le (h : c.Ok E) : pairSpan E ≤ span ℚ (family c E : Set (α → ℚ)) := by
  rw [pairSpan, span_le]
  rintro _ ⟨e, he, rfl⟩
  exact edge_mem_family h he

omit [Fintype α] in
theorem card_roots_add (c : Cert α) (E : Finset (α × α)) :
    (oddRoots c E).card + (c.bipRoots E).card = c.roots.card := by
  rw [oddRoots, Cert.bipRoots]
  exact Finset.card_filter_add_card_filter_not _

omit [Fintype α] in
theorem card_V (c : Cert α) :
    (c.V.filter fun v => c.root v ≠ v).card + c.roots.card = c.V.card := by
  rw [Cert.roots, add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem finrank_le (h : c.Ok E) : finrank ℚ (pairSpan E) + (c.bipRoots E).card ≤ c.V.card := by
  have h1 := Submodule.finrank_mono (pairSpan_le h)
  have h2 := finrank_span_le_card (R := ℚ) (family c E : Set (α → ℚ))
  have h3 : (family c E : Set (α → ℚ)).toFinset.card ≤
      (c.V.filter fun v => c.root v ≠ v).card + (oddRoots c E).card := by
    rw [Finset.toFinset_coe]
    exact (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  have := card_roots_add c E
  have := card_V c
  omega

/-! ### The orthogonal vectors -/

/-- The signed indicator of the component of root `r`. -/
def xvec (c : Cert α) (r : α) : α → ℚ := fun v => if v ∈ c.V ∧ c.root v = r then c.ε v else 0

omit [Fintype α] in
theorem orth_path (h : c.Ok E) {x : α → ℚ} (hx : ∀ e ∈ E, x e.1 + x e.2 = 0) :
    ∀ n, ∀ v ∈ c.V, c.depth v = n → x v = c.ε v * x (c.root v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hn
    by_cases hr : c.root v = v
    · have : c.ε v = 1 := by simp [Cert.ε, hr]
      rw [this, hr, one_mul]
    · obtain ⟨hedge, -, hroot, hdepth⟩ := h.tree v hv hr
      have hp : c.parent v ∈ c.V := by
        rcases hedge with he | he
        · exact (h.edge _ he).2.1
        · exact (h.edge _ he).1
      have hih := ih _ (hn ▸ hdepth) _ hp rfl
      rw [hroot, ε_parent h hv hr] at hih
      have hsum : x v + x (c.parent v) = 0 := by
        rcases hedge with he | he
        · exact hx _ he
        · have := hx _ he; simp only at this; linarith
      linarith

omit [Fintype α] in
theorem orth_odd (h : c.Ok E) {x : α → ℚ} (hx : ∀ e ∈ E, x e.1 + x e.2 = 0) {r : α}
    (hodd : c.Odd E r) : x r = 0 := by
  obtain ⟨hm, h1, h2⟩ := oddEdge_spec hodd
  set o := c.oddEdge E r
  obtain ⟨hu0, hw0, hr0⟩ := h.edge o hm
  have hp := orth_path h hx _ o.1 hu0 rfl
  have hq := orth_path h hx _ o.2 hw0 rfl
  rw [← hr0, h1] at hq
  rw [h1] at hp
  have heq : c.ε o.1 = c.ε o.2 := ε_eq_of_eq hr0 h2
  have hs := hx o hm
  have hsq := ε_sq (c := c) o.1
  rw [hp, hq, ← heq] at hs
  have h2x : c.ε o.1 * x r = 0 := by linarith
  have : x r = c.ε o.1 * (c.ε o.1 * x r) := by rw [← mul_assoc, hsq, one_mul]
  rw [this, h2x, mul_zero]

/-- The orthogonal family: coordinates off `V` and signed indicators of bipartite components. -/
def orthFamily (c : Cert α) (E : Finset (α × α)) : Finset (α → ℚ) :=
  (Finset.univ.filter fun v => v ∉ c.V).image (fun v => Pi.single v 1) ∪ (c.bipRoots E).image (xvec c)

theorem orth_mem (h : c.Ok E) {x : α → ℚ} (hx : ∀ e ∈ E, x e.1 + x e.2 = 0) :
    x ∈ span ℚ (orthFamily c E : Set (α → ℚ)) := by
  have hsum : x = ∑ v ∈ Finset.univ.filter (fun v => v ∉ c.V), x v • Pi.single v 1 +
      ∑ r ∈ c.bipRoots E, x r • xvec c r := by
    funext v
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, xvec]
    by_cases hv : v ∈ c.V
    · have hp := orth_path h hx _ v hv rfl
      have h1 : (∑ w ∈ Finset.univ.filter (fun v => v ∉ c.V), if v = w then x w else 0) = 0 := by
        rw [Finset.sum_ite_eq]; simp [hv]
      have h2 : (∑ r ∈ c.bipRoots E, if v ∈ c.V ∧ c.root v = r then x r * c.ε v else 0) =
          ∑ r ∈ c.bipRoots E, if c.root v = r then x r * c.ε v else 0 :=
        Finset.sum_congr rfl fun r _ => by simp [hv]
      rw [h1, h2, zero_add, Finset.sum_ite_eq]
      by_cases hb : c.root v ∈ c.bipRoots E
      · rw [ite_eq_left_iff.mpr (fun h => absurd hb h), hp, mul_comm]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hb), hp]
        have hrV := h.root_mem v hv
        have hodd : c.Odd E (c.root v) := by
          by_contra hn
          exact hb (by simp only [Cert.bipRoots, Cert.roots, Finset.mem_filter]; exact ⟨⟨hrV.1, hrV.2⟩, hn⟩)
        rw [orth_odd h hx hodd, mul_zero]
    · have h2 : (∑ r ∈ c.bipRoots E, if v ∈ c.V ∧ c.root v = r then x r * c.ε v else 0) = 0 :=
        Finset.sum_eq_zero fun r _ => by simp [hv]
      rw [h2, add_zero, Finset.sum_ite_eq]
      simp [hv]
  rw [hsum]
  refine add_mem (sum_mem fun v hv => smul_mem _ _ (subset_span ?_))
    (sum_mem fun r hr => smul_mem _ _ (subset_span ?_))
  · simp only [orthFamily, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
    exact Or.inl ⟨v, hv, rfl⟩
  · simp only [orthFamily, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
    exact Or.inr ⟨r, hr, rfl⟩

/-- The edge matrix, one row per edge. -/
def edgeMatrix (E : Finset (α × α)) : Matrix E α ℚ := fun e => pv e.1.1 e.1.2

theorem rank_edgeMatrix (E : Finset (α × α)) : (edgeMatrix E).rank = finrank ℚ (pairSpan E) := by
  rw [Matrix.rank_eq_finrank_span_row]
  have : Set.range (edgeMatrix E).row = (fun e : α × α => pv e.1 e.2) '' (E : Set (α × α)) := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩; exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, rfl⟩
  rw [this, pairSpan]

theorem dot_pv (u w : α) (x : α → ℚ) : pv u w ⬝ᵥ x = x u + x w := by
  simp [pv, add_dotProduct, single_dotProduct]

theorem ker_le (h : c.Ok E) :
    LinearMap.ker (edgeMatrix E).mulVecLin ≤ span ℚ (orthFamily c E : Set (α → ℚ)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine orth_mem h fun e he => ?_
  have := congrFun hx ⟨e, he⟩
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, edgeMatrix, dot_pv] using this

theorem le_finrank (h : c.Ok E) : c.V.card ≤ finrank ℚ (pairSpan E) + (c.bipRoots E).card := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (edgeMatrix E).mulVecLin
  rw [← Matrix.rank, rank_edgeMatrix, Module.finrank_fintype_fun_eq_card] at hrn
  have h1 := Submodule.finrank_mono (ker_le h)
  have h2 := finrank_span_le_card (R := ℚ) (orthFamily c E : Set (α → ℚ))
  have h3 : (orthFamily c E : Set (α → ℚ)).toFinset.card ≤
      (Finset.univ.filter fun v => v ∉ c.V).card + (c.bipRoots E).card := by
    rw [Finset.toFinset_coe]
    exact (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  have h4 : (Finset.univ.filter fun v => v ∉ c.V).card + c.V.card = Fintype.card α := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun v => v ∈ c.V)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ] at this
    omega
  omega

/-- **The rank of a pair graph.** -/
theorem pair_rank (h : c.Ok E) : finrank ℚ (pairSpan E) = c.V.card - (c.bipRoots E).card := by
  have := finrank_le h
  have := le_finrank h
  omega

end IntegerMultBounds.MathlibTM2.M8.Frames.PairRank
