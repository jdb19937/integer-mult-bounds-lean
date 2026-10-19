module

public import IntegerMultBounds.MathlibTM2.M8.Frames.Span
public import IntegerMultBounds.MathlibTM2.M8.Local.Scalar

/-!
# The plain frames of the PR97 side DAG

Node `n` of the side DAG gets the frame `nodeFrame n`, the `G`-orthogonal projector onto the span
of its support triples. Every support lies in the star of its first point (`instar`), where the
form is positive definite, so every node frame is a frame. They nest along the DAG:
* an argument's frame lies in its node's frame (`nodeFrame_arg`);
* a donor's frame lies in its linked user's frame (`nodeFrame_link`): a donor triple outside the
  user's support closes a path `u – x – y – w` of the user's pair graph, and
  `t_{cuw} = t_{cux} − t_{cxy} + t_{cyw}` (`tvec_path`);
* an output root `(c, T)` lies in the hyperplane frame `hyperFrame T = 1 − lineFrame T`
  (`nodeFrame_out`), and a centre root is the star frame `starFrame c` (`nodeFrame_centre`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Finset Matrix IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section
open Classical

/-- `A` lies in `B`: `B A = A = A B`. -/
def Nested (A B : Matrix (Fin 23) (Fin 23) ℚ) : Prop := B * A = A ∧ A * B = A

/-! ### Supports as sets of triples -/

/-- The first point of a support: a point of all its triples. -/
def _root_.IntegerMultBounds.MathlibTM2.M8.Local.Supp.point : Supp → ℕ
  | .three p0 _ _ => p0
  | .two x _ _ => x
  | .one c _ => c

theorem Supp.mem_triple {s : Supp} (hs : s.Ok) {S : Finset ℕ} (h : s.mem S) :
    IsTriple S ∧ s.point ∈ S ∧ s.point < 23 := by
  cases s with
  | three p0 p1 p2 =>
    obtain ⟨h01, h12, h2⟩ := hs
    simp only [Supp.mem] at h
    subst h
    refine ⟨⟨card_eq_three.mpr ⟨p0, p1, p2, by omega, by omega, by omega, rfl⟩, ?_⟩, by
      simp [Supp.point], by simp only [Supp.point]; omega⟩
    intro z hz; simp only [mem_insert, mem_singleton] at hz; omega
  | two x y Z =>
    obtain ⟨hxy, hy, hZ⟩ := hs
    obtain ⟨z, hz, hzx, hzy, -, rfl⟩ := h
    refine ⟨⟨card_eq_three.mpr ⟨x, y, z, by omega, by omega, by omega, rfl⟩, ?_⟩, by
      simp [Supp.point], by simp only [Supp.point]; omega⟩
    intro w hw; simp only [mem_insert, mem_singleton] at hw; omega
  | one c P =>
    obtain ⟨hc, -⟩ := hs
    obtain ⟨u, w, huw, hw, huc, hwc, rfl, -⟩ := h
    refine ⟨⟨card_eq_three.mpr ⟨c, u, w, by omega, by omega, by omega, rfl⟩, ?_⟩, by
      simp [Supp.point], hc⟩
    intro z hz; simp only [mem_insert, mem_singleton] at hz; omega

/-- All triples of points below `23`. -/
def allTriples : Finset (Finset ℕ) := (range 23).powersetCard 3

theorem mem_allTriples {S : Finset ℕ} : S ∈ allTriples ↔ IsTriple S := by
  simp only [allTriples, mem_powersetCard, IsTriple]
  constructor
  · rintro ⟨hsub, hc⟩; exact ⟨hc, fun z hz => mem_range.mp (hsub hz)⟩
  · rintro ⟨hc, hlt⟩; exact ⟨fun z hz => mem_range.mpr (hlt z hz), hc⟩

/-- The triples of a support. -/
def suppSet (s : Supp) : Finset (Finset ℕ) := allTriples.filter s.mem

theorem mem_suppSet {s : Supp} (hs : s.Ok) {S : Finset ℕ} : S ∈ suppSet s ↔ s.mem S := by
  simp only [suppSet, mem_filter, mem_allTriples]
  exact ⟨fun h => h.2, fun h => ⟨(Supp.mem_triple hs h).1, h⟩⟩

theorem instar {s : Supp} (hs : s.Ok) : InStar (suppSet s) s.point := by
  refine ⟨?_, fun S hS => ?_⟩
  · cases s with
    | three p0 p1 p2 => exact (show p0 < 23 by obtain ⟨_, _, _⟩ := hs; omega)
    | two x y Z => exact (show x < 23 by obtain ⟨_, _, _⟩ := hs; omega)
    | one c P => exact hs.1
  · have h := (mem_suppSet hs).mp hS
    exact ⟨(Supp.mem_triple hs h).1, (Supp.mem_triple hs h).2.1⟩

/-- The span of a support's triples. -/
def suppSpan (s : Supp) : Submodule ℚ (Fin 23 → ℚ) :=
  Submodule.span ℚ (vecs (suppSet s) : Set (Fin 23 → ℚ))

theorem tvec_mem_suppSpan {s : Supp} (hs : s.Ok) {S : Finset ℕ} (h : s.mem S) :
    tvec S ∈ suppSpan s :=
  Submodule.subset_span (by
    simp only [vecs, coe_image, Set.mem_image, mem_coe]
    exact ⟨S, (mem_suppSet hs).mpr h, rfl⟩)

theorem suppSpan_le {s s' : Supp} (hs : s.Ok) (h : ∀ S, s.mem S → tvec S ∈ suppSpan s') :
    suppSpan s ≤ suppSpan s' := by
  rw [suppSpan, Submodule.span_le]
  intro w hw
  simp only [vecs, coe_image, Set.mem_image, mem_coe] at hw
  obtain ⟨S, hS, rfl⟩ := hw
  exact h S ((mem_suppSet hs).mp hS)

/-! ### Paths in pair graphs -/

theorem tvec_insert3 {a b c : ℕ} (i : Fin 23) :
    tvec {a, b, c} i = if i.val = a ∨ i.val = b ∨ i.val = c then 1 else 0 := by
  simp [tvec, mem_insert, mem_singleton]

/-- The path identity `t_{cuw} = t_{cux} − t_{cxy} + t_{cyw}`. -/
theorem tvec_path {c u x y w : ℕ} (_hu : u ≠ c) (_hx : x ≠ c) (_hy : y ≠ c) (_hw : w ≠ c)
    (hux : u ≠ x) (hxy : x ≠ y) (hyw : y ≠ w) (huw : u ≠ w) :
    tvec {c, u, w} = tvec {c, u, x} - tvec {c, x, y} + tvec {c, y, w} := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, tvec_insert3]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem testBit_endsMask (ps : List Path) (i : ℕ) :
    (endsMask ps).testBit i = true ↔ ∃ p ∈ ps, i = pb p.u p.w := by
  induction ps with
  | nil => simp [endsMask]
  | cons p ps ih =>
    simp only [endsMask, show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl,
      Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons, testBit_bit, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨q, hq, rfl⟩)
      · exact ⟨p, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, rfl⟩
    · rintro ⟨q, rfl | hq, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨q, hq, rfl⟩

theorem pairIn_pair {c P a b : ℕ} (ha : a < 23) (hb : b < 23) (hac : a ≠ c) (hbc : b ≠ c)
    (hab : a ≠ b) (hbit : P.testBit (pb a b) = true) : PairIn c P {c, a, b} := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, hb, hac, hbc, rfl, hbit⟩
  · exact ⟨b, a, h, ha, hbc, hac, by rw [Finset.pair_comm], by rw [pb_comm]; exact hbit⟩

theorem relP_lt {c M : ℕ} {s : Supp} (hs : s.Ok) (h : relP c s = some M) : c < 23 := by
  cases s with
  | three p0 p1 p2 =>
    obtain ⟨h01, h12, h2⟩ := hs
    simp only [relP, beq_cond] at h
    split_ifs at h with e0 e1 e2 <;> omega
  | two x y Z =>
    obtain ⟨hxy, hy, -⟩ := hs
    simp only [relP, beq_cond] at h
    split_ifs at h with e0 e1 <;> omega
  | one c' P =>
    simp only [relP, beq_cond] at h
    split_ifs at h with e
    subst e
    exact hs.1

/-- **Links.** A passed span check puts every donor triple in the span of the user's triples. -/
theorem spanOk_mem {L : Link} {s st : Supp} (hs : s.Ok) (hst : st.Ok) (h : spanOk L s st = true) :
    ∀ S, s.mem S → tvec S ∈ suppSpan st := by
  intro S hS
  unfold spanOk at h
  split at h
  · -- the donor's pairs are among the user's
    obtain ⟨c, hc, hsub⟩ := List.any_eq_true.mp h
    split at hsub
    · rename_i pn pt hpn hpt
      have hc23 := relP_lt hs hpn
      apply tvec_mem_suppSpan hst
      rw [relP_spec hst hc23 hpt]
      obtain ⟨u, w, huw, hw, huc, hwc, rfl, hb⟩ := (relP_spec hs hc23 hpn S).mp hS
      exact ⟨u, w, huw, hw, huc, hwc, rfl, subB_spec hsub _ hb⟩
    · cases hsub
  · rename_i ps hps
    split at h
    · rename_i pn pt hpn hpt
      have hc23 := relP_lt hs hpn
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff] at h
      obtain ⟨hpaths, hends⟩ := h
      obtain ⟨u, w, huw, hw, huc, hwc, rfl, hb⟩ := (relP_spec hs hc23 hpn S).mp hS
      by_cases hin : pt.testBit (pb u w) = true
      · apply tvec_mem_suppSpan hst
        rw [relP_spec hst hc23 hpt]
        exact ⟨u, w, huw, hw, huc, hwc, rfl, hin⟩
      · -- a path of the user's pair graph closes the pair
        have hx : (Nat.xor pn (Nat.land pn pt)).testBit (pb u w) = true := by
          simp only [show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl,
            show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, Nat.testBit_xor,
            Nat.testBit_land, hb, Bool.true_and]
          simpa using hin
        rw [hends, testBit_endsMask] at hx
        obtain ⟨p, hp, hpe⟩ := hx
        have hok := hpaths p hp
        simp only [pathOk, Bool.and_eq_true, Bool.not_eq_true', blt_iff] at hok
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hx⟩, hy⟩, hw'⟩, hux⟩, hxy⟩, hyw⟩, huw'⟩, hu23⟩, hx23⟩, hy23⟩,
          hw23⟩, h1⟩, h2⟩, h3⟩ := hok
        have ne : ∀ {a b : ℕ}, Nat.beq a b = false → a ≠ b := fun {a b} h e => by
          rw [e, (beq_iff b b).mpr rfl] at h; cases h
        have hu := ne hu; have hx := ne hx; have hy := ne hy; have hw' := ne hw'
        have hux := ne hux; have hxy := ne hxy; have hyw := ne hyw; have huw' := ne huw'
        rw [testB_eq] at h1 h2 h3
        -- the path ends are the pair
        have hends' : ({L.point, u, w} : Finset ℕ) = {L.point, p.u, p.w} := by
          rcases lt_or_gt_of_ne huw' with hlt | hlt
          · obtain ⟨e1, e2⟩ := pb_inj huw hw hlt hw23 hpe
            rw [e1, e2]
          · rw [pb_comm p.u p.w] at hpe
            obtain ⟨e1, e2⟩ := pb_inj huw hw hlt hu23 hpe
            rw [e1, e2, Finset.pair_comm]
        have hmem : ∀ a b, a < 23 → b < 23 → a ≠ L.point → b ≠ L.point → a ≠ b →
            pt.testBit (pb a b) = true → tvec {L.point, a, b} ∈ suppSpan st :=
          fun a b ha hb hac hbc hab hbit => by
          apply tvec_mem_suppSpan hst
          rw [relP_spec hst hc23 hpt]
          exact pairIn_pair ha hb hac hbc hab hbit
        rw [hends', tvec_path hu hx hy hw' hux hxy hyw huw']
        exact Submodule.add_mem _ (Submodule.sub_mem _ (hmem _ _ hu23 hx23 hu hx hux h1)
          (hmem _ _ hx23 hy23 hx hy hxy h2)) (hmem _ _ hy23 hw23 hy hw' hyw h3)
    · cases h

/-! ### Node frames -/

/-- The frame of a support. -/
def suppFrame (s : Supp) : Matrix (Fin 23) (Fin 23) ℚ := frameOf (suppSet s)

theorem suppFrame_nest {s s' : Supp} (hs : s.Ok) (hs' : s'.Ok)
    (h : ∀ S, s.mem S → tvec S ∈ suppSpan s') : Nested (suppFrame s) (suppFrame s') :=
  frameOf_nest (instar hs') (suppSpan_le hs h)

theorem suppFrame_idem {s : Supp} (hs : s.Ok) : suppFrame s * suppFrame s = suppFrame s :=
  frameOf_idem (instar hs)

theorem suppFrame_bounded {s : Supp} (hs : s.Ok) : Height.Bounded (suppFrame s) (10 ^ 200) :=
  frameOf_bounded (instar hs)

/-- The frame of node `n`. -/
def nodeFrame (n : ℕ) : Matrix (Fin 23) (Fin 23) ℚ := suppFrame (recAt n).supp

theorem nodeFrame_arg {n : ℕ} (hv : ¬ n < leafCount) (hn : n < nodeCount) (pos : Bool) :
    Nested (nodeFrame (dag.arg n pos)) (nodeFrame n) := by
  have hargN : dag.arg n pos < nodeCount := (dag_valid.arg_lt n (by show leafCount ≤ n; omega) hn
    pos).trans hn
  refine suppFrame_nest (recOk_at _ hargN) (recOk_at n hn) fun S hS => ?_
  apply tvec_mem_suppSpan (recOk_at n hn)
  rw [(supp_add hv hn).1]
  cases pos
  · exact Or.inl hS
  · exact Or.inr hS

theorem nodeFrame_link {n : ℕ} {o : Bool} {t : ℕ} {pos : Bool} (h : dag.link n = some (o, t, pos)) :
    Nested (nodeFrame n) (nodeFrame t) := by
  obtain ⟨L, hL, -, rfl, -⟩ := dag_link h
  obtain ⟨hadd, hnt, htN, -, -, -, hspan⟩ := linkOk_donor hL
  have hnN : n < nodeCount := lt_trans hnt htN
  exact suppFrame_nest (recOk_at n hnN) (recOk_at _ htN)
    (spanOk_mem (recOk_at n hnN) (recOk_at _ htN) hspan)

theorem nodeFrame_idem {n : ℕ} (hn : n < nodeCount) : nodeFrame n * nodeFrame n = nodeFrame n :=
  suppFrame_idem (recOk_at n hn)

theorem nodeFrame_bounded {n : ℕ} (hn : n < nodeCount) :
    Height.Bounded (nodeFrame n) (10 ^ 200) :=
  suppFrame_bounded (recOk_at n hn)

/-! ### Root frames -/

/-- The line of a triple. -/
def lineFrame (T : Finset ℕ) : Matrix (Fin 23) (Fin 23) ℚ := frameOf {T}

/-- The hyperplane `G`-orthogonal to a triple. -/
def hyperFrame (T : Finset ℕ) : Matrix (Fin 23) (Fin 23) ℚ := 1 - lineFrame T

/-- The star of a point. -/
def starSet (c : ℕ) : Finset (Finset ℕ) := allTriples.filter fun S => c ∈ S

/-- The star frame of a point. -/
def starFrame (c : ℕ) : Matrix (Fin 23) (Fin 23) ℚ := frameOf (starSet c)

theorem dot_tvec {S T : Finset ℕ} (hT : ∀ z ∈ T, z < 23) :
    tvec S ⬝ᵥ tvec T = (S ∩ T).card := by
  have : ∀ i, tvec S i * tvec T i = tvec (S ∩ T) i := fun i => by
    simp only [tvec, mem_inter]; split_ifs <;> simp_all
  simp only [dotProduct, this]
  exact sum_tvec fun z hz => hT z (mem_inter.mp hz).2

theorem gform_tvec {S T : Finset ℕ} (hS : IsTriple S) (hT : IsTriple T) :
    gform (tvec S) (tvec T) = (S ∩ T).card - 1 := by
  rw [gform_eq, dot_tvec hT.2, sum_tvec hS.2, sum_tvec hT.2, hS.1, hT.1]
  norm_num

theorem instar_single {T : Finset ℕ} (hT : IsTriple T) {c : ℕ} (hc : c ∈ T) :
    InStar {T} c := ⟨hT.2 c hc, fun S hS => by rw [mem_singleton.mp hS]; exact ⟨hT, hc⟩⟩

theorem lineFrame_idem {T : Finset ℕ} (hT : IsTriple T) : lineFrame T * lineFrame T = lineFrame T := by
  obtain ⟨c, hc⟩ : T.Nonempty := card_pos.mp (by rw [hT.1]; norm_num)
  exact frameOf_idem (instar_single hT hc)

theorem hyperFrame_idem {T : Finset ℕ} (hT : IsTriple T) :
    hyperFrame T * hyperFrame T = hyperFrame T := by
  simp only [hyperFrame, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    lineFrame_idem hT]
  abel

theorem lineFrame_bounded {T : Finset ℕ} (hT : IsTriple T) :
    Height.Bounded (lineFrame T) (10 ^ 200) := by
  obtain ⟨c, hc⟩ : T.Nonempty := card_pos.mp (by rw [hT.1]; norm_num)
  exact frameOf_bounded (instar_single hT hc)

/-- Frames of triples meeting `T` in one point lie in the hyperplane of `T`. -/
theorem frameOf_hyper {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h𝒮 : InStar 𝒮 c) {T : Finset ℕ}
    (hT : IsTriple T) (hmeet : ∀ S ∈ 𝒮, (S ∩ T).card = 1) :
    Nested (frameOf 𝒮) (hyperFrame T) := by
  have horth : ∀ S ∈ 𝒮, ∀ T' ∈ ({T} : Finset (Finset ℕ)), gform (tvec S) (tvec T') = 0 := by
    intro S hS T' hT'
    rw [mem_singleton.mp hT', gform_tvec (h𝒮.2 S hS).1 hT, hmeet S hS]
    norm_num
  obtain ⟨h1, h2⟩ := frameOf_orth horth
  constructor
  · rw [hyperFrame, Matrix.sub_mul, Matrix.one_mul, lineFrame, h1, sub_zero]
  · rw [hyperFrame, Matrix.mul_sub, Matrix.mul_one, lineFrame, h2, sub_zero]

/-- An output root lies in the hyperplane of its triple. -/
theorem nodeFrame_out {t i : ℕ} (ht : t < leafCount) (hi : i < 3) :
    Nested (nodeFrame (rootAt (3 * t + i)).node) (hyperFrame (leafTriple t)) := by
  have hj : 3 * t + i < rootCount := by
    have : t < 1771 := ht
    show 3 * t + i < 5336
    omega
  have hn := root_node hj
  have hs := recOk_at _ hn
  obtain ⟨p0, p1, p2, hp, -⟩ := leaf_supp ht
  refine frameOf_hyper (instar hs) ⟨leafTriple_card ht, leafTriple_lt ht⟩ fun S hS => ?_
  have hmem := (mem_suppSet hs).mp hS
  obtain ⟨⟨hS3, hS23⟩, -⟩ := Supp.mem_triple hs hmem
  obtain ⟨c, -, hc⟩ := root_out ht hi hp hS3 hS23
  obtain ⟨-, he⟩ := hc.mp hmem
  rw [he, card_singleton]

theorem starSet_mem {c : ℕ} (hc : c < 23) : InStar (starSet c) c :=
  ⟨hc, fun S hS => by
    simp only [starSet, mem_filter, mem_allTriples] at hS
    exact ⟨hS.1, hS.2⟩⟩

/-- A centre root is the star of its point. -/
theorem nodeFrame_centre {c : ℕ} (hc : c < 23) :
    nodeFrame (rootAt (3 * leafCount + c)).node = starFrame c := by
  have hj : 3 * leafCount + c < rootCount := by
    show 3 * 1771 + c < 5336
    omega
  have hs := recOk_at _ (root_node hj)
  have hset : suppSet (recAt (rootAt (3 * leafCount + c)).node).supp = starSet c := by
    ext S
    simp only [suppSet, starSet, mem_filter, mem_allTriples]
    constructor
    · rintro ⟨hS, hm⟩
      exact ⟨hS, (root_centre hc hS.1 hS.2).mp hm⟩
    · rintro ⟨hS, hcS⟩
      exact ⟨hS, (root_centre hc hS.1 hS.2).mpr hcS⟩
  rw [nodeFrame, suppFrame, hset, starFrame]

/-- A leaf frame is the line of its triple. -/
theorem nodeFrame_leaf {t : ℕ} (ht : t < leafCount) : nodeFrame t = lineFrame (leafTriple t) := by
  have hs := recOk_at t (lt_trans ht leafCount_lt)
  have hset : suppSet (recAt t).supp = {leafTriple t} := by
    ext S
    rw [mem_suppSet hs, leaf_mem ht, mem_singleton]
  rw [nodeFrame, suppFrame, hset, lineFrame]

end

end IntegerMultBounds.MathlibTM2.M8.Frames
