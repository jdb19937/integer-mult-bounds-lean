module

public import IntegerMultBounds.MathlibTM2.M8.Local.Witness
public import IntegerMultBounds.MathlibTM2.M8.Local.Word
public import IntegerMultBounds.MathlibTM2.M8.Local.Triples
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The PR97 local word on scalars

Leaf `t` of the side DAG carries the triple `leafTriple t`, and the leaf triples are distinct
(`leafTriple_inj`), so a node's value is the sum of the sources whose triples its support contains
(`val_eq`). Root `3t + i` is the output `(c, T)` for the `i`-th point `c` of `T = leafTriple t`,
with the triples meeting `T` exactly in `c` (`root_out`); root `3v + c` is the centre of `c`, with
the triples through `c` (`root_centre`). Each output is read into the target of its own triple and
each centre into the targets of the triples through it (`targets`). By `root_parity`, every target
receives exactly its own source (`word_run_target`). With the banks exchanged, every source receives
its own target (`reflected_run_source`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

open Finset Classical Networks

/-! ### Leaves -/

/-- The triple of leaf `t`. -/
def leafTriple (t : ℕ) : Finset ℕ :=
  match (recAt t).supp with
  | .three p0 p1 p2 => {p0, p1, p2}
  | _ => ∅

theorem leafCount_lt : leafCount < nodeCount := by decide

theorem leaf_supp {t : ℕ} (ht : t < leafCount) :
    ∃ p0 p1 p2, (recAt t).supp = .three p0 p1 p2 ∧ p0 < p1 ∧ p1 < p2 ∧ p2 < 23 :=
  (nodeOk_leaf (allOk_parts (allOk_at t (lt_trans ht leafCount_lt))).1 ht).2.1

theorem leafTriple_of {t p0 p1 p2 : ℕ} (h : (recAt t).supp = .three p0 p1 p2) :
    leafTriple t = {p0, p1, p2} := by
  unfold leafTriple
  rw [h]

theorem leaf_mem {t : ℕ} (ht : t < leafCount) (S : Finset ℕ) :
    (recAt t).supp.mem S ↔ S = leafTriple t := by
  obtain ⟨p0, p1, p2, h, -⟩ := leaf_supp ht
  rw [leafTriple_of h, h]
  rfl

theorem leafTriple_card {t : ℕ} (ht : t < leafCount) : (leafTriple t).card = 3 := by
  obtain ⟨p0, p1, p2, h, h01, h12, -⟩ := leaf_supp ht
  rw [leafTriple_of h]
  exact card_eq_three.mpr ⟨p0, p1, p2, by omega, by omega, by omega, rfl⟩

theorem leafTriple_lt {t : ℕ} (ht : t < leafCount) : ∀ z ∈ leafTriple t, z < 23 := by
  obtain ⟨p0, p1, p2, h, h01, h12, h2⟩ := leaf_supp ht
  rw [leafTriple_of h]
  intro z hz
  simp only [mem_insert, mem_singleton] at hz
  omega

/-- The rank of a triple of points in lexicographic order. -/
def lexKey (a : ℕ × ℕ × ℕ) : ℕ := 529 * a.1 + 23 * a.2.1 + a.2.2

theorem lexKey_lt {a1 a2 a3 b1 b2 b3 : ℕ} (ha : a2 < 23 ∧ a3 < 23) (hb : b2 < 23 ∧ b3 < 23)
    (h : lexLt (a1, a2, a3) (b1, b2, b3) = true) : lexKey (a1, a2, a3) < lexKey (b1, b2, b3) := by
  simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, blt_iff, beq_iff] at h
  simp only [lexKey]
  omega

/-- The leaf triples increase in lexicographic order. -/
theorem leaf_key_lt : ∀ {s t : ℕ}, s < t → t < leafCount →
    lexKey (points3 (recAt s).supp) < lexKey (points3 (recAt t).supp)
  | _, 0, hst, _ => absurd hst (Nat.not_lt_zero _)
  | s, t + 1, hst, ht => by
    have hlex := (nodeOk_leaf (allOk_parts (allOk_at (t + 1) (lt_trans ht leafCount_lt))).1
      ht).2.2 (by omega)
    rw [Nat.add_sub_cancel] at hlex
    obtain ⟨p0, p1, p2, hp, -, hp12, hp2⟩ := leaf_supp (show t < leafCount by omega)
    obtain ⟨q0, q1, q2, hq, -, hq12, hq2⟩ := leaf_supp ht
    have hk : lexKey (points3 (recAt t).supp) < lexKey (points3 (recAt (t + 1)).supp) := by
      rw [hp, hq] at hlex ⊢
      exact lexKey_lt ⟨by omega, hp2⟩ ⟨by omega, hq2⟩ hlex
    rcases Nat.lt_succ_iff_lt_or_eq.mp hst with h | h
    · exact lt_trans (leaf_key_lt h (by omega)) hk
    · rw [h]
      exact hk

theorem sorted_eq {p0 p1 p2 q0 q1 q2 : ℕ} (hp : p0 < p1 ∧ p1 < p2) (hq : q0 < q1 ∧ q1 < q2)
    (h : ({p0, p1, p2} : Finset ℕ) = {q0, q1, q2}) : p0 = q0 ∧ p1 = q1 ∧ p2 = q2 := by
  have m : ∀ z, z ∈ ({p0, p1, p2} : Finset ℕ) ↔ z ∈ ({q0, q1, q2} : Finset ℕ) := fun z => by rw [h]
  have h0 := (m p0).mp (by simp)
  have h1 := (m p1).mp (by simp)
  have h2 := (m p2).mp (by simp)
  have g0 := (m q0).mpr (by simp)
  have g1 := (m q1).mpr (by simp)
  have g2 := (m q2).mpr (by simp)
  simp only [mem_insert, mem_singleton] at h0 h1 h2 g0 g1 g2
  omega

/-- Distinct leaves carry distinct triples. -/
theorem leafTriple_inj {s t : ℕ} (hs : s < leafCount) (ht : t < leafCount)
    (h : leafTriple s = leafTriple t) : s = t := by
  obtain ⟨p0, p1, p2, hp, hp01, hp12, -⟩ := leaf_supp hs
  obtain ⟨q0, q1, q2, hq, hq01, hq12, -⟩ := leaf_supp ht
  rw [leafTriple_of hp, leafTriple_of hq] at h
  obtain ⟨rfl, rfl, rfl⟩ := sorted_eq ⟨hp01, hp12⟩ ⟨hq01, hq12⟩ h
  have he : lexKey (points3 (recAt s).supp) = lexKey (points3 (recAt t).supp) := by rw [hp, hq]
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact absurd he (leaf_key_lt hlt ht).ne
  · exact heq
  · exact absurd he (leaf_key_lt hgt hs).ne'

/-! ### Values -/

/-- A node's value is the sum of the sources whose triples its support contains. -/
theorem val_eq (x : ℕ → ZMod 2) : ∀ n, n < nodeCount →
    dag.val x n = ∑ s ∈ range leafCount, if (recAt n).supp.mem (leafTriple s) then x s else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hv : n < leafCount
    · rw [dag.val_leaf x (show n < dag.v from hv), sum_eq_single n]
      · rw [ite_eq_left ((leaf_mem hv _).mpr rfl)]
      · intro s hs hsn
        rw [ite_eq_right]
        intro hm
        exact hsn (leafTriple_inj (mem_range.mp hs) hv ((leaf_mem hv _).mp hm))
      · intro h
        exact absurd (mem_range.mpr hv) h
    · have hvn : dag.v ≤ n := by show leafCount ≤ n; omega
      have ha := dag_valid.arg_lt n hvn hn false
      have hb := dag_valid.arg_lt n hvn hn true
      rw [dag.val_add x hvn ha hb, ih _ ha (by omega), ih _ hb (by omega), ← sum_add_distrib]
      apply sum_congr rfl
      intro s _
      obtain ⟨hmem, hdisj⟩ := supp_add hv hn
      by_cases h1 : (recAt (dag.arg n false)).supp.mem (leafTriple s)
      · have h2 : ¬ (recAt (dag.arg n true)).supp.mem (leafTriple s) := fun h2 => hdisj _ h1 h2
        rw [ite_eq_left ((hmem _).mpr (Or.inl h1)), ite_eq_left h1, ite_eq_right h2, add_zero]
      · by_cases h2 : (recAt (dag.arg n true)).supp.mem (leafTriple s)
        · rw [ite_eq_left ((hmem _).mpr (Or.inr h2)), ite_eq_right h1, ite_eq_left h2, zero_add]
        · rw [ite_eq_right (fun h => ((hmem _).mp h).elim h1 h2), ite_eq_right h1, ite_eq_right h2, add_zero]

/-! ### Triples relative to a point -/

theorem triple_split {S : Finset ℕ} {c : ℕ} (hS : S.card = 3) (hc : c ∈ S) :
    ∃ u w, u < w ∧ u ≠ c ∧ w ≠ c ∧ S = {c, u, w} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hS
  have key : ∀ u w, u ≠ w → u ≠ c → w ≠ c → ({x, y, z} : Finset ℕ) = {c, u, w} →
      ∃ u w, u < w ∧ u ≠ c ∧ w ≠ c ∧ ({x, y, z} : Finset ℕ) = {c, u, w} := by
    intro u w huw huc hwc he
    rcases lt_or_gt_of_ne huw with h | h
    · exact ⟨u, w, h, huc, hwc, he⟩
    · exact ⟨w, u, h, hwc, huc, by rw [he, pair_comm]⟩
  simp only [mem_insert, mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact key y z hyz (Ne.symm hxy) (Ne.symm hxz) rfl
  · exact key x z hxz hxy (Ne.symm hyz) (insert_comm _ _ _)
  · exact key x y hxy hxz hyz (rot3 _ _ _)

theorem touch_pair {a u w : ℕ} (huw : u < w) (hw : w < 23) (ha : a < 23) :
    (touch a).testBit (pb u w) = true ↔ a = u ∨ a = w := by
  rw [testBit_touch]
  constructor
  · rintro ⟨z, hz, hza, he⟩
    rcases lt_or_gt_of_ne hza with h | h
    · rw [pb_comm a z] at he
      exact Or.inr (pb_inj huw hw h ha he).2.symm
    · exact Or.inl (pb_inj huw hw h hz he).1.symm
  · rintro (rfl | rfl)
    · exact ⟨w, hw, by omega, rfl⟩
    · exact ⟨u, by omega, by omega, pb_comm _ _⟩

/-- The mask of an output `(c, {c, a, b})`: the pairs avoiding `c`, `a` and `b`. -/
def outMask (c a b : ℕ) : ℕ :=
  Nat.xor (pairsWithout c) (Nat.land (pairsWithout c) (Nat.lor (touch a) (touch b)))

theorem testBit_outMask (c a b i : ℕ) :
    (outMask c a b).testBit i =
      ((pairsWithout c).testBit i && !((touch a).testBit i || (touch b).testBit i)) := by
  simp only [outMask, show ∀ x y : ℕ, Nat.xor x y = x ^^^ y from fun _ _ => rfl,
    show ∀ x y : ℕ, Nat.land x y = x &&& y from fun _ _ => rfl,
    show ∀ x y : ℕ, Nat.lor x y = x ||| y from fun _ _ => rfl, Nat.testBit_xor, Nat.testBit_land,
    Nat.testBit_lor]
  cases (pairsWithout c).testBit i <;> cases (touch a).testBit i <;> cases (touch b).testBit i <;> rfl

theorem pairIn_centre {c : ℕ} {S : Finset ℕ} (hc : c < 23) (hS : S.card = 3)
    (h23 : ∀ z ∈ S, z < 23) : PairIn c (pairsWithout c) S ↔ c ∈ S := by
  constructor
  · rintro ⟨u, w, -, -, -, -, rfl, -⟩
    simp
  · intro hcS
    obtain ⟨u, w, huw, huc, hwc, rfl⟩ := triple_split hS hcS
    have hw : w < 23 := h23 w (by simp)
    exact ⟨u, w, huw, hw, huc, hwc, rfl,
      (testBit_pairsWithout hc _).mpr ⟨u, w, huw, hw, huc, hwc, rfl⟩⟩

theorem pairIn_out {c a b : ℕ} {S : Finset ℕ} (hc : c < 23) (ha : a < 23) (hb : b < 23)
    (hac : a ≠ c) (hbc : b ≠ c) (hS : S.card = 3) (h23 : ∀ z ∈ S, z < 23) :
    PairIn c (outMask c a b) S ↔ c ∈ S ∧ a ∉ S ∧ b ∉ S := by
  constructor
  · rintro ⟨u, w, huw, hw, huc, hwc, rfl, hbit⟩
    rw [testBit_outMask] at hbit
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hbit
    obtain ⟨-, hta, htb⟩ := hbit
    have hna : ¬ (a = u ∨ a = w) := fun h => by rw [(touch_pair huw hw ha).mpr h] at hta; cases hta
    have hnb : ¬ (b = u ∨ b = w) := fun h => by rw [(touch_pair huw hw hb).mpr h] at htb; cases htb
    refine ⟨by simp, ?_, ?_⟩ <;> simp only [mem_insert, mem_singleton, not_or] <;>
      exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hcS, haS, hbS⟩
    obtain ⟨u, w, huw, huc, hwc, rfl⟩ := triple_split hS hcS
    have hw : w < 23 := h23 w (by simp)
    simp only [mem_insert, mem_singleton, not_or] at haS hbS
    refine ⟨u, w, huw, hw, huc, hwc, rfl, ?_⟩
    have hta : (touch a).testBit (pb u w) = false := Bool.eq_false_iff.mpr fun h => by
      rcases (touch_pair huw hw ha).mp h with h | h <;> omega
    have htb : (touch b).testBit (pb u w) = false := Bool.eq_false_iff.mpr fun h => by
      rcases (touch_pair huw hw hb).mp h with h | h <;> omega
    rw [testBit_outMask, (testBit_pairsWithout hc _).mpr ⟨u, w, huw, hw, huc, hwc, rfl⟩, hta, htb]
    rfl

theorem out_iff {c a b : ℕ} {S T : Finset ℕ} (hac : a ≠ c) (hbc : b ≠ c) (hT : T = {c, a, b}) :
    (c ∈ S ∧ a ∉ S ∧ b ∉ S) ↔ (c ∈ S ∧ S ∩ T = {c}) := by
  subst hT
  constructor
  · rintro ⟨hc, ha, hb⟩
    refine ⟨hc, ?_⟩
    ext z
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl⟩
      · rfl
      · exact absurd hz ha
      · exact absurd hz hb
    · rintro rfl
      exact ⟨hc, Or.inl rfl⟩
  · rintro ⟨hc, he⟩
    refine ⟨hc, fun ha => ?_, fun hb => ?_⟩
    · have : a ∈ S ∩ {c, a, b} := mem_inter.mpr ⟨ha, by simp⟩
      rw [he, mem_singleton] at this
      exact hac this
    · have : b ∈ S ∩ {c, a, b} := mem_inter.mpr ⟨hb, by simp⟩
      rw [he, mem_singleton] at this
      exact hbc this

/-! ### Roots -/

theorem root_node {j : ℕ} (hj : j < rootCount) : (rootAt j).node < nodeCount :=
  dag_valid.root_lt j hj

/-- The root check, unfolded: an output for `j < 3v`, a centre for `j = 3v + c`. -/
theorem root_check {j : ℕ} (hj : j < rootCount) :
    (rootAt j).c < 23 ∧ ∃ M, relP (rootAt j).c (recAt (rootAt j).node).supp = some M ∧
      ((∃ a b, j < 3 * leafCount ∧ a < b ∧ b < 23 ∧ a ≠ (rootAt j).c ∧ b ≠ (rootAt j).c ∧
          (∀ p0 p1 p2, (recAt (j / 3)).supp = .three p0 p1 p2 →
            ((rootAt j).c = p0 ∧ a = p1 ∧ b = p2 ∧ j % 3 = 0) ∨
            ((rootAt j).c = p1 ∧ a = p0 ∧ b = p2 ∧ j % 3 = 1) ∨
            ((rootAt j).c = p2 ∧ a = p0 ∧ b = p1 ∧ j % 3 = 2)) ∧
          M = outMask (rootAt j).c a b) ∨
        (j = 3 * leafCount + (rootAt j).c ∧ M = pairsWithout (rootAt j).c)) := by
  have h := rootOk_at j hj
  unfold rootOk at h
  generalize rootAt j = q at h ⊢
  simp only [Bool.and_eq_true, blt_iff, records_get] at h
  obtain ⟨⟨-, hc⟩, h⟩ := h
  refine ⟨hc, ?_⟩
  revert h
  cases hM : relP q.c (recAt q.node).supp with
  | none => intro h; cases h
  | some M =>
    intro h
    refine ⟨M, rfl, ?_⟩
    cases hout : q.out with
    | none =>
      rw [hout] at h
      simp only [Bool.and_eq_true, beq_iff,
        show ∀ x y : ℕ, Nat.mul x y = x * y from fun _ _ => rfl,
        show ∀ x y : ℕ, Nat.add x y = x + y from fun _ _ => rfl] at h
      exact Or.inr h
    | some ab =>
      obtain ⟨a, b⟩ := ab
      rw [hout] at h
      simp only [Bool.and_eq_true, blt_iff, beq_iff, Bool.not_eq_true',
        show ∀ x y : ℕ, Nat.mul x y = x * y from fun _ _ => rfl,
        show ∀ x y : ℕ, Nat.div x y = x / y from fun _ _ => rfl] at h
      obtain ⟨⟨⟨⟨⟨⟨hj3, hab⟩, hb⟩, hac⟩, hbc⟩, hpts⟩, hMeq⟩ := h
      refine Or.inl ⟨a, b, hj3, hab, hb, fun he => ?_, fun he => ?_, fun p0 p1 p2 hs => ?_, ?_⟩
      · rw [he, show Nat.beq q.c q.c = true from (beq_iff _ _).mpr rfl] at hac; cases hac
      · rw [he, show Nat.beq q.c q.c = true from (beq_iff _ _).mpr rfl] at hbc; cases hbc
      · rw [hs] at hpts
        simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff, and_assoc, or_assoc,
          show ∀ x y : ℕ, Nat.mod x y = x % y from fun _ _ => rfl] using hpts
      · exact hMeq

/-- An output root: root `3t + i` has the triples meeting `leafTriple t` exactly in its `i`-th
point. -/
theorem root_out {t i : ℕ} (ht : t < leafCount) (hi : i < 3) {p0 p1 p2 : ℕ}
    (hp : (recAt t).supp = .three p0 p1 p2) {S : Finset ℕ} (hS : S.card = 3)
    (h23 : ∀ z ∈ S, z < 23) :
    ∃ c, ((c = p0 ∧ i = 0) ∨ (c = p1 ∧ i = 1) ∨ (c = p2 ∧ i = 2)) ∧
      ((recAt (rootAt (3 * t + i)).node).supp.mem S ↔ c ∈ S ∧ S ∩ leafTriple t = {c}) := by
  have hj : 3 * t + i < rootCount := by
    have : t < 1771 := ht
    show 3 * t + i < 5336
    omega
  obtain ⟨hc, M, hM, hcase⟩ := root_check hj
  rcases hcase with ⟨a, b, -, hab, hb, hac, hbc, hpts, hMeq⟩ | ⟨hjc, -⟩
  · have hdiv : (3 * t + i) / 3 = t := by omega
    have hmod : (3 * t + i) % 3 = i := by omega
    have h3 := hpts p0 p1 p2 (by rw [hdiv]; exact hp)
    rw [hmod] at h3
    refine ⟨(rootAt (3 * t + i)).c, ?_, ?_⟩
    · rcases h3 with ⟨h, -, -, h'⟩ | ⟨h, -, -, h'⟩ | ⟨h, -, -, h'⟩
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h, h'⟩)
    · rw [relP_spec (recOk_at _ (root_node hj)) hc hM S, hMeq,
        pairIn_out hc (by omega) hb hac hbc hS h23]
      apply out_iff hac hbc
      rw [leafTriple_of hp]
      rcases h3 with ⟨h, ha', hb', -⟩ | ⟨h, ha', hb', -⟩ | ⟨h, ha', hb', -⟩
      · rw [h, ha', hb']
      · rw [h, ha', hb']
        exact insert_comm _ _ _
      · rw [h, ha', hb']
        exact rot3 _ _ _
  · omega

/-- A centre root: root `3v + c` has the triples through `c`. -/
theorem root_centre {c : ℕ} (hc : c < 23) {S : Finset ℕ} (hS : S.card = 3)
    (h23 : ∀ z ∈ S, z < 23) :
    (recAt (rootAt (3 * leafCount + c)).node).supp.mem S ↔ c ∈ S := by
  have hj : 3 * leafCount + c < rootCount := by
    show 3 * 1771 + c < 5336
    omega
  obtain ⟨hc', M, hM, hcase⟩ := root_check hj
  rcases hcase with ⟨a, b, hlt, -⟩ | ⟨hjc, hMeq⟩
  · omega
  · have hcc : (rootAt (3 * leafCount + c)).c = c := by omega
    rw [relP_spec (recOk_at _ (root_node hj)) hc' hM S, hMeq, hcc]
    exact pairIn_centre hc hS h23

/-! ### The targets -/

/-- The targets of the roots: an output's own triple, and the triples through a centre. -/
def targets (j : ℕ) : List ℕ :=
  if j < 3 * leafCount then [j / 3]
  else (List.range leafCount).filter fun t => decide (j - 3 * leafCount ∈ leafTriple t)

theorem count_out {j t : ℕ} (hj : j < 3 * leafCount) :
    (targets j).count t = if j / 3 = t then 1 else 0 := by
  rw [targets, ite_eq_left hj, List.count_singleton]
  by_cases h : j / 3 = t <;> simp [h]

theorem count_centre {c t : ℕ} (ht : t < leafCount) :
    (targets (3 * leafCount + c)).count t = if c ∈ leafTriple t then 1 else 0 := by
  rw [targets, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  by_cases h : c ∈ leafTriple t
  · rw [ite_eq_left h, List.count_filter (by simpa using h),
      List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr ht)]
  · rw [ite_eq_right h, List.count_eq_zero_of_not_mem]
    simp [List.mem_filter, h]

theorem filter_three {p0 p1 p2 : ℕ} (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h12 : p1 ≠ p2)
    (P : ℕ → Prop) [DecidablePred P] :
    ((({p0, p1, p2} : Finset ℕ).filter P).card : ZMod 2) =
      (if P p0 then 1 else 0) + (if P p1 then 1 else 0) + (if P p2 then 1 else 0) := by
  rw [natCast_card_filter, sum_insert (by simp [h01, h02]), sum_insert (by simp [h12]),
    sum_singleton, add_assoc]

/-- Over the roots, the targets of `t` count the support memberships of `leafTriple s` an odd
number of times exactly when `s = t`. -/
theorem weight {s t : ℕ} (hs : s < leafCount) (ht : t < leafCount) :
    ∑ j ∈ range rootCount, ((targets j).count t : ZMod 2) *
      (if (recAt (rootAt j).node).supp.mem (leafTriple s) then 1 else 0) =
      if s = t then 1 else 0 := by
  have hS := leafTriple_card hs
  have h23 := leafTriple_lt hs
  obtain ⟨p0, p1, p2, hp, h01, h12, h2⟩ := leaf_supp ht
  have hT := leafTriple_of hp
  rw [show rootCount = 3 * leafCount + 23 from rfl, sum_range_add]
  -- the outputs of `t`
  have hout : ∑ j ∈ range (3 * leafCount), ((targets j).count t : ZMod 2) *
      (if (recAt (rootAt j).node).supp.mem (leafTriple s) then 1 else 0) =
      (((leafTriple t).filter fun c => c ∈ leafTriple s ∧
        leafTriple s ∩ leafTriple t = {c}).card : ZMod 2) := by
    rw [← sum_subset (s₁ := {3 * t, 3 * t + 1, 3 * t + 2})]
    · rw [sum_insert (by simp), sum_insert (by simp), sum_singleton, hT,
        filter_three (by omega) (by omega) (by omega), ← hT]
      have e : ∀ i < 3, ((targets (3 * t + i)).count t : ZMod 2) = 1 := fun i hi => by
        rw [count_out (by omega), ite_eq_left (by omega), Nat.cast_one]
      rw [e 1 (by omega), e 2 (by omega), show 3 * t = 3 * t + 0 from rfl, e 0 (by omega),
        one_mul, one_mul, one_mul]
      obtain ⟨c0, hc0, e0⟩ := root_out ht (show 0 < 3 by omega) hp hS h23
      obtain ⟨c1, hc1, e1⟩ := root_out ht (show 1 < 3 by omega) hp hS h23
      obtain ⟨c2, hc2, e2⟩ := root_out ht (show 2 < 3 by omega) hp hS h23
      obtain rfl : c0 = p0 := by omega
      obtain rfl : c1 = p1 := by omega
      obtain rfl : c2 = p2 := by omega
      simp only [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]
      ring
    · intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rw [mem_range]
      omega
    · intro j hj hnot
      rw [count_out (mem_range.mp hj), ite_eq_right, Nat.cast_zero, zero_mul]
      intro h
      apply hnot
      simp only [mem_insert, mem_singleton]
      omega
  -- the centres
  have hcentre : ∑ c ∈ range 23, ((targets (3 * leafCount + c)).count t : ZMod 2) *
      (if (recAt (rootAt (3 * leafCount + c)).node).supp.mem (leafTriple s) then 1 else 0) =
      (((leafTriple t).filter fun c => c ∈ leafTriple s).card : ZMod 2) := by
    rw [natCast_card_filter]
    have hsub : range 23 ∩ leafTriple t = leafTriple t :=
      inter_eq_right.mpr fun z hz => mem_range.mpr (leafTriple_lt ht z hz)
    rw [← hsub, ← sum_ite_mem]
    apply sum_congr rfl
    intro c hc
    rw [count_centre ht, if_congr (root_centre (mem_range.mp hc) hS h23) rfl rfl]
    split_ifs <;> simp
  rw [hout, hcentre, ← Nat.cast_add, root_parity _ _ hS (leafTriple_card ht)]
  exact if_congr ⟨leafTriple_inj hs ht, fun h => h ▸ rfl⟩ rfl rfl

theorem list_sum_range (f : ℕ → ZMod 2) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp

/-- **The PR97 local word.** On arbitrary contents, the word adds every source into the target of
the same triple and leaves sources and side slots unchanged. -/
theorem word_run_target (c : Reg → ZMod 2) {t : ℕ} (ht : t < leafCount) :
    Circuit.run (dag.word targets) c (.y t) = c (.y t) + c (.x t) := by
  rw [dag.word_run_y dag_valid targets c t, list_sum_range]
  refine congrArg (c (.y t) + ·) ?_
  have hval : ∀ j ∈ range rootCount, ((targets j).count t : ZMod 2) *
      dag.val (fun n => c (.x n)) (dag.rootNode j) =
      ∑ s ∈ range leafCount, c (.x s) * (((targets j).count t : ZMod 2) *
        if (recAt (rootAt j).node).supp.mem (leafTriple s) then 1 else 0) := by
    intro j hj
    rw [show dag.rootNode j = (rootAt j).node from rfl, val_eq _ _ (root_node (mem_range.mp hj)),
      mul_sum]
    apply sum_congr rfl
    intro s _
    split_ifs <;> ring
  rw [show dag.rootCount = rootCount from rfl, sum_congr rfl hval, sum_comm]
  simp_rw [← mul_sum]
  rw [sum_congr rfl fun s hs => by rw [weight (mem_range.mp hs) ht]]
  simp [mem_range.mpr ht]

/-- The read increment of the compiled operations on the sources, at a target: its source. -/
theorem readDelta_target (c : Reg → ZMod 2) {t : ℕ} (ht : t < leafCount) :
    dag.readDelta targets (Circuit.run dag.opsGates (part Reg.isX c)) (.y t) = c (.x t) := by
  have h := word_run_target c ht
  rw [dag.word_run dag_valid, Pi.add_apply] at h
  exact add_left_cancel h

theorem word_run_other (c : Reg → ZMod 2) (r : Reg) (hr : r.isY = false) :
    Circuit.run (dag.word targets) c r = c r :=
  dag.word_run_off_y dag_valid targets c r hr

/-- Sources and targets exchanged. -/
def Reg.swap : Reg → Reg
  | .x S => .y S
  | .y T => .x T
  | .aux s => .aux s

theorem Reg.swap_swap (r : Reg) : r.swap.swap = r := by cases r <;> rfl

theorem Reg.swap_injective : Function.Injective Reg.swap :=
  fun a b h => by rw [← Reg.swap_swap a, h, Reg.swap_swap]

/-- The reflected word: the banks exchanged. -/
def reflectedWord : Circuit.Program Reg (ZMod 2) := (dag.word targets).map (gateMap Reg.swap)

/-- **The reflected word** adds every target into the source of the same triple. -/
theorem reflected_run_source (c : Reg → ZMod 2) {t : ℕ} (ht : t < leafCount) :
    Circuit.run reflectedWord c (.x t) = c (.x t) + c (.y t) :=
  ((run_map Reg.swap_injective _ c).1 (.y t)).trans (word_run_target (c ∘ Reg.swap) ht)

theorem reflected_run_other (c : Reg → ZMod 2) (r : Reg) (hr : r.isX = false) :
    Circuit.run reflectedWord c r = c r := by
  have h := (run_map Reg.swap_injective (dag.word targets) c).1 r.swap
  rw [Reg.swap_swap] at h
  rw [reflectedWord, h, word_run_other _ _ (by cases r <;> simp_all [Reg.swap, Reg.isX, Reg.isY]),
    Function.comp_apply, Reg.swap_swap]

end

end IntegerMultBounds.MathlibTM2.M8.Local
