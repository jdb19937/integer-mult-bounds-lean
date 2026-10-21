module

public import IntegerMultBounds.MathlibTM2.M8.Frames.LiftFrame
public import IntegerMultBounds.MathlibTM2.M8.Frames.RootCheck

/-!
# Root-complement frames with computed bases

A design-B frame of several centres is the `G`-complement `W(X)` of the span of a set `X` of root
vectors (output triples `t_T` and centre vectors `w_c`), with no closed formula for its rank or
its nondegeneracy. Here a basis `B ⊆ X` of codes (`RootCheck`) represents it:
`rootFrame B = 1 − proj G [B]`. When `basisOk B gens` passes:
* the Gram matrix of `B` is invertible (`basisOk_unit`), so `rootFrame B` is a frame of rank
  `23 − |B|` (`rootFrame_idem`, `rootFrame_rank`) and height at most `2 · 10²⁰⁰`
  (`rootFrame_bounded`);
* every generator lies in the span of `B` (`basisOk_mem`).

Frames nest as their spans grow (`rootFrame_nest`); a frame lies in the hyperplane of an output,
the star of a centre and a one-centre frame whose roots it spans (`rootFrame_le_hyper`,
`rootFrame_le_star`, `rootFrame_le_lift`); a set of triples orthogonal to the basis has its frame
inside (`frameOf_le_rootFrame`). Two one-centre frames with nested masks and equal ranks are
equal (`liftFrame_eq_of_dim`), so a sub-mask spans a one-centre frame.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Matrix Finset RootCheck
open IntegerMultBounds.MathlibTM2.M8.Local (subB pairsWithout)

noncomputable section

/-! ### The vectors of the codes -/

/-- The triple of a code. -/
def tripleOf (k : ℕ) : Finset ℕ := {p0 k, p1 k, p2 k}

/-- The vector of a code. -/
def rvec (k : ℕ) : Fin 23 → ℚ := if k < cen then tvec (tripleOf k) else wvec (k - cen)

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem blt_cen {k : ℕ} (hk : k < cen) : Nat.blt k cen = true := Nat.blt_eq.mpr hk

theorem blt_cen' {k : ℕ} (hk : ¬ k < cen) : Nat.blt k cen = false := by
  rw [Bool.eq_false_iff]; intro h; exact hk (Nat.blt_eq.mp h)

theorem validCode_triple {k : ℕ} (hv : validCode k = true) (hk : k < cen) :
    p0 k < p1 k ∧ p1 k < p2 k ∧ p2 k < 23 := by
  simp only [validCode, blt_cen hk, Bool.cond_true, Bool.and_eq_true, Nat.blt_eq] at hv
  exact ⟨hv.1.1, hv.1.2, hv.2⟩

theorem validCode_centre {k : ℕ} (hv : validCode k = true) (hk : ¬ k < cen) : k - cen < 23 := by
  unfold validCode at hv
  rw [blt_cen' hk, Bool.cond_false] at hv
  exact Nat.blt_eq.mp hv

theorem tripleOf_isTriple {k : ℕ} (h : p0 k < p1 k ∧ p1 k < p2 k ∧ p2 k < 23) :
    IsTriple (tripleOf k) := by
  refine ⟨?_, ?_⟩
  · rw [tripleOf, card_insert_of_notMem (by simp; omega), card_pair (by omega)]
  · intro z hz
    simp only [tripleOf, mem_insert, mem_singleton] at hz
    omega

theorem eqN_eq (x y : ℕ) : eqN x y = if x = y then 1 else 0 := by
  unfold eqN
  by_cases h : x = y <;> simp [h]

/-- Membership in a triple of distinct points. -/
theorem memT_eq {x k : ℕ} (h : p0 k < p1 k ∧ p1 k < p2 k ∧ p2 k < 23) :
    memT x k = if x ∈ tripleOf k then 1 else 0 := by
  obtain ⟨h01, h12, -⟩ := h
  have : p0 k ≠ p1 k := by omega
  have : p1 k ≠ p0 k := by omega
  have : p0 k ≠ p2 k := by omega
  have : p2 k ≠ p0 k := by omega
  have : p1 k ≠ p2 k := by omega
  have : p2 k ≠ p1 k := by omega
  simp only [memT, eqN_eq, tripleOf, mem_insert, mem_singleton, Nat.add_eq]
  by_cases h0 : x = p0 k
  · have : x ≠ p1 k := by omega
    have : x ≠ p2 k := by omega
    simp [*]
  · by_cases h1 : x = p1 k
    · have : x ≠ p2 k := by omega
      simp [*]
    · by_cases h2 : x = p2 k <;> simp [*]

theorem card_inter_triple {k : ℕ} (h : p0 k < p1 k ∧ p1 k < p2 k ∧ p2 k < 23) (T : Finset ℕ) :
    (tripleOf k ∩ T).card =
      (if p0 k ∈ T then 1 else 0) + (if p1 k ∈ T then 1 else 0) + (if p2 k ∈ T then 1 else 0) := by
  rw [← filter_mem_eq_inter, card_filter, tripleOf, sum_insert (by simp; omega),
    sum_pair (by omega)]
  ring

theorem sumE_eq {k : ℕ} (hv : validCode k = true) : (sumE k : ℚ) = ∑ i, rvec k i := by
  by_cases hk : k < cen
  · have h := validCode_triple hv hk
    have ht := tripleOf_isTriple h
    simp only [sumE, rvec, hk, ite_true, blt_cen hk,
      Bool.cond_true, sum_tvec ht.2, ht.1]
    norm_num
  · simp only [sumE, rvec, hk, ite_false, blt_cen' hk,
      Bool.cond_false, sum_wvec (validCode_centre hv hk)]
    norm_num

theorem dot_tvec_wvec {S : Finset ℕ} (hS : IsTriple S) {c : ℕ} (hc : c < 23) :
    tvec S ⬝ᵥ wvec c = 3 + 7 * (if c ∈ S then 1 else 0) := by
  have h1 : tvec S ⬝ᵥ wvec c = (∑ i, tvec S i) + 7 * (tvec S ⬝ᵥ tvec {c}) := by
    simp only [dotProduct, wvec, mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, sum_tvec hS.2, hS.1, dot_tvec (by simpa using hc)]
  by_cases hcS : c ∈ S
  · rw [Finset.inter_singleton_of_mem hcS]; simp [hcS]; try norm_num
  · rw [Finset.inter_singleton_of_notMem hcS]; simp [hcS]

theorem dot_wvec_wvec {c c' : ℕ} (hc : c < 23) (hc' : c' < 23) :
    wvec c ⬝ᵥ wvec c' = 37 + 49 * (if c = c' then 1 else 0) := by
  have h1 : wvec c ⬝ᵥ wvec c' =
      23 + 7 * (∑ i, tvec {c} i) + 7 * (∑ i, tvec {c'} i) + 49 * (tvec {c} ⬝ᵥ tvec {c'}) := by
    simp only [dotProduct, wvec, Finset.mul_sum]
    rw [show (23 : ℚ) = ∑ _i : Fin 23, (1 : ℚ) by simp, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, sum_tvec (by simpa using hc), sum_tvec (by simpa using hc'), dot_tvec (by simpa using hc')]
  by_cases h : c = c'
  · subst h; simp; norm_num
  · rw [Finset.singleton_inter_of_notMem (by simpa using h)]; simp [h]; norm_num

/-- **The dot products of the codes.** -/
theorem dotE_eq {a b : ℕ} (ha : validCode a = true) (hb : validCode b = true) :
    (dotE a b : ℚ) = rvec a ⬝ᵥ rvec b := by
  by_cases hak : a < cen <;> by_cases hbk : b < cen
  · have h := validCode_triple ha hak
    have h' := validCode_triple hb hbk
    simp only [dotE, rvec, hak, hbk, ite_true, blt_cen hak,
      blt_cen hbk, Bool.cond_true, dot_tvec (tripleOf_isTriple h').2,
      card_inter_triple h, memT_eq h', Nat.add_eq]
    push_cast
    split_ifs <;> norm_num
  · have h := validCode_triple ha hak
    have hc := validCode_centre hb hbk
    simp only [dotE, rvec, hak, hbk, ite_true, ite_false, blt_cen hak,
      blt_cen' hbk, Bool.cond_true, Bool.cond_false,
      dot_tvec_wvec (tripleOf_isTriple h) hc, memT_eq h, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    split_ifs <;> norm_num
  · have hc := validCode_centre ha hak
    have h' := validCode_triple hb hbk
    simp only [dotE, rvec, hak, hbk, ite_true, ite_false, blt_cen hbk,
      blt_cen' hak, Bool.cond_true, Bool.cond_false,
      dotProduct_comm (wvec _), dot_tvec_wvec (tripleOf_isTriple h') hc, memT_eq h', Nat.add_eq,
      Nat.mul_eq, Nat.sub_eq]
    split_ifs <;> norm_num
  · have hc := validCode_centre ha hak
    have hc' := validCode_centre hb hbk
    simp only [dotE, rvec, hak, hbk, ite_false, blt_cen' hak,
      blt_cen' hbk, Bool.cond_false,
      dot_wvec_wvec hc hc']
    by_cases h : a = b
    · subst h; simp; norm_num
    · have : a - cen ≠ b - cen := by omega
      simp [this, beq_false h]

/-- **`9 G` of the codes.** -/
theorem g9_eq {a b : ℕ} (ha : validCode a = true) (hb : validCode b = true) :
    (g9 a b : ℚ) = 9 * gform (rvec a) (rvec b) := by
  rw [gform_eq, g9]
  push_cast
  rw [dotE_eq ha hb, sumE_eq ha, sumE_eq hb]
  ring

/-! ### Lists of rationals -/

/-- The dot product of two lists of rationals. -/
def dotQ : List ℚ → List ℚ → ℚ
  | x :: xs, y :: ys => x * y + dotQ xs ys
  | _, _ => 0

/-- `Σ l_i v_i`, over the shorter list. -/
def combV : List ℚ → List (Fin 23 → ℚ) → Fin 23 → ℚ
  | l :: ls, v :: vs => l • v + combV ls vs
  | _, _ => 0

theorem dot_cast : ∀ xs ys : List ℤ,
    ((RootCheck.dot xs ys : ℤ) : ℚ) = dotQ (xs.map (↑)) (ys.map (↑))
  | [], _ => by simp [RootCheck.dot, dotQ]
  | _ :: _, [] => by simp [RootCheck.dot, dotQ]
  | x :: xs, y :: ys => by simp [RootCheck.dot, dotQ, dot_cast xs ys]

theorem dotQ_comm : ∀ xs ys : List ℚ, dotQ xs ys = dotQ ys xs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp [dotQ, dotQ_comm xs ys, mul_comm]

theorem dotQ_map_dot : ∀ (l : List ℚ) (vs : List (Fin 23 → ℚ)) (x : Fin 23 → ℚ),
    dotQ l (vs.map fun v => v ⬝ᵥ x) = combV l vs ⬝ᵥ x
  | [], _, _ => by simp [dotQ, combV]
  | _ :: _, [], _ => by simp [dotQ, combV]
  | l :: ls, v :: vs, x => by
    simp only [List.map_cons, dotQ, combV, add_dotProduct, smul_dotProduct, smul_eq_mul,
      dotQ_map_dot ls vs x]

theorem combV_mem : ∀ (l : List ℚ) (vs : List (Fin 23 → ℚ)),
    combV l vs ∈ Submodule.span ℚ {v | v ∈ vs}
  | [], _ => by simp [combV]
  | _ :: _, [] => by simp [combV]
  | l :: ls, v :: vs => by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) ?_
    exact Submodule.span_mono (fun w hw => by simp_all) (combV_mem ls vs)

/-! ### The checks -/

theorem all_valid {B : List ℕ} (h : B.all validCode = true) : ∀ b ∈ B, validCode b = true :=
  fun b hb => List.all_eq_true.mp h b hb

theorem map_dotE {B : List ℕ} (hB : ∀ b ∈ B, validCode b = true) {g : ℕ} (hg : validCode g = true) :
    (B.map fun b => dotE b g).map (Int.cast : ℤ → ℚ) = (B.map rvec).map fun v => v ⬝ᵥ rvec g := by
  simp only [List.map_map]
  exact List.map_congr_left fun b hb => by simp [dotE_eq (hB b hb) hg]

/-- **Membership.** A passed residual check puts the generator in the span. -/
theorem memOk_mem {d : ℤ} (hd : d ≠ 0) {N : List (List ℤ)} {B : List ℕ}
    (hB : ∀ b ∈ B, validCode b = true) {g : ℕ} (hg : validCode g = true)
    (h : memOk d N (gramOf dotE B) B g = true) :
    rvec g ∈ Submodule.span ℚ {v | v ∈ B.map rvec} := by
  set l := N.map fun row => RootCheck.dot row (B.map fun b => g9 b g)
  set lq : List ℚ := l.map (↑)
  set vs := B.map rvec
  set y := combV lq vs
  have h1 : ((RootCheck.dot l (B.map fun b => dotE b g) : ℤ) : ℚ) = y ⬝ᵥ rvec g := by
    rw [dot_cast, map_dotE hB hg, dotQ_map_dot]
  have hrow : ((gramOf dotE B).map (fun row => RootCheck.dot row l)).map (Int.cast : ℤ → ℚ) =
      vs.map fun v => v ⬝ᵥ y := by
    simp only [gramOf, List.map_map, vs]
    refine List.map_congr_left fun a ha => ?_
    simp only [Function.comp_apply]
    rw [dot_cast, dotQ_comm, show (B.map fun b => dotE a b).map (Int.cast : ℤ → ℚ) =
        (B.map rvec).map fun v => v ⬝ᵥ rvec a by
      simp only [List.map_map]
      exact List.map_congr_left fun b hb => by
        simp [dotE_eq (hB a ha) (hB b hb), dotProduct_comm], dotQ_map_dot, dotProduct_comm]
  have h2 : ((quad (gramOf dotE B) l : ℤ) : ℚ) = y ⬝ᵥ y := by
    rw [quad, dot_cast, hrow, dotQ_map_dot]
  have hz : ((d * d * dotE g g - 2 * d * RootCheck.dot l (B.map fun b => dotE b g) +
      quad (gramOf dotE B) l : ℤ) : ℚ) = 0 := by
    have := beq_iff_eq.mp h
    exact_mod_cast this
  push_cast at hz
  rw [h1, h2, dotE_eq hg hg, dotProduct_comm y (rvec g)] at hz
  have hres : ((d : ℚ) • rvec g - y) ⬝ᵥ ((d : ℚ) • rvec g - y) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y (rvec g)]
    linear_combination hz
  have heq : (d : ℚ) • rvec g = y := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hres)
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have : rvec g = (d : ℚ)⁻¹ • y := by rw [← heq, smul_smul, inv_mul_cancel₀ hdq, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (combV_mem lq vs)

/-! ### The Gram check -/

theorem rowOk_spec {d : ℤ} {r : List ℤ} {i : ℕ} : ∀ {j0 : ℕ} {cs : List (List ℤ)},
    rowOk d r i j0 cs = true → ∀ j < cs.length,
      RootCheck.dot r (cs.getD j []) = if i = j0 + j then d else 0
  | _, [], _, j, hj => by simp at hj
  | j0, c :: cs, h, j, hj => by
    simp only [rowOk, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero =>
      rw [List.getD_cons_zero, h.1, Nat.add_zero]
      by_cases hij : i = j0
      · subst hij; simp [Nat.beq_refl]
      · simp [hij, beq_false hij]
    | succ j =>
      rw [List.getD_cons_succ, rowOk_spec h.2 j (by simpa using hj)]
      congr 1
      simp only [eq_iff_iff]
      omega

theorem mulRows_spec {d : ℤ} {C : List (List ℤ)} : ∀ {i0 : ℕ} {rs : List (List ℤ)},
    mulRows d C i0 rs = true → ∀ i < rs.length, ∀ j < C.length,
      RootCheck.dot (rs.getD i []) (C.getD j []) = if i0 + i = j then d else 0
  | _, [], _, i, hi, _, _ => by simp at hi
  | i0, r :: rs, h, i, hi, j, hj => by
    simp only [mulRows, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using rowOk_spec h.1 j hj
    | succ i =>
      rw [List.getD_cons_succ, mulRows_spec h.2 i (by simpa using hi) j hj]
      congr 1
      simp only [eq_iff_iff]
      omega

theorem cols_length : ∀ (n : ℕ) (rows : List (List ℤ)), (RootCheck.cols n rows).length = n
  | 0, _ => rfl
  | n + 1, rows => by simp [RootCheck.cols, cols_length n]

theorem cols_getD : ∀ (n : ℕ) (rows : List (List ℤ)) (j : ℕ), j < n →
    (RootCheck.cols n rows).getD j [] = rows.map fun r => r.getD j 0
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, rows, 0, _ => by
    simp only [RootCheck.cols, List.getD_cons_zero]
    exact List.map_congr_left fun r _ => by cases r <;> rfl
  | n + 1, rows, j + 1, hj => by
    simp only [RootCheck.cols, List.getD_cons_succ]
    rw [cols_getD n _ j (by omega), List.map_map]
    exact List.map_congr_left fun r _ => by cases r <;> simp

theorem dot_eq_sum : ∀ (xs ys : List ℤ),
    RootCheck.dot xs ys = ∑ k : Fin xs.length, xs.getD k 0 * ys.getD k 0
  | [], _ => by simp [RootCheck.dot]
  | x :: xs, [] => by simp [RootCheck.dot]
  | x :: xs, y :: ys => by
    rw [RootCheck.dot, dot_eq_sum xs ys, List.length_cons, Fin.sum_univ_succ]
    simp

/-- The columns of a list of codes. -/
def rootMat (B : List ℕ) : Matrix (Fin 23) (Fin B.length) ℚ := fun i j => rvec (B.get j) i

/-- The span of a list of codes. -/
def rspan (B : List ℕ) : Submodule ℚ (Fin 23 → ℚ) := Submodule.span ℚ {v | v ∈ B.map rvec}

theorem map_rvec_range (B : List ℕ) :
    {v | v ∈ B.map rvec} = Set.range (fun j : Fin B.length => rvec (B.get j)) := by
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨j, rfl⟩ := List.get_of_mem hb
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, List.get_mem B j, rfl⟩

/-- **The Gram check.** `Γ N = d · 1` with `d ≠ 0` makes the Gram matrix invertible. -/
theorem gram_unit {B : List ℕ} (hB : ∀ b ∈ B, validCode b = true) {d : ℤ} (hd : d ≠ 0)
    {N : List (List ℤ)} (h : mulRows d (RootCheck.cols B.length N) 0 (gramOf g9 B) = true) :
    IsUnit ((rootMat B)ᵀ * formG * rootMat B).det := by
  set r := B.length
  let Nm : Matrix (Fin r) (Fin r) ℚ := fun k j => ((N.getD k []).getD j 0 : ℤ)
  have hentry : ∀ i j : Fin r, ∑ k : Fin r, (g9 (B.get i) (B.get k) : ℚ) * Nm k j =
      if i = j then (d : ℚ) else 0 := by
    intro i j
    have hl : (gramOf g9 B).length = r := by simp [gramOf, r]
    have := mulRows_spec h i (by rw [hl]; exact i.2) j (by rw [cols_length]; exact j.2)
    rw [zero_add, cols_getD _ _ _ j.2, dot_eq_sum] at this
    have hrow : (gramOf g9 B).getD i [] = B.map fun b => g9 (B.get i) b := by
      simp [gramOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.get_eq_getElem,
        List.getElem?_eq_getElem i.2]
    rw [hrow] at this
    have hlen : (B.map fun b => g9 (B.get i) b).length = r := by simp [r]
    rw [Fintype.sum_equiv (finCongr hlen) _ (fun k : Fin r => (g9 (B.get i) (B.get k) : ℤ) *
        ((N.getD k []).getD j 0)) (fun k => by
          have hk : (k : ℕ) < B.length := by simpa using k.2
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
            Option.map_some, Option.getD_some, List.get_eq_getElem, finCongr_apply, Fin.val_cast]
          cases N[(k : ℕ)]? <;> simp)] at this
    have hc := congrArg (Int.cast : ℤ → ℚ) this
    push_cast at hc
    rw [hc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Fin.val_ne_of_ne hij]
  have hgram : ∀ i k : Fin r, ((rootMat B)ᵀ * formG * rootMat B) i k =
      (g9 (B.get i) (B.get k) : ℚ) / 9 := by
    intro i k
    rw [gram_apply, g9_eq (hB _ (List.get_mem B i)) (hB _ (List.get_mem B k))]
    simp only [rootMat]
    ring
  apply Matrix.isUnit_det_of_right_inverse (B := ((9 : ℚ) / d) • Nm)
  ext i j
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, smul_eq_mul]
  have hterm : ∀ k, ((rootMat B)ᵀ * formG * rootMat B) i k * Nm k j =
      ((g9 (B.get i) (B.get k) : ℚ) * Nm k j) * (1 / 9) := fun k => by rw [hgram]; ring
  simp only [hterm, ← Finset.sum_mul]
  rw [hentry i j]
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  split_ifs
  · field_simp
  · simp

/-- **The basis check**, unpacked: valid codes, an invertible Gram matrix and generators in the
span. -/
theorem basisOk_spec {B gens : List ℕ} (h : basisOk B gens = true) :
    (∀ b ∈ B, validCode b = true) ∧ IsUnit ((rootMat B)ᵀ * formG * rootMat B).det ∧
      ∀ g ∈ gens, rvec g ∈ rspan B := by
  unfold basisOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hB, hG⟩, h⟩ := h
  have hBv := all_valid hB
  have hGv := all_valid hG
  split at h
  · exact absurd h (by simp)
  · rename_i d N _
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hd, hmul⟩, hmem⟩ := h
    refine ⟨hBv, gram_unit hBv hd hmul, fun g hg => ?_⟩
    have := List.all_eq_true.mp hmem g hg
    simp only [Bool.or_eq_true, List.contains_iff_mem] at this
    rcases this with hgB | hok
    · exact Submodule.subset_span (List.mem_map_of_mem hgB)
    · exact memOk_mem hd hBv (hGv g hg) hok

/-! ### The frames -/

/-- **The root-complement frame** of a basis of codes. -/
def rootFrame (B : List ℕ) : Matrix (Fin 23) (Fin 23) ℚ := 1 - proj formG (rootMat B)

theorem rootMat_col_mem (B : List ℕ) (j : Fin B.length) : (fun i => rootMat B i j) ∈ rspan B :=
  Submodule.subset_span (show rvec (B.get j) ∈ B.map rvec from List.mem_map_of_mem (List.get_mem B j))

/-- Vectors of a span factor through the columns. -/
theorem factor_rootMat {κ : Type*} {B : List ℕ} {X : Matrix (Fin 23) κ ℚ}
    (hX : ∀ k, (fun i => X i k) ∈ rspan B) : ∃ C : Matrix (Fin B.length) κ ℚ, X = rootMat B * C := by
  have hcol : ∀ k, ∃ a : Fin B.length → ℚ, (fun i => X i k) = rootMat B *ᵥ a := by
    intro k
    have h := hX k
    rw [rspan, map_rvec_range] at h
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp h
    refine ⟨a, ?_⟩
    rw [← ha]
    funext i
    simp [rootMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  choose a ha using hcol
  refine ⟨Matrix.of fun j k => a k j, ?_⟩
  ext i k
  have := congrFun (ha k) i
  simp only [mulVec, dotProduct] at this
  rw [Matrix.mul_apply]
  simpa using this

/-- A projector onto vectors of the span lies in the projector of the span. -/
theorem proj_le_root {κ : Type*} [Fintype κ] [DecidableEq κ] {B : List ℕ}
    (hB : IsUnit ((rootMat B)ᵀ * formG * rootMat B).det) {X : Matrix (Fin 23) κ ℚ}
    (hX : ∀ k, (fun i => X i k) ∈ rspan B) : Nested (proj formG X) (proj formG (rootMat B)) := by
  obtain ⟨C, hC⟩ := factor_rootMat hX
  exact ⟨proj_nest_left hB hC, proj_nest_right hB hC⟩

/-- Complements reverse nesting. -/
theorem nested_one_sub {A E : Matrix (Fin 23) (Fin 23) ℚ} (h : Nested A E) :
    Nested (1 - E) (1 - A) := by
  constructor
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.2]; abel
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.1]; abel

variable {B : List ℕ} {gens : List ℕ} (hok : basisOk B gens = true)
include hok

theorem basisOk_unit : IsUnit ((rootMat B)ᵀ * formG * rootMat B).det := (basisOk_spec hok).2.1

theorem basisOk_mem {g : ℕ} (hg : g ∈ gens) : rvec g ∈ rspan B := (basisOk_spec hok).2.2 g hg

theorem rootFrame_idem : rootFrame B * rootFrame B = rootFrame B := by
  have h := proj_idem (basisOk_unit hok)
  simp only [rootFrame, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h]; abel

/-- **The rank** is `23` less the size of the basis. -/
theorem rootFrame_rank : (rootFrame B).rank = 23 - B.length := by
  have hP := proj_idem (basisOk_unit hok)
  have h := Exchange.rank_sub_add _ 1 hP (Matrix.one_mul 1) (Matrix.mul_one _) (Matrix.one_mul _)
  rw [rank_one, Fintype.card_fin, proj_rank (basisOk_unit hok), Fintype.card_fin] at h
  rw [rootFrame]
  omega

/-- The columns as an integer matrix. -/
def rootMatZ (B : List ℕ) : Matrix (Fin 23) (Fin B.length) ℤ := fun i j =>
  if B.get j < cen then (if i.val ∈ tripleOf (B.get j) then 1 else 0)
  else (if i.val = B.get j - cen then 8 else 1)

omit hok in
theorem rootMatZ_cast (B : List ℕ) : castQ (rootMatZ B) = rootMat B := by
  ext i j
  simp only [castQ, rootMatZ, rootMat, rvec, map_apply, eq_intCast, List.get_eq_getElem]
  split_ifs with h1 h2 h2
  · simp [tvec, h2]
  · simp [tvec, h2]
  · simp [wvec, tvec, h2]; norm_num
  · simp [wvec, tvec, h2]

omit hok in
theorem rootMatZ_le (B : List ℕ) (i : Fin 23) (j : Fin B.length) : |rootMatZ B i j| ≤ 8 := by
  simp only [rootMatZ]
  split_ifs <;> norm_num

/-- **Heights.** -/
theorem rootFrame_bounded : Height.Bounded (rootFrame B) (2 * 10 ^ 200) := by
  have hB := basisOk_unit hok
  rw [← rootMatZ_cast] at hB
  rw [rootFrame, ← rootMatZ_cast]
  exact frame_compl_bounded8 (rootMatZ_le B) hB

/-- **Nesting.** A frame whose span holds the other's basis lies in it. -/
theorem rootFrame_nest {B' : List ℕ} (h : ∀ b ∈ B', rvec b ∈ rspan B) :
    Nested (rootFrame B) (rootFrame B') :=
  nested_one_sub (proj_le_root (basisOk_unit hok) fun k => h _ (List.get_mem B' k))

/-- A frame lies in the complement of every frame of triples its span holds. -/
theorem rootFrame_le_compl {𝒮 : Finset (Finset ℕ)} (h : ∀ S ∈ 𝒮, tvec S ∈ rspan B) :
    Nested (rootFrame B) (1 - frameOf 𝒮) :=
  nested_one_sub (proj_le_root (basisOk_unit hok) fun a => by
    obtain ⟨S, hS, ha⟩ := Finset.mem_image.mp (basisOf_sub 𝒮 a.2)
    change a.1 ∈ rspan B
    rw [← ha]
    exact h S hS)

/-- **Hyperplanes.** A frame lies in the hyperplane of every output its span holds. -/
theorem rootFrame_le_hyper {T : Finset ℕ} (h : tvec T ∈ rspan B) :
    Nested (rootFrame B) (hyperFrame T) :=
  rootFrame_le_compl hok fun S hS => by rw [Finset.mem_singleton.mp hS]; exact h

/-- **Stars.** A frame lies in the star of every centre its span holds. -/
theorem rootFrame_le_star {c : ℕ} (hc : c < 23) (h : wvec c ∈ rspan B) :
    Nested (rootFrame B) (starFrame c) := by
  rw [show starFrame c = 1 - centreLine c by rw [← starFrame_add_centreLine hc]; abel]
  exact nested_one_sub (proj_le_root (basisOk_unit hok) fun _ => h)

/-- **One-centre frames.** A frame lies in the one-centre frame of the outputs and the centre
that its span holds. -/
theorem rootFrame_le_lift {c M : ℕ} (hc : c < 23) (hM : subB M (pairsWithout c) = true) {r : Bool}
    (hS : ∀ S ∈ liftSet c M, tvec S ∈ rspan B) (hw : r = true → wvec c ∈ rspan B) :
    Nested (rootFrame B) (liftFrame c M r) := by
  cases r
  · simpa [liftFrame] using rootFrame_le_compl hok hS
  · rw [liftFrame_true hc hM]
    refine nested_one_sub (proj_le_root (basisOk_unit hok) fun k => ?_)
    cases k with
    | inl a =>
      obtain ⟨S, hS', ha⟩ := Finset.mem_image.mp (basisOf_sub _ a.2)
      change a.1 ∈ rspan B
      rw [← ha]
      exact hS S hS'
    | inr u => exact hw rfl

omit hok in
/-- **Orthogonal triples.** The frame of triples `G`-orthogonal to the basis lies in the frame. -/
theorem frameOf_le_rootFrame {𝒮 : Finset (Finset ℕ)}
    (horth : ∀ S ∈ 𝒮, ∀ b ∈ B, gform (tvec S) (rvec b) = 0) :
    Nested (frameOf 𝒮) (rootFrame B) := by
  have hz : (basisMat 𝒮)ᵀ * formG * rootMat B = 0 := by
    ext a j
    rw [gram_apply, Matrix.zero_apply]
    obtain ⟨S, hS, ha⟩ := Finset.mem_image.mp (basisOf_sub 𝒮 a.2)
    change gform a.1 (rvec (B.get j)) = 0
    rw [← ha]
    exact horth S hS _ (List.get_mem B j)
  have hz' : (rootMat B)ᵀ * formG * basisMat 𝒮 = 0 := cross_symm hz
  have h1 : proj formG (rootMat B) * frameOf 𝒮 = 0 := by
    rw [frameOf, proj, proj]
    rw [show rootMat B * ((rootMat B)ᵀ * formG * rootMat B)⁻¹ * (rootMat B)ᵀ * formG *
        (basisMat 𝒮 * ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * (basisMat 𝒮)ᵀ * formG) =
        rootMat B * ((rootMat B)ᵀ * formG * rootMat B)⁻¹ * ((rootMat B)ᵀ * formG * basisMat 𝒮) *
          (((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * (basisMat 𝒮)ᵀ * formG) by
      simp only [Matrix.mul_assoc], hz', Matrix.mul_zero, Matrix.zero_mul]
  have h2 : frameOf 𝒮 * proj formG (rootMat B) = 0 := by
    rw [frameOf, proj, proj]
    rw [show basisMat 𝒮 * ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * (basisMat 𝒮)ᵀ * formG *
        (rootMat B * ((rootMat B)ᵀ * formG * rootMat B)⁻¹ * (rootMat B)ᵀ * formG) =
        basisMat 𝒮 * ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * ((basisMat 𝒮)ᵀ * formG * rootMat B) *
          (((rootMat B)ᵀ * formG * rootMat B)⁻¹ * (rootMat B)ᵀ * formG) by
      simp only [Matrix.mul_assoc], hz, Matrix.mul_zero, Matrix.zero_mul]
  exact nested_of_orth (A := proj formG (rootMat B)) ⟨Matrix.one_mul _, Matrix.mul_one _⟩ h1 h2

omit hok in
/-- **Sub-masks.** Two one-centre frames with nested masks and equal ranks are equal. -/
theorem liftFrame_eq_of_dim {c M M' : ℕ} (hc : c < 23) (hM : subB M (pairsWithout c) = true)
    (hsub : subB M' M = true) (hok : okC c M = true) (hok' : okC c M' = true)
    (hdim : dimC c M' = dimC c M) (r : Bool) : liftFrame c M r = liftFrame c M' r := by
  have hM' : subB M' (pairsWithout c) = true := by
    unfold subB at hsub hM ⊢
    rw [IntegerMultBounds.MathlibTM2.M8.Local.beq_iff] at hsub hM ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have e1 := congrArg (fun x => Nat.testBit x i) hsub
    have e2 := congrArg (fun x => Nat.testBit x i) hM
    simp only [show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, Nat.testBit_land] at e1 e2 ⊢
    cases h1 : M'.testBit i <;> cases h2 : M.testBit i <;> simp_all
  have hN := liftFrame_nest hc hM hsub (r := r) (r' := r) id
  have hA := liftFrame_idem hc hM r
  have hB := liftFrame_idem hc hM' r
  have h := Exchange.rank_sub_add _ _ hA hB hN.2 hN.1
  rw [liftFrame_rank hc hM hok, liftFrame_rank hc hM' hok', hdim] at h
  have h0 := eq_zero_of_rank (show (liftFrame c M' r - liftFrame c M r).rank = 0 by omega)
  exact (sub_eq_zero.mp h0).symm

omit hok in
/-- **Inside a one-centre frame.** A basis of roots of a one-centre frame spans a part of its
roots, so its frame contains the one-centre frame. -/
theorem liftFrame_le_rootFrame {c M : ℕ} (hc : c < 23) (hM : subB M (pairsWithout c) = true)
    {r : Bool} (hroot : ∀ b ∈ B, (b < cen ∧ tripleOf b ∈ liftSet c M) ∨ (b = cen + c ∧ r = true)) :
    Nested (liftFrame c M r) (rootFrame B) := by
  have h := liftSet_star hc hM
  cases r
  · have hmem : ∀ j : Fin B.length, (fun i => rootMat B i j) ∈
        Submodule.span ℚ (Set.range fun a : basisOf (liftSet c M) => (a : Fin 23 → ℚ)) := by
      intro j
      rcases hroot _ (List.get_mem B j) with ⟨hb, hS⟩ | ⟨-, h⟩
      · have : tvec (tripleOf (B.get j)) ∈ Submodule.span ℚ (vecs (liftSet c M) : Set _) :=
          Submodule.subset_span (Finset.mem_image_of_mem _ hS)
        rw [← basisOf_span, show ((basisOf (liftSet c M) : Finset _) : Set (Fin 23 → ℚ)) =
          Set.range fun a : basisOf (liftSet c M) => (a : Fin 23 → ℚ) by simp] at this
        have hb' : B[(j : ℕ)] < cen := by simpa using hb
        simpa [rootMat, rvec, hb'] using this
      · exact absurd h (by simp)
    have hX : ∀ j : Fin B.length, ∃ a : basisOf (liftSet c M) → ℚ,
        (fun i => rootMat B i j) = basisMat (liftSet c M) *ᵥ a := by
      intro j
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hmem j)
      refine ⟨a, ?_⟩
      rw [← ha]
      funext i
      simp [basisMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]
    choose a ha using hX
    have hC : rootMat B = basisMat (liftSet c M) * Matrix.of fun k j => a j k := by
      ext i j
      have := congrFun (ha j) i
      simp only [mulVec, dotProduct] at this
      rw [Matrix.mul_apply]
      simpa using this
    have hu := basis_gram_isUnit h
    simpa [liftFrame, rootFrame] using
      nested_one_sub (A := proj formG (rootMat B)) (E := frameOf (liftSet c M))
        ⟨proj_nest_left hu hC, proj_nest_right hu hC⟩
  · set E := fromCols (basisMat (liftSet c M)) (wcol c)
    have hu : IsUnit (Eᵀ * formG * E).det :=
      fromCols_gram_isUnit (basis_gram_isUnit h) (wcol_gram_isUnit hc) (cross_wcol h)
    have hmem : ∀ j : Fin B.length, (fun i => rootMat B i j) ∈
        Submodule.span ℚ (Set.range fun k => fun i => E i k) := by
      intro j
      rcases hroot _ (List.get_mem B j) with ⟨hb, hS⟩ | ⟨hb, -⟩
      · have : tvec (tripleOf (B.get j)) ∈ Submodule.span ℚ (vecs (liftSet c M) : Set _) :=
          Submodule.subset_span (Finset.mem_image_of_mem _ hS)
        rw [← basisOf_span] at this
        have hle : Submodule.span ℚ ((basisOf (liftSet c M) : Finset (Fin 23 → ℚ)) : Set _) ≤
            Submodule.span ℚ (Set.range fun k => fun i => E i k) := by
          refine Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Sum.inl ⟨v, hv⟩, ?_⟩
          funext i
          simp [E, basisMat]
        have hb' : B[(j : ℕ)] < cen := by simpa using hb
        simpa [rootMat, rvec, hb'] using hle this
      · refine Submodule.subset_span ⟨Sum.inr (), ?_⟩
        have hb' : B[(j : ℕ)] = cen + c := by simpa using hb
        funext i
        simp [E, wcol, rootMat, rvec, hb']
    obtain ⟨C, hC⟩ : ∃ C : Matrix (basisOf (liftSet c M) ⊕ Unit) (Fin B.length) ℚ, rootMat B = E * C := by
      have hX : ∀ j : Fin B.length, ∃ a, (fun i => rootMat B i j) = E *ᵥ a := by
        intro j
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hmem j)
        refine ⟨a, ?_⟩
        rw [← ha]
        funext i
        simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
      choose a ha using hX
      refine ⟨Matrix.of fun k j => a j k, ?_⟩
      ext i j
      have := congrFun (ha j) i
      simp only [mulVec, dotProduct] at this
      rw [Matrix.mul_apply]
      simpa using this
    rw [liftFrame_true hc hM, rootFrame]
    exact nested_one_sub ⟨proj_nest_left hu hC, proj_nest_right hu hC⟩

end

end IntegerMultBounds.MathlibTM2.M8.Frames
