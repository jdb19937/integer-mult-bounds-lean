module

public import IntegerMultBounds.MathlibTM2.M8.Frames.PairMask
public import IntegerMultBounds.MathlibTM2.M8.Frames.PairRank
public import IntegerMultBounds.MathlibTM2.M8.Local.Bits

/-!
# Soundness of the pair-mask checks

The checks of `Frames.PairMask` are sound for any list `U` of later-neighbour masks and any list
of components: when the layers are disjoint, cover the points on edges, each lies in the
neighbours of the one before and each component is closed, the layers are a parity forest
(`cert_ok`): a point's root is its component's, its depth its layer, its sign the layer's parity,
and its parent any neighbour in the layer before. A component is odd exactly when an edge joins
two of its even or two of its odd layers (`odd_iff`), so `PairRank.pair_rank` gives the rank
(`mask_rank`). Nothing about how the components were found is used.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Module Submodule PairRank IntegerMultBounds.MathlibTM2.M8.Local

/-! ### Bits of the primitives -/

theorem tb_lor (a b i : ℕ) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_lor a b i

theorem tb_land (a b i : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_land a b i

theorem tb_minus (x v i : ℕ) : (minus x v).testBit i = (x.testBit i && !v.testBit i) := by
  rw [minus, show Nat.xor x (Nat.land x v) = x ^^^ Nat.land x v from rfl, Nat.testBit_xor, tb_land]
  cases x.testBit i <;> cases v.testBit i <;> rfl

theorem land_ne_zero {a b : ℕ} : Nat.land a b ≠ 0 ↔ ∃ x, a.testBit x = true ∧ b.testBit x = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [tb_land, Bool.and_eq_true] at hi
    exact ⟨i, hi⟩
  · rintro ⟨x, ha, hb⟩ h0
    have := congrArg (fun n => n.testBit x) h0
    simp only [tb_land, ha, hb, Nat.zero_testBit] at this
    cases this

theorem ne_zero_iff_bit {a : ℕ} : a ≠ 0 ↔ ∃ x, a.testBit x = true := by
  constructor
  · exact Nat.exists_testBit_of_ne_zero
  · rintro ⟨x, hx⟩ h0
    rw [h0, Nat.zero_testBit] at hx
    cases hx

theorem tb_ifBit (y u w : ℕ) :
    (bif Nat.beq y 0 then 0 else bit u).testBit w = true ↔ y ≠ 0 ∧ u = w := by
  rw [beq_cond]
  split_ifs with h
  · simp [h]
  · simp [h, testBit_bit]

/-! ### Neighbours -/

section Nbr

variable (U : List ℕ)

/-- `u` and `w` are joined. -/
def Adj (u w : ℕ) : Prop := (U.getD u 0).testBit w = true ∨ (U.getD w 0).testBit u = true

/-- `w` lies on an edge. -/
def OnEdge (w : ℕ) : Prop := (∃ x, (U.getD w 0).testBit x = true) ∨ ∃ i, (U.getD i 0).testBit w = true

theorem testBit_upFrom (L w : ℕ) : ∀ (U : List ℕ) (u : ℕ),
    (upFrom L u U).testBit w = true ↔ ∃ i, L.testBit (u + i) = true ∧ (U.getD i 0).testBit w = true
  | [], u => by simp [upFrom]
  | x :: U, u => by
    rw [upFrom, tb_lor, Bool.or_eq_true, testBit_upFrom L w U, cond_ite, testB_eq]
    constructor
    · rintro (h | ⟨i, h1, h2⟩)
      · split_ifs at h with hL
        · exact ⟨0, by simpa using hL, by simpa using h⟩
        · simp at h
      · exact ⟨i + 1, by rw [show u + (i + 1) = Nat.add u 1 + i by simp [Nat.add_eq]; omega]; exact h1,
          by simpa using h2⟩
    · rintro ⟨i, h1, h2⟩
      cases i with
      | zero =>
        left
        simp only [Nat.add_zero] at h1
        simp only [List.getD_cons_zero] at h2
        simp [h1, h2]
      | succ i =>
        right
        exact ⟨i, by rw [show Nat.add u 1 + i = u + (i + 1) by simp [Nat.add_eq]; omega]; exact h1,
          by simpa using h2⟩

theorem testBit_downFrom (L w : ℕ) : ∀ (U : List ℕ) (u : ℕ),
    (downFrom L u U).testBit w = true ↔ ∃ i, w = u + i ∧ Nat.land (U.getD i 0) L ≠ 0
  | [], u => by simp [downFrom]
  | x :: U, u => by
    rw [downFrom, tb_lor, Bool.or_eq_true, testBit_downFrom L w U, tb_ifBit]
    constructor
    · rintro (⟨h, rfl⟩ | ⟨i, h1, h2⟩)
      · exact ⟨0, rfl, by simpa using h⟩
      · exact ⟨i + 1, by simp [Nat.add_eq] at h1; omega, by simpa using h2⟩
    · rintro ⟨i, h1, h2⟩
      cases i with
      | zero => left; exact ⟨by simpa using h2, by omega⟩
      | succ i => right; exact ⟨i, by simp [Nat.add_eq]; omega, by simpa using h2⟩

/-- **The neighbours of a set** are the points joined to it. -/
theorem testBit_nbr (L w : ℕ) : (nbr U L).testBit w = true ↔ ∃ u, L.testBit u = true ∧ Adj U u w := by
  rw [nbr, tb_lor, Bool.or_eq_true, testBit_upFrom, testBit_downFrom]
  constructor
  · rintro (⟨i, h1, h2⟩ | ⟨i, rfl, h2⟩)
    · exact ⟨i, by simpa using h1, Or.inl h2⟩
    · obtain ⟨x, hx, hL⟩ := land_ne_zero.mp h2
      exact ⟨x, hL, Or.inr (by simpa using hx)⟩
  · rintro ⟨u, hL, h | h⟩
    · exact Or.inl ⟨u, by simpa using hL, h⟩
    · exact Or.inr ⟨w, by simp, land_ne_zero.mpr ⟨u, h, hL⟩⟩

theorem testBit_touchedFrom (w : ℕ) : ∀ (U : List ℕ) (u : ℕ),
    (touchedFrom u U).testBit w = true ↔
      ∃ i, (w = u + i ∧ U.getD i 0 ≠ 0) ∨ (U.getD i 0).testBit w = true
  | [], u => by simp [touchedFrom]
  | x :: U, u => by
    rw [touchedFrom, tb_lor, tb_lor, Bool.or_eq_true, Bool.or_eq_true, tb_ifBit,
      testBit_touchedFrom w U]
    constructor
    · rintro ((⟨h, rfl⟩ | h) | ⟨i, h⟩)
      · exact ⟨0, Or.inl ⟨rfl, by simpa using h⟩⟩
      · exact ⟨0, Or.inr (by simpa using h)⟩
      · refine ⟨i + 1, ?_⟩
        rcases h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨by simp [Nat.add_eq] at h1; omega, by simpa using h2⟩
        · exact Or.inr (by simpa using h)
    · rintro ⟨i, h⟩
      cases i with
      | zero =>
        left
        rcases h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨by simpa using h2, by omega⟩
        · exact Or.inr (by simpa using h)
      | succ i =>
        right
        refine ⟨i, ?_⟩
        rcases h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨by simp [Nat.add_eq]; omega, by simpa using h2⟩
        · exact Or.inr (by simpa using h)

/-- **The points on edges.** -/
theorem testBit_touched (w : ℕ) : (touchedFrom 0 U).testBit w = true ↔ OnEdge U w := by
  rw [testBit_touchedFrom, OnEdge]
  constructor
  · rintro ⟨i, ⟨rfl, h⟩ | h⟩
    · exact Or.inl (ne_zero_iff_bit.mp (by simpa using h))
    · exact Or.inr ⟨i, h⟩
  · rintro (h | ⟨i, h⟩)
    · exact ⟨w, Or.inl ⟨by simp, ne_zero_iff_bit.mpr h⟩⟩
    · exact ⟨i, Or.inr h⟩

end Nbr

/-! ### Layers -/

/-- Two masks share no point. -/
def Disj (A B : ℕ) : Prop := ∀ v, A.testBit v = true → B.testBit v = false

theorem Disj.symm {A B : ℕ} (h : Disj A B) : Disj B A := fun v hB => by
  cases hA : A.testBit v
  · rfl
  · rw [h v hA] at hB; cases hB

theorem testBit_unionL (v : ℕ) : ∀ ls : List ℕ,
    (unionL ls).testBit v = true ↔ ∃ L ∈ ls, L.testBit v = true
  | [] => by simp [unionL]
  | L :: ls => by simp [unionL, testBit_unionL v ls]

theorem disjL_spec : ∀ (acc : ℕ) (ls : List ℕ), disjL acc ls = true →
    (∀ L ∈ ls, Disj L acc) ∧ ls.Pairwise Disj
  | _, [] => by simp
  | acc, L :: ls => by
    rw [disjL, Bool.and_eq_true, beq_iff]
    rintro ⟨h0, h⟩
    obtain ⟨h1, h2⟩ := disjL_spec _ ls h
    have hL : Disj L acc := fun v hv => by
      have := congrArg (fun n => n.testBit v) h0
      simpa [tb_land, hv] using this
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun L' hL' => ?_, h2⟩⟩
    · intro L' hL'
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact hL
      · intro v hv
        have := h1 L' hL' v hv
        simp only [tb_lor, Bool.or_eq_false_iff] at this
        exact this.1
    · intro v hv
      cases hL'v : L'.testBit v
      · rfl
      · have := h1 L' hL' v hL'v
        simp only [tb_lor, Bool.or_eq_false_iff] at this
        rw [this.2] at hv; cases hv

/-- The first layer of `v`. -/
def layerIdx (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | L :: ls => if L.testBit v = true then 0 else layerIdx v ls + 1

theorem layerIdx_mem (v : ℕ) : ∀ ls : List ℕ, (unionL ls).testBit v = true →
    layerIdx v ls < ls.length ∧ (ls.getD (layerIdx v ls) 0).testBit v = true
  | [], h => by simp [unionL] at h
  | L :: ls, h => by
    rw [layerIdx]
    split_ifs with hL
    · simpa using hL
    · rw [unionL, tb_lor, Bool.or_eq_true] at h
      have := layerIdx_mem v ls (h.resolve_left hL)
      simpa using this

theorem layerIdx_eq (v : ℕ) : ∀ (ls : List ℕ) (i : ℕ), ls.Pairwise Disj → i < ls.length →
    (ls.getD i 0).testBit v = true → layerIdx v ls = i
  | [], _, _, hi, _ => by simp at hi
  | L :: ls, 0, _, _, h => by simp only [List.getD_cons_zero] at h; simp [layerIdx, h]
  | L :: ls, i + 1, hp, hi, h => by
    rw [List.pairwise_cons] at hp
    simp only [List.getD_cons_succ] at h
    simp only [List.length_cons] at hi
    have hmem : ls.getD i 0 ∈ ls := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have hL : L.testBit v = false := (hp.1 _ hmem).symm v h
    simp [layerIdx, hL, layerIdx_eq v ls i hp.2 (by omega) h]

/-- **Even and odd layers**: a point of disjoint layers lies in the even or the odd part by the
parity of its layer. -/
theorem testBit_parts (v : ℕ) : ∀ ls : List ℕ, ls.Pairwise Disj →
    (parts ls).1.testBit v = ((unionL ls).testBit v && decide (layerIdx v ls % 2 = 0)) ∧
      (parts ls).2.testBit v = ((unionL ls).testBit v && decide (layerIdx v ls % 2 = 1))
  | [], _ => by simp [parts, unionL]
  | L :: ls, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨h1, h2⟩ := testBit_parts v ls hp.2
    simp only [parts, unionL, tb_lor, layerIdx]
    by_cases hL : L.testBit v = true
    swap
    · rw [Bool.not_eq_true] at hL
      have e : ∀ n : ℕ, ((n + 1) % 2 = 0 ↔ n % 2 = 1) ∧ ((n + 1) % 2 = 1 ↔ n % 2 = 0) :=
        fun n => ⟨by omega, by omega⟩
      simp [h1, h2, (e _).1, (e _).2, hL]
    · have hu : (unionL ls).testBit v = false := by
        cases hu : (unionL ls).testBit v
        · rfl
        · obtain ⟨L', hL', hv⟩ := (testBit_unionL v ls).mp hu
          rw [(hp.1 L' hL') v hL] at hv; cases hv
      simp [h1, h2, hu, hL]

theorem layersOk_spec (U : List ℕ) : ∀ (L : ℕ) (ls : List ℕ) (j : ℕ), layersOk U L ls = true →
    j + 1 < (L :: ls).length → ∀ w, ((L :: ls).getD (j + 1) 0).testBit w = true →
      ∃ u, ((L :: ls).getD j 0).testBit u = true ∧ Adj U u w
  | _, [], _, _, hj, _, _ => by simp at hj
  | L, L' :: ls, j, h, hj, w, hw => by
    rw [layersOk, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hw ⊢
      exact (testBit_nbr U L w).mp (subB_spec h.1 w hw)
    | succ j =>
      simp only [List.getD_cons_succ] at hw ⊢
      exact layersOk_spec U L' ls j h.2 (by simpa using hj) w hw

/-! ### Components -/

/-- The component of `v`. -/
def compOf (v : ℕ) : List (ℕ × List ℕ) → Option (ℕ × List ℕ)
  | [] => none
  | p :: cs => if (unionL p.2).testBit v = true then some p else compOf v cs

theorem compOf_some (v : ℕ) {p : ℕ × List ℕ} : ∀ cs : List (ℕ × List ℕ), compOf v cs = some p →
    p ∈ cs ∧ (unionL p.2).testBit v = true
  | [], h => by simp [compOf] at h
  | q :: cs, h => by
    rw [compOf] at h
    split_ifs at h with hq
    · cases h; exact ⟨List.mem_cons_self .., hq⟩
    · have := compOf_some v cs h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- Components whose layers are disjoint. -/
def CompsDisj (cs : List (ℕ × List ℕ)) : Prop :=
  cs.Pairwise fun p q => ∀ A ∈ p.2, ∀ B ∈ q.2, Disj A B

theorem compOf_eq (v : ℕ) {p : ℕ × List ℕ} : ∀ cs : List (ℕ × List ℕ), CompsDisj cs → p ∈ cs →
    (unionL p.2).testBit v = true → compOf v cs = some p
  | [], _, hp, _ => by simp at hp
  | q :: cs, hd, hp, hv => by
    rw [CompsDisj, List.pairwise_cons] at hd
    rw [compOf]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [hv]
    · have hq : (unionL q.2).testBit v = false := by
        cases hq : (unionL q.2).testBit v
        · rfl
        · obtain ⟨A, hA, hAv⟩ := (testBit_unionL v _).mp hq
          obtain ⟨B, hB, hBv⟩ := (testBit_unionL v _).mp hv
          rw [hd.1 p hp A hA B hB v hAv] at hBv; cases hBv
      simp [hq, compOf_eq v cs hd.2 hp hv]

theorem layersOf_eq : ∀ cs : List (ℕ × List ℕ), layersOf cs = cs.flatMap Prod.snd
  | [] => rfl
  | p :: cs => by rw [layersOf, layersOf_eq cs, List.flatMap_cons]

theorem compOk_spec {U : List ℕ} {p : ℕ × List ℕ} (h : compOk U p = true) :
    ∃ ls, p.2 = bit p.1 :: ls ∧ p.1 < 23 ∧ layersOk U (bit p.1) ls = true ∧
      subB (nbr U (unionL p.2)) (unionL p.2) = true := by
  obtain ⟨r, ls⟩ := p
  rw [compOk] at h
  cases ls with
  | nil => cases h
  | cons L ls =>
    simp only [Bool.and_eq_true, blt_iff, beq_iff] at h
    obtain ⟨⟨⟨hr, rfl⟩, hl⟩, hs⟩ := h
    exact ⟨ls, rfl, hr, hl, hs⟩

theorem compsOk_spec (U : List ℕ) : ∀ cs : List (ℕ × List ℕ), compsOk U cs = true →
    ∀ p ∈ cs, compOk U p = true
  | [], _ => by simp
  | p :: cs, h => by
    rw [compsOk, Bool.and_eq_true] at h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact compsOk_spec U cs h.2 q hq

theorem bipCount_eq (U : List ℕ) : ∀ cs : List (ℕ × List ℕ),
    bipCount U cs = (cs.filter fun p => freeOf U (parts p.2).1 && freeOf U (parts p.2).2).length
  | [] => rfl
  | p :: cs => by
    rw [bipCount, List.filter_cons, bipCount_eq U cs, cond_ite]
    split_ifs <;> simp [Nat.add_eq, Nat.add_comm]

theorem popc_eq (x : ℕ) : ∀ n, popc x n = ∑ i ∈ Finset.range n, if x.testBit i = true then 1 else 0
  | 0 => rfl
  | n + 1 => by rw [popc, Finset.sum_range_succ, popc_eq x n, cond_ite, Nat.add_eq, testB_eq]

/-! ### The parity forest of the layers -/

/-- A point below 23. -/
def fin23 (n : ℕ) : Fin 23 := if h : n < 23 then ⟨n, h⟩ else 0

theorem fin23_val {n : ℕ} (h : n < 23) : (fin23 n).val = n := by simp [fin23, h]

section Cert

variable (U : List ℕ) (Vm : ℕ) (cs : List (ℕ × List ℕ))

/-- The edges, each from its smaller point. -/
def edgesU : Finset (Fin 23 × Fin 23) :=
  Finset.univ.filter fun e => (U.getD e.1 0).testBit e.2 = true

/-- The root of `v`: its component's. -/
def rootF (v : Fin 23) : Fin 23 :=
  match compOf v cs with
  | some p => fin23 p.1
  | none => v

/-- The depth of `v`: its layer. -/
def depthF (v : Fin 23) : ℕ :=
  match compOf v cs with
  | some p => layerIdx v p.2
  | none => 0

open Classical in
/-- The parity forest of the layers: the parent of a point is a neighbour one layer up. -/
noncomputable def certL : Cert (Fin 23) where
  V := Finset.univ.filter fun v => Vm.testBit v = true
  root := rootF cs
  parent v :=
    if h : ∃ u : Fin 23, Adj U u v ∧ compOf u cs = compOf v cs ∧ depthF cs u + 1 = depthF cs v
    then h.choose else v
  sign v := decide (depthF cs v % 2 = 1)
  depth := depthF cs

/-- The hypotheses of the checks. -/
structure Good : Prop where
  lt : ∀ u w, (U.getD u 0).testBit w = true → u < 23 ∧ w < 23
  pts : ∀ v, Vm.testBit v = true ↔ OnEdge U v
  disj : (layersOf cs).Pairwise Disj
  cover : ∀ v, (unionL (layersOf cs)).testBit v = Vm.testBit v
  comp : ∀ p ∈ cs, compOk U p = true

variable {U Vm cs}

variable (hg : Good U Vm cs)
include hg

theorem Good.compsDisj : CompsDisj cs := by
  have := hg.disj
  rw [layersOf_eq, List.pairwise_flatMap] at this
  exact this.2

theorem Good.layers {p : ℕ × List ℕ} (hp : p ∈ cs) : p.2.Pairwise Disj := by
  have := hg.disj
  rw [layersOf_eq, List.pairwise_flatMap] at this
  exact this.1 p hp

theorem Good.exists_comp {v : ℕ} (hv : Vm.testBit v = true) :
    ∃ p ∈ cs, (unionL p.2).testBit v = true := by
  rw [← hg.cover, testBit_unionL, layersOf_eq] at hv
  obtain ⟨L, hL, hLv⟩ := hv
  obtain ⟨p, hp, hLp⟩ := List.mem_flatMap.mp hL
  exact ⟨p, hp, (testBit_unionL v _).mpr ⟨L, hLp, hLv⟩⟩

theorem Good.mem_pts {p : ℕ × List ℕ} (hp : p ∈ cs) {v : ℕ} (hv : (unionL p.2).testBit v = true) :
    Vm.testBit v = true := by
  rw [← hg.cover, testBit_unionL, layersOf_eq]
  obtain ⟨L, hL, hLv⟩ := (testBit_unionL v _).mp hv
  exact ⟨L, List.mem_flatMap.mpr ⟨p, hp, hL⟩, hLv⟩

theorem Good.compOf_adj {p : ℕ × List ℕ} {u w : ℕ} (hu : compOf u cs = some p) (h : Adj U u w) :
    compOf w cs = some p := by
  obtain ⟨hp, hpu⟩ := compOf_some u cs hu
  obtain ⟨ls, -, -, -, hs⟩ := compOk_spec (hg.comp p hp)
  exact compOf_eq w cs hg.compsDisj hp (subB_spec hs w ((testBit_nbr U _ w).mpr ⟨u, hpu, h⟩))

omit hg in
theorem rootF_of {p : ℕ × List ℕ} {v : Fin 23} (h : compOf v cs = some p) :
    rootF cs v = fin23 p.1 := by
  simp [rootF, h]

omit hg in
theorem depthF_of {p : ℕ × List ℕ} {v : Fin 23} (h : compOf v cs = some p) :
    depthF cs v = layerIdx v p.2 := by
  simp [depthF, h]

theorem Good.root_lt {p : ℕ × List ℕ} (hp : p ∈ cs) : p.1 < 23 := by
  obtain ⟨_, _, h, _⟩ := compOk_spec (hg.comp p hp)
  exact h

theorem Good.root_mem {p : ℕ × List ℕ} (hp : p ∈ cs) : (unionL p.2).testBit p.1 = true := by
  obtain ⟨ls, he, -⟩ := compOk_spec (hg.comp p hp)
  rw [he, unionL, tb_lor, testBit_bit]
  simp

theorem Good.compOf_root {p : ℕ × List ℕ} (hp : p ∈ cs) : compOf (fin23 p.1).val cs = some p := by
  rw [fin23_val (hg.root_lt hp)]
  exact compOf_eq _ cs hg.compsDisj hp (hg.root_mem hp)

theorem Good.compOf_pt {v : ℕ} (hv : Vm.testBit v = true) :
    ∃ p ∈ cs, compOf v cs = some p := by
  obtain ⟨p, hp, hpv⟩ := hg.exists_comp hv
  exact ⟨p, hp, compOf_eq v cs hg.compsDisj hp hpv⟩

omit hg in
theorem adj_edges {u w : Fin 23} (h : Adj U u w) :
    (u, w) ∈ edgesU U ∨ (w, u) ∈ edgesU U := by
  simpa [edgesU, Adj] using h

/-- **The layers are a parity forest.** -/
theorem cert_ok : (certL U Vm cs).Ok (edgesU U) := by
  refine ⟨fun e he => ?_, fun v hv => ?_, fun v hv hr => ?_⟩
  · simp only [edgesU, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have h1 : Vm.testBit e.1 = true := (hg.pts _).mpr (Or.inl ⟨_, he⟩)
    have h2 : Vm.testBit e.2 = true := (hg.pts _).mpr (Or.inr ⟨_, he⟩)
    refine ⟨by simpa [certL] using h1, by simpa [certL] using h2, ?_⟩
    obtain ⟨p, -, hp⟩ := hg.compOf_pt h1
    show rootF cs e.1 = rootF cs e.2
    rw [rootF_of hp, rootF_of (hg.compOf_adj hp (Or.inl he))]
  · simp only [certL, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨p, hp, hpv⟩ := hg.compOf_pt hv
    rw [rootF_of hpv, rootF_of (hg.compOf_root hp)]
    refine ⟨?_, rfl⟩
    rw [fin23_val (hg.root_lt hp)]
    exact hg.mem_pts hp (hg.root_mem hp)
  · simp only [certL, Finset.mem_filter, Finset.mem_univ, true_and] at hv hr ⊢
    obtain ⟨p, hp, hpv⟩ := hg.compOf_pt hv
    obtain ⟨ls, he, hlt, hl, -⟩ := compOk_spec (hg.comp p hp)
    obtain ⟨_, hpv'⟩ := compOf_some _ cs hpv
    obtain ⟨hi, hiv⟩ := layerIdx_mem _ _ hpv'
    have hex : ∃ u : Fin 23, Adj U u v ∧ compOf u cs = compOf v cs ∧ depthF cs u + 1 = depthF cs v := by
      rw [depthF_of hpv]
      rcases hj : layerIdx (↑v) p.2 with _ | j
      · rw [hj, he] at hiv
        simp only [List.getD_cons_zero, testBit_bit, decide_eq_true_eq] at hiv
        exact absurd (by rw [rootF_of hpv]; exact Fin.ext (by rw [fin23_val hlt, hiv])) hr
      · rw [hj] at hiv hi
        rw [he] at hiv hi
        obtain ⟨u, hu, hadj⟩ := layersOk_spec U _ ls j hl hi _ hiv
        have hu23 : u < 23 := by rcases hadj with h | h <;> [exact (hg.lt _ _ h).1; exact (hg.lt _ _ h).2]
        have hcu : compOf u cs = some p := by
          rw [hg.compOf_adj hpv (show Adj U v u from hadj.symm)]
        refine ⟨⟨u, hu23⟩, hadj, by rw [hpv]; exact hcu, ?_⟩
        rw [depthF_of (v := ⟨u, hu23⟩) hcu]
        congr 1
        refine layerIdx_eq _ _ _ (hg.layers hp) (by rw [he]; simp at hi ⊢; omega) ?_
        rw [he]; exact hu
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨hadj, hc, hd⟩ := hex.choose_spec
    refine ⟨adj_edges hadj |>.symm, ?_, ?_, by omega⟩
    · generalize depthF cs hex.choose = a at hd ⊢
      rw [← hd]
      simp only [ne_eq, decide_eq_decide]
      omega
    · show rootF cs _ = rootF cs v
      rw [rootF_of (hc.trans hpv), rootF_of hpv]

end Cert

theorem freeOf_false (U : List ℕ) (S : ℕ) :
    freeOf U S = false ↔ ∃ u w, S.testBit u = true ∧ S.testBit w = true ∧ Adj U u w := by
  rw [freeOf, Bool.eq_false_iff, ne_eq, beq_iff, ← ne_eq, land_ne_zero]
  constructor
  · rintro ⟨w, hn, hw⟩
    obtain ⟨u, hu, ha⟩ := (testBit_nbr U S w).mp hn
    exact ⟨u, w, hu, hw, ha⟩
  · rintro ⟨u, w, hu, hw, ha⟩
    exact ⟨w, (testBit_nbr U S w).mpr ⟨u, hu, ha⟩, hw⟩

section Dim

variable {U : List ℕ} {Vm : ℕ} {cs : List (ℕ × List ℕ)} (hg : Good U Vm cs)
include hg

/-- The component is bipartite: no edge inside its even or its odd layers. -/
abbrev bipB (U : List ℕ) (p : ℕ × List ℕ) : Bool := freeOf U (parts p.2).1 && freeOf U (parts p.2).2

theorem Good.parts_of {p : ℕ × List ℕ} (hp : p ∈ cs) {v : ℕ} (hv : (unionL p.2).testBit v = true) :
    (parts p.2).1.testBit v = decide (layerIdx v p.2 % 2 = 0) ∧
      (parts p.2).2.testBit v = decide (layerIdx v p.2 % 2 = 1) := by
  have := testBit_parts v p.2 (hg.layers hp)
  rw [hv, Bool.true_and, Bool.true_and] at this
  exact this

theorem Good.union_of_parts {p : ℕ × List ℕ} (hp : p ∈ cs) {v : ℕ}
    (hv : (parts p.2).1.testBit v = true ∨ (parts p.2).2.testBit v = true) :
    (unionL p.2).testBit v = true := by
  have := testBit_parts v p.2 (hg.layers hp)
  rcases hv with hv | hv
  · rw [this.1, Bool.and_eq_true] at hv; exact hv.1
  · rw [this.2, Bool.and_eq_true] at hv; exact hv.1

theorem Good.adj_lt {u w : ℕ} (h : Adj U u w) : u < 23 ∧ w < 23 := by
  rcases h with h | h
  · exact hg.lt _ _ h
  · exact (hg.lt _ _ h).symm

/-- **A component is odd** exactly when an edge joins two of its even or two of its odd layers. -/
theorem Good.odd_iff {p : ℕ × List ℕ} (hp : p ∈ cs) :
    (certL U Vm cs).Odd (edgesU U) (fin23 p.1) ↔ bipB U p = false := by
  have hroot := hg.compOf_root hp
  constructor
  · rintro ⟨e, he, hr, hs⟩
    simp only [edgesU, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have h1 : Vm.testBit e.1 = true := (hg.pts _).mpr (Or.inl ⟨_, he⟩)
    obtain ⟨q, hq, hqe⟩ := hg.compOf_pt h1
    change rootF cs e.1 = _ at hr
    rw [rootF_of hqe] at hr
    have hqp : q = p := by
      have := hg.compOf_root hq
      rw [hr] at this
      rw [hroot] at this
      exact (Option.some_inj.mp this).symm
    subst hqp
    have h2 := hg.compOf_adj hqe (Or.inl he)
    have hs' : layerIdx e.1 q.2 % 2 = layerIdx e.2 q.2 % 2 := by
      simp only [certL, depthF_of hqe, depthF_of (v := e.2) h2, decide_eq_decide] at hs
      omega
    have hp1 := hg.parts_of hp (compOf_some _ cs hqe).2
    have hp2 := hg.parts_of hp (compOf_some _ cs h2).2
    rw [Bool.and_eq_false_iff, freeOf_false, freeOf_false]
    rcases Nat.mod_two_eq_zero_or_one (layerIdx e.1 q.2) with h0 | h0
    · left
      exact ⟨e.1, e.2, by rw [hp1.1]; simpa using h0, by rw [hp2.1]; simpa [← hs'] using h0,
        Or.inl he⟩
    · right
      exact ⟨e.1, e.2, by rw [hp1.2]; simpa using h0, by rw [hp2.2]; simpa [← hs'] using h0,
        Or.inl he⟩
  · intro h
    have hcase : ∃ S, freeOf U S = false ∧
        ∀ v, S.testBit v = true → (unionL p.2).testBit v = true ∧
          ∀ v', S.testBit v' = true → layerIdx v p.2 % 2 = layerIdx v' p.2 % 2 := by
      rw [bipB, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · refine ⟨_, h, fun v hv => ⟨hg.union_of_parts hp (Or.inl hv), fun v' hv' => ?_⟩⟩
        have a := (hg.parts_of hp (hg.union_of_parts hp (Or.inl hv))).1
        have b := (hg.parts_of hp (hg.union_of_parts hp (Or.inl hv'))).1
        rw [a] at hv; rw [b] at hv'
        simp only [decide_eq_true_eq] at hv hv'
        omega
      · refine ⟨_, h, fun v hv => ⟨hg.union_of_parts hp (Or.inr hv), fun v' hv' => ?_⟩⟩
        have a := (hg.parts_of hp (hg.union_of_parts hp (Or.inr hv))).2
        have b := (hg.parts_of hp (hg.union_of_parts hp (Or.inr hv'))).2
        rw [a] at hv; rw [b] at hv'
        simp only [decide_eq_true_eq] at hv hv'
        omega
    obtain ⟨S, hS, hSp⟩ := hcase
    obtain ⟨u, w, hu, hw, ha⟩ := (freeOf_false U S).mp hS
    obtain ⟨hu23, hw23⟩ := hg.adj_lt ha
    have hcu := compOf_eq u cs hg.compsDisj hp (hSp u hu).1
    have hcw := compOf_eq w cs hg.compsDisj hp (hSp w hw).1
    have hpar := (hSp u hu).2 w hw
    rcases ha with ha | ha
    · refine ⟨(⟨u, hu23⟩, ⟨w, hw23⟩), by simpa [edgesU] using ha, rootF_of (v := ⟨u, hu23⟩) hcu, ?_⟩
      simp only [certL, depthF_of (v := ⟨u, hu23⟩) hcu, depthF_of (v := ⟨w, hw23⟩) hcw, hpar]
    · refine ⟨(⟨w, hw23⟩, ⟨u, hu23⟩), by simpa [edgesU] using ha, rootF_of (v := ⟨w, hw23⟩) hcw, ?_⟩
      simp only [certL, depthF_of (v := ⟨u, hu23⟩) hcu, depthF_of (v := ⟨w, hw23⟩) hcw, hpar]

theorem Good.roots_ne {p q : ℕ × List ℕ} (hp : p ∈ cs) (hq : q ∈ cs)
    (h : ∀ A ∈ p.2, ∀ B ∈ q.2, Disj A B) : fin23 p.1 ≠ fin23 q.1 := by
  intro he
  have e : p.1 = q.1 := by
    have := congrArg Fin.val he
    rwa [fin23_val (hg.root_lt hp), fin23_val (hg.root_lt hq)] at this
  obtain ⟨A, hA, hAv⟩ := (testBit_unionL _ _).mp (hg.root_mem hp)
  obtain ⟨B, hB, hBv⟩ := (testBit_unionL _ _).mp (hg.root_mem hq)
  rw [← e, h A hA B hB _ hAv] at hBv
  cases hBv

theorem Good.bipRoots_eq :
    (certL U Vm cs).bipRoots (edgesU U) = ((cs.filter (bipB U)).map fun p => fin23 p.1).toFinset := by
  ext r
  simp only [Cert.bipRoots, Cert.roots, Finset.mem_filter, List.mem_toFinset, List.mem_map,
    List.mem_filter]
  constructor
  · rintro ⟨⟨hv, hr⟩, hodd⟩
    simp only [certL, Finset.mem_filter, Finset.mem_univ, true_and] at hv hr
    obtain ⟨p, hp, hpv⟩ := hg.compOf_pt hv
    rw [rootF_of hpv] at hr
    rw [← hr, hg.odd_iff hp, Bool.not_eq_false] at hodd
    exact ⟨p, ⟨hp, hodd⟩, hr⟩
  · rintro ⟨p, ⟨hp, hb⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [certL, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [fin23_val (hg.root_lt hp)]
      exact hg.mem_pts hp (hg.root_mem hp)
    · exact rootF_of (hg.compOf_root hp)
    · rw [hg.odd_iff hp, hb]; simp

theorem Good.card_bipRoots : ((certL U Vm cs).bipRoots (edgesU U)).card = bipCount U cs := by
  rw [hg.bipRoots_eq, List.toFinset_card_of_nodup, List.length_map, bipCount_eq]
  have hd : (cs.map fun p => fin23 p.1).Pairwise (· ≠ ·) :=
    List.pairwise_map.mpr (hg.compsDisj.imp_of_mem fun hp hq h => hg.roots_ne hp hq h)
  exact hd.sublist ((List.filter_sublist).map _)

omit hg in
theorem card_V : (certL U Vm cs).V.card = popc Vm 23 := by
  rw [popc_eq, certL, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if Vm.testBit i = true then 1 else 0) 23

/-- **The rank of the pair graph**, when the checks pass. -/
theorem Good.rank : finrank ℚ (pairSpan (edgesU U)) = popc Vm 23 - bipCount U cs := by
  rw [pair_rank (cert_ok hg), card_V, hg.card_bipRoots]

end Dim

/-! ### The masks of a pair mask -/

theorem testBit_upper (c M u w : ℕ) : (upper c M u).testBit w = true ↔
    u ≠ c ∧ u < w ∧ w < 23 ∧ w ≠ c ∧ M.testBit (23 * u + w) = true := by
  unfold upper
  rw [beq_cond]
  by_cases hu : u = c
  · simp [hu]
  · simp only [hu, ite_false]
    simp only [show ∀ a b, Nat.xor a b = a ^^^ b from fun _ _ => rfl, Nat.testBit_xor, tb_land,
      testBit_bit, show ∀ a b, Nat.shiftLeft a b = a <<< b from fun _ _ => rfl,
      show ∀ a b, Nat.shiftRight a b = a >>> b from fun _ _ => rfl,
      show ∀ a b, Nat.mod a b = a % b from fun _ _ => rfl, Nat.mul_eq, Nat.add_eq,
      show (8388608 : ℕ) = 2 ^ 23 by norm_num, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_mod_two_pow]
    by_cases hw : u + 1 ≤ w
    · rw [Nat.add_sub_cancel' hw]
      by_cases hwc : c = w
      · subst hwc; simp [hu]
      · simp [hu, hwc, Ne.symm hwc, hw, show u < w by omega]
    · simp [hw, show ¬ u < w by omega]

theorem getD_ups (c M : ℕ) : ∀ (n u i : ℕ),
    (ups c M u n).getD i 0 = if i < n then upper c M (u + i) else 0
  | 0, _, _ => by simp [ups]
  | n + 1, u, 0 => by simp [ups]
  | n + 1, u, i + 1 => by
    rw [ups, List.getD_cons_succ, getD_ups c M n, Nat.add_eq]
    simp only [Nat.add_lt_add_iff_right]
    rw [show u + 1 + i = u + (i + 1) by omega]

theorem okC_good {c M : ℕ} (h : okC c M = true) : Good (upsOf c M) (ptsOf c M) (comps c M) := by
  rw [okC, Bool.and_eq_true, Bool.and_eq_true, beq_iff] at h
  obtain ⟨⟨hd, hc⟩, hk⟩ := h
  refine ⟨fun u w hw => ?_, fun v => testBit_touched _ v, (disjL_spec 0 _ hd).2,
    fun v => by rw [hc], compsOk_spec _ _ hk⟩
  rw [upsOf, getD_ups] at hw
  split_ifs at hw with hu
  · exact ⟨hu, ((testBit_upper c M _ w).mp (by simpa using hw)).2.2.1⟩
  · simp at hw

/-- **The rank of a pair mask's graph** is `dimC`, when `okC` passes. -/
theorem dim_eq {c M : ℕ} (h : okC c M = true) :
    finrank ℚ (pairSpan (edgesU (upsOf c M))) = dimC c M := by
  rw [(okC_good h).rank, dimC, Nat.sub_eq]

end IntegerMultBounds.MathlibTM2.M8.Frames
