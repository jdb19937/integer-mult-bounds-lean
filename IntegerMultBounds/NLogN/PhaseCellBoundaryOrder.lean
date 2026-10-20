module

public import IntegerMultBounds.NLogN.PhaseCellBoundarySupport
public import IntegerMultBounds.NLogN.PhaseCellBandSolve
public import IntegerMultBounds.NLogN.SchurFill
import IntegerMultBounds.NLogN.PhaseCellIntervals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! # The boundary order of the phase-cell solve

The boundary `B = univ \ I` of the phase-cell solve is the complement of the interior vertices
(`Interior`, band inside the array and inside one phase cell). After the interior is eliminated
(`boundary_support`), every remaining coupling is a band entry or joins one phase cell.

* **Count.** A vertex outside the interior lies within `w` of an array end or within `w` of a
  cell start, and the phase rises by one at each of the at most `t - s` cell starts
  (`cellStarts_card`), so `|B| ≤ 2w (t - s + 1)` (`boundary_card`).
* **Order.** Rank the boundary vertices in physical order (`bRank`, `bOrder`). A band entry
  joins ranks at distance at most `w`, or wraps around the line through the last `w` ranks; a
  same-cell entry joins ranks at distance at most `4w`, since only the first and last `w`
  vertices of a cell and the `w` vertices at each array end are boundary. So the boundary system
  lies in the bordered band `RankRel B (4w)` (`schur_rankRel`), which is closed under fill in
  rank order (`rankRel_closed`).
* **Factors.** Elimination in rank order keeps every exact or rounded LU factor entry of the
  boundary system in that relation (`boundary_factors`, `boundary_factors_r`), and a rank row
  outside the last `4w` ranks meets at most `12w + 1` boundary vertices (`rankRel_row_card`).
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset SchurDominance
variable (s t : ℕ) [NeZero s]

/-! ### The phase at the ends of the line -/

omit [NeZero s] in
theorem phase_zero : PhaseCell.phase s t 0=0 := by
  rw [PhaseCellIntervals.phase_eq_nearest_gap]
  unfold nearest
  norm_num [Int.floor_eq_zero_iff]

/-- The phase of the last index is at most `t - s`. -/
theorem phase_last_le (hst : s<t) : PhaseCell.phase s t ((s : ℤ)-1)≤(t : ℤ)-s := by
  have hs : (0 : ℝ)<s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hs0 : (s : ℝ)≠0 := ne_of_gt hs
  have hst' : (s : ℝ)<t := by exact_mod_cast hst
  rw [PhaseCellIntervals.phase_eq_nearest_gap]
  unfold nearest
  have hlt : ((t : ℝ)/s-1)*(((s : ℤ)-1 : ℤ) : ℝ)+1/2<(((t : ℤ)-s+1 : ℤ) : ℝ) := by
    push_cast
    have e : ((t : ℝ)/s-1)*((s : ℝ)-1)=(t : ℝ)-t/s-s+1 := by field_simp; ring
    rw [e]
    have : (1 : ℝ)/2<(t : ℝ)/s := by
      rw [lt_div_iff₀ hs]; linarith
    linarith
  have := Int.floor_lt.mpr hlt
  omega

omit [NeZero s] in
/-- With no phase change on `(a, b]` the phase is constant there. -/
theorem phase_const {a b : ℤ} (hab : a≤b)
    (h : ∀ j, a<j → j≤b → PhaseCell.phase s t (j-1)=PhaseCell.phase s t j) :
    PhaseCell.phase s t a=PhaseCell.phase s t b := by
  induction b, hab using Int.leInduction with
  | base => rfl
  | succ b hab ih =>
    rw [ih (fun j hj hjb => h j hj (by omega))]
    have := h (b+1) (by omega) le_rfl
    rwa [show b+1-1=b by ring] at this

/-! ### Cell starts and the boundary count -/

/-- The cell starts: the indices `j ∈ [1, s)` where the phase changes. -/
noncomputable def cellStarts : Finset ℕ :=
  (Finset.Ico 1 s).filter fun j : ℕ => PhaseCell.phase s t ((j : ℤ)-1)≠PhaseCell.phase s t j

/-- The phase rises by one at every cell start. -/
theorem cellStarts_card (hst : s<t) : (cellStarts s t).card≤t-s := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hmono := PhaseCellIntervals.phase_monotone hs hst.le
  have key : ∀ m : ℕ, 1≤m →
      ((((Finset.Ico 1 m).filter fun j : ℕ =>
        PhaseCell.phase s t ((j : ℤ)-1)≠PhaseCell.phase s t j).card : ℕ) : ℤ)≤
        PhaseCell.phase s t ((m : ℤ)-1)-PhaseCell.phase s t 0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hI : Finset.Ico 1 (m+1)=insert m (Finset.Ico 1 m) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hI, Finset.filter_insert]
      have hle : PhaseCell.phase s t ((m : ℤ)-1)≤PhaseCell.phase s t m := hmono (by omega)
      have e : (((m+1 : ℕ) : ℤ)-1)=(m : ℤ) := by push_cast; ring
      rw [e]
      split_ifs with hP
      · rw [Finset.card_insert_of_notMem (by simp)]
        push_cast
        have : PhaseCell.phase s t ((m : ℤ)-1)<PhaseCell.phase s t m := lt_of_le_of_ne hle hP
        omega
      · omega
  have h := key s hs
  have h0 := phase_zero s t
  have hl := phase_last_le s t hst
  unfold cellStarts
  omega

omit [NeZero s] in
/-- A vertex outside the interior lies near an array end or near a cell start. -/
theorem not_interior_near (w : ℕ) (k : ZMod s) (hk : ¬Interior s t w k) :
    k.val<w ∨ s≤k.val+w ∨ ∃ j∈cellStarts s t, j≤k.val+w ∧ k.val<j+w := by
  by_cases h1 : w≤k.val
  · by_cases h2 : k.val+w<s
    · right; right
      by_contra hc
      push Not at hc
      apply hk
      refine ⟨h1, h2, phase_const s t (by omega) fun j hj hjb => ?_⟩
      by_contra hne
      have hj0 : 0≤j := by omega
      have hmem : j.toNat∈cellStarts s t := by
        unfold cellStarts
        rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rwa [Int.toNat_of_nonneg hj0]
      have := hc j.toNat hmem (by omega)
      omega
    · right; left; omega
  · left; omega

/-- **The boundary count.** The complement of the interior has at most `2w (t - s + 1)`
vertices. -/
theorem boundary_card (hst : s<t) (w : ℕ) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t w j) : (univ\I).card≤2*w*(t-s+1) := by
  have hsub : (univ\I).image ZMod.val⊆(Finset.range w∪Finset.Ico (s-w) s)∪
      (cellStarts s t).biUnion fun j => Finset.Ico (j-w) (j+w) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hkI : ¬Interior s t w k := fun h => (Finset.mem_sdiff.mp hk).2 ((hI k).mpr h)
    have hlt := ZMod.val_lt k
    rcases not_interior_near s t w k hkI with h | h | ⟨j, hj, hj1, hj2⟩
    · simp [h]
    · simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩)
      rw [Finset.mem_Ico]; omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (ZMod.val_injective s)] at hcard
  have h1 := Finset.card_union_le (Finset.range w∪Finset.Ico (s-w) s)
    ((cellStarts s t).biUnion fun j => Finset.Ico (j-w) (j+w))
  have h2 := Finset.card_union_le (Finset.range w) (Finset.Ico (s-w) s)
  have h3 : ((cellStarts s t).biUnion fun j => Finset.Ico (j-w) (j+w)).card≤
      (cellStarts s t).card*(2*w) := by
    refine (Finset.card_biUnion_le).trans ?_
    rw [← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
    rw [Nat.card_Ico]; omega
  have h4 := cellStarts_card s t hst
  have h5 : (cellStarts s t).card*(2*w)≤(t-s)*(2*w) := Nat.mul_le_mul_right _ h4
  simp only [Finset.card_range, Nat.card_Ico] at h2
  have e : 2*w*(t-s+1)=(t-s)*(2*w)+2*w := by ring
  omega

/-! ### Ranks in physical order -/

/-- The rank of `i` among the vertices of `B` in physical order. -/
def bRank (B : Finset (ZMod s)) (x : ZMod s) : ℕ := (B.filter (fun k : ZMod s => ZMod.val k<ZMod.val x)).card

omit [NeZero s] in
variable {s} in
theorem bRank_lt {B : Finset (ZMod s)} {i : ZMod s} (hi : i∈B) : bRank s B i<B.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, hi, lt_irrefl i.val⟩)

omit [NeZero s] in
variable {s} in
theorem bRank_strictMono {B : Finset (ZMod s)} {i j : ZMod s} (hi : i∈B) (hij : i.val<j.val) :
    bRank s B i<bRank s B j := by
  refine Finset.card_lt_card (Finset.ssubset_def.mpr ⟨fun k hk => ?_, fun h => ?_⟩)
  · rw [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, hk.2.trans hij⟩
  · have := (Finset.mem_filter.mp (h (Finset.mem_filter.mpr ⟨hi, hij⟩))).2
    exact lt_irrefl i.val this

omit [NeZero s] in
variable {s} in
/-- Ranks count the vertices of `B` in a physical interval. -/
theorem bRank_sub {B : Finset (ZMod s)} {i j : ZMod s} (hij : i.val≤j.val) :
    bRank s B j=bRank s B i+(B.filter fun k => i.val≤k.val ∧ k.val<j.val).card := by
  unfold bRank
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_union]
    by_cases hkB : k∈B
    · simp only [hkB, true_and]; omega
    · simp [hkB]
  · rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_filter] at hk hk'
    omega

omit [NeZero s] in
variable {s} in
theorem bRank_top {B : Finset (ZMod s)} (i : ZMod s) :
    B.card=bRank s B i+(B.filter fun k => i.val≤k.val).card := by
  unfold bRank
  rw [← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · congr 1
    ext k
    simp only [Finset.mem_filter]
    constructor
    · intro hk; exact ⟨hk, by omega⟩
    · intro hk; exact hk.1
  · rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_filter] at hk hk'
    omega

variable {s} in
/-- A physical interval holds at most its length of vertices. -/
theorem card_filter_interval (B : Finset (ZMod s)) (a c : ℕ) :
    (B.filter fun k => a≤k.val ∧ k.val<c).card≤c-a := by
  have h : (B.filter fun k => a≤k.val ∧ k.val<c).image ZMod.val⊆Finset.Ico a c := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_Ico]; exact hk.2
  have := Finset.card_le_card h
  rwa [Finset.card_image_of_injective _ (ZMod.val_injective s), Nat.card_Ico] at this

/-! ### The bordered rank band -/

/-- The bordered band in rank order: ranks within `D`, or a vertex among the last `D` ranks. -/
def RankRel (B : Finset (ZMod s)) (D : ℕ) (i j : ZMod s) : Prop :=
  (bRank s B i≤bRank s B j+D ∧ bRank s B j≤bRank s B i+D) ∨ B.card≤bRank s B i+D ∨
    B.card≤bRank s B j+D

instance (B : Finset (ZMod s)) (D : ℕ) (i j : ZMod s) : Decidable (RankRel s B D i j) := by
  unfold RankRel; infer_instance

omit [NeZero s] in
theorem rankRel_closed (B : Finset (ZMod s)) (D : ℕ) : FillClosed (bRank s B) (RankRel s B D) := by
  intro k i j hki hkj hik hkj'
  unfold RankRel at *
  omega

omit [NeZero s] in
theorem rankRel_mono (B : Finset (ZMod s)) {D D' : ℕ} (hD : D≤D') {i j : ZMod s}
    (h : RankRel s B D i j) : RankRel s B D' i j := by
  unfold RankRel at *
  omega

/-- A band entry joins ranks at distance at most `w`, or wraps through the last `w` ranks. -/
theorem band_rankRel (B : Finset (ZMod s)) (w : ℕ) (i j : ZMod s) (m : ℤ) (hm : |m|≤w)
    (hij : i+(m : ZMod s)=j) : RankRel s B w i j := by
  by_cases hbig : s≤w
  · have hB : B.card≤s := by
      have := Finset.card_le_univ B
      rwa [ZMod.card] at this
    unfold RankRel; omega
  have hm' := abs_le.mp hm
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have hs : (0 : ℤ)<s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hv : (j.val : ℤ)=((i.val : ℤ)+m)%s := by
    have h2 : j=(((i.val : ℤ)+m : ℤ) : ZMod s) := by
      rw [←hij, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [h2, ZMod.val_intCast]
  have hcase : (j.val : ℤ)=(i.val : ℤ)+m ∨ (j.val : ℤ)=(i.val : ℤ)+m+s ∨
      (j.val : ℤ)=(i.val : ℤ)+m-s := by
    rcases lt_or_ge ((i.val : ℤ)+m) 0 with hneg | hnn
    · right; left
      rw [hv, Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    · rcases lt_or_ge ((i.val : ℤ)+m) s with hlt | hge
      · left; rw [hv, Int.emod_eq_of_lt hnn hlt]
      · right; right
        rw [hv, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold RankRel
  rcases hcase with h | h | h
  · rcases le_total i.val j.val with hle | hle
    · have e := bRank_sub (B := B) hle
      have hc := card_filter_interval B i.val j.val
      left; omega
    · have e := bRank_sub (B := B) hle
      have hc := card_filter_interval B j.val i.val
      left; omega
  · -- `i` near `0`, `j` near the end: `j` is among the last `w` ranks
    have e := bRank_top (B := B) j
    have hc : (B.filter fun k => j.val≤k.val).card≤s-j.val := by
      have := card_filter_interval B j.val s
      refine le_trans (Finset.card_le_card fun k hk => ?_) this
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2, ZMod.val_lt k⟩
    right; right; omega
  · -- `i` near the end
    have e := bRank_top (B := B) i
    have hc : (B.filter fun k => i.val≤k.val).card≤s-i.val := by
      have := card_filter_interval B i.val s
      refine le_trans (Finset.card_le_card fun k hk => ?_) this
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2, ZMod.val_lt k⟩
    right; left; omega

/-- Boundary vertices of one cell between `i` and `j` lie within `w` of `i`, of `j`, or of an
array end. -/
theorem same_cell_interval (hst : s<t) (w : ℕ) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t w j) (i j : ZMod s) (hc : cell s t i=cell s t j) :
    ((univ\I).filter fun k => i.val≤k.val ∧ k.val<j.val).card≤4*w := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hsub : ((univ\I).filter fun k => i.val≤k.val ∧ k.val<j.val).image ZMod.val⊆
      ((Finset.range w∪Finset.Ico (s-w) s)∪Finset.Ico i.val (i.val+w))∪
        Finset.Ico (j.val+1-w) j.val := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hk
    obtain ⟨hkB, hik, hkj⟩ := hk
    have hkI : ¬Interior s t w k := fun h => (Finset.mem_sdiff.mp hkB).2 ((hI k).mpr h)
    have hlt := ZMod.val_lt k
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    unfold cell at hc
    have hpk : PhaseCell.phase s t (k.val : ℤ)=PhaseCell.phase s t (i.val : ℤ) :=
      PhaseCellIntervals.phase_eq_of_between hs hst.le (by exact_mod_cast hik)
        (by exact_mod_cast hkj.le) hc
    by_cases h1 : w≤k.val
    · by_cases h2 : k.val+w<s
      · have hne : PhaseCell.phase s t (k.val-w : ℤ)≠PhaseCell.phase s t (k.val+w : ℤ) :=
          fun h => hkI ⟨h1, h2, h⟩
        by_cases hlo : (i.val : ℤ)≤(k.val : ℤ)-w
        · -- the right end of the band leaves the cell: `j < k + w`
          have hl : PhaseCell.phase s t ((k.val : ℤ)-w)=PhaseCell.phase s t (i.val : ℤ) :=
            PhaseCellIntervals.phase_eq_of_between hs hst.le hlo (by omega) hc
          by_cases hhi : (k.val : ℤ)+w≤(j.val : ℤ)
          · exfalso
            have hr : PhaseCell.phase s t ((k.val : ℤ)+w)=PhaseCell.phase s t (i.val : ℤ) :=
              PhaseCellIntervals.phase_eq_of_between hs hst.le (by omega) hhi hc
            exact hne (hl.trans hr.symm)
          · right; omega
        · left; right; omega
      · left; left; right; omega
    · left; left; left; omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (ZMod.val_injective s)] at hcard
  have h1 := Finset.card_union_le ((Finset.range w∪Finset.Ico (s-w) s)∪
    Finset.Ico i.val (i.val+w)) (Finset.Ico (j.val+1-w) j.val)
  have h2 := Finset.card_union_le (Finset.range w∪Finset.Ico (s-w) s) (Finset.Ico i.val (i.val+w))
  have h3 := Finset.card_union_le (Finset.range w) (Finset.Ico (s-w) s)
  simp only [Finset.card_range, Nat.card_Ico] at h1 h2 h3
  omega

/-- A same-cell entry joins boundary ranks at distance at most `4w`. -/
theorem cell_rankRel (hst : s<t) (w : ℕ) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t w j) (i j : ZMod s) (hc : cell s t i=cell s t j) :
    RankRel s (univ\I) (4*w) i j := by
  unfold RankRel
  left
  rcases le_total i.val j.val with hle | hle
  · have e := bRank_sub (B := univ\I) hle
    have hb := same_cell_interval s t hst w I hI i j hc
    omega
  · have e := bRank_sub (B := univ\I) hle
    have hb := same_cell_interval s t hst w I hI j i hc.symm
    omega

/-- **The boundary system in rank order.** After eliminating interior vertices, every coupling
between boundary vertices lies in the bordered rank band of half width `4w`. -/
theorem schur_rankRel (hst : s<t) (p u : ℕ) (ks : List (ZMod s))
    (hks : ∀ k∈ks, Interior s t (PhaseCellBand.width p u) k) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j) (i j : ZMod s)
    (h : (run (realMatrix s t p u) univ ks).1 i j≠0) :
    RankRel s (univ\I) (4*PhaseCellBand.width p u) i j := by
  rcases boundary_support s t hst p u ks hks univ i j h with ⟨m, hm, hij⟩ | hc
  · exact rankRel_mono s _ (by omega) (band_rankRel s _ _ i j m hm hij)
  · exact cell_rankRel s t hst _ I hI i j hc

/-! ### The boundary order and its factors -/

/-- The boundary order: the vertices of `B` in physical order. -/
def bOrder (B : Finset (ZMod s)) : List (ZMod s) := (physOrder s).filter fun k => k∈B

theorem bOrder_toFinset (B : Finset (ZMod s)) : (bOrder s B).toFinset=B := by
  ext x
  have := physOrder_toFinset s
  simp only [bOrder, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hx
    refine ⟨?_, hx⟩
    have hmem : x∈(physOrder s).toFinset := by rw [this]; exact Finset.mem_univ x
    exact List.mem_toFinset.mp hmem

omit [NeZero s] in
theorem bOrder_sorted (B : Finset (ZMod s)) :
    (bOrder s B).Pairwise fun a b => bRank s B a<bRank s B b := by
  unfold bOrder
  refine ((physOrder_sorted s).filter _).imp_of_mem fun {a b} ha _ hab => ?_
  have haB : a∈B := by
    have := (List.mem_filter.mp ha).2
    simpa using this
  exact bRank_strictMono haB hab

/-- **The boundary factors.** Eliminating the boundary vertices in physical order, every exact
LU factor entry of the boundary system lies in the bordered rank band of half width `4w`. -/
theorem boundary_factors (hst : s<t) (p u : ℕ) (ks : List (ZMod s))
    (hks : ∀ k∈ks, Interior s t (PhaseCellBand.width p u) k) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j) :
    (∀ i k, luL (run (realMatrix s t p u) univ ks).1 (univ\I) (bOrder s (univ\I)) i k≠0 →
      i=k ∨ RankRel s (univ\I) (4*PhaseCellBand.width p u) i k) ∧
    (∀ k j, luU (run (realMatrix s t p u) univ ks).1 (univ\I) (bOrder s (univ\I)) k j≠0 →
      RankRel s (univ\I) (4*PhaseCellBand.width p u) k j) :=
  fill_support _ _ (rankRel_closed s _ _) _ _ _ (by rw [bOrder_toFinset]) (bOrder_sorted s _)
    fun i _ j _ h => schur_rankRel s t hst p u ks hks I hI i j h

/-- The same for rounded elimination with any rounding that keeps zero. -/
theorem boundary_factors_r (hst : s<t) (p u : ℕ) (ks : List (ZMod s))
    (hks : ∀ k∈ks, Interior s t (PhaseCellBand.width p u) k) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j)
    (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (hrd0 : rd 0=0) (hmul0 : ∀ b, mul 0 b=0) :
    (∀ i k, luLr rd mul (run (realMatrix s t p u) univ ks).1 (univ\I) (bOrder s (univ\I)) i k≠0 →
      i=k ∨ (RankRel s (univ\I) (4*PhaseCellBand.width p u) i k ∧
        bRank s (univ\I) k<bRank s (univ\I) i)) ∧
    (∀ k j, luUr rd mul (run (realMatrix s t p u) univ ks).1 (univ\I) (bOrder s (univ\I)) k j≠0 →
      RankRel s (univ\I) (4*PhaseCellBand.width p u) k j ∧
        bRank s (univ\I) k≤bRank s (univ\I) j) :=
  fill_support_r rd mul hrd0 hmul0 _ _ (rankRel_closed s _ _) _ _ _ (by rw [bOrder_toFinset])
    (bOrder_sorted s _) fun i _ j _ h => schur_rankRel s t hst p u ks hks I hI i j h

/-- **Rows of the bordered band.** A vertex outside the last `D` ranks is related to at most
`3D + 1` vertices of `B`. -/
theorem rankRel_row_card (B : Finset (ZMod s)) (D : ℕ) (i : ZMod s)
    (hr : bRank s B i+D<B.card) : (B.filter fun k => RankRel s B D i k).card≤3*D+1 := by
  have hsub : (B.filter fun k => RankRel s B D i k).image (bRank s B)⊆
      Finset.Icc (bRank s B i-D) (bRank s B i+D)∪Finset.Ico (B.card-D) B.card := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hk
    have hlt := bRank_lt hk.1
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
    unfold RankRel at hk
    omega
  have hinj : Set.InjOn (bRank s B) (B.filter fun k => RankRel s B D i k : Set (ZMod s)) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).1
    have hb' := (Finset.mem_filter.mp hb).1
    by_contra hne
    have hv : a.val≠b.val := fun h => hne ((ZMod.val_injective s) h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact absurd hab (bRank_strictMono ha' h).ne
    · exact absurd hab (bRank_strictMono hb' h).ne'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  have h1 := Finset.card_union_le (Finset.Icc (bRank s B i-D) (bRank s B i+D))
    (Finset.Ico (B.card-D) B.card)
  simp only [Nat.card_Icc, Nat.card_Ico] at h1
  omega

end IntegerMultBounds.NLogN.PhaseCellMatrix
