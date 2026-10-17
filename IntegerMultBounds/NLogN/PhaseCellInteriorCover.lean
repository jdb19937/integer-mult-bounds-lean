module

public import IntegerMultBounds.NLogN.PhaseCellBoundarySupport
public import IntegerMultBounds.NLogN.PhaseCellIntervals

/-! Interior vertices of one phase cell form a consecutive interval inside the
array. Every interior vertex therefore lies in an interval `lo + [0, L)` that
consists of interior vertices of one cell and contains every interior vertex
of that cell, as the exact and rounded cell solves require. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset
variable (s t : ℕ) [NeZero s]

theorem interior_convex (hst : s<t) (w : ℕ) (v₁ v v₂ : ZMod s)
    (h₁ : Interior s t w v₁) (h₂ : Interior s t w v₂) (hc : cell s t v₁=cell s t v₂)
    (hlo : v₁.val ≤ v.val) (hhi : v.val ≤ v₂.val) :
    Interior s t w v ∧ cell s t v=cell s t v₁ := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  obtain ⟨a₁, b₁, p₁⟩ := h₁
  obtain ⟨a₂, b₂, p₂⟩ := h₂
  have hmono := PhaseCellIntervals.phase_monotone hs hst.le
  unfold cell at hc ⊢
  -- Both endpoints' bands sit in the cell's phase.
  have e₁ : PhaseCell.phase s t (v₁.val : ℤ)=PhaseCell.phase s t ((v₁.val : ℤ)-w) :=
    PhaseCellIntervals.phase_eq_of_between hs hst.le (by omega) (by omega) p₁
  have e₂ : PhaseCell.phase s t ((v₂.val : ℤ)+w)=PhaseCell.phase s t (v₂.val : ℤ) := by
    rw [←p₂]
    exact (PhaseCellIntervals.phase_eq_of_between hs hst.le (by omega) (by omega) p₂).symm
  have hlow : PhaseCell.phase s t ((v₁.val : ℤ)-w)≤PhaseCell.phase s t ((v.val : ℤ)-w) :=
    hmono (by omega)
  have hmid : PhaseCell.phase s t ((v.val : ℤ)-w)≤PhaseCell.phase s t ((v.val : ℤ)+w) :=
    hmono (by omega)
  have hup : PhaseCell.phase s t ((v.val : ℤ)+w)≤PhaseCell.phase s t ((v₂.val : ℤ)+w) :=
    hmono (by omega)
  have hv₁ : PhaseCell.phase s t ((v₁.val : ℤ)-w)≤PhaseCell.phase s t (v.val : ℤ) :=
    hmono (by omega)
  have hv₂ : PhaseCell.phase s t (v.val : ℤ)≤PhaseCell.phase s t (v₂.val : ℤ) :=
    hmono (by omega)
  refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩

/-- Every interior vertex lies in a full interior interval of its cell. -/
theorem interior_cover (hst : s<t) (w : ℕ) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t w j) (i : ZMod s) (hi : i∈I) :
    ∃ lo : ZMod s, ∃ L : ℕ, 0<L ∧ lo.val+L≤s ∧
      (∀ k<L, Interior s t w (lo+(k : ZMod s)) ∧ lo+(k : ZMod s)∈I) ∧
      (∀ k<L, cell s t (lo+(k : ZMod s))=cell s t lo) ∧
      (∀ j∈I, cell s t j=cell s t lo → ∃ k<L, lo+(k : ZMod s)=j) ∧
      ∃ a<L, lo+(a : ZMod s)=i := by
  classical
  set T := I.filter (fun j => cell s t j=cell s t i)
  have hiT : i∈T := mem_filter.mpr ⟨hi, rfl⟩
  obtain ⟨lo, hloT, hlo⟩ := exists_min_image T ZMod.val ⟨i, hiT⟩
  obtain ⟨hh, hhT, hhh⟩ := exists_max_image T ZMod.val ⟨i, hiT⟩
  have hloI := (mem_filter.mp hloT).1
  have hhI := (mem_filter.mp hhT).1
  have hlocell := (mem_filter.mp hloT).2
  have hhcell := (mem_filter.mp hhT).2
  have hloint := (hI lo).mp hloI
  have hhint := (hI hh).mp hhI
  have hhs : hh.val<s := ZMod.val_lt hh
  have hlh : lo.val≤hh.val := hlo hh hhT
  -- Offsets from `lo` stay inside the array.
  have hval (k : ℕ) (hk : lo.val+k≤hh.val) : (lo+(k : ZMod s)).val=lo.val+k := by
    have hks : (k : ZMod s).val=k := ZMod.val_cast_of_lt (by omega)
    rw [ZMod.val_add_of_lt (by omega), hks]
  have hcover (j : ZMod s) (hj : lo.val ≤ j.val) (hj' : j.val ≤ hh.val) :
      Interior s t w j ∧ cell s t j=cell s t lo :=
    interior_convex s t hst w lo j hh hloint hhint (hlocell.trans hhcell.symm) hj hj'
  have hrepr (j : ZMod s) (hj : lo.val ≤ j.val) (hj' : j.val ≤ hh.val) :
      lo+((j.val-lo.val : ℕ) : ZMod s)=j := by
    apply ZMod.val_injective
    rw [hval _ (by omega)]
    omega
  refine ⟨lo, hh.val-lo.val+1, by omega, by omega, fun k hk => ?_, fun k hk => ?_,
    fun j hj hjc => ?_, ⟨i.val-lo.val, ?_, hrepr i (hlo i hiT) (hhh i hiT)⟩⟩
  · have hv := hval k (by omega)
    have h := hcover (lo+(k : ZMod s)) (by omega) (by omega)
    exact ⟨h.1, (hI _).mpr h.1⟩
  · have hv := hval k (by omega)
    exact (hcover (lo+(k : ZMod s)) (by omega) (by omega)).2
  · have hjT : j∈T := mem_filter.mpr ⟨hj, hjc.trans hlocell⟩
    exact ⟨j.val-lo.val, by have := hlo j hjT; have := hhh j hjT; omega,
      hrepr j (hlo j hjT) (hhh j hjT)⟩
  · have := hhh i hiT
    have := hlo i hiT
    omega

end IntegerMultBounds.NLogN.PhaseCellMatrix
