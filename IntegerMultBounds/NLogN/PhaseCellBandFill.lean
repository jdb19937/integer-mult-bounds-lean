module

public import IntegerMultBounds.NLogN.SchurFill
import IntegerMultBounds.NLogN.PhaseCellBoundarySupport
public import IntegerMultBounds.NLogN.PhaseCellMatrix
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! Fill of the banded factorization of the actual rounded matrix. In
physical order, every entry of the elimination factors lies within the band
of the selected width or in the `w`-wide cyclic border, so every non-border
row of either factor has at most `3w+1` entries. A line solve with stored
factors therefore touches `O(s w)` entries. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset SchurDominance
variable (s t : ℕ) [NeZero s]

/-- Band-or-border support relation in physical order. -/
def BandRel (w : ℕ) (i j : ZMod s) : Prop :=
  (i.val ≤ j.val + w ∧ j.val ≤ i.val + w) ∨ s ≤ i.val + w ∨ s ≤ j.val + w

instance (w : ℕ) : DecidableRel (BandRel s w) := fun i j => by
  unfold BandRel
  infer_instance

omit [NeZero s] in
theorem bandRel_closed (w : ℕ) : FillClosed (fun x : ZMod s => x.val) (BandRel s w) := by
  intro k i j hki hkj hik hkj'
  simp only at hki hkj
  unfold BandRel at *
  omega

theorem matrix_bandRel (p u : ℕ) (i j : ZMod s) (h : realMatrix s t p u i j≠0) :
    BandRel s (PhaseCellBand.width p u) i j := by
  obtain ⟨m, hm, hij⟩ := matrix_support s t p u i j h
  have hm' := abs_le.mp hm
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hv : (j.val : ℤ)=((i.val : ℤ)+m)%s := by
    have h2 : j=(((i.val : ℤ)+m : ℤ) : ZMod s) := by
      rw [←hij, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [h2, ZMod.val_intCast]
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  unfold BandRel
  by_cases hb : s ≤ i.val + PhaseCellBand.width p u
  · exact Or.inr (Or.inl hb)
  rcases lt_or_ge ((i.val : ℤ)+m) 0 with hneg | hnn
  · have : ((i.val : ℤ)+m)%s=(i.val : ℤ)+m+s := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this] at hv
    omega
  · rcases lt_or_ge ((i.val : ℤ)+m) s with hlt | hge
    · rw [Int.emod_eq_of_lt hnn hlt] at hv
      omega
    · omega

/-- Every factor entry of the actual rounded matrix lies in the band or border. -/
theorem factor_bandRel (p u : ℕ) (ks : List (ZMod s)) (hks : univ⊆ks.toFinset)
    (hsort : ks.Pairwise (fun a b => a.val<b.val)) :
    (∀ i k, luL (realMatrix s t p u) univ ks i k≠0 → i=k ∨ BandRel s (PhaseCellBand.width p u) i k) ∧
      (∀ k j, luU (realMatrix s t p u) univ ks k j≠0 → BandRel s (PhaseCellBand.width p u) k j) :=
  fill_support _ _ (bandRel_closed s _) ks _ univ hks hsort
    (fun i _ j _ h => matrix_bandRel s t p u i j h)

/-- A non-border row meets at most `3w+1` band-or-border columns. -/
theorem bandRel_row_card (w : ℕ) (i : ZMod s) (hi : i.val+w<s) :
    (univ.filter (fun k => BandRel s w i k)).card≤3*w+1 := by
  classical
  have hinj : Set.InjOn (fun k : ZMod s => k.val) ↑(univ.filter (fun k => BandRel s w i k)) :=
    fun a _ b _ h => ZMod.val_injective s h
  calc (univ.filter (fun k => BandRel s w i k)).card
      =((univ.filter (fun k => BandRel s w i k)).image (fun k : ZMod s => k.val)).card :=
        (card_image_of_injOn hinj).symm
    _≤(Icc (i.val-w) (i.val+w)∪Ico (s-w) s).card := by
        apply card_le_card
        intro x hx
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
        have hkR := (mem_filter.mp hk).2
        have hks := ZMod.val_lt k
        unfold BandRel at hkR
        simp only [mem_union, mem_Icc, mem_Ico]
        omega
    _≤(Icc (i.val-w) (i.val+w)).card+(Ico (s-w) s).card := card_union_le _ _
    _≤3*w+1 := by
        rw [Nat.card_Icc, Nat.card_Ico]
        omega

end IntegerMultBounds.NLogN.PhaseCellMatrix
