module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
public import IntegerMultBounds.MathlibTM2.M8.Frames.RootMoveCheck
public import IntegerMultBounds.MathlibTM2.M8.Global.FrameMoments

/-! Exact child ranks and moments of certified computed-frame chains.
The integer rank table is linked to the actual rational projector differences,
so a histogram of these steps concerns the actual frame moves. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.RootBank

open Matrix

noncomputable section

theorem Record.basis_length_le (entry : Record) (h : entry.check = true) :
    entry.basis.length ≤ 23 := by
  have hu := (Record.check_spec h).2.1
  rw [← rootMatZ_cast] at hu
  simpa only [Fintype.card_fin] using card_le_of_isUnit (Bz := rootMatZ entry.basis) hu

theorem Record.difference_rank {a b : Record} (ha : a.check = true) (hb : b.check = true)
    (hab : Nested a.frame b.frame) :
    (b.frame - a.frame).rank = a.basis.length - b.basis.length := by
  have hr := Exchange.rank_sub_add a.frame b.frame (a.idem ha) (b.idem hb) hab.2 hab.1
  rw [a.rank ha, b.rank hb] at hr
  have hla := a.basis_length_le ha
  have hlb := b.basis_length_le hb
  omega

theorem Record.frame_eq_iff_length {a b : Record} (ha : a.check = true) (hb : b.check = true)
    (hab : Nested a.frame b.frame) : a.frame = b.frame ↔ a.basis.length = b.basis.length := by
  constructor
  · intro h
    have hr := congrArg Matrix.rank h
    rw [a.rank ha, b.rank hb] at hr
    have hla := a.basis_length_le ha
    have hlb := b.basis_length_le hb
    omega
  · intro h
    have hr := Record.difference_rank ha hb hab
    rw [h, Nat.sub_self] at hr
    exact (sub_eq_zero.mp (Global.eq_zero_of_rank_eq_zero hr)).symm

theorem Record.stepMoment {M : Type} [AddCommMonoid M] (φ : Nat → M)
    {a b : Record} (ha : a.check = true) (hb : b.check = true) (hab : Nested a.frame b.frame) :
    Global.stepMoment φ a.frame b.frame =
      if a.basis.length = b.basis.length then 0 else φ (a.basis.length - b.basis.length) := by
  rw [Global.stepMoment_eq, Global.rank_sub_comm, Record.difference_rank ha hb hab]
  by_cases h : a.basis.length = b.basis.length
  · rw [ite_eq_left h, ite_eq_left ((Record.frame_eq_iff_length ha hb hab).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun he => h ((Record.frame_eq_iff_length ha hb hab).mp he))]

theorem chainMoment_rankSteps {M : Type} [AddCommMonoid M] (φ : Nat → M)
    (bank : Nat → Record) (size : Nat) (hbank : ∀ i < size, (bank i).check = true) :
    ∀ ids, chainCheck bank size ids = true →
      Global.chainMoment φ (ids.map fun i => (bank i).frame) =
        ((rankSteps bank ids).map φ).sum
  | [], _ => rfl
  | [_], _ => rfl
  | i :: j :: ids, h => by
    have hi := chainCheck_bounds bank size (i :: j :: ids) h i (by simp)
    have hj := chainCheck_bounds bank size (i :: j :: ids) h j (by simp)
    have hedge := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have htail := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
    have hab := Record.nested (hbank i hi) hedge
    have hrank := Exchange.rank_sub_add (bank i).frame (bank j).frame
      ((bank i).idem (hbank i hi)) ((bank j).idem (hbank j hj)) hab.2 hab.1
    rw [(bank i).rank (hbank i hi), (bank j).rank (hbank j hj)] at hrank
    have hla := (bank i).basis_length_le (hbank i hi)
    have hlb := (bank j).basis_length_le (hbank j hj)
    have hle : (bank j).basis.length ≤ (bank i).basis.length := by omega
    rw [List.map_cons, List.map_cons, Global.chainMoment_cons_cons,
      Record.stepMoment φ (hbank i hi) (hbank j hj) hab]
    change (if (bank i).basis.length = (bank j).basis.length then 0
      else φ ((bank i).basis.length - (bank j).basis.length)) +
      Global.chainMoment φ ((j :: ids).map fun k => (bank k).frame) = _
    rw [chainMoment_rankSteps φ bank size hbank (j :: ids) htail]
    simp only [rankSteps]
    by_cases he : (bank i).basis.length = (bank j).basis.length
    · rw [ite_eq_left he, he, Nat.sub_self, ite_eq_left rfl, zero_add]
    · rw [ite_eq_right he, ite_eq_right (by omega), List.map_cons, List.sum_cons]

end

end IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
