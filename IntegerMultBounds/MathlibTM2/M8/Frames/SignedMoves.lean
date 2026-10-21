module

public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFrames
public import IntegerMultBounds.MathlibTM2.M8.Global.FrameMoments

/-! Exact move moments for mixed positive-span and root-complement chains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.Signed

def rankSteps (bank : Nat → RootBank.Record) : List Frame → List Nat
  | [] => []
  | [_] => []
  | a :: b :: frames =>
      let rank := b.rankValue bank - a.rankValue bank
      if rank = 0 then rankSteps bank (b :: frames)
      else rank :: rankSteps bank (b :: frames)

noncomputable section

theorem chainMoment_rankSteps {M : Type} [AddCommMonoid M] (φ : Nat → M)
    (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) :
    ∀ frames, chainCheck bank size frames = true →
      Global.chainMoment φ (frames.map (Frame.eval bank)) =
        ((rankSteps bank frames).map φ).sum
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: frames, h => by
    have ha := chainCheck_valid bank size (a :: b :: frames) h a (by simp)
    have hb := chainCheck_valid bank size (a :: b :: frames) h b (by simp)
    have hedge := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have htail := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
    have hab := Frame.nested bank size hbank ha hb hedge
    have hr := Exchange.rank_sub_add (a.eval bank) (b.eval bank)
      (a.idem bank size hbank ha) (b.idem bank size hbank hb) hab.2 hab.1
    rw [a.rank_eval bank size hbank ha, b.rank_eval bank size hbank hb] at hr
    have hd : (b.eval bank - a.eval bank).rank = b.rankValue bank - a.rankValue bank := by
      omega
    have he : a.eval bank = b.eval bank ↔ b.rankValue bank - a.rankValue bank = 0 := by
      constructor
      · intro he
        rw [← he, sub_self, Matrix.rank_zero] at hd
        exact hd.symm
      · intro he
        exact (sub_eq_zero.mp (Global.eq_zero_of_rank_eq_zero (hd.trans he))).symm
    rw [List.map_cons, List.map_cons, Global.chainMoment_cons_cons,
      Global.stepMoment_eq, Global.rank_sub_comm, hd]
    rw [show Global.chainMoment φ (b.eval bank :: frames.map (Frame.eval bank)) =
      ((rankSteps bank (b :: frames)).map φ).sum from
        chainMoment_rankSteps φ bank size hbank (b :: frames) htail]
    simp only [rankSteps]
    by_cases hz : b.rankValue bank - a.rankValue bank = 0
    · rw [ite_eq_left (he.mpr hz), ite_eq_left hz, zero_add]
    · rw [ite_eq_right (fun h => hz (he.mp h)), ite_eq_right hz,
        List.map_cons, List.sum_cons]

/-- A checked batch certifies the actual projector cost on each wire. -/
theorem chainsCheck_moment {M : Type} [AddCommMonoid M] (φ : Nat → M)
    (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true)
    (chains : List (List Frame)) (h : chainsCheck bank size chains = true)
    (frames : List Frame) (hmem : frames ∈ chains) :
    Global.chainMoment φ (frames.map (Frame.eval bank)) =
      ((rankSteps bank frames).map φ).sum :=
  chainMoment_rankSteps φ bank size hbank frames (List.all_eq_true.mp h frames hmem)

end
end IntegerMultBounds.MathlibTM2.M8.Frames.Signed
