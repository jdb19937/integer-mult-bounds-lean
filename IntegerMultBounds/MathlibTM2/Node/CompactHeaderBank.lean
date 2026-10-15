module

public import IntegerMultBounds.MathlibTM2.Node.CompactHeaderBuild

/-! Placement of runtime-built original descriptors in the native bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section
variable {T N A : ℕ} {s : Shape}

lemma compactRawHeader_injective (hN : 66 ≤ N) :
    Function.Injective (compactRawHeader hN) := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin N => z.val) h)

/-- A header fill matches every native header and empty work stack. Raw data is
left empty for the codec to load, so the equality excludes tape 65. -/
theorem compactHeaderFill_native (d : Inputs s) (hN : 66 ≤ N)
    (ι : Fin N → Fin T) (hι : Function.Injective ι)
    (src : Fin 13 → Fin T) (R : Fin T → List (Fin (A+4)))
    (hvalues : ∀ i,(R (src i)).length =
      ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
    (hempty : ∀ j,R (ι j)=[]) (j : Fin N) (hj : j.val≠65) :
    compactHeaderFill (fun i => ι (compactRawHeader hN i))
      (fun i => compactHeaderWord A (R (src i)).length) 13 R (ι j) =
      compactRawWords d (fun _ => false) j := by
  by_cases hh : j.val<13
  · let i : Fin 13 := ⟨j.val,hh⟩
    have hi : compactRawHeader hN i=j := Fin.ext rfl
    rw [←hi]
    have hd : Function.Injective (fun i => ι (compactRawHeader hN i)) :=
      hι.comp (compactRawHeader_injective hN)
    rw [compactHeaderFill_at (fun i => ι (compactRawHeader hN i)) hd]
    rw [ite_eq_left i.isLt,hvalues]
    simp [compactHeaderWord,compactRawWords,compactStageWords,compactRawHeader]
  · have hout : ∀ i,ι (compactRawHeader hN i)≠ι j := by
      intro i he
      have hv := congrArg Fin.val (hι he)
      exact hh (hv ▸ i.isLt)
    rw [compactHeaderFill_out _ _ _ _ _ hout,hempty]
    simp [compactRawWords,compactStageWords,hh,hj]

end
end IntegerMultBounds.MathlibTM2.Node
