module

public import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
public import IntegerMultBounds.Machine.RecursiveVolumeRoleBank
public import IntegerMultBounds.Machine.RecursiveMixedSchedule
public import IntegerMultBounds.Machine.SharedBankRawCompose
public import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
public import IntegerMultBounds.Machine.RecursiveViewFrameRoleBank
public import IntegerMultBounds.Machine.Shared50OrderedPieces
public import IntegerMultBounds.Machine.RecursiveScalarSchedule
public import IntegerMultBounds.Machine.RecursiveScalarIndex
public import IntegerMultBounds.Networks.AffineFieldBijective

/-! A recursive full H/D swap in the physically identical cross-field view is
exactly the original selected scalar interchange. No data transposition is used
to enter or leave the view, and every other World/I/O role is retained. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50RecursiveChildPermutation
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index)
open RecursiveCoordinateDigits (preDigits suffix)
variable {m b : ℕ} {v : Descriptor}
local instance : NeZero (modulus b) := ⟨ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

private theorem update_rank (x : Fin m → ZMod (modulus b)) (i : Fin m) (z : ZMod (modulus b)) :
    ((preDigits x i).val*prime^b+z.val)*prime^((m-1-i.val)*b)+(suffix x i).val =
      (FlatCoordinateLayout.rank (Function.update x i z)).val := by
  have h := RecursiveCoordinateDigits.one_update x i z
  simpa only [modulus,← pow_mul,Nat.mul_comm] using h.symm

/-- Same flat index on both sides of the paid child call. -/
theorem swapped_index (hw : v.width=m*b) (x : Address m b v) (i j : Fin m) :
    Fin.cast (RecursiveAffineViews.cross_volume prime b v i j hw)
      (RecursiveInterchangeScaling.index (Shared50RecursiveNodeTranspose.swapAddress
        (RecursiveScalarCoordinates.crossAddress x i j))) =
      index hw {x with h := Function.update x.h i (x.d j),d := Function.update x.d j (x.h i)} := by
  apply Fin.ext
  rw [Fin.val_cast,RecursiveInterchangeScaling.index_val,RecursiveScalarCoordinates.index_val]
  have he := RecursiveAffineViews.cross_index prime b v i j hw
    x.beforeRows.val x.row.val x.before.val (preDigits x.h i).val (x.d j).val (suffix x.h i).val
    x.middle.val (preDigits x.d j).val (x.h i).val (suffix x.d j).val x.after.val
  rw [update_rank x.h i (x.d j),update_rank x.d j (x.h i)] at he
  convert he using 1
  dsimp [Shared50RecursiveNodeTranspose.swapAddress,RecursiveScalarCoordinates.crossAddress]
  simp only [RecursiveAffineViews.cross,RecursiveInterchangeLayout.child]
  congr 1
  · change (preDigits x.h i).val+prime^(i.val*b)*x.before.val = _
    ring
  · exact FlatCoordinateLayout.finEquiv_symm_val _
  · change (preDigits x.d j).val+prime^(j.val*b)*(x.middle.val+v.between*(suffix x.h i).val) = _
    ring
  · exact FlatCoordinateLayout.finEquiv_symm_val _
  · change x.after.val+v.afterD*(suffix x.d j).val = _
    ring

/-- Cyclic packing changes the proof view, never the full H/D permutation. -/
theorem transpose_independent {c d : ℕ} {α : Type*} (hc : 0 < c) (hd : 0 < d)
    (hcv : c ∣ v.rows) (hdv : d ∣ v.rows) (x : Fin (volume prime v) → α) :
    Shared50RecursiveNodeRows.transpose hcv x = Shared50RecursiveNodeRows.transpose hdv x := by
  funext z
  obtain ⟨a,rfl⟩ := RecursiveScalarIndex.scaling_surjective (v := v) z
  have h1 := Shared50RecursiveNodeTranspose.transpose_all hc hcv x
    (Shared50RecursiveNodeTranspose.swapAddress a)
  have h2 := Shared50RecursiveNodeTranspose.transpose_all hd hdv x
    (Shared50RecursiveNodeTranspose.swapAddress a)
  have he : Shared50RecursiveNodeTranspose.swapAddress (Shared50RecursiveNodeTranspose.swapAddress a) = a := rfl
  rw [he] at h1 h2
  exact h1.trans h2.symm

/-- Literal reinterpretation under the same-volume selected-child descriptor. -/
def toChild {α : Type*} (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → α) :
    Fin (volume prime (RecursiveAffineViews.cross prime b v i j)) → α :=
  fun z => x (Fin.cast (RecursiveAffineViews.cross_volume prime b v i j hw) z)

/-- Return the child's full transpose to the same parent slots. -/
def array {α : Type*} (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → α) :
    Fin (volume prime v) → α := fun z =>
  Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j x)
    (Fin.cast (RecursiveAffineViews.cross_volume prime b v i j hw).symm z)

theorem array_entry {α : Type*} (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → α)
    (a : Address m b v) :
    array hw i j x (index hw {a with h := Function.update a.h i (a.d j),d := Function.update a.d j (a.h i)}) =
      x (index hw a) := by
  rw [← swapped_index hw a i j]
  unfold array
  rw [Fin.cast_cast,Fin.cast_eq_self]
  rw [Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)]
  change x (Fin.cast (RecursiveAffineViews.cross_volume prime b v i j hw)
    (RecursiveInterchangeScaling.index (RecursiveScalarCoordinates.crossAddress a i j))) = x (index hw a)
  exact congrArg x (RecursiveScalarCoordinates.view_index (.cross i j) hw a)

theorem toChild_word {α : Type*} (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → α) :
    List.ofFn (toChild hw i j x) = List.ofFn x :=
  (List.ofFn_congr (RecursiveAffineViews.cross_volume prime b v i j hw).symm x).symm

theorem return_word {α : Type*} (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → α) :
    List.ofFn (Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j x)) =
      List.ofFn (array hw i j x) :=
  List.ofFn_congr (RecursiveAffineViews.cross_volume prime b v i j hw) _

/-- View entry is literally the same physical source tape. -/
theorem toChild_source (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source (toChild hw i j x) = RecursiveShiftRoleBank.source x := by
  change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0 (List.ofFn (toChild hw i j x))) = _
  rw [toChild_word]
  rfl

/-- The returned child source is literally the updated selected parent tape. -/
theorem return_source (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source (Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j x)) =
      RecursiveShiftRoleBank.source (array hw i j x) := by
  change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
    (List.ofFn (Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j x)))) = _
  rw [return_word]
  rfl

/-- Binary values survive because child interchange is a literal permutation. -/
theorem array_encoded (hw : v.width=m*b) (i j : Fin m) (x : Fin (volume prime v) → ZMod 2) :
    array hw i j (fun z => SparseRoleCircuit.encode (a := 0) (x z)) =
      fun z => SparseRoleCircuit.encode (a := 0) (array hw i j x z) := rfl

end
end IntegerMultBounds.Machine.Shared50RecursiveChildPermutation
