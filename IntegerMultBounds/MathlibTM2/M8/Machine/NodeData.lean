module

public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeLayout
public import IntegerMultBounds.Machine.RecursiveScalarIndex
public import IntegerMultBounds.Machine.Shared50RecursiveNodeSemantics

/-!
# The node data through split, temporaries, pieces and merge

For an input bit array `x` of a node, cut into rows over the contract roles:
* after the split and `tempInit`, the node bank holds the row bits on the contract roles, the
  zero bit on every temporary, and a blank input/output tape (`init_encoded`);
* the pieces then put on every contract role the routed transpose of the rows, and `tempClear`
  makes the temporaries blank again, which is exactly the merge input of the parent transpose
  (`clear_network`), given each child call's exact interchange semantics.

This is `Shared50RecursiveNodeSemantics`, `Shared50RecursiveNodeBinary` and
`Shared50RecursiveNodePieces` with temporaries.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open Classical
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveInterchangeRows (groups rowLength pack roleIndex)
open Shared50RecursiveNodeRows (suffixPack suffixUnpack swapSuffix roleSwap transpose)
open NodeLayout
open Shared50RecursiveNodeSemantics (encoded)

variable [Net] {b : ℕ} {v : Descriptor}

local instance : NeZero (ActualAffineScaling.modulus b) :=
  ⟨ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
local instance : NeZero (prime ^ b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩

namespace NodeData

def rank (hw : v.width = width * b) (x : Fin width → ZMod (prime ^ b)) : Fin (prime ^ v.width) :=
  Fin.cast (by rw [← pow_mul, Nat.mul_comm b, hw]) (FlatCoordinateLayout.rank x)

/-- The parent H/D interchange on the row index of one role. -/
theorem scalar_index (hw : v.width = width * b)
    (a : RecursiveScalarCoordinates.Address width b (role v roleCount)) :
    RecursiveScalarCoordinates.index (v := role v roleCount) hw a = roleIndex prime roleCount v
      (pack a.beforeRows a.row) (suffixPack (a.before, rank hw a.h, a.middle, rank hw a.d, a.after)) := by
  apply Fin.ext
  trans RecursiveInterchangeLayout.index prime (role v roleCount) a.beforeRows.val a.row.val a.before.val
    (FlatCoordinateLayout.rank a.h).val a.middle.val (FlatCoordinateLayout.rank a.d).val a.after.val
  · exact RecursiveScalarCoordinates.index_val (v := role v roleCount) hw a
  · change RecursiveInterchangeLayout.index prime (role v roleCount) a.beforeRows.val a.row.val a.before.val
      (FlatCoordinateLayout.rank a.h).val a.middle.val (FlatCoordinateLayout.rank a.d).val a.after.val =
        (pack (pack a.beforeRows a.row) (suffixPack (a.before, rank hw a.h, a.middle, rank hw a.d, a.after))).val
    simp only [RecursiveInterchangeRows.pack_val, suffixPack, RecursiveInterchangeRows.suffixIndex,
      rank, RecursiveInterchangeLayout.index, role, rowLength]
    dsimp only [Fin.cast, ActualAffineScaling.modulus]
    ring

theorem roleSwap_scalar (hw : v.width = width * b)
    (a : RecursiveScalarCoordinates.Address width b (role v roleCount)) :
    roleSwap (RecursiveScalarCoordinates.index (v := role v roleCount) hw a) =
      RecursiveScalarCoordinates.index (v := role v roleCount) hw {a with h := a.d, d := a.h} := by
  rw [scalar_index, scalar_index]
  simp only [roleSwap, RecursiveInterchangeRows.roleIndex, Fin.cast_cast, Fin.cast_eq_self,
    RecursiveInterchangeRows.pack, Equiv.symm_apply_apply]
  exact congrArg (fun k => RecursiveInterchangeRows.roleIndex prime roleCount v
    (RecursiveInterchangeRows.pack a.beforeRows a.row) k)
    (Shared50RecursiveNodeRows.swapSuffix_pack (v := v) a.before (rank hw a.h) a.middle (rank hw a.d) a.after)

/-- The bits of one role's rows. -/
def splitBits (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (j : Fin roleCount) (z : Fin (volume prime (role v roleCount))) : ZMod 2 :=
  let gk := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime roleCount v) z)
  x (Fin.cast (RecursiveInterchangeRows.volume_split prime roleCount v hd).symm (pack gk.1 (pack j gk.2)))

theorem encode_split (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (j : Fin roleCount) (z : Fin (volume prime (role v roleCount))) :
    SparseRoleCircuit.encode (splitBits hd x j z) =
      RecursiveRowsSerialization.roleArray hd (encoded x) j z := rfl

/-- The bit streams of the node's wires: rows on the contract roles, zero temporaries. -/
def splitWire (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2) :
    Wire → Fin (volume prime (role v roleCount)) → ZMod 2
  | .inl i => splitBits hd x ((Net.net).roleEquiv.symm i)
  | .inr _ => 0

theorem world_selected (i : World) : world i = wires (Fin.natAdd 1 ((Net.net).roleEquiv.symm i)) := by
  rw [wires_role, Equiv.apply_symm_apply]

theorem not_temp_world (i : World) : ¬ IsTemp (world i) := by
  rintro ⟨k, hk⟩
  have h := wireSlot_injective hk
  simp at h

theorem not_temp_io : ¬ IsTemp io := by
  rintro ⟨k, hk⟩
  exact tempSlot_ne_io k hk.symm

theorem temp_unselected (k : Fin tempCount) : ¬∃ j, wires j = tempSlot k := by
  rintro ⟨j, hj⟩
  induction j using Fin.addCases with
  | left j =>
    rw [show Fin.castAdd roleCount j = Fin.castAdd roleCount (0 : Fin 1) from by
      congr 1; exact Subsingleton.elim _ _, wires_io] at hj
    exact tempSlot_ne_io k hj
  | right j =>
    rw [wires_role] at hj
    have h := wireSlot_injective hj
    simp at h

/-- After the split and `tempInit`: row bits, zero temporaries and a blank input/output tape. -/
theorem init_encoded (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2) :
    RoleOps.run (tempOps (SparseRoleCircuit.encode (a := 0) 0))
      (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x)) =
      encodedBits (splitWire hd x) (fun _ => blank) := by
  funext i
  rw [run_tempOps]
  induction i using Fin.addCases with
  | left k =>
    have hk : Fin.castAdd 1 k = wireSlot (wireEquiv k) := by simp [wireSlot]
    rw [hk, encodedBits_wire]
    rcases hw : wireEquiv k with w | t
    · have hn := not_temp_world w
      simp only [world] at hn
      simp only [hn, ↓reduceIte]
      funext z
      have he := RecursiveRowsSerialization.roleData_entry wires wires_injective (Equiv.refl _) hd
        (encoded x) ((Net.net).roleEquiv.symm w) z
      rw [← world_selected] at he
      simp only [world] at he
      rw [he]
      rfl
    · have ht : IsTemp (wireSlot (.inr t)) := ⟨(Net.net).tempEquiv.symm t, by simp [tempSlot]⟩
      simp only [ht, ↓reduceIte]
      rfl
  | right k =>
    have hk : Fin.natAdd wireCount k = io := by
      rw [show k = 0 from Subsingleton.elim _ _]; rfl
    rw [hk]
    simp only [not_temp_io, ↓reduceIte]
    rw [encodedBits_io]
    rw [← wires_io]
    exact RecursiveRowsSerialization.roleData_common_blank wires wires_injective _ hd _

/-- After the pieces and `tempClear`: exactly the merge input of the parent transpose. -/
theorem clear_network (hw : v.width = width * b) (hd : roleCount ∣ v.rows)
    (child : Transport.Child (role v roleCount)) (hc : Transport.ChildSpec (v := role v roleCount) hw child)
    (x : Fin (volume prime v) → ZMod 2) :
    RoleOps.run (tempOps blank)
      (Transport.run (v := role v roleCount) hw child pieces (encodedBits (splitWire hd x) (fun _ => blank))) =
      RecursiveRowsSerialization.roleData wires mergeRoute hd (transpose hd (encoded x)) := by
  funext i
  rw [run_tempOps]
  by_cases ht : IsTemp i
  · simp only [ht, ↓reduceIte]
    obtain ⟨k, rfl⟩ := ht
    exact (RecursiveRowsSerialization.putData_unselected wires _ _ (temp_unselected k)).symm
  · simp only [ht, ↓reduceIte]
    induction i using Fin.addCases with
    | left k =>
      have hk : Fin.castAdd 1 k = wireSlot (wireEquiv k) := by simp [wireSlot]
      rw [hk]
      rcases hwk : wireEquiv k with w | t
      · funext z
        obtain ⟨a, rfl⟩ := RecursiveScalarIndex.surjective (v := role v roleCount) hw z
        have he := Transport.run_entry (v := role v roleCount) hw child hc (splitWire hd x)
          (fun t => rfl) (fun _ => blank) w a
        rw [he]
        have hr := RecursiveRowsSerialization.roleData_entry wires wires_injective mergeRoute hd
          (transpose hd (encoded x)) ((Net.net).roleEquiv.symm w)
          (RecursiveScalarCoordinates.index (v := role v roleCount) hw a)
        rw [← world_selected] at hr
        simp only [world] at hr
        rw [hr, Shared50RecursiveNodeRows.split_transpose, roleSwap_scalar, mergeRoute_symm,
          Equiv.apply_symm_apply]
        rfl
      · exfalso
        apply ht
        refine ⟨(Net.net).tempEquiv.symm t, ?_⟩
        rw [hk, hwk]
        simp [tempSlot]
    | right k =>
      have hk : Fin.natAdd wireCount k = io := by
        rw [show k = 0 from Subsingleton.elim _ _]; rfl
      rw [hk, Transport.run_io (v := role v roleCount) hw child hc, encodedBits_io, ← wires_io]
      exact (RecursiveRowsSerialization.roleData_common_blank wires wires_injective _ hd _).symm

end NodeData

end
end IntegerMultBounds.MathlibTM2.M8.Machine
