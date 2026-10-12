module

public import IntegerMultBounds.Schoenhage.SwapPrim
public import IntegerMultBounds.Spec.PointwiseProducts
public import Mathlib.Data.List.GetD

/-! The address-field interchange on a record array. A record array is the
concatenation of equal-length blocks, so the bit-level interchange with
suffix `B · R` (`R` the block length) moves whole blocks: it is the record
list with its `H` and `D` address fields interchanged, re-flattened
(`swapList_flatMap`). For the paper's records, `R = 2 r w`
(`swapList_array`), so one call of `SwapPrim.prim` exchanges two address
chunks of the transform's record array. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.ChunkSwapRecords

open Machine Spec.SignedRingProduct
open BinaryAdjacentWidthInterchange (volume index transpose transpose_entry index_coordinates)
open RecursiveInterchangeRows (pack pack_val)

variable {α β : Type*}

/-- Reading a concatenation of blocks of equal length `R`. -/
theorem getD_flatMap_uniform (f : β → List α) {R : ℕ} (hR : ∀ x, (f x).length = R) (dflt : α) :
    ∀ (xs : List β) (k j : ℕ) (hk : k < xs.length), j < R →
      (xs.flatMap f).getD (k * R + j) dflt = (f xs[k]).getD j dflt
  | [], k, _, hk, _ => absurd hk (by simp)
  | x :: xs, 0, j, _, hj => by
    simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
    rw [List.getD_append _ _ _ _ (by rw [hR]; exact hj)]
  | x :: xs, k + 1, j, hk, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by rw [hR]; nlinarith)]
    rw [hR, show (k + 1) * R + j - R = k * R + j by rw [Nat.succ_mul]; omega]
    exact getD_flatMap_uniform f hR dflt xs k j (by simpa using hk) hj

theorem length_flatMap_uniform (f : β → List α) {R : ℕ} (hR : ∀ x, (f x).length = R) (xs : List β) :
    (xs.flatMap f).length = xs.length * R := by
  rw [List.length_flatMap]
  simp only [hR, List.map_const', List.sum_replicate, smul_eq_mul]

/-- The record list with its `H` and `D` address fields interchanged. -/
def swapRecs [Inhabited β] (P H G D B : ℕ) (xs : List β) : List β :=
  List.ofFn fun z : Fin (volume P D G H B) =>
    xs.getD (transpose (id : Fin (volume P H G D B) → _) z).val default

theorem index_pack_val {P H G D B R : ℕ} (p : Fin P) (h : Fin H) (g : Fin G) (d : Fin D) (b : Fin B)
    (j : Fin R) : (index p h g d (pack b j)).val = (index p h g d b).val * R + j.val := by
  simp only [index, pack_val]
  ring

theorem transpose_id_index {P H G D B : ℕ} (p : Fin P) (h : Fin H) (g : Fin G) (d : Fin D) (b : Fin B) :
    (transpose (id : Fin (volume P H G D B) → _) (index p d g h b)).val = (index p h g d b).val := by
  rw [transpose_entry]; rfl

/-- `swapList_flatMap`: the bit-level interchange with suffix `B · R` of a
concatenation of `R`-bit blocks interchanges the blocks' address fields. -/
theorem swapList_flatMap [Inhabited β] (f : β → List Bool) {R : ℕ} (hR : ∀ x, (f x).length = R)
    (P H G D B : ℕ) (xs : List β) (hxs : xs.length = volume P H G D B) :
    SwapPrim.swapList P H G D (B * R) (xs.flatMap f) = (swapRecs P H G D B xs).flatMap f := by
  have hvol : volume P D G H (B * R) = volume P D G H B * R := by
    unfold volume; ring
  apply List.ext_getElem
  · rw [length_flatMap_uniform f hR, SwapPrim.swapList, List.length_ofFn, swapRecs, List.length_ofFn,
      hvol]
  intro n hn hn'
  rw [SwapPrim.swapList, List.length_ofFn] at hn
  simp only [SwapPrim.swapList, List.getElem_ofFn]
  rw [← List.getD_eq_getElem _ false hn']
  set z : Fin (volume P D G H (B * R)) := ⟨n, hn⟩
  have hz := index_coordinates z
  set c := BinaryAdjacentWidthInterchange.coordinates z
  obtain ⟨⟨b, j⟩, hb⟩ := finProdFinEquiv.surjective c.2.2.2.2
  rw [← hb] at hz
  change index c.1 c.2.1 c.2.2.1 c.2.2.2.1 (pack b j) = z at hz
  have hnz : n = z.val := rfl
  have hj := j.isLt
  have hsrc : (transpose (id : Fin (volume P H G D (B * R)) → _) z).val =
      (index c.1 c.2.2.2.1 c.2.2.1 c.2.1 b).val * R + j.val := by
    rw [← hz, transpose_id_index, index_pack_val]
  have hdst : n = (index c.1 c.2.1 c.2.2.1 c.2.2.2.1 b).val * R + j.val := by
    rw [hnz, ← hz, index_pack_val]
  have hsrcLt : (index c.1 c.2.2.2.1 c.2.2.1 c.2.1 b).val < xs.length := by
    rw [hxs]; exact (index _ _ _ _ _).isLt
  have hdstLt : (index c.1 c.2.1 c.2.2.1 c.2.2.2.1 b).val < (swapRecs P H G D B xs).length := by
    rw [swapRecs, List.length_ofFn]; exact (index _ _ _ _ _).isLt
  rw [hsrc, getD_flatMap_uniform f hR false xs _ _ hsrcLt hj, hdst,
    getD_flatMap_uniform f hR false (swapRecs P H G D B xs) _ _ hdstLt hj]
  congr 2
  simp only [swapRecs, List.getElem_ofFn, Fin.eta, transpose_id_index]
  exact (List.getD_eq_getElem _ _ hsrcLt).symm

/-- `swapList_array`: on the paper's record array (records of `2 r w` bits),
the interchange with suffix `B · 2rw` exchanges two record-address fields. -/
theorem swapList_array {r : ℕ} (w P H G D B : ℕ) (fs : List (Rec r))
    (hfs : fs.length = volume P H G D B) :
    SwapPrim.swapList P H G D (B * (2 * r * w)) (array w fs) = array w (swapRecs P H G D B fs) := by
  unfold array
  exact swapList_flatMap (fun f : Rec r => record w f.1 f.2) (fun f => length_record w f.1 f.2) P H G D B fs hfs

end IntegerMultBounds.Schoenhage.ChunkSwapRecords
