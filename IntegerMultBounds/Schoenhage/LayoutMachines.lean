module

public import IntegerMultBounds.Schoenhage.LayoutArray
public import IntegerMultBounds.Resampling.SwapCost

/-! The layout moves of §6 as runs of the tensor driver. Every move is one
address-field interchange (`SwapPrim`): a single-bit move interchanges a
field of width `0` with one of width `1` across `m` bits, its inverse the
widths `1` and `0`, and a chunk exchange two fields of width `K`. A field
swap of widths `(hh, g, dd)` above a suffix of `2^ρ` records is the record map
`onTop (2^ρ) (fieldSwap hh g dd)` (`swapRecs_ofFn`), so a script of swap
records turns the record array into the array of the composed record maps
(`result_ops`), within the interchange's uniform cost per record
(`driveCost_ops_le`). The paper's prefix moves and chunk exchanges, as such
a script, store the array in the paper's layout (`result_layout`); the
reversed script restores the natural order (`result_undo`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.LayoutMachines
noncomputable section

open Machine Spec.SignedRingProduct LayoutMoves LayoutArray ChunkSwapRecords
open Resampling AxisDriver Script
open BinaryAdjacentWidthInterchange (volume index transpose transpose_entry index_coordinates coordinates)
open RecursiveInterchangeRows (pack pack_val)

/-! ### Field swaps of any adjacent widths -/

/-- Interchange the fields of widths `hh` (low) and `dd` (high) across `g` bits:
the record at address `t` with fields `(p, d, x, h)` is read from `(p, h, x, d)`. -/
def fieldSwap (hh g dd t : ℕ) : ℕ :=
  ((t / 2 ^ hh / 2 ^ g / 2 ^ dd * 2 ^ hh + t % 2 ^ hh) * 2 ^ g + t / 2 ^ hh % 2 ^ g) * 2 ^ dd +
    t / 2 ^ hh / 2 ^ g % 2 ^ dd

theorem fieldSwap_swapTop (K g : ℕ) : fieldSwap K g K = swapTop K g := rfl

theorem fieldSwap_moveTop (m : ℕ) : fieldSwap 0 m 1 = moveTop m := by
  funext t; simp [fieldSwap, moveTop, Nat.mod_one]

theorem fieldSwap_backTop (m : ℕ) : fieldSwap 1 m 0 = backTop m := by
  funext t; simp [fieldSwap, backTop, Nat.mod_one]

/-- The interchange reads the record at the swapped address. -/
theorem transpose_val (P hh g dd B : ℕ) (z : Fin (volume P (2 ^ dd) (2 ^ g) (2 ^ hh) B)) :
    (transpose (id : Fin (volume P (2 ^ hh) (2 ^ g) (2 ^ dd) B) → _) z).val =
      onTop B (fieldSwap hh g dd) id z.val := by
  have hzv := congrArg Fin.val (index_coordinates z)
  simp only [index, pack_val] at hzv
  have h1 := (coordinates z).2.1.isLt
  have h2 := (coordinates z).2.2.1.isLt
  have h3 := (coordinates z).2.2.2.1.isLt
  have h4 := (coordinates z).2.2.2.2.isLt
  simp only [transpose, index, pack_val, id, onTop, fieldSwap]
  rw [← hzv]
  simp only [div_shift' h4, mod_shift' h4, div_shift' h3, mod_shift' h3, div_shift' h2, mod_shift' h2,
    div_shift' h1, mod_shift' h1]

/-- `swapRecs_ofFn`: a field swap above `B` records acts on a record list read from `u` as the
record map `onTop B (fieldSwap hh g dd)`. -/
theorem swapRecs_ofFn {β : Type*} [Inhabited β] {N : ℕ} (P hh g dd B : ℕ)
    (hN : volume P (2 ^ hh) (2 ^ g) (2 ^ dd) B = N) (u : ℕ → β) :
    swapRecs P (2 ^ hh) (2 ^ g) (2 ^ dd) B (List.ofFn fun y : Fin N => u y) =
      List.ofFn fun y : Fin N => onTop B (fieldSwap hh g dd) u y := by
  have hN' : volume P (2 ^ dd) (2 ^ g) (2 ^ hh) B = N := by rw [← hN]; unfold volume; ring
  apply List.ext_getElem
  · simp [swapRecs, hN']
  intro n hn hn'
  simp only [swapRecs, List.getElem_ofFn]
  set z : Fin (volume P (2 ^ dd) (2 ^ g) (2 ^ hh) B) := ⟨n, by simpa [swapRecs] using hn⟩
  have hlt : (transpose (id : Fin (volume P (2 ^ hh) (2 ^ g) (2 ^ dd) B) → _) z).val < N := by
    have := (transpose (id : Fin (volume P (2 ^ hh) (2 ^ g) (2 ^ dd) B) → _) z).isLt
    omega
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
  simp only [onTop]
  rw [show (transpose (id : Fin (volume P (2 ^ hh) (2 ^ g) (2 ^ dd) B) → _) z).val =
      onTop B (fieldSwap hh g dd) id n from transpose_val P hh g dd B z]
  rfl

/-! ### Scripts of field swaps -/

/-- One field swap `(hh, g, dd, ρ)`: widths `hh`, `g`, `dd` above `2^ρ` records. -/
abbrev Op := ℕ × ℕ × ℕ × ℕ

/-- The record map of a field swap. -/
def opMap {β : Type*} (o : Op) (w : ℕ → β) : ℕ → β := onTop (2 ^ o.2.2.2) (fieldSwap o.1 o.2.1 o.2.2.1) w

/-- Run field swaps in order. -/
def runOps {β : Type*} : List Op → (ℕ → β) → ℕ → β
  | [], w => w
  | o :: os, w => runOps os (opMap o w)

/-- A field swap fits an address of `n` bits with adjacent field widths. -/
def OpOK (n : ℕ) (o : Op) : Prop := o.1 ≤ o.2.2.1 + 1 ∧ o.2.2.1 ≤ o.1 + 1 ∧ o.1 + o.2.1 + o.2.2.1 + o.2.2.2 ≤ n

/-- The prefix size `2^(n - hh - g - dd - ρ)` of a field swap. -/
def opP (n : ℕ) (o : Op) : ℕ := 2 ^ (n - o.1 - o.2.1 - o.2.2.1 - o.2.2.2)

/-- The headers of a field swap on records of `R` bits. -/
def opHdrs (n R : ℕ) (o : Op) : List (List Bool) := swapHdrsG (opP n o) (2 ^ o.2.1) o.1 o.2.2.1 (2 ^ o.2.2.2 * R)

/-- The script record of a field swap. -/
def opRec (n R : ℕ) (o : Op) : AxisDriver.Rec := .swap (opHdrs n R o)

theorem opP_volume {n : ℕ} {o : Op} (h : OpOK n o) :
    volume (opP n o) (2 ^ o.1) (2 ^ o.2.1) (2 ^ o.2.2.1) (2 ^ o.2.2.2) = 2 ^ n := by
  unfold volume opP
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  obtain ⟨-, -, h3⟩ := h
  omega

variable {E : ℕ} (S : AxisSpec E)

theorem length_array_ofFn {r w N : ℕ} (u : ℕ → Rec r) :
    (array w (List.ofFn fun y : Fin N => u y)).length = 2 ^ 0 * (2 * r * w) * N := by
  rw [length_array, List.length_ofFn]; ring

/-- One field swap record on the record array. -/
theorem opRec_spec {r w n : ℕ} (hw : 0 < 2 * r * w) {o : Op} (ho : OpOK n o) (u : ℕ → Rec r) :
    SwapPrim.Pre (swIn (opHdrs n (2 * r * w) o) (array w (List.ofFn fun y : Fin (2 ^ n) => u y))) ∧
      swapF (opHdrs n (2 * r * w) o) (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) =
        array w (List.ofFn fun y : Fin (2 ^ n) => opMap o u y) := by
  have hvol := opP_volume ho
  have hl : (array w (List.ofFn fun y : Fin (2 ^ n) => u y)).length =
      opP n o * 2 ^ o.1 * 2 ^ o.2.1 * 2 ^ o.2.2.1 * (2 ^ o.2.2.2 * (2 * r * w)) := by
    rw [length_array, List.length_ofFn, ← hvol]; unfold volume; ring
  obtain ⟨hpre, hsw⟩ := swapRecG_spec (opP n o) (2 ^ o.2.1) o.1 o.2.2.1 (2 ^ o.2.2.2 * (2 * r * w))
    (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) (by unfold opP; positivity) (by positivity)
    (by positivity) ho.1 ho.2.1 hl
  refine ⟨hpre, ?_⟩
  rw [opHdrs, hsw, swapList_array w _ _ _ _ _ _ (by rw [List.length_ofFn, hvol]),
    swapRecs_ofFn _ _ _ _ _ hvol]
  rfl

/-- `result_ops`: a script of field swaps turns the record array into the array of the composed
record maps, and every record meets the interchange's precondition. -/
theorem result_ops {r w n : ℕ} (hw : 0 < 2 * r * w) :
    ∀ (os : List Op), (∀ o ∈ os, OpOK n o) → ∀ u : ℕ → Rec r,
      Valid S (os.map (opRec n (2 * r * w))) (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) ∧
      result S (os.map (opRec n (2 * r * w))) (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) =
        array w (List.ofFn fun y : Fin (2 ^ n) => runOps os u y)
  | [], _, u => ⟨trivial, rfl⟩
  | o :: os, hos, u => by
    obtain ⟨hpre, hsw⟩ := opRec_spec hw (hos o (by simp)) u
    obtain ⟨hv, hr⟩ := result_ops hw os (fun o' h => hos o' (by simp [h])) (opMap o u)
    refine ⟨⟨by simp [opHdrs, swapHdrsG], hpre, ?_⟩, ?_⟩
    · rw [hsw]; exact hv
    · simp only [List.map_cons, result, opRec]
      rw [show swapF (opHdrs n (2 * r * w) o) _ = _ from hsw, hr]
      rfl

/-- `driveCost_ops_le`: the driver's cost on a script of field swaps is at most a constant times the
array length times `max(1, hh, dd)^τ` per record, plus three steps per record. -/
theorem driveCost_ops_le : ∃ C : ℝ, 0 < C ∧ ∀ {r w n : ℕ}, 0 < 2 * r * w →
    ∀ (os : List Op), (∀ o ∈ os, OpOK n o) → ∀ u : ℕ → Rec r,
      (driveCost S (os.map (opRec n (2 * r * w))) (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) : ℝ) ≤
        (os.map fun o => C * (2 * r * w * 2 ^ n : ℕ) * ((max 1 (max o.1 o.2.2.1) : ℕ) : ℝ) ^ Parameters.tau + 3).sum := by
  obtain ⟨C, hC, hb⟩ := SwapCost.swapCost_le
  refine ⟨C, hC, fun {r w n} hw => ?_⟩
  intro os
  induction os with
  | nil => intro _ _; simp [driveCost]
  | cons o os ih =>
    intro hos u
    have ho := hos o (by simp)
    obtain ⟨-, hsw⟩ := opRec_spec hw ho u
    have hl : (array w (List.ofFn fun y : Fin (2 ^ n) => u y)).length =
        opP n o * 2 ^ o.1 * 2 ^ o.2.1 * 2 ^ o.2.2.1 * (2 ^ o.2.2.2 * (2 * r * w)) := by
      rw [length_array, List.length_ofFn, ← opP_volume ho]; unfold volume; ring
    have h1 := hb (opP n o) (2 ^ o.2.1) o.1 o.2.2.1 (2 ^ o.2.2.2 * (2 * r * w))
      (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) (by unfold opP; positivity) (by positivity)
      (by positivity) ho.1 ho.2.1 hl
    have hlen : (array w (List.ofFn fun y : Fin (2 ^ n) => u y)).length = 2 * r * w * 2 ^ n := by
      rw [length_array, List.length_ofFn]
    rw [hlen] at h1
    have h2 := ih (fun o' h => hos o' (by simp [h])) (opMap o u)
    simp only [List.map_cons, driveCost, opRec, List.sum_cons]
    rw [show swapF (opHdrs n (2 * r * w) o) _ = _ from hsw]
    have h1' : (swapCost (opHdrs n (2 * r * w) o) (array w (List.ofFn fun y : Fin (2 ^ n) => u y)) : ℝ) ≤
        C * ((2 * r * w * 2 ^ n : ℕ) : ℝ) * ((max 1 (max o.1 o.2.2.1) : ℕ) : ℝ) ^ Parameters.tau := h1
    push_cast at h1' h2 ⊢
    linarith

/-! ### The paper's moves as field swaps -/

/-- Single-bit moves `(m, ρ)` as field swaps of widths `0` and `1`. -/
def moveOps (qs : List (ℕ × ℕ)) : List Op := qs.map fun q => (0, q.1, 1, q.2)

/-- Their inverses, widths `1` and `0`. -/
def backOps (qs : List (ℕ × ℕ)) : List Op := qs.map fun q => (1, q.1, 0, q.2)

/-- Chunk exchanges `(K, γ, ρ)` as field swaps of widths `K` and `K`. -/
def exOps (qs : List (ℕ × ℕ × ℕ)) : List Op := qs.map fun q => (q.1, q.2.1, q.1, q.2.2)

theorem runOps_append {β : Type*} : ∀ (a b : List Op) (w : ℕ → β), runOps (a ++ b) w = runOps b (runOps a w)
  | [], _, _ => rfl
  | o :: a, b, w => runOps_append a b (opMap o w)

theorem runOps_moveOps {β : Type*} : ∀ (qs : List (ℕ × ℕ)) (w : ℕ → β), runOps (moveOps qs) w = runMoves qs w
  | [], _ => rfl
  | q :: qs, w => by
    simp only [moveOps, List.map_cons, runOps, runMoves]
    rw [← moveOps, runOps_moveOps qs]
    congr 1
    simp only [opMap, fieldSwap_moveTop, moveOp_eq_onTop]

theorem runOps_exOps {β : Type*} : ∀ (qs : List (ℕ × ℕ × ℕ)) (w : ℕ → β), runOps (exOps qs) w = runSwaps qs w
  | [], _ => rfl
  | q :: qs, w => by
    simp only [exOps, List.map_cons, runOps, runSwaps]
    rw [← exOps, runOps_exOps qs]
    rfl

theorem runOps_backOps_reverse {β : Type*} : ∀ (qs : List (ℕ × ℕ)) (w : ℕ → β),
    runOps (backOps qs.reverse) w = runMovesBack qs w
  | [], _ => rfl
  | q :: qs, w => by
    simp only [List.reverse_cons, backOps, List.map_append, runOps_append, List.map_cons, List.map_nil]
    rw [← backOps, runOps_backOps_reverse qs]
    simp only [runOps, runMovesBack, opMap, fieldSwap_backTop, moveBackOp]

theorem runOps_exOps_reverse {β : Type*} : ∀ (qs : List (ℕ × ℕ × ℕ)) (w : ℕ → β),
    runOps (exOps qs.reverse) w = runSwapsBack qs w
  | [], _ => rfl
  | q :: qs, w => by
    simp only [List.reverse_cons, exOps, List.map_append, runOps_append, List.map_cons, List.map_nil]
    rw [← exOps, runOps_exOps_reverse qs]
    simp only [runOps, runSwapsBack, opMap, fieldSwap_swapTop, swapOp_eq_onTop]

/-! ### The moves fit the address -/

section Bounds

variable {α : Type*} [DecidableEq α]

/-- Every prefix move `(m, ρ)` satisfies `m + ρ + 1 ≤` the address length. -/
theorem prefixParams_bound : ∀ (ss : List α) (k : ℕ) (ord : List α), ord.Nodup → ss.Nodup →
    (∀ s ∈ ss, s ∈ ord ∧ s ∉ ord.take k) → k ≤ ord.length →
    ∀ q ∈ prefixParams k ss ord, q.1 + q.2 + 1 ≤ ord.length
  | [], _, _, _, _, _, _, q, hq => by simp [prefixParams] at hq
  | s :: ss, k, ord, hnd, hss, hmem, hk, q, hq => by
    have hs1 := hmem s (by simp)
    have hsd : s ∈ ord.drop k := by
      have := hs1.1
      rw [← List.take_append_drop k ord, List.mem_append] at this
      exact this.resolve_left hs1.2
    obtain ⟨X, R, h1, h2, h3⟩ := moveAfter_split hnd hsd
    simp only [prefixParams, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rw [h3]
      have := congrArg List.length h1
      simp only [List.length_append, List.length_cons] at this
      dsimp only; omega
    · have hperm := moveAfter_perm hnd hsd
      have hss' := (List.nodup_cons.mp hss)
      have hklen : k < ord.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by omega)] at hsd
        simp at hsd
      rw [← hperm.length_eq]
      refine prefixParams_bound ss (k + 1) _ (hperm.nodup_iff.mpr hnd) hss'.2 ?_ ?_ q hq
      · intro s' hs'
        have h' := hmem s' (by simp [hs'])
        refine ⟨hperm.mem_iff.mpr h'.1, ?_⟩
        have hlen : (ord.take k).length = k := List.length_take_of_le hk
        rw [h2, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
          show k + 1 - k = 1 by omega]
        simp only [List.take_succ_cons, List.take_zero, List.mem_append, List.mem_singleton, not_or]
        exact ⟨h'.2, fun e => hss'.1 (e ▸ hs')⟩
      · rw [hperm.length_eq]; omega

theorem length_prefixParams : ∀ (ss : List α) (k : ℕ) (ord : List α), (prefixParams k ss ord).length = ss.length
  | [], _, _ => rfl
  | _ :: ss, k, _ => by simp [prefixParams, length_prefixParams ss (k + 1)]

end Bounds

/-- Every chunk exchange of `m` blocks of `K` slots satisfies `2K + γ + ρ ≤ m K`. -/
theorem exParams_bound {m K : ℕ} (e : Fin m × Fin m) :
    2 * (exParams K e).1 + (exParams K e).2.1 + (exParams K e).2.2 ≤ m * K := by
  unfold exParams
  split_ifs with h
  · simp
  · have ha := e.1.isLt
    have hb := e.2.isLt
    have hne : e.1.val ≠ e.2.val := fun h' => h (Fin.ext h')
    have hsum : 2 + (max e.1.val e.2.val - min e.1.val e.2.val - 1) + (m - 1 - max e.1.val e.2.val) ≤ m := by
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · rw [max_eq_right hl.le, min_eq_left hl.le]; omega
      · rw [max_eq_left hl.le, min_eq_right hl.le]; omega
    calc 2 * K + (max e.1.val e.2.val - min e.1.val e.2.val - 1) * K + (m - 1 - max e.1.val e.2.val) * K
        = (2 + (max e.1.val e.2.val - min e.1.val e.2.val - 1) + (m - 1 - max e.1.val e.2.val)) * K := by ring
      _ ≤ m * K := Nat.mul_le_mul_right _ hsum

/-! ### The layout script -/

variable {r : ℕ} {ts : List ℕ} {ℓ K : ℕ}

/-- The prefix moves of the paper's layout. -/
def layoutMoves (ts : List ℕ) (ℓ K : ℕ) : List (ℕ × ℕ) := prefixParams 0 (prefixSlots ts ℓ K) (initOrder ts)

/-- The chunk exchanges of the paper's layout. -/
def layoutSwaps (ts : List ℕ) (ℓ K : ℕ) : List (ℕ × ℕ × ℕ) :=
  (selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0).map (exParams K)

/-- The field swaps storing the array in the paper's layout. -/
def layoutOpList (ts : List ℕ) (ℓ K : ℕ) : List Op := moveOps (layoutMoves ts ℓ K) ++ exOps (layoutSwaps ts ℓ K)

/-- The field swaps restoring the natural order. -/
def undoOpList (ts : List ℕ) (ℓ K : ℕ) : List Op :=
  exOps (layoutSwaps ts ℓ K).reverse ++ backOps (layoutMoves ts ℓ K).reverse

/-- The address length `n = log₂ M`. -/
abbrev addrBits (ts : List ℕ) : ℕ := Nat.log 2 ts.prod

theorem length_initOrder (hL : LayoutOK r ts ℓ K) : (initOrder ts).length = addrBits ts := by
  simp only [addrBits, log_prod_eq_sum hL.1, initOrder, List.length_flatMap, length_slotsDesc]

theorem chunks_le (hL : LayoutOK r ts ℓ K) : (ℓ - 1) / K * ts.length * K ≤ addrBits ts := by
  obtain ⟨-, h2, -, -⟩ := layout_moves_eq hL
  have hlen := congrArg List.length h2
  rw [List.length_append, List.length_map, List.length_reverse, List.length_range] at hlen
  have harr : (arrange ts ℓ K (applySwaps (selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0)
      (axisToChunk ((ℓ - 1) / K) ts.length))).length = (ℓ - 1) / K * ts.length * K := by
    have hblk : ∀ y, (LayoutMoves.blk ts ℓ K y).length = K := fun y => by simp [LayoutMoves.blk, LayoutMoves.chunk, length_slotsDesc]
    unfold arrange
    rw [length_flatten_const _ (fun b hb => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
      exact hblk _), List.length_map, List.length_finRange]
  simp only [addrBits]
  omega

theorem layoutOpList_ok (hL : LayoutOK r ts ℓ K) : ∀ o ∈ layoutOpList ts ℓ K, OpOK (addrBits ts) o := by
  intro o ho
  simp only [layoutOpList, List.mem_append, moveOps, exOps, layoutSwaps, List.map_map, List.mem_map,
    Function.comp_def] at ho
  rcases ho with ⟨q, hq, rfl⟩ | ⟨e, -, rfl⟩
  · have hb := prefixParams_bound (prefixSlots ts ℓ K) 0 (initOrder ts) initOrder_nodup (prefixSlots_nodup hL)
      (fun s hs => ⟨prefixSlots_sub hL s hs, by simp⟩) (Nat.zero_le _) q hq
    rw [length_initOrder hL] at hb
    refine ⟨by simp, by simp, ?_⟩; dsimp only; omega
  · have hb := exParams_bound (K := K) e
    have hc := chunks_le hL
    refine ⟨by simp, by simp, ?_⟩; dsimp only; omega

theorem undoOpList_ok (hL : LayoutOK r ts ℓ K) : ∀ o ∈ undoOpList ts ℓ K, OpOK (addrBits ts) o := by
  intro o ho
  have hall := layoutOpList_ok hL
  simp only [undoOpList, List.mem_append, exOps, backOps, List.mem_map, List.mem_reverse] at ho
  rcases ho with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · have := hall (q.1, q.2.1, q.1, q.2.2) (by simp [layoutOpList, exOps, hq])
    exact this
  · have := hall (0, q.1, 1, q.2) (by simp [layoutOpList, moveOps, hq])
    obtain ⟨-, -, h3⟩ := this
    exact ⟨by simp, by simp, by dsimp only at h3 ⊢; omega⟩

/-- `result_layout`: the layout script stores the record array in the paper's layout. -/
theorem result_layout (hL : LayoutOK r ts ℓ K) {w : ℕ} (hw : 0 < 2 * r * w) (z : ℕ → Rec r) :
    Valid S ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y)) ∧
      result S ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
          (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y)) =
        array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)) := by
  have hin : (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y) =
      List.ofFn fun y : Fin (2 ^ addrBits ts) => (fun y => z (y % 2 ^ addrBits ts)) y :=
    List.ofFn_inj.mpr (funext fun y => by simp [Nat.mod_eq_of_lt y.isLt])
  rw [hin]
  obtain ⟨hv, hr⟩ := result_ops S hw _ (layoutOpList_ok hL) (fun y => z (y % 2 ^ addrBits ts))
  refine ⟨hv, ?_⟩
  rw [hr, layoutOpList, runOps_append, runOps_moveOps, runOps_exOps]
  have := layoutOps_paper hL z
  simp only [layoutMoves, layoutSwaps] at this ⊢
  rw [this]

/-- `result_undo`: the reversed script restores the natural order. -/
theorem result_undo (hL : LayoutOK r ts ℓ K) {w : ℕ} (hw : 0 < 2 * r * w) (z : ℕ → Rec r) :
    Valid S ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y))) ∧
      result S ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
          (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y))) =
        array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y) := by
  obtain ⟨hv, hr⟩ := result_ops S hw _ (undoOpList_ok hL) (fun y => z ((paperPerm hL).logi y))
  refine ⟨hv, ?_⟩
  rw [hr, undoOpList, runOps_append, runOps_exOps_reverse, runOps_backOps_reverse]
  have := layoutOps_undo hL z
  simp only [layoutMoves, layoutSwaps] at this ⊢
  rw [this]
  exact congrArg (array w) (List.ofFn_inj.mpr (funext fun y => by simp [Nat.mod_eq_of_lt y.isLt]))

/-! ### Cost -/

theorem sum_map_le_card {ι : Type*} (L : List ι) (f : ι → ℝ) (c : ℝ) (h : ∀ x ∈ L, f x ≤ c) :
    (L.map f).sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    push_cast; linarith

/-- `driveCost_layout_le`: the layout script costs at most `C V + 3` per prefix move and
`C V max(1, K)^τ + 3` per chunk exchange, `V = 2 r w M` the array length; there are
`|prefixSlots|` moves and at most `q D - 1` exchanges. The same holds for the undo script. -/
theorem driveCost_layout_le : ∃ C : ℝ, 0 < C ∧ ∀ {r : ℕ} {ts : List ℕ} {ℓ K w : ℕ} (hL : LayoutOK r ts ℓ K),
    0 < 2 * r * w → ∀ z : ℕ → Rec r,
      (driveCost S ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
          (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y)) : ℝ) ≤
        (layoutMoves ts ℓ K).length * (C * (2 * r * w * 2 ^ addrBits ts : ℕ) + 3) +
          (layoutSwaps ts ℓ K).length *
            (C * (2 * r * w * 2 ^ addrBits ts : ℕ) * ((max 1 K : ℕ) : ℝ) ^ Parameters.tau + 3) ∧
      (driveCost S ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
          (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y))) : ℝ) ≤
        (layoutMoves ts ℓ K).length * (C * (2 * r * w * 2 ^ addrBits ts : ℕ) + 3) +
          (layoutSwaps ts ℓ K).length *
            (C * (2 * r * w * 2 ^ addrBits ts : ℕ) * ((max 1 K : ℕ) : ℝ) ^ Parameters.tau + 3) := by
  obtain ⟨C, hC, hb⟩ := driveCost_ops_le S
  refine ⟨C, hC, fun {r ts ℓ K w} hL hw z => ?_⟩
  have htau := Machine.Shared50RecursiveBudgetBound.exponent_range.1
  set V : ℝ := ((2 * r * w * 2 ^ addrBits ts : ℕ) : ℝ)
  have hV : 0 ≤ V := Nat.cast_nonneg _
  have hK1 : (1 : ℝ) ≤ ((max 1 K : ℕ) : ℝ) ^ Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 K) htau.le
  have hmove : ∀ q : ℕ × ℕ, C * V * ((max 1 (max 0 1) : ℕ) : ℝ) ^ Parameters.tau + 3 ≤ C * V + 3 ∧
      C * V * ((max 1 (max 1 0) : ℕ) : ℝ) ^ Parameters.tau + 3 ≤ C * V + 3 := fun _ => by
    simp
  have hex : ∀ q ∈ layoutSwaps ts ℓ K,
      C * V * ((max 1 (max q.1 q.1) : ℕ) : ℝ) ^ Parameters.tau + 3 ≤
        C * V * ((max 1 K : ℕ) : ℝ) ^ Parameters.tau + 3 := by
    intro q hq
    simp only [layoutSwaps, List.mem_map] at hq
    obtain ⟨e, -, rfl⟩ := hq
    have hle : max 1 (max (exParams K e).1 (exParams K e).1) ≤ max 1 K := by
      unfold exParams; split_ifs <;> simp
    have : ((max 1 (max (exParams K e).1 (exParams K e).1) : ℕ) : ℝ) ^ Parameters.tau ≤
        ((max 1 K : ℕ) : ℝ) ^ Parameters.tau :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) htau.le
    have hCV : 0 ≤ C * V := by positivity
    nlinarith
  constructor
  · have h := hb hw _ (layoutOpList_ok hL) z
    refine h.trans ?_
    simp only [layoutOpList, List.map_append, List.sum_append, moveOps, exOps, List.map_map, Function.comp_def]
    gcongr
    · have := sum_map_le_card (layoutMoves ts ℓ K)
        (fun q => C * V * ((max 1 (max 0 1) : ℕ) : ℝ) ^ Parameters.tau + 3) (C * V + 3)
        (fun q _ => (hmove q).1)
      simpa [V] using this
    · exact sum_map_le_card (layoutSwaps ts ℓ K) _ _ hex
  · have h := hb hw _ (undoOpList_ok hL) (fun y => z ((paperPerm hL).logi y))
    refine h.trans ?_
    simp only [undoOpList, List.map_append, List.sum_append, backOps, exOps, List.map_map, Function.comp_def]
    rw [add_comm]
    gcongr
    · have := sum_map_le_card (layoutMoves ts ℓ K).reverse
        (fun q => C * V * ((max 1 (max 1 0) : ℕ) : ℝ) ^ Parameters.tau + 3) (C * V + 3)
        (fun q _ => (hmove q).2)
      simpa [V] using this
    · have := sum_map_le_card (layoutSwaps ts ℓ K).reverse _ _ (fun q hq => hex q (List.mem_reverse.mp hq))
      simpa [V] using this

/-- The move counts: `|prefixSlots|` prefix moves and at most `q D - 1` chunk exchanges. -/
theorem layout_counts (hL : LayoutOK r ts ℓ K) :
    (layoutMoves ts ℓ K).length = (longs ts ℓ).length + (ℓ - 1) % K * ts.length ∧
      (layoutSwaps ts ℓ K).length ≤ (ℓ - 1) / K * ts.length - 1 := by
  obtain ⟨-, -, h3, h4⟩ := layout_moves_eq hL
  refine ⟨by rw [layoutMoves, length_prefixParams, h3], by rw [layoutSwaps, List.length_map]; exact h4⟩

/-! ### The driver runs -/

/-- `runs_layout`: with the layout script on the script tape, the tensor driver stores the record array
in the paper's layout. -/
theorem runs_layout (hL : LayoutOK r ts ℓ K) {w : ℕ} (hw : 0 < 2 * r * w) (z : ℕ → Rec r)
    (L : List (List Bool)) :
    Runs (drive S) (bank S.ρ S.X (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y))
        ⟨L, ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w))).flatMap AxisDriver.Rec.words⟩)
      (· = bank S.ρ S.X (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)))
        ⟨(((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w))).flatMap AxisDriver.Rec.words).reverse ++ L,
          []⟩)
      (driveCost S ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y))) := by
  obtain ⟨hv, hr⟩ := result_layout S hL hw z
  have := runs_drive S _ _ L hv
  rwa [hr] at this

/-- `runs_undo`: with the undo script on the script tape, the tensor driver restores the natural order. -/
theorem runs_undo (hL : LayoutOK r ts ℓ K) {w : ℕ} (hw : 0 < 2 * r * w) (z : ℕ → Rec r)
    (L : List (List Bool)) :
    Runs (drive S) (bank S.ρ S.X (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)))
        ⟨L, ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w))).flatMap AxisDriver.Rec.words⟩)
      (· = bank S.ρ S.X (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y))
        ⟨(((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w))).flatMap AxisDriver.Rec.words).reverse ++ L,
          []⟩)
      (driveCost S ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)))) := by
  obtain ⟨hv, hr⟩ := result_undo S hL hw z
  have := runs_drive S _ _ L hv
  rwa [hr] at this

end
end IntegerMultBounds.Schoenhage.LayoutMachines
