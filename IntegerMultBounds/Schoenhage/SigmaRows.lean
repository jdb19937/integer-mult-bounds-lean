module

public import IntegerMultBounds.Schoenhage.PaperSigma

/-! The word lists a tape program writes for the exponent tables of the §6
slot rounds. An axis row lists the physical bits of the axis's slots
`0, …, ℓ - 2` in the paper's layout: the bottom slots at `A + h'D` (`A =
DqK + D - 1 - i`), then the chunk-group slots at `B + c·DK + ρ` (`B =
(D - 1 - i) K`) (`axisRow_paper`). A slot round's table reads the first `h`
entries of each participating axis's row, pairs them with the axis's slot-`h`
bit and weights `W, 2W, 4W, …` (`roundEntries`, `slotTableP_rows`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN TwistDescriptors

variable {r : ℕ}

/-! ### Axis rows -/

/-- The bottom part of an axis row: `A + h'D` for `h' < b`. -/
def bottomRow (D A b : ℕ) : List ℕ := (List.range b).map fun h' => A + h' * D

/-- One chunk group of an axis row: `U + ρ` for `ρ < K`. -/
def chunkRun (K U : ℕ) : List ℕ := (List.range K).map fun ρ => U + ρ

/-- The chunk part of an axis row: chunk group `c` starts at `B + c·DK`. -/
def chunkRow (DK K B q : ℕ) : List ℕ := (List.range q).flatMap fun c => chunkRun K (B + c * DK)

/-- An axis row: its bottom slots, then its chunk-group slots. -/
def axisRow (D DK K b q A B : ℕ) : List ℕ := bottomRow D A b ++ chunkRow DK K B q

theorem range_mul_flatMap (K : ℕ) : ∀ q : ℕ,
    List.range (q * K) = (List.range q).flatMap fun c => (List.range K).map fun ρ => c * K + ρ
  | 0 => by simp
  | q + 1 => by
    rw [Nat.succ_mul, List.range_add, range_mul_flatMap K q, List.range_succ, List.flatMap_append]
    simp [Nat.add_comm]

/-- `axisRow_paper`: axis `i`'s row lists the physical bits of its slots below `ℓ - 1`. -/
theorem axisRow_paper {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (i : ℕ) :
    axisRow ts.length (ts.length * K) K ((ℓ - 1) % K) ((ℓ - 1) / K)
        (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1 - i)) ((ts.length - 1 - i) * K) =
      (List.range (ℓ - 1)).map (paperSigma ts ℓ K i) := by
  have hK : 0 < K := hL.2.2.1
  set D := ts.length
  set b := (ℓ - 1) % K
  set q := (ℓ - 1) / K
  have hbq : b + q * K = ℓ - 1 := by have := Nat.mod_add_div (ℓ - 1) K; simp only [b, q]; linarith
  have hbK : b < K := Nat.mod_lt _ hK
  rw [← hbq, List.range_add, List.map_append, range_mul_flatMap K q]
  unfold axisRow bottomRow chunkRow chunkRun
  congr 1
  · apply List.map_congr_left
    intro h' hh'
    have hlt : h' < b := List.mem_range.mp hh'
    unfold paperSigma
    simp only [show h' < (ℓ - 1) % K from hlt, ↓reduceIte]
    ring
  · simp only [List.map_flatMap, List.map_map]
    apply List.flatMap_congr
    intro c hc
    have hcq : c < q := List.mem_range.mp hc
    apply List.map_congr_left
    intro ρ hρ
    have hρK : ρ < K := List.mem_range.mp hρ
    simp only [Function.comp_apply]
    have h1 : ¬ b + (c * K + ρ) < (ℓ - 1) % K := by omega
    have h2 : b + (c * K + ρ) < ℓ - 1 := by
      have : c * K + K ≤ q * K := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hcq
      omega
    have e1 : (b + (c * K + ρ) - (ℓ - 1) % K) / K = c := by
      rw [show b + (c * K + ρ) - (ℓ - 1) % K = ρ + K * c by
          have : K * c = c * K := Nat.mul_comm _ _
          simp only [b]; omega,
        Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hρK, zero_add]
    have e2 : (b + (c * K + ρ) - (ℓ - 1) % K) % K = ρ := by
      rw [show b + (c * K + ρ) - (ℓ - 1) % K = ρ + K * c by
          have : K * c = c * K := Nat.mul_comm _ _
          simp only [b]; omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρK]
    unfold paperSigma
    simp only [h1, h2, ↓reduceIte, e1, e2]
    ring

/-- The rows of all axes, from axis `0`: the bottom start drops by one and the chunk start by `K`
per axis. -/
def axisRows (D DK K b q A0 B0 : ℕ) : List (List ℕ) :=
  (List.range D).map fun i => axisRow D DK K b q (A0 - i) (B0 - i * K)

theorem axisRows_paper {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) :
    axisRows ts.length (ts.length * K) K ((ℓ - 1) % K) ((ℓ - 1) / K)
        (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)) ((ts.length - 1) * K) =
      (List.range ts.length).map fun i => (List.range (ℓ - 1)).map (paperSigma ts ℓ K i) := by
  unfold axisRows
  apply List.map_congr_left
  intro i hi
  have hiD : i < ts.length := List.mem_range.mp hi
  rw [← axisRow_paper hL i]
  congr 1
  · omega
  · rw [← Nat.sub_mul]

/-! ### The top slots -/

/-- The physical bits of the top slots: long axis `k` (in axis order) at `T0 - k`. -/
def topBits (flags : List Bool) (T0 : ℕ) : List ℕ := (List.range ((flags.filter id).length)).map (T0 - ·)

/-! ### Round tables -/

/-- An axis's entries: its slot bit `X` with each lower bit, weights `W, 2W, 4W, …`. -/
def axisEntries (X W : ℕ) : List ℕ → List Entry
  | [] => []
  | v :: vs => (X, v, W) :: axisEntries X (2 * W) vs

theorem axisEntries_eq (X W : ℕ) (vs : List ℕ) :
    axisEntries X W vs = (List.range vs.length).map fun h' => (X, vs.getD h' 0, W * 2 ^ h') := by
  induction vs generalizing W with
  | nil => rfl
  | cons v vs ih =>
    rw [axisEntries, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero, pow_zero, mul_one, Function.comp_def, List.getD_cons_succ, pow_succ]
    congr 2
    funext h'
    ring_nf

/-- `slotTableP_rows`: a slot round's table, from the rows and the slot-`h` bit of each axis. -/
theorem slotTableP_rows (ts : List ℕ) (ℓ K : ℕ) (r' : ℕ) {h : ℕ} (hh : h ≤ ℓ - 1) (Is : List ℕ) :
    slotTableP ts ℓ K r' Is h = Is.flatMap fun i =>
      axisEntries (paperSigma ts ℓ K i h) (2 * (2 * r' / 2 ^ (h + 1)))
        (((List.range (ℓ - 1)).map (paperSigma ts ℓ K i)).take h) := by
  unfold slotTableP
  apply List.flatMap_congr
  intro i hi
  rw [axisEntries_eq, List.length_take, List.length_map, List.length_range, Nat.min_eq_left hh]
  apply List.map_congr_left
  intro h' hh'
  have hlt : h' < h := List.mem_range.mp hh'
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_take, List.getElem_map, List.getElem_range, Prod.mk.injEq, true_and]
  ring

end IntegerMultBounds.Schoenhage
