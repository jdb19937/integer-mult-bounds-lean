module

public import IntegerMultBounds.Schoenhage.LayoutMoves
public import IntegerMultBounds.Machine.RadixDigitMoveBlockRows
public import IntegerMultBounds.Schoenhage.ChunkSwapRecords

/-! The layout moves of §6 on a record array. An array is stored in a name
order when its physical address bits, most significant first, hold the
logical bits `ps` (`stored`): the record at physical address `y` is the
logical record at `addrOf ps y`. A single-bit move (`moveOp`, the record-level
form of `Machine.RadixDigitMoveBlockRows.unmove`) and a chunk exchange (`swapOp`, the
record-level form of `ChunkSwapRecords.swapRecs`) turn an array stored in one
order into the same array stored in the reordered order (`moveOp_stored`,
`swapOp_stored`). Running the prefix moves and the chunk exchanges of the
paper's layout on the array in natural order therefore stores it in the
paper's layout: the record at physical address `y` is the logical record at
`(paperPerm hL).logi y` (`layoutOps_paper`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.LayoutArray

open Spec.SignedRingProduct LayoutMoves

/-! ### Logical addresses from physical bits -/

/-- The logical address of physical address `y` when its bits, most significant first, hold the
logical bits `ps`. -/
def addrOf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, y => bitAt y ps.length * 2 ^ p + addrOf ps y

theorem bitAt_div (y a b : ℕ) : bitAt (y / 2 ^ a) b = bitAt y (a + b) := by
  unfold bitAt; rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- `addrOf` reads only the low `ps.length` bits. -/
theorem addrOf_congr : ∀ (ps : List ℕ) {y y' : ℕ}, (∀ k < ps.length, bitAt y k = bitAt y' k) →
    addrOf ps y = addrOf ps y'
  | [], _, _, _ => rfl
  | p :: ps, y, y', h => by
    simp only [addrOf]
    rw [h ps.length (by simp), addrOf_congr ps fun k hk => h k (by simp; omega)]

theorem addrOf_append : ∀ (L₁ L₂ : List ℕ) (y : ℕ),
    addrOf (L₁ ++ L₂) y = addrOf L₁ (y / 2 ^ L₂.length) + addrOf L₂ y
  | [], L₂, y => by simp [addrOf]
  | p :: L₁, L₂, y => by
    simp only [List.cons_append, addrOf, List.length_append, addrOf_append L₁ L₂ y, bitAt_div]
    rw [Nat.add_comm L₂.length L₁.length]; ring

/-- The array stored in order `ps`. -/
def stored {β : Type*} (ps : List ℕ) (z : ℕ → β) : ℕ → β := fun y => z (addrOf ps y)

/-! ### Bits of mixed-radix indices -/

theorem div_shift {a e ρ : ℕ} (he : e < 2 ^ ρ) : (a * 2 ^ ρ + e) / 2 ^ ρ = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt he, zero_add]

theorem bitAt_shift_low {a e ρ k : ℕ} (hk : k < ρ) : bitAt (a * 2 ^ ρ + e) k = bitAt e k := by
  rw [Nat.add_comm]
  apply bitAt_add_mul
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 hk) a

theorem bitAt_mod_low {y ρ k : ℕ} (hk : k < ρ) : bitAt (y % 2 ^ ρ) k = bitAt y k := by
  unfold bitAt; exact bit_mod_pow hk

theorem bitAt_eq_mod_div (y ρ m : ℕ) : bitAt y (m + ρ) = y / 2 ^ ρ / 2 ^ m % 2 := by
  unfold bitAt; rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm]

/-! ### A single-bit move -/

/-- Move the bit just above the low `m + ρ` bits down past `m` bits: physical address `y` with
fields `(p, j, x, e)` (widths `·, 1, m, ρ`) reads the old address with fields `(p, x, j, e)`. -/
def moveOp {β : Type*} (m ρ : ℕ) (w : ℕ → β) : ℕ → β := fun y =>
  w (((y / 2 ^ ρ / 2 ^ m / 2 * 2 ^ m + y / 2 ^ ρ % 2 ^ m) * 2 + y / 2 ^ ρ / 2 ^ m % 2) * 2 ^ ρ + y % 2 ^ ρ)

/-- `moveOp_stored`: moving a bit realizes `moveAfter` on the stored order. -/
theorem moveOp_stored {β : Type*} (A X R : List ℕ) (s : ℕ) (z : ℕ → β) :
    moveOp X.length R.length (stored (A ++ (X ++ s :: R)) z) = stored (A ++ (s :: (X ++ R))) z := by
  funext y
  simp only [moveOp, stored]
  congr 1
  set ρ := R.length
  set m := X.length
  set u := y / 2 ^ ρ
  set v := u / 2 ^ m
  have he : y % 2 ^ ρ < 2 ^ ρ := Nat.mod_lt _ (by positivity)
  have hx : u % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
  have hj : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
  set o := ((v / 2 * 2 ^ m + u % 2 ^ m) * 2 + v % 2) * 2 ^ ρ + y % 2 ^ ρ
  have ho : o / 2 ^ ρ = (v / 2 * 2 ^ m + u % 2 ^ m) * 2 + v % 2 := div_shift he
  have ho1 : o / 2 ^ (ρ + 1) = v / 2 * 2 ^ m + u % 2 ^ m := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ho]; omega
  have ho2 : o / 2 ^ (m + (ρ + 1)) = v / 2 := by
    rw [Nat.add_comm m, pow_add, ← Nat.div_div_eq_div_mul, ho1, div_shift hx]
  have hy2 : y / 2 ^ (m + ρ + 1) = v / 2 := by
    rw [show m + ρ + 1 = ρ + m + 1 by ring, pow_succ, pow_add, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul]
  simp only [addrOf_append, List.length_append, List.length_cons, addrOf]
  rw [ho2, show X.length + R.length + 1 = m + ρ + 1 from rfl, hy2]
  have hX : addrOf X (o / 2 ^ (R.length + 1)) = addrOf X (y / 2 ^ R.length) := by
    rw [show R.length = ρ from rfl, ho1]
    apply addrOf_congr
    intro k hk
    rw [bitAt_shift_low hk, bitAt_mod_low hk]
  have hR : addrOf R o = addrOf R y := by
    apply addrOf_congr
    intro k hk
    rw [bitAt_shift_low hk, bitAt_mod_low hk]
  have hbit : bitAt o R.length = bitAt y (X.length + R.length) := by
    rw [bitAt_eq_mod_div y ρ m]
    unfold bitAt
    rw [show R.length = ρ from rfl, ho, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [hX, hR, hbit]
  ring

/-! ### A chunk exchange -/

/-- Exchange two `K`-bit address chunks separated by `γ` bits above the low `ρ` bits: physical
address `y` with fields `(p, c₁, g, c₂, e)` reads the old address with fields `(p, c₂, g, c₁, e)`. -/
def swapOp {β : Type*} (K γ ρ : ℕ) (w : ℕ → β) : ℕ → β := fun y =>
  w ((((y / 2 ^ ρ / 2 ^ K / 2 ^ γ / 2 ^ K * 2 ^ K + y / 2 ^ ρ % 2 ^ K) * 2 ^ γ +
    y / 2 ^ ρ / 2 ^ K % 2 ^ γ) * 2 ^ K + y / 2 ^ ρ / 2 ^ K / 2 ^ γ % 2 ^ K) * 2 ^ ρ + y % 2 ^ ρ)

theorem div_pow_add (y a b : ℕ) : y / 2 ^ (a + b) = y / 2 ^ b / 2 ^ a := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm]

/-- `swapOp_stored`: exchanging two chunks of equal width realizes the exchange on the stored order. -/
theorem swapOp_stored {β : Type*} (A X G Y R : List ℕ) (hXY : X.length = Y.length) (z : ℕ → β) :
    swapOp X.length G.length R.length (stored (A ++ (X ++ (G ++ (Y ++ R)))) z) =
      stored (A ++ (Y ++ (G ++ (X ++ R)))) z := by
  funext y
  simp only [swapOp, stored]
  congr 1
  set ρ := R.length
  set K := X.length
  set γ := G.length
  set u := y / 2 ^ ρ
  set u2 := u / 2 ^ K
  set u3 := u2 / 2 ^ γ
  have he : y % 2 ^ ρ < 2 ^ ρ := Nat.mod_lt _ (by positivity)
  have hc2 : u % 2 ^ K < 2 ^ K := Nat.mod_lt _ (by positivity)
  have hg : u2 % 2 ^ γ < 2 ^ γ := Nat.mod_lt _ (by positivity)
  have hc1 : u3 % 2 ^ K < 2 ^ K := Nat.mod_lt _ (by positivity)
  set o := (((u3 / 2 ^ K * 2 ^ K + u % 2 ^ K) * 2 ^ γ + u2 % 2 ^ γ) * 2 ^ K + u3 % 2 ^ K) * 2 ^ ρ + y % 2 ^ ρ
  have ho0 : o / 2 ^ ρ = ((u3 / 2 ^ K * 2 ^ K + u % 2 ^ K) * 2 ^ γ + u2 % 2 ^ γ) * 2 ^ K + u3 % 2 ^ K :=
    div_shift he
  have ho1 : o / 2 ^ (K + ρ) = (u3 / 2 ^ K * 2 ^ K + u % 2 ^ K) * 2 ^ γ + u2 % 2 ^ γ := by
    rw [div_pow_add, ho0, div_shift hc1]
  have ho2 : o / 2 ^ (γ + (K + ρ)) = u3 / 2 ^ K * 2 ^ K + u % 2 ^ K := by
    rw [div_pow_add, ho1, div_shift hg]
  have ho3 : o / 2 ^ (K + (γ + (K + ρ))) = u3 / 2 ^ K := by
    rw [div_pow_add, ho2, div_shift hc2]
  have hy1 : y / 2 ^ (K + ρ) = u2 := div_pow_add y K ρ
  have hy2 : y / 2 ^ (γ + (K + ρ)) = u3 := by rw [div_pow_add, hy1]
  have hy3 : y / 2 ^ (K + (γ + (K + ρ))) = u3 / 2 ^ K := by rw [div_pow_add, hy2]
  have hYK : Y.length = K := hXY.symm
  simp only [addrOf_append, List.length_append, hYK]
  rw [show X.length = K from rfl, show G.length = γ from rfl, show R.length = ρ from rfl,
    ho3, hy3]
  have hX : addrOf X (o / 2 ^ (γ + (K + ρ))) = addrOf X (y / 2 ^ ρ) := by
    rw [ho2]
    apply addrOf_congr
    intro k hk
    rw [bitAt_shift_low hk, bitAt_mod_low hk]
  have hG : addrOf G (o / 2 ^ (K + ρ)) = addrOf G (y / 2 ^ (K + ρ)) := by
    rw [ho1, hy1]
    apply addrOf_congr
    intro k hk
    rw [bitAt_shift_low hk, bitAt_mod_low hk]
  have hY : addrOf Y (o / 2 ^ ρ) = addrOf Y (y / 2 ^ (γ + (K + ρ))) := by
    rw [ho0, hy2]
    apply addrOf_congr
    intro k hk
    rw [hYK] at hk
    rw [bitAt_shift_low hk, bitAt_mod_low hk]
  have hR : addrOf R o = addrOf R y := by
    apply addrOf_congr
    intro k hk
    rw [bitAt_shift_low hk, bitAt_mod_low hk]
  rw [hX, hG, hY, hR]
  ring

/-! ### Sequences of moves on a name order -/

section Sequence

variable {α : Type*} [DecidableEq α] (pos : α → ℕ) {β : Type*}

/-- The widths `(m, ρ)` of the move of `s` to position `k` in `ord`. -/
def moveParams (k : ℕ) (s : α) (ord : List α) : ℕ × ℕ :=
  ((ord.drop k).idxOf s, (ord.drop k).length - (ord.drop k).idxOf s - 1)

/-- The widths of the moves of `movePrefix k ss ord`. -/
def prefixParams : ℕ → List α → List α → List (ℕ × ℕ)
  | _, [], _ => []
  | k, s :: ss, ord => moveParams k s ord :: prefixParams (k + 1) ss (moveAfter k s ord)

/-- Run single-bit moves with the given widths. -/
def runMoves : List (ℕ × ℕ) → (ℕ → β) → ℕ → β
  | [], w => w
  | q :: qs, w => runMoves qs (moveOp q.1 q.2 w)

omit [DecidableEq α] in
theorem not_mem_left_of_nodup {X R : List α} {s : α} (h : (X ++ s :: R).Nodup) : s ∉ X :=
  fun hX => List.disjoint_of_nodup_append h hX (List.mem_cons_self)

/-- One prefix move as a split of the order. -/
theorem moveAfter_split {k : ℕ} {s : α} {ord : List α} (hnd : ord.Nodup) (hs : s ∈ ord.drop k) :
    ∃ X R : List α, ord = ord.take k ++ (X ++ s :: R) ∧
      moveAfter k s ord = ord.take k ++ (s :: (X ++ R)) ∧ moveParams k s ord = (X.length, R.length) := by
  obtain ⟨X, R, hXR⟩ := List.append_of_mem hs
  have hd : (X ++ s :: R).Nodup := hXR ▸ hnd.sublist (List.drop_sublist _ _)
  have hsX := not_mem_left_of_nodup hd
  refine ⟨X, R, by rw [← hXR, List.take_append_drop], ?_, ?_⟩
  · simp only [moveAfter, hXR, List.erase_append_right _ hsX, List.erase_cons_head]
  · simp only [moveParams, hXR, List.idxOf_append_of_notMem hsX, List.idxOf_cons_self,
      List.length_append, List.length_cons]
    ext <;> simp <;> omega

theorem moveAfter_perm {k : ℕ} {s : α} {ord : List α} (hnd : ord.Nodup) (hs : s ∈ ord.drop k) :
    (moveAfter k s ord).Perm ord := by
  obtain ⟨X, R, h1, h2, -⟩ := moveAfter_split hnd hs
  rw [h2]
  conv_rhs => rw [h1]
  exact List.Perm.append_left _ (List.perm_middle).symm

/-- `runMoves_prefix`: the single-bit moves of `prefixParams` realize `movePrefix` on the array. -/
theorem runMoves_prefix (z : ℕ → β) : ∀ (ss : List α) (k : ℕ) (ord : List α), ord.Nodup → ss.Nodup →
    (∀ s ∈ ss, s ∈ ord ∧ s ∉ ord.take k) → k ≤ ord.length →
    runMoves (prefixParams k ss ord) (stored (ord.map pos) z) = stored ((movePrefix k ss ord).map pos) z
  | [], _, _, _, _, _, _ => rfl
  | s :: ss, k, ord, hnd, hss, hmem, hk => by
    have hs1 := hmem s (by simp)
    have hsd : s ∈ ord.drop k := by
      have := hs1.1
      rw [← List.take_append_drop k ord, List.mem_append] at this
      exact this.resolve_left hs1.2
    obtain ⟨X, R, h1, h2, h3⟩ := moveAfter_split hnd hsd
    simp only [prefixParams, runMoves, movePrefix, h3]
    have hstep : moveOp X.length R.length (stored (ord.map pos) z) =
        stored ((moveAfter k s ord).map pos) z := by
      have e1 : ord.map pos = (ord.take k).map pos ++ (X.map pos ++ pos s :: R.map pos) := by
        conv_lhs => rw [h1]
        simp
      have e2 : (moveAfter k s ord).map pos = (ord.take k).map pos ++ (pos s :: (X.map pos ++ R.map pos)) := by
        rw [h2]; simp
      rw [e1, e2]
      have := moveOp_stored ((ord.take k).map pos) (X.map pos) (R.map pos) (pos s) z
      simpa only [List.length_map] using this
    rw [hstep]
    have hperm := moveAfter_perm hnd hsd
    have hss' := (List.nodup_cons.mp hss)
    have hklen : k < ord.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hsd
      simp at hsd
    apply runMoves_prefix z ss (k + 1) _ (hperm.nodup_iff.mpr hnd) hss'.2
    · intro s' hs'
      have h' := hmem s' (by simp [hs'])
      refine ⟨hperm.mem_iff.mpr h'.1, ?_⟩
      have hlen : (ord.take k).length = k := List.length_take_of_le hk
      rw [h2, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
        show k + 1 - k = 1 by omega]
      simp only [List.take_succ_cons, List.take_zero, List.mem_append, List.mem_singleton, not_or]
      exact ⟨h'.2, fun e => hss'.1 (e ▸ hs')⟩
    · rw [hperm.length_eq]; omega

end Sequence

/-! ### Sequences of chunk exchanges -/

section Exchanges

variable {α : Type*} (pos : α → ℕ) {β : Type*}

/-- A list split around two of its positions `u < v`. -/
theorem split_two {γ : Type*} (L : List γ) {u v : ℕ} (huv : u < v) (hv : v < L.length) :
    L = L.take u ++ L[u] :: ((L.drop (u + 1)).take (v - u - 1) ++ L[v] :: L.drop (v + 1)) := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]; omega
  intro n h1 h2
  simp only [List.getElem_append, List.length_take, List.getElem_cons, List.length_drop,
    List.getElem_take, List.getElem_drop]
  split_ifs <;> first | rfl | (congr 1; omega) | omega

/-- The index map exchanging `u` and `v`. -/
def swapIdx (u v n : ℕ) : ℕ := if n = u then v else if n = v then u else n

theorem swapIdx_comm {u v : ℕ} (h : u ≠ v) (n : ℕ) : swapIdx u v n = swapIdx v u n := by
  unfold swapIdx; split_ifs <;> omega

theorem swapIdx_lt {u v n m : ℕ} (hu : u < m) (hv : v < m) (hn : n < m) : swapIdx u v n < m := by
  unfold swapIdx; split_ifs <;> omega

/-- The same list with positions `u < v` exchanged. -/
theorem split_two_swap {γ : Type*} (L S : List γ) {u v : ℕ} (huv : u < v) (hv : v < L.length)
    (hS : S.length = L.length)
    (hSL : ∀ n (hn : n < S.length), S[n] = L[swapIdx u v n]'(swapIdx_lt (by omega) hv (by omega))) :
    S = L.take u ++ L[v] :: ((L.drop (u + 1)).take (v - u - 1) ++ L[u] :: L.drop (v + 1)) := by
  have hv' : v < S.length := by omega
  refine (split_two S huv hv').trans ?_
  congr 1
  · apply List.ext_getElem
    · simp only [List.length_take]; omega
    intro n h1 h2
    simp only [List.length_take] at h1
    simp only [List.getElem_take]
    rw [hSL]
    congr 1; unfold swapIdx; split_ifs <;> omega
  · congr 1
    · rw [hSL]; congr 1; unfold swapIdx; simp
    · congr 1
      · apply List.ext_getElem
        · simp only [List.length_take, List.length_drop]; omega
        intro n h1 h2
        simp only [List.length_take, List.length_drop] at h1
        simp only [List.getElem_take, List.getElem_drop]
        rw [hSL]
        congr 1; unfold swapIdx; split_ifs <;> omega
      · congr 1
        · rw [hSL]; congr 1; unfold swapIdx; split_ifs <;> omega
        · apply List.ext_getElem
          · simp only [List.length_drop]; omega
          intro n h1 h2
          simp only [List.length_drop] at h1
          simp only [List.getElem_drop]
          rw [hSL]
          congr 1; unfold swapIdx; split_ifs <;> omega

theorem length_flatten_const {γ : Type*} {K : ℕ} : ∀ (L : List (List γ)), (∀ b ∈ L, b.length = K) →
    L.flatten.length = L.length * K
  | [], _ => by simp
  | b :: L, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      h b (by simp), length_flatten_const L (fun c hc => h c (by simp [hc]))]
    ring

/-- The arrangement of `m` blocks in which position `x` holds block `σ x`. -/
def arrBlocks {m : ℕ} (blkF : ℕ → List α) (σ : Equiv.Perm (Fin m)) : List (List α) :=
  (List.finRange m).map fun x => blkF (σ x)

/-- The widths `(K, γ, ρ)` of the exchange of positions `e.1` and `e.2` of `m` blocks of `K` slots. -/
def exParams {m : ℕ} (K : ℕ) (e : Fin m × Fin m) : ℕ × ℕ × ℕ :=
  if e.1 = e.2 then (0, 0, 0) else
    (K, ((max e.1.val e.2.val) - (min e.1.val e.2.val) - 1) * K, (m - 1 - max e.1.val e.2.val) * K)

/-- Run chunk exchanges with the given widths. -/
def runSwaps : List (ℕ × ℕ × ℕ) → (ℕ → β) → ℕ → β
  | [], w => w
  | q :: qs, w => runSwaps qs (swapOp q.1 q.2.1 q.2.2 w)

theorem swap_val {m : ℕ} (a b : Fin m) (n : ℕ) (hn : n < m) :
    (Equiv.swap a b ⟨n, hn⟩).val = swapIdx a.val b.val n := by
  rw [Equiv.swap_apply_def]
  unfold swapIdx
  by_cases h1 : n = a.val
  · have : (⟨n, hn⟩ : Fin m) = a := Fin.ext h1
    rw [if_pos this, if_pos h1]
  · have h1' : (⟨n, hn⟩ : Fin m) ≠ a := fun e => h1 (congrArg Fin.val e)
    rw [if_neg h1', if_neg h1]
    by_cases h2 : n = b.val
    · have : (⟨n, hn⟩ : Fin m) = b := Fin.ext h2
      rw [if_pos this, if_pos h2]
    · have h2' : (⟨n, hn⟩ : Fin m) ≠ b := fun e => h2 (congrArg Fin.val e)
      rw [if_neg h2', if_neg h2]

theorem arrBlocks_swap_get {m : ℕ} (blkF : ℕ → List α) (σ : Equiv.Perm (Fin m)) (a b : Fin m) (n : ℕ)
    (hn : n < (arrBlocks blkF (σ * Equiv.swap a b)).length) :
    (arrBlocks blkF (σ * Equiv.swap a b))[n] =
      (arrBlocks blkF σ)[swapIdx a.val b.val n]'(by
        simp only [arrBlocks, List.length_map, List.length_finRange] at hn ⊢
        exact swapIdx_lt a.2 b.2 hn) := by
  have hnm : n < m := by simpa [arrBlocks] using hn
  have key : (Equiv.swap a b) ⟨n, hnm⟩ = ⟨swapIdx a.val b.val n, swapIdx_lt a.2 b.2 hnm⟩ :=
    Fin.ext (swap_val a b n hnm)
  simp only [arrBlocks, List.getElem_map, List.getElem_finRange, Equiv.Perm.coe_mul, Function.comp_apply,
    Fin.cast_mk]
  rw [key]

/-- One exchange of two blocks of the arrangement. -/
theorem swapOp_arrBlocks {m K : ℕ} (blkF : ℕ → List α) (hK : ∀ y, (blkF y).length = K)
    (pre : List α) (σ : Equiv.Perm (Fin m)) (e : Fin m × Fin m) (z : ℕ → β) :
    swapOp (exParams K e).1 (exParams K e).2.1 (exParams K e).2.2
        (stored ((pre ++ (arrBlocks blkF σ).flatten).map pos) z) =
      stored ((pre ++ (arrBlocks blkF (σ * Equiv.swap e.1 e.2)).flatten).map pos) z := by
  by_cases he : e.1 = e.2
  · have hid : σ * Equiv.swap e.1 e.2 = σ := by rw [he, Equiv.swap_self]; exact mul_one σ
    rw [hid]
    simp only [exParams, he, ↓reduceIte]
    have := swapOp_stored ((pre ++ (arrBlocks blkF σ).flatten).map pos) [] [] [] [] rfl z
    simpa using this
  -- order the two positions
  set lo := min e.1.val e.2.val
  set hi := max e.1.val e.2.val
  have hne : e.1.val ≠ e.2.val := fun h => he (Fin.ext h)
  have hlohi : lo < hi := by simp only [lo, hi]; omega
  have hhi : hi < m := by simp only [hi]; exact max_lt e.1.2 e.2.2
  set L := arrBlocks blkF σ
  have hL : L.length = m := by simp [L, arrBlocks]
  have hall : ∀ b ∈ L, b.length = K := by
    intro b hb; simp only [L, arrBlocks, List.mem_map] at hb; obtain ⟨x, -, rfl⟩ := hb; exact hK _
  have hsplit := split_two L hlohi (by rw [hL]; exact hhi)
  have hswap := split_two_swap L (arrBlocks blkF (σ * Equiv.swap e.1 e.2)) hlohi (by rw [hL]; exact hhi)
    (by simp [L, arrBlocks]) (by
      intro n hn
      rw [arrBlocks_swap_get]
      congr 1
      simp only [lo, hi]
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]
      · rw [min_eq_right h.le, max_eq_left h.le, swapIdx_comm hne])
  have hx : L[lo].length = K := hall _ (List.getElem_mem _)
  have hy : L[hi].length = K := hall _ (List.getElem_mem _)
  set M := (L.drop (lo + 1)).take (hi - lo - 1)
  set Z := L.drop (hi + 1)
  have hM : M.flatten.length = (hi - lo - 1) * K := by
    rw [length_flatten_const M (fun b hb => hall b (List.mem_of_mem_drop (List.mem_of_mem_take hb)))]
    simp only [M, List.length_take, List.length_drop, hL]; congr 1; omega
  have hZ : Z.flatten.length = (m - 1 - hi) * K := by
    rw [length_flatten_const Z (fun b hb => hall b (List.mem_of_mem_drop hb))]
    simp only [Z, List.length_drop, hL]; congr 1; omega
  have hparams : exParams K e = (K, (hi - lo - 1) * K, (m - 1 - hi) * K) := by
    simp only [exParams, he, ↓reduceIte, lo, hi]
  rw [hparams]
  conv_lhs => rw [hsplit]
  rw [hswap]
  have hA := swapOp_stored ((pre ++ (L.take lo).flatten).map pos) (L[lo].map pos) (M.flatten.map pos)
    (L[hi].map pos) (Z.flatten.map pos) (by simp [hx, hy]) z
  simp only [List.length_map, hx, hM, hZ] at hA
  convert hA using 2 <;> simp

/-- `runSwaps_apply`: the exchanges realize `applySwaps` on the arrangement. -/
theorem runSwaps_apply {m K : ℕ} (blkF : ℕ → List α) (hK : ∀ y, (blkF y).length = K) (pre : List α)
    (z : ℕ → β) : ∀ (es : List (Fin m × Fin m)) (σ : Equiv.Perm (Fin m)),
    runSwaps (es.map (exParams K)) (stored ((pre ++ (arrBlocks blkF σ).flatten).map pos) z) =
      stored ((pre ++ (arrBlocks blkF (applySwaps es σ)).flatten).map pos) z
  | [], _ => rfl
  | e :: es, σ => by
    simp only [List.map_cons, runSwaps, applySwaps]
    rw [swapOp_arrBlocks pos blkF hK pre σ e z]
    exact runSwaps_apply blkF hK pre z es _

end Exchanges

/-! ### The paper's layout -/

section Paper

variable {r : ℕ} {β : Type*}

/-- The logical bit of slot `(i, h)`. -/
def slotPos (ts : List ℕ) (x : ℕ × ℕ) : ℕ := axOff ts x.1 + x.2

theorem addrOf_map_range (f : ℕ → ℕ) (y : ℕ) : ∀ n : ℕ,
    addrOf ((List.range n).reverse.map f) y = ∑ Q ∈ Finset.range n, bitAt y Q * 2 ^ f Q
  | 0 => by simp [addrOf]
  | n + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, addrOf, addrOf_map_range f y n, Finset.sum_range_succ]
    simp only [List.length_map, List.length_reverse, List.length_range]
    ring

theorem ofBits_eq_sum (f : ℕ → ℕ) : ∀ n : ℕ, ofBits n f = ∑ P ∈ Finset.range n, f P % 2 * 2 ^ P
  | 0 => rfl
  | n + 1 => by rw [ofBits, ofBits_eq_sum f n, Finset.sum_range_succ]

theorem addrOf_natural (y n : ℕ) : addrOf (List.range n).reverse y = y % 2 ^ n := by
  have h := addrOf_map_range id y n
  simp only [List.map_id, id] at h
  rw [h, ← ofBits_bitAt n (y % 2 ^ n) (Nat.mod_lt _ (by positivity)), ofBits_eq_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [bitAt_mod_low (Finset.mem_range.mp hQ), Nat.mod_eq_of_lt (bitAt_lt_two y Q)]

/-- The address read through a bit permutation's `τ` is its logical address. -/
theorem addrOf_bitPerm {n : ℕ} (π : BitPerm n) (y : ℕ) :
    addrOf ((List.range n).reverse.map π.τ) y = π.logi y := by
  rw [addrOf_map_range, BitPerm.logi, ofBits_eq_sum]
  symm
  apply Finset.sum_nbij' π.σ π.τ
  · intro P hP; exact Finset.mem_range.mpr (π.σ_lt P (Finset.mem_range.mp hP))
  · intro Q hQ; exact Finset.mem_range.mpr (π.τ_lt Q (Finset.mem_range.mp hQ))
  · intro P hP; exact π.τσ P (Finset.mem_range.mp hP)
  · intro Q hQ; exact π.στ Q (Finset.mem_range.mp hQ)
  · intro P hP
    rw [Nat.mod_eq_of_lt (bitAt_lt_two y _), π.τσ P (Finset.mem_range.mp hP)]

theorem initOrder_slotPos : ∀ {ts : List ℕ}, PowAxes r ts →
    (initOrder ts).map (slotPos ts) = (List.range (Nat.log 2 ts.prod)).reverse
  | [], _ => by simp [initOrder]
  | t :: ts, h => by
    have ih := initOrder_slotPos (powAxes_cons h)
    rw [log_prod_cons h, Nat.add_comm, List.range_add, List.reverse_append, ← ih]
    simp only [initOrder, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.map_append, List.flatMap_map]
    congr 1
    · simp only [slotsDesc, List.map_map, Function.comp_def, slotPos, axOff, axLen, List.drop_one,
        List.tail_cons, List.getD_cons_zero, zero_add, List.map_reverse]
    · simp only [List.map_flatMap, slotsDesc, List.map_map, Function.comp_def, slotPos, axOff, axLen,
        List.drop_succ_cons, List.getD_cons_succ]

/-- `layoutOps_paper`: the prefix moves and chunk exchanges of the paper's layout, run on the
array in natural order, store it in the paper's layout. -/
theorem layoutOps_paper {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (z : ℕ → β) :
    runSwaps ((selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0).map (exParams K))
        (runMoves (prefixParams 0 (prefixSlots ts ℓ K) (initOrder ts))
          (fun y => z (y % 2 ^ Nat.log 2 ts.prod))) =
      fun y => z ((paperPerm hL).logi y) := by
  obtain ⟨hmove, horder, -, -⟩ := layout_moves_eq hL
  have hinit : (fun y => z (y % 2 ^ Nat.log 2 ts.prod)) = stored ((initOrder ts).map (slotPos ts)) z := by
    funext y; simp only [stored, initOrder_slotPos hL.1, addrOf_natural]
  rw [hinit, runMoves_prefix (slotPos ts) z (prefixSlots ts ℓ K) 0 (initOrder ts) (initOrder_nodup (ts := ts))
    (prefixSlots_nodup hL) (fun s hs => ⟨prefixSlots_sub hL s hs, by simp⟩) (Nat.zero_le _), hmove]
  have hblk : ∀ y, (blk ts ℓ K y).length = K := fun y => by simp [blk, chunk, length_slotsDesc]
  have harr : ∀ σ, arrange ts ℓ K σ = (arrBlocks (blk ts ℓ K) σ).flatten := fun σ => rfl
  rw [harr, runSwaps_apply (slotPos ts) (blk ts ℓ K) hblk (prefixSlots ts ℓ K) z, ← harr, horder]
  funext y
  simp only [stored, List.map_map]
  congr 1
  rw [← addrOf_bitPerm (paperPerm hL) y]
  rfl

end Paper

/-! ### The machines' payload maps and the inverse moves -/

section Payload

variable {γ : Type*}

/-- An address map acting above a suffix of size `E`. -/
def onTop (E : ℕ) (f : ℕ → ℕ) (w : ℕ → γ) : ℕ → γ := fun y => w (f (y / E) * E + y % E)

/-- The single-bit move above the suffix: `(p, j, x) ↦ (p, x, j)`, `x` of width `m`. -/
def moveTop (m t : ℕ) : ℕ := (t / 2 ^ m / 2 * 2 ^ m + t % 2 ^ m) * 2 + t / 2 ^ m % 2

/-- Its inverse: `(p, x, j) ↦ (p, j, x)`. -/
def backTop (m t : ℕ) : ℕ := (t / 2 / 2 ^ m * 2 + t % 2) * 2 ^ m + t / 2 % 2 ^ m

/-- The chunk exchange above the suffix: `(p, c₁, g, c₂) ↦ (p, c₂, g, c₁)`. -/
def swapTop (K g t : ℕ) : ℕ :=
  ((t / 2 ^ K / 2 ^ g / 2 ^ K * 2 ^ K + t % 2 ^ K) * 2 ^ g + t / 2 ^ K % 2 ^ g) * 2 ^ K +
    t / 2 ^ K / 2 ^ g % 2 ^ K

theorem moveOp_eq_onTop (m ρ : ℕ) (w : ℕ → γ) : moveOp m ρ w = onTop (2 ^ ρ) (moveTop m) w := rfl

theorem swapOp_eq_onTop (K g ρ : ℕ) (w : ℕ → γ) : swapOp K g ρ w = onTop (2 ^ ρ) (swapTop K g) w := rfl

theorem div_shift' {a e E : ℕ} (he : e < E) : (a * E + e) / E = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, zero_add]

theorem mod_shift' {a e E : ℕ} (he : e < E) : (a * E + e) % E = e := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

theorem onTop_comp {E : ℕ} (hE : 0 < E) (f g : ℕ → ℕ) (w : ℕ → γ) :
    onTop E f (onTop E g w) = onTop E (fun t => g (f t)) w := by
  funext y
  have he : y % E < E := Nat.mod_lt _ hE
  simp only [onTop]
  rw [div_shift' he, mod_shift' he]

theorem onTop_id {E : ℕ} (w : ℕ → γ) : onTop E id w = w := by
  funext y; simp only [onTop, id, Nat.div_add_mod']

theorem backTop_moveTop (m t : ℕ) : backTop m (moveTop m t) = t := by
  have hx : t % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
  have hj : t / 2 ^ m % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold backTop moveTop
  simp only [div_shift' hj, mod_shift' hj, div_shift' hx, mod_shift' hx, Nat.div_add_mod']

theorem moveTop_backTop (m t : ℕ) : moveTop m (backTop m t) = t := by
  have hx : t / 2 % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
  have hj : t % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold backTop moveTop
  simp only [div_shift' hj, mod_shift' hj, div_shift' hx, mod_shift' hx, Nat.div_add_mod']

theorem swapTop_swapTop (K g t : ℕ) : swapTop K g (swapTop K g t) = t := by
  have h1 : t % 2 ^ K < 2 ^ K := Nat.mod_lt _ (by positivity)
  have h2 : t / 2 ^ K % 2 ^ g < 2 ^ g := Nat.mod_lt _ (by positivity)
  have h3 : t / 2 ^ K / 2 ^ g % 2 ^ K < 2 ^ K := Nat.mod_lt _ (by positivity)
  have h4 : t / 2 ^ K / 2 ^ g / 2 ^ K * 2 ^ K + t % 2 ^ K < 2 ^ K * (t / 2 ^ K / 2 ^ g / 2 ^ K + 1) := by
    nlinarith
  unfold swapTop
  simp only [div_shift' h1, mod_shift' h1, div_shift' h2, mod_shift' h2, div_shift' h3, mod_shift' h3]
  simp only [Nat.div_add_mod']

/-- The inverse single-bit move: physical fields `(p, x, j, e)` read the old `(p, j, x, e)`. -/
def moveBackOp (m ρ : ℕ) (w : ℕ → γ) : ℕ → γ := onTop (2 ^ ρ) (backTop m) w

theorem moveBackOp_moveOp (m ρ : ℕ) (w : ℕ → γ) : moveBackOp m ρ (moveOp m ρ w) = w := by
  rw [moveBackOp, moveOp_eq_onTop, onTop_comp (by positivity)]
  simp only [moveTop_backTop]
  exact onTop_id w

theorem swapOp_swapOp (K g ρ : ℕ) (w : ℕ → γ) : swapOp K g ρ (swapOp K g ρ w) = w := by
  rw [swapOp_eq_onTop, swapOp_eq_onTop, onTop_comp (by positivity)]
  simp only [swapTop_swapTop]
  exact onTop_id w

/-- The inverse moves, in reverse order. -/
def runMovesBack : List (ℕ × ℕ) → (ℕ → γ) → ℕ → γ
  | [], w => w
  | q :: qs, w => moveBackOp q.1 q.2 (runMovesBack qs w)

theorem runMovesBack_runMoves : ∀ (qs : List (ℕ × ℕ)) (w : ℕ → γ), runMovesBack qs (runMoves qs w) = w
  | [], _ => rfl
  | q :: qs, w => by
    simp only [runMoves, runMovesBack, runMovesBack_runMoves qs, moveBackOp_moveOp]

/-- The exchanges in reverse order. -/
def runSwapsBack : List (ℕ × ℕ × ℕ) → (ℕ → γ) → ℕ → γ
  | [], w => w
  | q :: qs, w => swapOp q.1 q.2.1 q.2.2 (runSwapsBack qs w)

theorem runSwapsBack_runSwaps : ∀ (qs : List (ℕ × ℕ × ℕ)) (w : ℕ → γ), runSwapsBack qs (runSwaps qs w) = w
  | [], _ => rfl
  | q :: qs, w => by
    simp only [runSwaps, runSwapsBack, runSwapsBack_runSwaps qs, swapOp_swapOp]

/-- An address map above a suffix of `E` records acts on their flattened symbols as on the records,
with the suffix `E · R` (`R` symbols per record). -/
theorem onTop_flatten {E R : ℕ} (hR : 0 < R) (f : ℕ → ℕ) (F : ℕ → ℕ → γ) :
    onTop (E * R) f (fun i => F (i / R) (i % R)) = fun i => onTop E f (fun k => F k (i % R)) (i / R) := by
  funext i
  simp only [onTop]
  have hq : (f (i / (E * R)) * (E * R) + i % (E * R)) / R = f (i / R / E) * E + i / R % E := by
    rw [show f (i / (E * R)) * (E * R) = f (i / (E * R)) * E * R by ring, Nat.add_comm,
      Nat.add_mul_div_right _ _ hR, Nat.mod_mul_left_div_self, Nat.div_div_eq_div_mul, Nat.mul_comm R E]
    ring
  have hr : (f (i / (E * R)) * (E * R) + i % (E * R)) % R = i % R := by
    rw [show f (i / (E * R)) * (E * R) = f (i / (E * R)) * E * R by ring, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_mul_left_mod]
  rw [hq, hr]

end Payload

/-! ### The machines -/

section Machines

open Machine.RecursiveInterchangeRows (pack pack_val)

/-- The radix-2 digit move's inverse direction (`Machine.RadixDigitMoveBlockRows.unmove` with `Q = 2`,
`S = 2^m`) is the single-bit move above a suffix of size `E`. -/
theorem unmove_eq_onTop {a P m E : ℕ} (g : ℕ → Fin (a + 4)) (z : Fin (P * 2 * (2 ^ m * E))) :
    Machine.RadixDigitMoveBlockRows.unmove (P := P) (Q := 2) (S := 2 ^ m) (E := E) (fun i => g i.val) z =
      onTop E (moveTop m) g z.val := by
  simp only [Machine.RadixDigitMoveBlockRows.unmove, pack_val, onTop, moveTop, finProdFinEquiv, Equiv.coe_fn_symm_mk,
    Fin.coe_divNat, Fin.coe_modNat]
  congr 1
  rw [Nat.mod_mul_left_div_self, Nat.mod_mul_left_mod, Nat.div_div_eq_div_mul z.val E (2 ^ m),
    Nat.mul_comm E (2 ^ m)]

/-- The §4 interchange payload (`SwapPrim.swapList`) with two `K`-bit fields separated by `g` bits
is the chunk exchange above a suffix of size `B`. -/
theorem swapList_eq_onTop (P K g B : ℕ) (xs : List Bool) :
    SwapPrim.swapList P (2 ^ K) (2 ^ g) (2 ^ K) B xs =
      List.ofFn fun z : Fin (Machine.BinaryAdjacentWidthInterchange.volume P (2 ^ K) (2 ^ g) (2 ^ K) B) =>
        xs.getD (onTop B (swapTop K g) id z.val) false := by
  unfold SwapPrim.swapList
  congr 1
  funext z
  congr 1
  have hzv := congrArg Fin.val (Machine.BinaryAdjacentWidthInterchange.index_coordinates z)
  simp only [Machine.BinaryAdjacentWidthInterchange.index, pack_val] at hzv
  have h1 := (Machine.BinaryAdjacentWidthInterchange.coordinates z).2.1.isLt
  have h2 := (Machine.BinaryAdjacentWidthInterchange.coordinates z).2.2.1.isLt
  have h3 := (Machine.BinaryAdjacentWidthInterchange.coordinates z).2.2.2.1.isLt
  have h4 := (Machine.BinaryAdjacentWidthInterchange.coordinates z).2.2.2.2.isLt
  simp only [Machine.BinaryAdjacentWidthInterchange.transpose, Machine.BinaryAdjacentWidthInterchange.index, pack_val, id,
    onTop, swapTop]
  rw [← hzv]
  simp only [div_shift' h4, mod_shift' h4, div_shift' h3, mod_shift' h3, div_shift' h2, mod_shift' h2,
    div_shift' h1, mod_shift' h1]

end Machines

/-- `layoutOps_undo`: the exchanges in reverse order and then the inverse moves in reverse order
take the array stored in the paper's layout back to natural order. -/
theorem layoutOps_undo {r : ℕ} {β : Type*} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (z : ℕ → β) :
    runMovesBack (prefixParams 0 (prefixSlots ts ℓ K) (initOrder ts))
        (runSwapsBack ((selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0).map (exParams K))
          (fun y => z ((paperPerm hL).logi y))) =
      fun y => z (y % 2 ^ Nat.log 2 ts.prod) := by
  rw [← layoutOps_paper hL z, runSwapsBack_runSwaps, runMovesBack_runMoves]

end IntegerMultBounds.Schoenhage.LayoutArray
