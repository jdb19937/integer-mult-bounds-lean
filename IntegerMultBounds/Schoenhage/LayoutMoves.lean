module

public import IntegerMultBounds.Schoenhage.PaperRounds

/-! The layout moves of §6 as reorderings of slot names. A layout is the list
of slot names `(i, h)` in physical order, most significant first. A prefix
move takes one slot to the position just after the prefix already formed
(`moveAfter`); moving a list of slots in turn leaves them, in order, after the
prefix, followed by the other slots in their relative order (`movePrefix_eq`).
A chunk exchange swaps two blocks of a list of blocks (`swapBlocks`); scanning
the target positions left to right and exchanging the block found there with
the required one, when they differ, reaches any target arrangement of distinct
blocks with at most one exchange per position but the last (`selectBlocks_eq`,
`selectCount_le`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.LayoutMoves

variable {α : Type*} [DecidableEq α]

/-! ### Prefix moves -/

/-- Move `s` to position `k`, just after the first `k` entries. -/
def moveAfter (k : ℕ) (s : α) (ord : List α) : List α := ord.take k ++ s :: (ord.drop k).erase s

/-- Move the slots of `ss` in turn, each just after the prefix formed so far. -/
def movePrefix : ℕ → List α → List α → List α
  | _, [], ord => ord
  | k, s :: ss, ord => movePrefix (k + 1) ss (moveAfter k s ord)

theorem moveAfter_append (pre rest : List α) (s : α) :
    moveAfter pre.length s (pre ++ rest) = pre ++ s :: rest.erase s := by
  simp [moveAfter, List.take_append_of_le_length le_rfl]

/-- `movePrefix_eq`: moving distinct slots of the rest leaves them after the prefix, followed by
the other slots in their relative order. -/
theorem movePrefix_eq : ∀ (ss pre rest : List α), rest.Nodup → ss.Nodup → (∀ s ∈ ss, s ∈ rest) →
    movePrefix pre.length ss (pre ++ rest) = pre ++ ss ++ rest.filter (fun x => x ∉ ss)
  | [], pre, rest, _, _, _ => by simp [movePrefix]
  | s :: ss, pre, rest, hr, hss, hsub => by
    have hs : s ∉ ss := (List.nodup_cons.mp hss).1
    simp only [movePrefix]
    rw [moveAfter_append]
    have e : pre ++ s :: rest.erase s = (pre ++ [s]) ++ rest.erase s := by simp
    rw [e, show pre.length + 1 = (pre ++ [s]).length by simp]
    rw [movePrefix_eq ss (pre ++ [s]) (rest.erase s) (hr.erase s) (List.nodup_cons.mp hss).2
      (fun x hx => (List.mem_erase_of_ne (fun e => hs (by rw [← e]; exact hx))).mpr (hsub x (by simp [hx])))]
    rw [hr.erase_eq_filter, List.filter_filter]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    congr 3
    apply List.filter_congr
    intro x _
    by_cases h1 : x = s <;> by_cases h2 : x ∈ ss <;> simp [h1, h2]

/-! ### Chunk exchanges -/

/-- The exchanges of the left-to-right scan on positions `k, k+1, …`: at position `k`, when the
block there is not the required one, exchange it with the position holding the required one.
The arrangement is `tgt ∘ σ`: position `x` holds the target's block `σ x`. -/
def selectSwaps {m : ℕ} (σ : Equiv.Perm (Fin m)) (k : ℕ) : List (Fin m × Fin m) :=
  if hk : k < m then
    if σ ⟨k, hk⟩ = ⟨k, hk⟩ then selectSwaps σ (k + 1)
    else (⟨k, hk⟩, σ.symm ⟨k, hk⟩) ::
      selectSwaps (σ * Equiv.swap ⟨k, hk⟩ (σ.symm ⟨k, hk⟩)) (k + 1)
  else []
termination_by m - k

/-- Apply a list of exchanges to an arrangement. -/
def applySwaps {m : ℕ} : List (Fin m × Fin m) → Equiv.Perm (Fin m) → Equiv.Perm (Fin m)
  | [], σ => σ
  | e :: es, σ => applySwaps es (σ * Equiv.swap e.1 e.2)

/-- After the scan from position `k`, an arrangement fixing every position below `k` is the target. -/
theorem applySwaps_selectSwaps {m : ℕ} : ∀ (σ : Equiv.Perm (Fin m)) (k : ℕ),
    (∀ x : Fin m, x.val < k → σ x = x) → applySwaps (selectSwaps σ k) σ = 1 := by
  intro σ k hfix
  induction h : m - k generalizing σ k with
  | zero =>
    rw [selectSwaps, dite_eq_right_of_eq_false (by simp; omega), applySwaps]
    ext x; simp only [Equiv.Perm.coe_one, id_eq]
    exact congrArg Fin.val (hfix x (by omega))
  | succ n ih =>
    have hk : k < m := by omega
    rw [selectSwaps, dite_eq_left_of_eq_true (by simp [hk])]
    split_ifs with hσ
    · exact ih σ (k + 1) (fun x hx => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
        · exact hfix x hx
        · have : x = ⟨k, hk⟩ := Fin.ext hx
          rw [this]; exact hσ) (by omega)
    · simp only [applySwaps]
      set v := σ.symm ⟨k, hk⟩
      have hv : σ v = ⟨k, hk⟩ := by simp [v]
      have hvk : k ≤ v.val := by
        by_contra hc
        have := hfix v (by omega)
        rw [hv] at this
        exact absurd (congrArg Fin.val this) (by simp; omega)
      apply ih _ (k + 1) _ (by omega)
      intro x hx
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
      · have hxk : x ≠ ⟨k, hk⟩ := fun e => by rw [e] at hx; simp at hx
        have hxv : x ≠ v := fun e => by rw [e] at hx; omega
        rw [Equiv.swap_apply_of_ne_of_ne hxk hxv]
        exact hfix x hx
      · have : x = ⟨k, hk⟩ := Fin.ext hx
        rw [this, Equiv.swap_apply_left, hv]

/-- The scan from position `k` uses at most one exchange per position from `k` to `m - 2`. -/
theorem selectSwaps_length_le {m : ℕ} : ∀ (σ : Equiv.Perm (Fin m)) (k : ℕ),
    (∀ x : Fin m, x.val < k → σ x = x) → (selectSwaps σ k).length ≤ m - 1 - k := by
  intro σ k hfix
  induction h : m - k generalizing σ k with
  | zero => rw [selectSwaps, dite_eq_right_of_eq_false (by simp; omega)]; simp
  | succ n ih =>
    have hk : k < m := by omega
    rw [selectSwaps, dite_eq_left_of_eq_true (by simp [hk])]
    split_ifs with hσ
    · have := ih σ (k + 1) (fun x hx => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
        · exact hfix x hx
        · have : x = ⟨k, hk⟩ := Fin.ext hx
          rw [this]; exact hσ) (by omega)
      omega
    · -- the last position is never exchanged: a permutation fixing all others fixes it
      have hlast : k + 1 < m := by
        by_contra hc
        apply hσ
        have hkm : k = m - 1 := by omega
        set y := σ.symm ⟨k, hk⟩
        have hy : σ y = ⟨k, hk⟩ := by simp [y]
        have hyk : y = ⟨k, hk⟩ := by
          by_contra hne
          have hylt : y.val < k := by
            have := y.isLt
            have : y.val ≠ k := fun e => hne (Fin.ext e)
            omega
          have := hfix y hylt
          rw [hy] at this
          exact hne this.symm
        rw [← hyk, hy, hyk]
      simp only [List.length_cons]
      set v := σ.symm ⟨k, hk⟩
      have hv : σ v = ⟨k, hk⟩ := by simp [v]
      have hvk : k ≤ v.val := by
        by_contra hc
        have := hfix v (by omega)
        rw [hv] at this
        exact absurd (congrArg Fin.val this) (by simp; omega)
      have := ih (σ * Equiv.swap ⟨k, hk⟩ v) (k + 1) (fun x hx => by
        rw [Equiv.Perm.mul_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
        · have hxk : x ≠ ⟨k, hk⟩ := fun e => by rw [e] at hx; simp at hx
          have hxv : x ≠ v := fun e => by rw [e] at hx; omega
          rw [Equiv.swap_apply_of_ne_of_ne hxk hxv]
          exact hfix x hx
        · have : x = ⟨k, hk⟩ := Fin.ext hx
          rw [this, Equiv.swap_apply_left, hv]) (by omega)
      omega

/-- `selectBlocks_eq`: the scan sorts any arrangement into the target with at most `m - 1` exchanges. -/
theorem selectBlocks_eq {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    applySwaps (selectSwaps σ 0) σ = 1 ∧ (selectSwaps σ 0).length ≤ m - 1 :=
  ⟨applySwaps_selectSwaps σ 0 (fun _ h => absurd h (Nat.not_lt_zero _)),
    by simpa using selectSwaps_length_le σ 0 (fun _ h => absurd h (Nat.not_lt_zero _))⟩

/-! ### The paper's slot orders -/

/-- The slots `(i, lo + len - 1), …, (i, lo)` of axis `i`, from the top down. -/
def slotsDesc (i lo len : ℕ) : List (ℕ × ℕ) := (List.range len).reverse.map fun h => (i, lo + h)

theorem slotsDesc_split (i lo a c : ℕ) :
    slotsDesc i lo (c + a) = slotsDesc i (lo + c) a ++ slotsDesc i lo c := by
  simp only [slotsDesc, List.range_add, List.reverse_append, List.map_append, List.map_reverse,
    List.map_map]
  congr 2
  apply List.map_congr_left
  intro h _
  simp only [Function.comp_apply]
  ring_nf

theorem mem_slotsDesc {i lo len : ℕ} {x : ℕ × ℕ} :
    x ∈ slotsDesc i lo len ↔ x.1 = i ∧ lo ≤ x.2 ∧ x.2 < lo + len := by
  obtain ⟨a, h⟩ := x
  simp only [slotsDesc, List.mem_map, List.mem_reverse, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨h', hh', rfl, rfl⟩; omega
  · rintro ⟨rfl, h1, h2⟩; exact ⟨h - lo, by omega, rfl, by omega⟩

theorem slotsDesc_nodup (i lo len : ℕ) : (slotsDesc i lo len).Nodup := by
  unfold slotsDesc
  exact List.Nodup.map (fun a b e => by simpa using e) (List.nodup_reverse.mpr List.nodup_range)

/-- The descending chunks of one axis concatenate to its descending slots. -/
theorem flatMap_chunks (i b K : ℕ) : ∀ q : ℕ,
    (List.range q).flatMap (fun j => slotsDesc i (b + (q - 1 - j) * K) K) = slotsDesc i b (q * K)
  | 0 => by simp [slotsDesc]
  | q + 1 => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have e : (List.range q).flatMap (fun j => slotsDesc i (b + (q + 1 - 1 - (j + 1)) * K) K) =
        (List.range q).flatMap (fun j => slotsDesc i (b + (q - 1 - j) * K) K) := by
      congr 1; funext j; congr 3; omega
    simp only [Nat.succ_eq_add_one] at e ⊢
    rw [e, flatMap_chunks i b K q, show (q + 1) * K = q * K + K by ring, slotsDesc_split]
    simp

variable (ts : List ℕ) (ℓ K : ℕ)

/-- The initial order: axis by axis, each from its top slot down. -/
def initOrder : List (ℕ × ℕ) := (List.range ts.length).flatMap fun i => slotsDesc i 0 (axLen ts i)

/-- The top slots `ℓ - 1` of the long axes, in axis order. -/
def topSlots : List (ℕ × ℕ) := (longs ts ℓ).map fun i => (i, ℓ - 1)

/-- The bottom slots `h < b`, from `h = b - 1` down, each in axis order. -/
def bottomSlots : List (ℕ × ℕ) :=
  (List.range ((ℓ - 1) % K)).reverse.flatMap fun h => (List.range ts.length).map fun i => (i, h)

/-- The slots moved to the prefix, in order. -/
def prefixSlots : List (ℕ × ℕ) := topSlots ts ℓ ++ bottomSlots ts ℓ K

/-- Chunk `j` (from the top) of axis `i`: slots `b + (q-1-j)K + K - 1, …, b + (q-1-j)K`. -/
def chunk (i j : ℕ) : List (ℕ × ℕ) :=
  slotsDesc i ((ℓ - 1) % K + ((ℓ - 1) / K - 1 - j) * K) K

/-- The chunks axis by axis. -/
def axisMajor : List (ℕ × ℕ) :=
  (List.range ts.length).flatMap fun i => (List.range ((ℓ - 1) / K)).flatMap fun j => chunk ℓ K i j

/-- The chunks chunk by chunk: `(1,1), (2,1), …, (D,1), (1,2), …, (D,q)`. -/
def chunkMajor : List (ℕ × ℕ) :=
  (List.range ((ℓ - 1) / K)).flatMap fun j => (List.range ts.length).flatMap fun i => chunk ℓ K i j

theorem axis_chunks (i : ℕ) :
    ((List.range ((ℓ - 1) / K)).flatMap fun j => chunk ℓ K i j) =
      slotsDesc i ((ℓ - 1) % K) ((ℓ - 1) / K * K) :=
  flatMap_chunks i ((ℓ - 1) % K) K ((ℓ - 1) / K)

variable {ts ℓ K}

theorem mem_topSlots {x : ℕ × ℕ} : x ∈ topSlots ts ℓ ↔ x.1 ∈ longs ts ℓ ∧ x.2 = ℓ - 1 := by
  obtain ⟨i, h⟩ := x
  simp only [topSlots, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩

theorem mem_bottomSlots {x : ℕ × ℕ} : x ∈ bottomSlots ts ℓ K ↔ x.1 < ts.length ∧ x.2 < (ℓ - 1) % K := by
  obtain ⟨i, h⟩ := x
  simp only [bottomSlots, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨h', hh', j, hj, rfl, rfl⟩; exact ⟨hj, hh'⟩
  · rintro ⟨hi, hh⟩; exact ⟨h, hh, i, hi, rfl, rfl⟩

theorem mem_longs {i : ℕ} : i ∈ longs ts ℓ ↔ i < ts.length ∧ axLen ts i = ℓ := by
  simp [longs]

/-- Removing the prefix slots from an axis leaves its chunk slots. -/
theorem axis_filter {i : ℕ} (hi : i < ts.length) (hax : axLen ts i = ℓ - 1 ∨ axLen ts i = ℓ)
    (hℓ : 1 ≤ ℓ) (_hK : 1 ≤ K) :
    (slotsDesc i 0 (axLen ts i)).filter (fun x => x ∉ prefixSlots ts ℓ K) =
      slotsDesc i ((ℓ - 1) % K) ((ℓ - 1) / K * K) := by
  set b := (ℓ - 1) % K
  set qK := (ℓ - 1) / K * K
  have hbq : b + qK = ℓ - 1 := by
    simp only [b, qK]; rw [mul_comm]; exact Nat.mod_add_div _ _
  have hmid : (slotsDesc i b qK).filter (fun x => x ∉ prefixSlots ts ℓ K) = slotsDesc i b qK := by
    rw [List.filter_eq_self]
    intro x hx
    rw [mem_slotsDesc] at hx
    simp only [prefixSlots, List.mem_append, mem_topSlots, mem_bottomSlots, decide_eq_true_eq]
    omega
  have hbot : (slotsDesc i 0 b).filter (fun x => x ∉ prefixSlots ts ℓ K) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [mem_slotsDesc] at hx
    simp only [prefixSlots, List.mem_append, mem_bottomSlots, decide_eq_true_eq, not_not]
    right; omega
  have hlow : slotsDesc i 0 (b + qK) = slotsDesc i b qK ++ slotsDesc i 0 b := by
    rw [slotsDesc_split, zero_add]
  rcases hax with e | e
  · rw [e, ← hbq, hlow, List.filter_append, hmid, hbot, List.append_nil]
  · have htop : (slotsDesc i (b + qK) 1).filter (fun x => x ∉ prefixSlots ts ℓ K) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      rw [mem_slotsDesc] at hx
      simp only [prefixSlots, List.mem_append, mem_topSlots, mem_longs, decide_eq_true_eq, not_not]
      left; refine ⟨⟨by rw [hx.1]; exact hi, by rw [hx.1]; exact e⟩, by omega⟩
    have hsplit : slotsDesc i 0 ℓ = slotsDesc i (b + qK) 1 ++ slotsDesc i 0 (b + qK) := by
      have := slotsDesc_split i 0 1 (b + qK)
      rw [zero_add] at this
      rw [← this]; congr 1; omega
    rw [e, hsplit, List.filter_append, htop, List.nil_append, hlow, List.filter_append, hmid, hbot,
      List.append_nil]

theorem mem_initOrder {x : ℕ × ℕ} : x ∈ initOrder ts ↔ x.1 < ts.length ∧ x.2 < axLen ts x.1 := by
  obtain ⟨i, h⟩ := x
  simp only [initOrder, List.mem_flatMap, List.mem_range, mem_slotsDesc]
  constructor
  · rintro ⟨j, hj, rfl, -, hh⟩; exact ⟨hj, by simpa using hh⟩
  · rintro ⟨hi, hh⟩; exact ⟨i, hi, rfl, Nat.zero_le _, by simpa using hh⟩

theorem initOrder_nodup : (initOrder ts).Nodup := by
  unfold initOrder
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => slotsDesc_nodup _ _ _, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro i j _ _ hij x hx hy
  rw [mem_slotsDesc] at hx hy
  exact hij (hx.1.symm.trans hy.1)

theorem prefixSlots_nodup (hL : LayoutOK r ts ℓ K) : (prefixSlots ts ℓ K).Nodup := by
  have hK := hL.2.2.1
  unfold prefixSlots
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact List.Nodup.map (fun a b e => by simpa using e) ((List.nodup_range).filter _)
  · unfold bottomSlots
    rw [List.nodup_flatMap]
    refine ⟨fun h _ => List.Nodup.map (fun a b e => by simpa using e) List.nodup_range, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_reverse.mpr List.nodup_range)
    intro h h' _ _ hne x hx hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, e⟩ := hy
    exact hne (Prod.mk.inj e).2.symm
  · intro x hx y hy hxy
    subst hxy
    rw [mem_topSlots] at hx
    rw [mem_bottomSlots] at hy
    have := Nat.mod_le (ℓ - 1) K
    omega

theorem prefixSlots_sub (hL : LayoutOK r ts ℓ K) : ∀ x ∈ prefixSlots ts ℓ K, x ∈ initOrder ts := by
  intro x hx
  rw [mem_initOrder]
  simp only [prefixSlots, List.mem_append, mem_topSlots, mem_longs, mem_bottomSlots] at hx
  rcases hx with ⟨⟨hi, hax⟩, hh⟩ | ⟨hi, hh⟩
  · refine ⟨hi, ?_⟩; rw [hax, hh]; have := hL.2.2.2; omega
  · refine ⟨hi, ?_⟩
    have := Nat.mod_le (ℓ - 1) K
    rcases hL.2.1 x.1 hi with e | e <;> rw [e] <;> omega

/-- Removing the prefix slots from the initial order leaves the chunks axis by axis. -/
theorem initOrder_filter (hL : LayoutOK r ts ℓ K) :
    (initOrder ts).filter (fun x => x ∉ prefixSlots ts ℓ K) = axisMajor ts ℓ K := by
  unfold initOrder axisMajor
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [axis_filter hi (hL.2.1 i hi) hL.2.2.2 hL.2.2.1, axis_chunks]

/-- The prefix moves of §6 turn the initial order into the prefix slots followed by the chunks
axis by axis. -/
theorem movePrefix_paper (hL : LayoutOK r ts ℓ K) :
    movePrefix 0 (prefixSlots ts ℓ K) (initOrder ts) = prefixSlots ts ℓ K ++ axisMajor ts ℓ K := by
  have := movePrefix_eq (prefixSlots ts ℓ K) [] (initOrder ts) initOrder_nodup (prefixSlots_nodup hL)
    (prefixSlots_sub hL)
  rw [← initOrder_filter hL]
  simpa using this

/-! ### Chunk arrangements -/

theorem flatMap_range_mul {γ : Type*} (g : ℕ → ℕ → List γ) (b : ℕ) : ∀ a : ℕ,
    ((List.range a).flatMap fun j => (List.range b).flatMap fun i => g i j) =
      ((List.range (a * b)).map fun y => g (y % b) (y / b)).flatten
  | 0 => by simp
  | a + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_mul g b a, Nat.succ_mul, List.range_add,
      List.map_append, List.flatten_append, List.map_map]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    show ((List.range b).map fun i => g i a).flatten = _
    congr 1
    refine List.map_congr_left (fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    congr 1
    · rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi']
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi', zero_add]

variable (ts ℓ K)

/-- The chunk at chunk-major position `y`. -/
def blk (y : ℕ) : List (ℕ × ℕ) := chunk ℓ K (y % ts.length) (y / ts.length)

/-- An arrangement of the chunks: position `x` holds the chunk at chunk-major position `σ x`. -/
def arrange (σ : Equiv.Perm (Fin ((ℓ - 1) / K * ts.length))) : List (ℕ × ℕ) :=
  ((List.finRange _).map fun x => blk ts ℓ K (σ x)).flatten

/-- The permutation taking axis-major positions to chunk-major ones. -/
def axisToChunk (q D : ℕ) : Equiv.Perm (Fin (q * D)) :=
  (finCongr (Nat.mul_comm q D)).trans
    (finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv))

theorem axisToChunk_val (q D : ℕ) (x : Fin (q * D)) :
    (axisToChunk q D x).val = x.val % q * D + x.val / q := by
  simp [axisToChunk, finProdFinEquiv, Fin.divNat, Fin.modNat]
  ring

theorem map_finRange_eq {γ : Type*} (m : ℕ) (f : ℕ → γ) :
    (List.finRange m).map (fun x => f x.val) = (List.range m).map f := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

variable {ts ℓ K}

theorem chunkMajor_eq_arrange : chunkMajor ts ℓ K = arrange ts ℓ K 1 := by
  rw [chunkMajor, flatMap_range_mul (fun i j => chunk ℓ K i j) ts.length, arrange]
  congr 1
  rw [← map_finRange_eq]
  rfl

theorem chunkIdx {q D x : ℕ} (hx : x < q * D) :
    (x % q * D + x / q) % D = x / q ∧ (x % q * D + x / q) / D = x % q := by
  have hq : 0 < q := by rcases Nat.eq_zero_or_pos q with h | h <;> simp_all
  have hD : x / q < D := by rw [Nat.div_lt_iff_lt_mul hq]; linarith [Nat.mul_comm q D]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hD]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hD), Nat.div_eq_of_lt hD,
      zero_add]

theorem axisMajor_eq_arrange :
    axisMajor ts ℓ K = arrange ts ℓ K (axisToChunk ((ℓ - 1) / K) ts.length) := by
  rw [axisMajor, flatMap_range_mul (fun j i => chunk ℓ K i j) ((ℓ - 1) / K), arrange]
  congr 1
  symm
  rw [List.map_congr_left (g := fun x : Fin ((ℓ - 1) / K * ts.length) =>
      (fun y => chunk ℓ K (y / ((ℓ - 1) / K)) (y % ((ℓ - 1) / K))) x.val) (fun x _ => ?_),
    Nat.mul_comm ts.length]
  · exact map_finRange_eq ((ℓ - 1) / K * ts.length) (fun y => chunk ℓ K (y / ((ℓ - 1) / K)) (y % ((ℓ - 1) / K)))
  · simp only [blk, axisToChunk_val]
    obtain ⟨h1, h2⟩ := chunkIdx x.isLt
    rw [h1, h2]

/-- One exchange of the chunks at positions `u` and `v`. -/
theorem arrange_swap (σ : Equiv.Perm (Fin ((ℓ - 1) / K * ts.length))) (u v : Fin ((ℓ - 1) / K * ts.length)) :
    arrange ts ℓ K (σ * Equiv.swap u v) =
      ((List.finRange _).map fun x => blk ts ℓ K (σ (Equiv.swap u v x))).flatten := rfl

/-- `chunkExchanges_paper`: the left-to-right exchanges turn the chunks axis by axis into the chunks
chunk by chunk, with at most `Dq - 1` exchanges. -/
theorem chunkExchanges_paper :
    arrange ts ℓ K (applySwaps (selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0)
        (axisToChunk ((ℓ - 1) / K) ts.length)) = chunkMajor ts ℓ K ∧
      (selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0).length ≤ (ℓ - 1) / K * ts.length - 1 := by
  obtain ⟨h1, h2⟩ := selectBlocks_eq (axisToChunk ((ℓ - 1) / K) ts.length)
  exact ⟨by rw [h1, chunkMajor_eq_arrange], h2⟩

/-! ### The final order is the paper's layout -/

theorem getElem_flatMap_uniform {γ δ : Type*} (f : γ → List δ) {R : ℕ} (hR : ∀ x, (f x).length = R) :
    ∀ (xs : List γ) (k j : ℕ) (hk : k < xs.length) (hj : j < R) (h : k * R + j < (xs.flatMap f).length),
      (xs.flatMap f)[k * R + j] = (f xs[k])[j]'(by rw [hR]; exact hj)
  | [], k, _, hk, _, _ => absurd hk (by simp)
  | x :: xs, 0, j, _, hj, h => by
    simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
    rw [List.getElem_append_left (by rw [hR]; exact hj)]
  | x :: xs, k + 1, j, hk, hj, h => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    have hle : (f x).length ≤ (k + 1) * R + j := by rw [hR]; nlinarith
    rw [List.getElem_append_right hle]
    have e : (k + 1) * R + j - (f x).length = k * R + j := by rw [hR, Nat.succ_mul]; omega
    simp only [e]
    exact getElem_flatMap_uniform f hR xs k j (by simpa using hk) hj _

theorem length_slotsDesc (i lo len : ℕ) : (slotsDesc i lo len).length = len := by simp [slotsDesc]

theorem getElem_slotsDesc (i lo len t : ℕ) (ht : t < (slotsDesc i lo len).length) :
    (slotsDesc i lo len)[t] = (i, lo + (len - 1 - t)) := by
  simp [slotsDesc]

theorem length_topSlots : (topSlots ts ℓ).length = (longs ts ℓ).length := by simp [topSlots]

theorem length_bottomSlots : (bottomSlots ts ℓ K).length = (ℓ - 1) % K * ts.length := by
  simp [bottomSlots, List.length_flatMap]

theorem chunkMajor_flatMap :
    chunkMajor ts ℓ K = (List.range ((ℓ - 1) / K * ts.length)).flatMap (blk ts ℓ K) := by
  rw [chunkMajor, flatMap_range_mul (fun i j => chunk ℓ K i j) ts.length]
  rfl

theorem length_chunkMajor (_hK : 1 ≤ K) :
    (chunkMajor ts ℓ K).length = (ℓ - 1) / K * ts.length * K := by
  rw [chunkMajor_flatMap, List.length_flatMap]
  simp [blk, chunk, length_slotsDesc]

theorem getElem_idx {γ : Type*} (l : List γ) {a b : ℕ} (ha : a < l.length) (hb : b < l.length) (e : a = b) :
    l[a] = l[b] := by subst e; rfl

theorem length_flatMap_const {γ δ : Type*} (f : γ → List δ) {R : ℕ} (hR : ∀ x, (f x).length = R)
    (xs : List γ) : (xs.flatMap f).length = xs.length * R := by
  rw [List.length_flatMap]; simp only [hR, List.map_const', List.sum_replicate, smul_eq_mul]

/-- Entry `m` of a concatenation of blocks of length `R`. -/
theorem getElem_flatMap_div {γ δ : Type*} (f : γ → List δ) {R : ℕ} (hR : ∀ x, (f x).length = R)
    (xs : List γ) (m : ℕ) (h : m < (xs.flatMap f).length) (hk : m / R < xs.length)
    (hj : m % R < (f xs[m / R]).length) :
    (xs.flatMap f)[m] = (f xs[m / R])[m % R] := by
  have hR0 : 0 < R := Nat.pos_of_ne_zero fun h0 => by
    rw [length_flatMap_const f hR, h0, mul_zero] at h; exact Nat.not_lt_zero _ h
  have e : m = m / R * R + m % R := (Nat.div_add_mod' m R).symm
  rw [getElem_idx _ h (by rw [← e]; exact h) e]
  exact getElem_flatMap_uniform f hR xs (m / R) (m % R) hk (Nat.mod_lt _ hR0) _

theorem getElem_bottomSlots (m : ℕ) (hm : m < (bottomSlots ts ℓ K).length) :
    (bottomSlots ts ℓ K)[m] = (m % ts.length, (ℓ - 1) % K - 1 - m / ts.length) := by
  have hD : 0 < ts.length := Nat.pos_of_ne_zero fun h0 => by
    rw [length_bottomSlots, h0, mul_zero] at hm; exact Nat.not_lt_zero _ hm
  have hm' := hm
  rw [length_bottomSlots] at hm'
  have hmb : m / ts.length < (ℓ - 1) % K := by rw [Nat.div_lt_iff_lt_mul hD]; exact hm'
  unfold bottomSlots at hm ⊢
  rw [getElem_flatMap_div (fun h => (List.range ts.length).map fun i => (i, h)) (R := ts.length)
    (fun _ => by simp) _ m hm (by simpa using hmb) (by simpa using Nat.mod_lt _ hD)]
  simp

theorem getElem_chunkMajor (hK : 1 ≤ K) (m : ℕ) (hm : m < (chunkMajor ts ℓ K).length) :
    (chunkMajor ts ℓ K)[m] =
      ((m / K) % ts.length,
        (ℓ - 1) % K + ((ℓ - 1) / K - 1 - m / K / ts.length) * K + (K - 1 - m % K)) := by
  have hlen := length_chunkMajor (ts := ts) (ℓ := ℓ) hK
  have hmK : m / K < (ℓ - 1) / K * ts.length := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [hlen] at hm; exact hm
  simp only [chunkMajor_flatMap]
  rw [getElem_flatMap_div (blk ts ℓ K) (R := K) (fun y => by simp [blk, chunk, length_slotsDesc]) _ m
    (by rw [← chunkMajor_flatMap]; exact hm) (by simpa using hmK)
    (by simp [blk, chunk, length_slotsDesc]; exact Nat.mod_lt _ (by omega))]
  simp [blk, chunk, getElem_slotsDesc]

theorem divmod_add {a c K : ℕ} (hc : c < K) : (a * K + c) / K = a ∧ (a * K + c) % K = c := by
  have hK : 0 < K := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hc, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- Reverse a mixed-radix position: `(A K - 1) - (y K + t) = (A - 1 - y) K + (K - 1 - t)`. -/
theorem rev_split {A K y t : ℕ} (hy : y < A) (ht : t < K) :
    A * K - 1 - (y * K + t) = (A - 1 - y) * K + (K - 1 - t) := by
  have h1 : (y + 1) * K ≤ A * K := Nat.mul_le_mul_right K (by omega)
  rw [Nat.sub_mul, Nat.sub_mul, one_mul]
  rw [Nat.add_mul, one_mul] at h1
  omega

theorem paperSlot_chunk {Q : ℕ} (hQ : Q < ts.length * ((ℓ - 1) / K) * K) :
    paperSlot ts ℓ K Q = (ts.length - 1 - Q / K % ts.length,
      (ℓ - 1) % K + Q / K / ts.length * K + Q % K) := by
  rw [paperSlot, ite_eq_left hQ]

theorem paperSlot_bottom {Q : ℕ} (h1 : ts.length * ((ℓ - 1) / K) * K ≤ Q)
    (h2 : Q < ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K)) :
    paperSlot ts ℓ K Q = (ts.length - 1 - (Q - ts.length * ((ℓ - 1) / K) * K) % ts.length,
      (Q - ts.length * ((ℓ - 1) / K) * K) / ts.length) := by
  rw [paperSlot, ite_eq_right (by omega), ite_eq_left h2]

theorem paperSlot_top {Q : ℕ} (h1 : ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) ≤ Q) :
    paperSlot ts ℓ K Q = ((longs ts ℓ).getD ((longs ts ℓ).length - 1 -
      (Q - ts.length * ((ℓ - 1) / K) * K - ts.length * ((ℓ - 1) % K))) 0, ℓ - 1) := by
  rw [paperSlot, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- `paper_order`: the prefix slots followed by the chunks chunk by chunk are the paper's layout,
most significant bit first: entry `k` is the slot of physical bit `n - 1 - k`. -/
theorem paper_order (hL : LayoutOK r ts ℓ K) :
    prefixSlots ts ℓ K ++ chunkMajor ts ℓ K =
      (List.range (Nat.log 2 ts.prod)).reverse.map (paperSlot ts ℓ K) := by
  have hK : 1 ≤ K := hL.2.2.1
  have hn := log_prod_layout hL
  generalize hD : ts.length = D at hn
  generalize hq : (ℓ - 1) / K = q at hn
  generalize hb : (ℓ - 1) % K = b at hn
  generalize hLg : (longs ts ℓ).length = Lg at hn
  generalize hN : D * q * K = N at hn
  generalize hB : D * b = Bt at hn
  have hlenT : (topSlots ts ℓ).length = Lg := by rw [length_topSlots, hLg]
  have hlenB : (bottomSlots ts ℓ K).length = Bt := by rw [length_bottomSlots, hb, hD, ← hB, Nat.mul_comm]
  have hlenC : (chunkMajor ts ℓ K).length = N := by
    rw [length_chunkMajor hK, hq, hD, ← hN]; ring
  apply List.ext_getElem
  · simp only [List.length_append, prefixSlots, hlenT, hlenB, hlenC, List.length_map, List.length_reverse,
      List.length_range, hn]; ring
  intro k hk1 hk2
  simp only [List.length_append, prefixSlots, hlenT, hlenB, hlenC] at hk1
  rw [List.getElem_map, List.getElem_reverse, List.getElem_range]
  simp only [List.length_range, hn]
  simp only [prefixSlots, List.append_assoc, List.getElem_append, hlenT, hlenB]
  by_cases htop : k < Lg
  · -- a top slot
    rw [dite_eq_left_of_eq_true (eq_true htop)]
    simp only [topSlots, List.getElem_map]
    rw [paperSlot_top (by rw [hD, hq, hb, hN, hB]; omega), hD, hq, hb, hN, hB]
    congr 1
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact getElem_idx _ _ _ (by omega)
  rw [dite_eq_right_of_eq_false (eq_false htop)]
  by_cases hbot : k - Lg < Bt
  · -- a bottom slot
    rw [dite_eq_left_of_eq_true (eq_true hbot), getElem_bottomSlots, hD, hb]
    have hDpos : 0 < D := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hB; omega
    set m := k - Lg with hm
    have hu : m / D < b := by rw [Nat.div_lt_iff_lt_mul hDpos, Nat.mul_comm, hB]; exact hbot
    have hv : m % D < D := Nat.mod_lt _ hDpos
    have hmuv : m = m / D * D + m % D := (Nat.div_add_mod' m D).symm
    have hrev := rev_split (A := b) (K := D) hu hv
    rw [← hmuv, Nat.mul_comm b D, hB] at hrev
    rw [paperSlot_bottom (by rw [hD, hq, hN]; omega) (by rw [hD, hq, hb, hN, hB]; omega), hD, hq, hN]
    have hQ : N + Bt + Lg - 1 - k - N = (b - 1 - m / D) * D + (D - 1 - m % D) := by rw [← hrev]; omega
    rw [hQ, (divmod_add (by omega)).1, (divmod_add (by omega)).2]
    congr 1; omega
  · -- a chunk slot
    rw [dite_eq_right_of_eq_false (eq_false hbot), getElem_chunkMajor hK, hD, hq, hb]
    have hDpos : 0 < D := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul, zero_mul] at hN; omega
    set m := k - Lg - Bt with hm
    have hmN : m < N := by omega
    have hy : m / K < q * D := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [show q * D * K = N by rw [← hN]; ring]; exact hmN
    have ht : m % K < K := Nat.mod_lt _ (by omega)
    have hmyt : m = m / K * K + m % K := (Nat.div_add_mod' m K).symm
    have hj : m / K / D < q := by rw [Nat.div_lt_iff_lt_mul hDpos]; exact hy
    have hi : m / K % D < D := Nat.mod_lt _ hDpos
    have hyji : m / K = m / K / D * D + m / K % D := (Nat.div_add_mod' _ D).symm
    have hrev := rev_split (A := q * D) (K := K) hy ht
    rw [← hmyt, show q * D * K = N by rw [← hN]; ring] at hrev
    have hY := rev_split (A := q) (K := D) hj hi
    rw [← hyji] at hY
    rw [paperSlot_chunk (by rw [hD, hq, hN]; omega), hD, hb]
    have hQ : N + Bt + Lg - 1 - k = (q * D - 1 - m / K) * K + (K - 1 - m % K) := by rw [← hrev]; omega
    rw [hQ, (divmod_add (by omega)).1, (divmod_add (by omega)).2, hY, (divmod_add (by omega)).1,
      (divmod_add (by omega)).2]
    congr 1
    omega

/-- `layout_moves_eq`: the §6 layout moves reach the paper's layout. Moving the prefix slots in
turn and then exchanging chunks by the left-to-right scan turns the initial order (axis by axis,
top slot first) into the paper's order of physical bits, most significant first; there are
`Lg + bD` prefix moves and at most `Dq - 1` chunk exchanges. -/
theorem layout_moves_eq (hL : LayoutOK r ts ℓ K) :
    movePrefix 0 (prefixSlots ts ℓ K) (initOrder ts) =
        prefixSlots ts ℓ K ++ arrange ts ℓ K (axisToChunk ((ℓ - 1) / K) ts.length) ∧
      prefixSlots ts ℓ K ++ arrange ts ℓ K (applySwaps (selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0)
        (axisToChunk ((ℓ - 1) / K) ts.length)) =
        (List.range (Nat.log 2 ts.prod)).reverse.map (paperSlot ts ℓ K) ∧
      (prefixSlots ts ℓ K).length = (longs ts ℓ).length + (ℓ - 1) % K * ts.length ∧
      (selectSwaps (axisToChunk ((ℓ - 1) / K) ts.length) 0).length ≤ (ℓ - 1) / K * ts.length - 1 := by
  obtain ⟨hex, hcount⟩ := chunkExchanges_paper (ts := ts) (ℓ := ℓ) (K := K)
  refine ⟨by rw [movePrefix_paper hL, axisMajor_eq_arrange], by rw [hex, paper_order hL], ?_, hcount⟩
  rw [prefixSlots, List.length_append, length_topSlots, length_bottomSlots]

end IntegerMultBounds.Schoenhage.LayoutMoves
