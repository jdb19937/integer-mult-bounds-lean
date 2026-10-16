module

public import IntegerMultBounds.Schoenhage.LayoutMachines

/-! The §6 layout script in closed form, ready to be written on tapes. The prefix
moves of `layoutMoves` take the slots of `prefixSlots` in turn: the top slot of
the `k`-th long axis `i` sits behind `i (ℓ - 1)` remaining slots
(`topMoves`), and the bottom slot `h` of axis `i` behind
`i (ℓ - 1 - b + h) + (ℓ - 1 - b)` of them, `b = (ℓ - 1) mod K` (`botMoves`);
each move's remaining width is the address length minus the slots already
moved, minus the slots in front, minus one (`layoutMoves_eq`). The chunk
exchanges are the left-to-right scan run on the list of block indices
(`selectL`, `layoutSwaps_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.LayoutScript

open LayoutMoves LayoutArray LayoutMachines

section Params

variable {α : Type*} [BEq α] [LawfulBEq α]

/-- The move widths of moving the slots `ss` in turn out of the remaining slots `rest`. -/
def paramsOf : List α → List α → List (ℕ × ℕ)
  | _, [] => []
  | rest, s :: ss => (rest.idxOf s, rest.length - rest.idxOf s - 1) :: paramsOf (rest.erase s) ss

omit [LawfulBEq α] in
theorem paramsOf_append (rest : List α) (ss tt : List α) :
    paramsOf rest (ss ++ tt) = paramsOf rest ss ++ paramsOf (ss.foldl List.erase rest) tt := by
  induction ss generalizing rest with
  | nil => rfl
  | cons s ss ih => simp only [List.cons_append, paramsOf, List.foldl_cons, ih, List.cons_append]

end Params

theorem prefixParams_eq_paramsOf {α : Type*} [DecidableEq α] : ∀ (ss pre rest : List α),
    prefixParams pre.length ss (pre ++ rest) = paramsOf rest ss
  | [], _, _ => rfl
  | s :: ss, pre, rest => by
    simp only [prefixParams, paramsOf, moveParams, List.drop_left, moveAfter_append]
    rw [show pre ++ s :: rest.erase s = (pre ++ [s]) ++ rest.erase s by simp,
      show pre.length + 1 = (pre ++ [s]).length by simp, prefixParams_eq_paramsOf ss]


/-! ### Blocks -/

section Blocks

variable {β : Type*} [DecidableEq β]

/-- The concatenation of the blocks `f 0, …, f (D-1)`. -/
def blocks (f : ℕ → List β) (D : ℕ) : List β := (List.range D).flatMap f

omit [DecidableEq β] in
theorem blocks_split (f : ℕ → List β) {i D : ℕ} (hi : i < D) :
    blocks f D = blocks f i ++ (f i ++ ((List.range (D - i - 1)).map (· + (i + 1))).flatMap f) := by
  obtain ⟨e, rfl⟩ : ∃ e, D = i + 1 + e := ⟨D - i - 1, by omega⟩
  unfold blocks
  rw [show i + 1 + e - i - 1 = e by omega, List.range_add, List.range_succ]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, List.flatMap_map]
  congr 2
  apply List.flatMap_congr; intro x _; congr 1; omega

omit [DecidableEq β] in
theorem length_blocks (f : ℕ → List β) (D : ℕ) :
    (blocks f D).length = ((List.range D).map fun i => (f i).length).sum := by
  simp [blocks, List.length_flatMap]

omit [DecidableEq β] in
theorem blocks_congr {f g : ℕ → List β} {D : ℕ} (h : ∀ i < D, f i = g i) : blocks f D = blocks g D := by
  unfold blocks
  apply List.flatMap_congr
  intro i hi; exact h i (List.mem_range.mp hi)

/-- Blocks whose members are tagged by the block: `s ∈ f i → s.1 = i`. -/
def Tagged (f : ℕ → List (ℕ × ℕ)) : Prop := ∀ i, ∀ s ∈ f i, s.1 = i

theorem not_mem_blocks_lt {f : ℕ → List (ℕ × ℕ)} (hf : Tagged f) {s : ℕ × ℕ} {i : ℕ} (hs : s.1 = i) :
    s ∉ blocks f i := by
  intro h
  simp only [blocks, List.mem_flatMap, List.mem_range] at h
  obtain ⟨i', hi', hm⟩ := h
  have := hf i' s hm; omega

theorem not_mem_blocks_after {f : ℕ → List (ℕ × ℕ)} (hf : Tagged f) {s : ℕ × ℕ} {i D : ℕ} (hs : s.1 = i) :
    s ∉ ((List.range (D - i - 1)).map (· + (i + 1))).flatMap f := by
  intro h
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨i', ⟨t, -, rfl⟩, hm⟩ := h
  have := hf _ s hm; omega

/-- The position of a member of block `i`: the earlier blocks' lengths plus its position in the block. -/
theorem idxOf_blocks {f : ℕ → List (ℕ × ℕ)} (hf : Tagged f) {i D : ℕ} (hi : i < D) {s : ℕ × ℕ}
    (hs : s ∈ f i) : (blocks f D).idxOf s = (blocks f i).length + (f i).idxOf s := by
  have h1 := hf i s hs
  rw [blocks_split f hi, List.idxOf_append_of_notMem (not_mem_blocks_lt hf h1),
    List.idxOf_append_of_mem hs]

/-- Removing a member of block `i` removes it from that block. -/
theorem erase_blocks {f : ℕ → List (ℕ × ℕ)} (hf : Tagged f) {i D : ℕ} (hi : i < D) {s : ℕ × ℕ}
    (hs : s ∈ f i) : (blocks f D).erase s = blocks (Function.update f i ((f i).erase s)) D := by
  have h1 := hf i s hs
  rw [blocks_split f hi, blocks_split _ hi, List.erase_append_right _ (not_mem_blocks_lt hf h1),
    List.erase_append_left _ hs, Function.update_self]
  congr 1
  · apply blocks_congr; intro i' hi'; rw [Function.update_of_ne (by omega)]
  · congr 1
    apply List.flatMap_congr
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨t, -, rfl⟩ := hx
    rw [Function.update_of_ne (by omega)]

end Blocks

section Moves

/-! ### The top moves -/

theorem tagged_slotsDesc (lo : ℕ) (f : ℕ → ℕ) : Tagged fun i => slotsDesc i lo (f i) :=
  fun _ _ hs => (mem_slotsDesc.mp hs).1

theorem slotsDesc_succ (i lo len : ℕ) : slotsDesc i lo (len + 1) = (i, lo + len) :: slotsDesc i lo len := by
  simp [slotsDesc, List.range_succ]

theorem sum_range_const (i c : ℕ) {g : ℕ → ℕ} (h : ∀ j < i, g j = c) :
    ((List.range i).map g).sum = i * c := by
  rw [List.map_congr_left (g := fun _ => c) (fun j hj => h j (List.mem_range.mp hj))]
  simp

/-- The top moves: the long axis `i` moved `k`-th sits behind `i (ℓ - 1)` slots out of `L - k`. -/
def topMovesF (ℓ : ℕ) : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | L, i :: is => (i * (ℓ - 1), L - i * (ℓ - 1) - 1) :: topMovesF ℓ (L - 1) is

theorem slotsDesc_top (i : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    slotsDesc i 0 ℓ = (i, ℓ - 1) :: slotsDesc i 0 (ℓ - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  simp [slotsDesc_succ]

theorem paramsOf_tops {ℓ D : ℕ} (hℓ : 1 ≤ ℓ) : ∀ (is : List ℕ) (f : ℕ → ℕ),
    is.Pairwise (· < ·) → (∀ i ∈ is, i < D ∧ f i = ℓ) → (∀ i < D, i ∉ is → f i = ℓ - 1) →
    paramsOf (blocks (fun i => slotsDesc i 0 (f i)) D) (is.map fun i => (i, ℓ - 1)) =
        topMovesF ℓ (blocks (fun i => slotsDesc i 0 (f i)) D).length is ∧
      (is.map fun i => (i, ℓ - 1)).foldl List.erase (blocks (fun i => slotsDesc i 0 (f i)) D) =
        blocks (fun i => slotsDesc i 0 (ℓ - 1)) D
  | [], f, _, _, h3 => by
    refine ⟨rfl, ?_⟩
    simp only [List.map_nil, List.foldl_nil]
    exact blocks_congr fun i hi => by rw [h3 i hi (by simp)]
  | i0 :: is, f, h1, h2, h3 => by
    obtain ⟨hi0, hf0⟩ := h2 i0 (by simp)
    have hlt : ∀ i ∈ is, i0 < i := (List.pairwise_cons.mp h1).1
    have hmem : (i0, ℓ - 1) ∈ slotsDesc i0 0 (f i0) := by
      rw [mem_slotsDesc]; omega
    have hmemB : (i0, ℓ - 1) ∈ blocks (fun i => slotsDesc i 0 (f i)) D := by
      simp only [blocks, List.mem_flatMap, List.mem_range]; exact ⟨i0, hi0, hmem⟩
    have hidx : (blocks (fun i => slotsDesc i 0 (f i)) D).idxOf (i0, ℓ - 1) = i0 * (ℓ - 1) := by
      rw [idxOf_blocks (tagged_slotsDesc 0 f) hi0 hmem, length_blocks, hf0, slotsDesc_top i0 hℓ,
        List.idxOf_cons_self, add_zero]
      apply sum_range_const
      intro j hj
      rw [length_slotsDesc]
      apply h3 j (by omega)
      intro hjm
      rcases List.mem_cons.mp hjm with e | e
      · omega
      · have := hlt j e; omega
    have herase : (blocks (fun i => slotsDesc i 0 (f i)) D).erase (i0, ℓ - 1) =
        blocks (fun i => slotsDesc i 0 (Function.update f i0 (ℓ - 1) i)) D := by
      rw [erase_blocks (tagged_slotsDesc 0 f) hi0 hmem]
      apply blocks_congr
      intro i _
      by_cases hi : i = i0
      · subst hi
        rw [Function.update_self, Function.update_self, hf0, slotsDesc_top i hℓ, List.erase_cons_head]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
    have hlen : (blocks (fun i => slotsDesc i 0 (Function.update f i0 (ℓ - 1) i)) D).length =
        (blocks (fun i => slotsDesc i 0 (f i)) D).length - 1 := by
      rw [← herase, List.length_erase_of_mem hmemB]
    obtain ⟨ih1, ih2⟩ := paramsOf_tops hℓ is (Function.update f i0 (ℓ - 1)) (List.pairwise_cons.mp h1).2
      (fun i hi => by
        refine ⟨(h2 i (by simp [hi])).1, ?_⟩
        rw [Function.update_of_ne (by have := hlt i hi; omega)]
        exact (h2 i (by simp [hi])).2)
      (fun i hi hnot => by
        by_cases he : i = i0
        · subst he; rw [Function.update_self]
        · rw [Function.update_of_ne he]; exact h3 i hi (by simp [he, hnot]))
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, paramsOf, hidx, herase, ih1, hlen, topMovesF]
    · rw [List.map_cons, List.foldl_cons, herase, ih2]

/-! ### The bottom moves -/

/-- Axis `i` with its bottom slots `h ≥ c` removed: slots `ℓ - 2, …, b`, then `c - 1, …, 0`. -/
def axisRest (ℓ b i c : ℕ) : List (ℕ × ℕ) := slotsDesc i b (ℓ - 1 - b) ++ slotsDesc i 0 c

theorem tagged_axisRest (ℓ b : ℕ) (g : ℕ → ℕ) : Tagged fun i => axisRest ℓ b i (g i) := by
  intro i s hs
  simp only [axisRest, List.mem_append] at hs
  rcases hs with h | h <;> exact (mem_slotsDesc.mp h).1

theorem length_axisRest (ℓ b i c : ℕ) : (axisRest ℓ b i c).length = ℓ - 1 - b + c := by
  simp [axisRest, length_slotsDesc]

/-- The moves of one bottom level `h`, axes `i, i+1, …` (`e` of them), out of `L` remaining slots. -/
def levelF (ℓ b h : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | _, _, 0 => []
  | i, L, e + 1 => (i * (ℓ - 1 - b + h) + (ℓ - 1 - b), L - (i * (ℓ - 1 - b + h) + (ℓ - 1 - b)) - 1) ::
      levelF ℓ b h (i + 1) (L - 1) e

/-- The bottom moves: levels `c - 1` down to `0`, each over the `D` axes. -/
def botF (ℓ b D : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | c + 1, L => levelF ℓ b c 0 L D ++ botF ℓ b D c (L - D)

/-- The remaining slots during level `h`, the axes below `i` already moved. -/
def levelRest (ℓ b h i i' : ℕ) : List (ℕ × ℕ) := axisRest ℓ b i' (if i' < i then h else h + 1)

theorem tagged_levelRest (ℓ b h i : ℕ) : Tagged (levelRest ℓ b h i) := by
  intro i' s hs
  simp only [levelRest, axisRest, List.mem_append] at hs
  rcases hs with h | h <;> exact (mem_slotsDesc.mp h).1

theorem paramsOf_level {ℓ b h D : ℕ} (hb : h < b) (hbl : b ≤ ℓ - 1) : ∀ (e i : ℕ), i + e = D →
    paramsOf (blocks (levelRest ℓ b h i) D) ((List.range e).map fun t => (i + t, h)) =
        levelF ℓ b h i (blocks (levelRest ℓ b h i) D).length e ∧
      ((List.range e).map fun t => (i + t, h)).foldl List.erase (blocks (levelRest ℓ b h i) D) =
        blocks (fun i' => axisRest ℓ b i' h) D
  | 0, i, hie => by
    refine ⟨rfl, ?_⟩
    simp only [List.range_zero, List.map_nil, List.foldl_nil]
    exact blocks_congr fun i' hi' => by simp only [levelRest]; rw [ite_eq_left (by omega)]
  | e + 1, i, hie => by
    have hi : i < D := by omega
    have hcur : levelRest ℓ b h i i = slotsDesc i b (ℓ - 1 - b) ++ (i, h) :: slotsDesc i 0 h := by
      simp only [levelRest, axisRest, lt_irrefl, ite_false, slotsDesc_succ, zero_add]
    have hnot : (i, h) ∉ slotsDesc i b (ℓ - 1 - b) := by rw [mem_slotsDesc]; omega
    have hmem : (i, h) ∈ levelRest ℓ b h i i := by rw [hcur]; simp
    have hmemB : (i, h) ∈ blocks (levelRest ℓ b h i) D := by
      simp only [blocks, List.mem_flatMap, List.mem_range]; exact ⟨i, hi, hmem⟩
    have hidx : (blocks (levelRest ℓ b h i) D).idxOf (i, h) = i * (ℓ - 1 - b + h) + (ℓ - 1 - b) := by
      rw [idxOf_blocks (tagged_levelRest ℓ b h i) hi hmem, length_blocks, hcur,
        List.idxOf_append_of_notMem hnot, List.idxOf_cons_self, length_slotsDesc, add_zero]
      congr 1
      apply sum_range_const; intro j hj
      simp only [levelRest, length_axisRest, ite_eq_left hj]
    have herase : (blocks (levelRest ℓ b h i) D).erase (i, h) = blocks (levelRest ℓ b h (i + 1)) D := by
      rw [erase_blocks (tagged_levelRest ℓ b h i) hi hmem]
      apply blocks_congr
      intro i' _
      by_cases he : i' = i
      · subst he
        rw [Function.update_self, hcur, List.erase_append_right _ hnot, List.erase_cons_head]
        simp only [levelRest, axisRest, lt_add_one, ite_true]
      · rw [Function.update_of_ne he]
        simp only [levelRest]
        by_cases h1 : i' < i
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    have hlen : (blocks (levelRest ℓ b h (i + 1)) D).length = (blocks (levelRest ℓ b h i) D).length - 1 := by
      rw [← herase, List.length_erase_of_mem hmemB]
    obtain ⟨ih1, ih2⟩ := paramsOf_level (D := D) hb hbl e (i + 1) (by omega)
    have hmap : (List.range (e + 1)).map (fun t => (i + t, h)) =
        (i, h) :: (List.range e).map fun t => (i + 1 + t, h) := by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Function.comp_def, add_zero]
      congr 2; funext t; congr 1; omega
    refine ⟨?_, ?_⟩
    · rw [hmap]
      rw [paramsOf, hidx, herase, ih1, hlen, levelF]
    · rw [hmap, List.foldl_cons, herase, ih2]

theorem paramsOf_bottoms {ℓ b D : ℕ} (hbl : b ≤ ℓ - 1) : ∀ c : ℕ, c ≤ b →
    paramsOf (blocks (fun i => axisRest ℓ b i c) D)
        ((List.range c).reverse.flatMap fun h => (List.range D).map fun i => (i, h)) =
      botF ℓ b D c (blocks (fun i => axisRest ℓ b i c) D).length
  | 0, _ => rfl
  | c + 1, hc => by
    have hlev := paramsOf_level (ℓ := ℓ) (h := c) (D := D) (by omega) hbl D 0 (by omega)
    have e0 : blocks (levelRest ℓ b c 0) D = blocks (fun i => axisRest ℓ b i (c + 1)) D :=
      blocks_congr fun _ _ => by simp [levelRest]
    rw [e0] at hlev
    simp only [zero_add] at hlev
    obtain ⟨h1, h2⟩ := hlev
    have hlen : (blocks (fun i => axisRest ℓ b i c) D).length =
        (blocks (fun i => axisRest ℓ b i (c + 1)) D).length - D := by
      rw [length_blocks, length_blocks]
      simp only [length_axisRest]
      rw [sum_range_const D (ℓ - 1 - b + c) (fun _ _ => rfl),
        sum_range_const D (ℓ - 1 - b + (c + 1)) (fun _ _ => rfl)]
      rw [show ℓ - 1 - b + (c + 1) = (ℓ - 1 - b + c) + 1 by omega, Nat.mul_succ]; omega
    have h2' : List.foldl List.erase (blocks (fun i => axisRest ℓ b i (c + 1)) D)
        (List.map (fun i => (i, c)) (List.range D)) = blocks (fun i => axisRest ℓ b i c) D := h2
    have h1' : paramsOf (blocks (fun i => axisRest ℓ b i (c + 1)) D) (List.map (fun i => (i, c)) (List.range D)) =
        levelF ℓ b c 0 (blocks (fun i => axisRest ℓ b i (c + 1)) D).length D := h1
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons, paramsOf_append, h1', h2', botF, paramsOf_bottoms hbl c (by omega), hlen]

/-! ### The prefix moves of the paper's layout -/

theorem beq_inst_eq {α : Type*} (i₁ i₂ : BEq α) [h₁ : @LawfulBEq α i₁] [h₂ : @LawfulBEq α i₂] : i₁ = i₂ := by
  cases i₁ with | mk f =>
  cases i₂ with | mk g =>
  congr
  funext a b
  have e1 : f a b = true ↔ a = b := @beq_iff_eq α ⟨f⟩ h₁ a b
  have e2 : g a b = true ↔ a = b := @beq_iff_eq α ⟨g⟩ h₂ a b
  exact Bool.eq_iff_iff.mpr (e1.trans e2.symm)

variable {r : ℕ} {ts : List ℕ} {ℓ K : ℕ}

theorem axisRest_full (ℓ b i : ℕ) (hb : b ≤ ℓ - 1) : axisRest ℓ b i b = slotsDesc i 0 (ℓ - 1) := by
  rw [axisRest]
  conv_rhs => rw [show ℓ - 1 = b + (ℓ - 1 - b) by omega]
  rw [slotsDesc_split, zero_add]

/-- `layoutMoves_eq`: the prefix moves of the paper's layout in closed form: the top moves of
the long axes out of the `n` address bits, then the bottom levels `b - 1, …, 0` out of the
remaining `D (ℓ - 1)` slots. -/
theorem layoutMoves_eq (hL : LayoutOK r ts ℓ K) :
    layoutMoves ts ℓ K = topMovesF ℓ (addrBits ts) (longs ts ℓ) ++
      botF ℓ ((ℓ - 1) % K) ts.length ((ℓ - 1) % K) (ts.length * (ℓ - 1)) := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  have hb : (ℓ - 1) % K ≤ ℓ - 1 := Nat.mod_le _ _
  have h0 := prefixParams_eq_paramsOf (prefixSlots ts ℓ K) [] (initOrder ts)
  simp only [List.length_nil, List.nil_append] at h0
  have hinst : (instBEqOfDecidableEq : BEq (ℕ × ℕ)) = instBEqProd := beq_inst_eq _ _
  unfold layoutMoves
  have hinit : initOrder ts = blocks (fun i => slotsDesc i 0 (axLen ts i)) ts.length := rfl
  obtain ⟨t1, t2⟩ := paramsOf_tops (D := ts.length) hℓ (longs ts ℓ) (axLen ts)
    ((List.pairwise_lt_range).filter _)
    (fun i hi => by rw [mem_longs] at hi; exact hi)
    (fun i hi hnot => by
      rcases hL.2.1 i hi with e | e
      · exact e
      · exact absurd (mem_longs.mpr ⟨hi, e⟩) hnot)
  have hfull : blocks (fun i => slotsDesc i 0 (ℓ - 1)) ts.length =
      blocks (fun i => axisRest ℓ ((ℓ - 1) % K) i ((ℓ - 1) % K)) ts.length :=
    blocks_congr fun i _ => (axisRest_full ℓ _ i hb).symm
  have hbot := paramsOf_bottoms (ℓ := ℓ) (D := ts.length) hb ((ℓ - 1) % K) le_rfl
  have hlenB : (blocks (fun i => axisRest ℓ ((ℓ - 1) % K) i ((ℓ - 1) % K)) ts.length).length =
      ts.length * (ℓ - 1) := by
    rw [length_blocks]; simp only [length_axisRest]
    rw [sum_range_const _ _ (fun _ _ => rfl)]; congr 1; omega
  rw [hinst] at h0
  rw [h0, prefixSlots, paramsOf_append]
  rw [show topSlots ts ℓ = (longs ts ℓ).map fun i => (i, ℓ - 1) from rfl, hinit, t1, t2, hfull,
    show bottomSlots ts ℓ K = (List.range ((ℓ - 1) % K)).reverse.flatMap
      (fun h => (List.range ts.length).map fun i => (i, h)) from rfl, hbot, hlenB, ← hinit,
    length_initOrder hL]

end Moves

/-! ### The chunk exchanges as a scan of a list -/

section Swaps

/-- The left-to-right scan on a list of block indices, `e` positions from `k`: when position `k`
does not hold block `k`, exchange it with the position holding block `k`. -/
def selectL : List ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | _, _, 0 => []
  | A, k, e + 1 =>
    if A.getD k 0 = k then selectL A (k + 1) e
    else (k, A.idxOf k) :: selectL ((A.set k k).set (A.idxOf k) (A.getD k 0)) (k + 1) e

/-- The arrangement as a list: position `x` holds block `σ x`. -/
def arr {m : ℕ} (σ : Equiv.Perm (Fin m)) : List ℕ := List.ofFn fun x => (σ x).val

theorem length_arr {m : ℕ} (σ : Equiv.Perm (Fin m)) : (arr σ).length = m := by simp [arr]

theorem getD_arr {m : ℕ} (σ : Equiv.Perm (Fin m)) {k : ℕ} (hk : k < m) :
    (arr σ).getD k 0 = (σ ⟨k, hk⟩).val := by
  simp [arr, List.getD_eq_getElem?_getD, hk]

theorem idxOf_arr {m : ℕ} (σ : Equiv.Perm (Fin m)) {k : ℕ} (hk : k < m) :
    (arr σ).idxOf k = (σ.symm ⟨k, hk⟩).val := by
  have hnd : (arr σ).Nodup := by
    rw [arr, List.nodup_ofFn]
    intro a b h; exact σ.injective (Fin.ext h)
  have hv := (σ.symm ⟨k, hk⟩).isLt
  have hget : (arr σ)[(σ.symm ⟨k, hk⟩).val]'(by rw [length_arr]; exact hv) = k := by
    simp [arr]
  conv_lhs => rw [← hget]
  exact hnd.idxOf_getElem _ _

theorem arr_mul_swap {m : ℕ} (σ : Equiv.Perm (Fin m)) {k : ℕ} (hk : k < m) (v : Fin m) (hv : σ v = ⟨k, hk⟩) :
    arr (σ * Equiv.swap ⟨k, hk⟩ v) = ((arr σ).set k k).set v.val ((arr σ).getD k 0) := by
  rw [getD_arr σ hk]
  apply List.ext_getElem (by simp [arr])
  intro x h1 h2
  simp only [length_arr] at h1
  simp only [arr, List.getElem_ofFn, Equiv.Perm.coe_mul, Function.comp_apply, List.getElem_set]
  by_cases hxv : x = v.val
  · have : (⟨x, h1⟩ : Fin m) = v := Fin.ext hxv
    rw [this, Equiv.swap_apply_right, ite_eq_left hxv.symm]
  · rw [ite_eq_right (Ne.symm hxv)]
    by_cases hxk : x = k
    · have : (⟨x, h1⟩ : Fin m) = ⟨k, hk⟩ := Fin.ext hxk
      rw [this, Equiv.swap_apply_left, hv, ite_eq_left hxk.symm]
    · rw [ite_eq_right (Ne.symm hxk), Equiv.swap_apply_of_ne_of_ne (fun e => hxk (congrArg Fin.val e))
        (fun e => hxv (congrArg Fin.val e))]

/-- `selectSwaps_list`: the scan of an arrangement is the list scan of its block indices. -/
theorem selectSwaps_list {m : ℕ} : ∀ (e k : ℕ) (σ : Equiv.Perm (Fin m)), m - k = e →
    (selectSwaps σ k).map (fun x => (x.1.val, x.2.val)) = selectL (arr σ) k e
  | 0, k, σ, h => by
    rw [selectSwaps, dite_eq_right_of_eq_false (by simp; omega)]; rfl
  | e + 1, k, σ, h => by
    have hk : k < m := by omega
    rw [selectSwaps, dite_eq_left_of_eq_true (by simp [hk]), selectL, getD_arr σ hk]
    by_cases hσ : σ ⟨k, hk⟩ = ⟨k, hk⟩
    · rw [ite_eq_left hσ, ite_eq_left (by rw [hσ])]
      exact selectSwaps_list e (k + 1) σ (by omega)
    · rw [ite_eq_right hσ, ite_eq_right (fun e => hσ (Fin.ext e)), List.map_cons, idxOf_arr σ hk]
      have hv : σ (σ.symm ⟨k, hk⟩) = ⟨k, hk⟩ := by simp
      rw [selectSwaps_list e (k + 1) _ (by omega), arr_mul_swap σ hk _ hv, getD_arr σ hk]

/-- The exchange widths of positions `k ≠ j` among `m` blocks of `K` slots. -/
def exParamsN (m K : ℕ) (e : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if e.1 = e.2 then (0, 0, 0) else (K, (max e.1 e.2 - min e.1 e.2 - 1) * K, (m - 1 - max e.1 e.2) * K)

variable {r : ℕ} {ts : List ℕ} {ℓ K : ℕ}

/-- `layoutSwaps_eq`: the chunk exchanges of the paper's layout are the list scan of the
axis-major arrangement `x ↦ (x mod q) D + x / q`. -/
theorem layoutSwaps_eq :
    layoutSwaps ts ℓ K = (selectL ((List.range ((ℓ - 1) / K * ts.length)).map fun x =>
        x % ((ℓ - 1) / K) * ts.length + x / ((ℓ - 1) / K)) 0 ((ℓ - 1) / K * ts.length)).map
      (exParamsN ((ℓ - 1) / K * ts.length) K) := by
  have harr : arr (axisToChunk ((ℓ - 1) / K) ts.length) = (List.range ((ℓ - 1) / K * ts.length)).map
      fun x => x % ((ℓ - 1) / K) * ts.length + x / ((ℓ - 1) / K) := by
    apply List.ext_getElem (by simp [arr])
    intro x h1 h2
    simp [arr, axisToChunk_val]
  rw [layoutSwaps, ← harr, ← selectSwaps_list _ 0 _ (by omega), List.map_map]
  congr 1
  funext e
  simp only [Function.comp_apply, exParams, exParamsN, Fin.ext_iff]

end Swaps

end IntegerMultBounds.Schoenhage.LayoutScript
