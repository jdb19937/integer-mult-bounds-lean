module

public import IntegerMultBounds.Resampling.AxisRounds
public import IntegerMultBounds.Resampling.FlatTensor

/-! Flat arrays of entries for the tensor driver: positions in uniform-width
lists (`getD_flatten_uniform`), lines nested in blocks (`mapBlocks_nest`),
composed blockwise maps (`mapBlocks_comp`), and the flat pass keeping
lengths and entry properties (`flatPass_props`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.ScriptSem

open AxisRounds FlatTensor

/-- Bits of a uniform-width list at an entry and offset. -/
theorem getD_flatten_uniform (B : ℕ) : ∀ (es : List (List Bool)), (∀ e ∈ es, e.length = B) →
    ∀ (i b : ℕ), i < es.length → b < B → es.flatten.getD (i * B + b) false = (es.getD i []).getD b false
  | [], _, i, _, hi, _ => by simp at hi
  | e :: es, h, i, b, hi, hb => by
    have he := h e (by simp)
    rw [List.flatten_cons]
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.getD_cons_zero]
      rw [List.getD_append _ _ _ _ (by omega)]
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [he]; nlinarith), he,
        show (i + 1) * B + b - B = i * B + b by rw [Nat.succ_mul]; omega,
        getD_flatten_uniform B es (fun x hx => h x (by simp [hx])) i b (by simp at hi; omega) hb]
      simp

/-- A position in `A · B` rows of width `B` is a row and an offset. -/
theorem decomp2 {z A B : ℕ} (h : z < A * B) : ∃ a b, a < A ∧ b < B ∧ z = a * B + b := by
  have hB : 0 < B := by rcases Nat.eq_zero_or_pos B with hB | hB <;> simp_all
  refine ⟨z / B, z % B, ?_, Nat.mod_lt _ hB, (Nat.div_add_mod' z B).symm⟩
  rw [Nat.div_lt_iff_lt_mul hB]; exact h

theorem length_swapList' (P H G D B : ℕ) (xs : List Bool) :
    (Schoenhage.SwapPrim.swapList P H G D B xs).length = P * D * G * H * B := length_swapList P H G D B xs

/-! ### Blockwise maps -/

variable {α : Type*}

theorem length_block (n b : ℕ) (xs : List α) (N : ℕ) (hl : xs.length = N * n) (hb : b < N) :
    (block n b xs).length = n := by
  simp only [block, List.length_take, List.length_drop, hl]
  have : (b + 1) * n ≤ N * n := Nat.mul_le_mul_right _ hb
  rw [Nat.succ_mul] at this; omega

/-- Lines inside blocks: mapping lines of `n` is mapping, in every block of `k n`, its lines. -/
theorem mapBlocks_nest (n k N : ℕ) (g : List α → List α) (xs : List α) (x : α) (hn : 0 < n) (hk : 0 < k)
    (hl : xs.length = N * (k * n)) (hg : ∀ l : List α, l.length = n → (g l).length = n) :
    mapBlocks n g xs = mapBlocks (k * n) (mapBlocks n g) xs := by
  have eN : N * (k * n) = N * k * n := by ring
  have hgb : ∀ b, b < N * k → (g (block n b xs)).length = n := fun b hb =>
    hg _ (length_block n b xs (N * k) (by rw [hl]; ring) hb)
  have hinner : ∀ c, c < N → (mapBlocks n g (block (k * n) c xs)).length = k * n := fun c hc => by
    rw [length_mapBlocks n n _ _ (fun b hb => hg _ (length_block n b _ k (by
      rw [length_block _ _ _ N hl hc]) (by rw [length_block _ _ _ N hl hc, Nat.mul_div_cancel _ hn] at hb; exact hb))),
      length_block _ _ _ N hl hc, Nat.mul_div_cancel _ hn]
  have hdiv1 : xs.length / n = N * k := by rw [hl, eN, Nat.mul_div_cancel _ hn]
  have hdiv2 : xs.length / (k * n) = N := by rw [hl, Nat.mul_div_cancel _ (by positivity)]
  have hL1 := length_mapBlocks n n g xs (fun b hb => hgb b (hdiv1 ▸ hb))
  have hL2 := length_mapBlocks (k * n) (k * n) (mapBlocks n g) xs (fun c hc => hinner c (hdiv2 ▸ hc))
  apply ext_getD' x
  · rw [hL1, hL2, hdiv1, hdiv2]; ring
  · intro z hz
    rw [hL1, hdiv1] at hz
    obtain ⟨c, z1, hc, hz1, rfl⟩ := decomp2 (show z < N * (k * n) by nlinarith)
    obtain ⟨b, j, hb, hj, rfl⟩ := decomp2 hz1
    rw [getD_mapBlocks (k * n) (k * n) N _ xs (by positivity) hl hinner hc hz1,
      getD_mapBlocks n n k g _ hn (length_block _ _ _ N hl hc) (fun b' hb' => hg _ (length_block n b' _ k
        (length_block _ _ _ N hl hc) hb')) hb hj]
    rw [show c * (k * n) + (b * n + j) = (c * k + b) * n + j by ring,
      getD_mapBlocks n n (N * k) g xs hn (by rw [hl]; ring) hgb (by nlinarith) hj]
    congr 2
    apply ext_getD' x
    · rw [length_block _ _ _ (N * k) (by rw [hl]; ring) (by nlinarith),
        length_block _ _ _ k (length_block _ _ _ N hl hc) hb]
    · intro i hi
      rw [length_block _ _ _ (N * k) (by rw [hl]; ring) (by nlinarith)] at hi
      rw [getD_block _ _ _ hi, getD_block _ _ _ hi, getD_block _ _ _ (by nlinarith)]
      congr 1; ring

theorem block_mapBlocks (n N : ℕ) (g : List α → List α) (xs : List α) (x : α) (hn : 0 < n) (hl : xs.length = N * n)
    (hg : ∀ b, b < N → (g (block n b xs)).length = n) (b : ℕ) (hb : b < N) :
    block n b (mapBlocks n g xs) = g (block n b xs) := by
  have hL : (mapBlocks n g xs).length = N * n := by
    rw [length_mapBlocks n n g xs (fun c hc => hg c (by rw [hl, Nat.mul_div_cancel _ hn] at hc; exact hc)), hl,
      Nat.mul_div_cancel _ hn]
  apply ext_getD' x
  · rw [length_block _ _ _ N hL hb, hg b hb]
  · intro j hj
    rw [length_block _ _ _ N hL hb] at hj
    rw [getD_block _ _ _ hj, getD_mapBlocks n n N g xs hn hl hg hb hj]

theorem mapBlocks_comp (n N : ℕ) (f g : List α → List α) (xs : List α) (x : α) (hn : 0 < n) (hl : xs.length = N * n)
    (hg : ∀ l : List α, l.length = n → (g l).length = n) (hf : ∀ l : List α, l.length = n → (f l).length = n) :
    mapBlocks n f (mapBlocks n g xs) = mapBlocks n (f ∘ g) xs := by
  have hgb : ∀ b, b < N → (g (block n b xs)).length = n := fun b hb => hg _ (length_block n b xs N hl hb)
  have hL : (mapBlocks n g xs).length = N * n := by
    rw [length_mapBlocks n n g xs (fun c hc => hgb c (by rw [hl, Nat.mul_div_cancel _ hn] at hc; exact hc)), hl,
      Nat.mul_div_cancel _ hn]
  have hbm := block_mapBlocks n N g xs x hn hl hgb
  have hL1 : (mapBlocks n f (mapBlocks n g xs)).length = N * n := by
    rw [length_mapBlocks n n f _ (fun c hc => by
        rw [hL, Nat.mul_div_cancel _ hn] at hc; rw [hbm c hc]; exact hf _ (hgb c hc)), hL, Nat.mul_div_cancel _ hn]
  have hL2 : (mapBlocks n (f ∘ g) xs).length = N * n := by
    rw [length_mapBlocks n n (f ∘ g) xs (fun c hc => by
        rw [hl, Nat.mul_div_cancel _ hn] at hc; exact hf _ (hgb c hc)), hl, Nat.mul_div_cancel _ hn]
  apply ext_getD' x
  · rw [hL1, hL2]
  · intro z hz
    rw [hL1] at hz
    obtain ⟨b, j, hb, hj, rfl⟩ := decomp2 hz
    rw [getD_mapBlocks n n N f _ hn hL (fun c hc => by rw [hbm c hc]; exact hf _ (hgb c hc)) hb hj,
      getD_mapBlocks n n N (f ∘ g) xs hn hl (fun c hc => hf _ (hgb c hc)) hb hj, hbm b hb]
    rfl

theorem mem_trL (M n : ℕ) (x : α) (xs : List α) (hl : xs.length = M * n) {e : α} (he : e ∈ trL M n x xs) :
    e ∈ xs := by
  rw [trL, List.mem_ofFn] at he
  obtain ⟨z, rfl⟩ := he
  have hM : 0 < M := Nat.pos_of_ne_zero fun h => by subst h; exact absurd z.isLt (by simp)
  have hz := z.isLt
  have hi : z.val % M * n + z.val / M < xs.length := by
    rw [hl]
    have h1 : z.val % M < M := Nat.mod_lt _ hM
    have h2 : z.val / M < n := by rw [Nat.div_lt_iff_lt_mul hM]; exact hz
    nlinarith
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-! ### The flat pass on general entries -/

theorem prod_pos_pow {d : ℕ} (lg : Fin d → ℕ) : 0 < ∏ i, 2 ^ lg i := Finset.prod_pos fun _ _ => by positivity

/-- The flat pass keeps the length and any property of the entries kept by the line maps. -/
theorem flatPass_props (P : α → Prop) : ∀ (d : ℕ) (lg : Fin d → ℕ) (G : Fin d → List α → List α) (x : α)
    (xs : List α),
    (∀ i (l : List α), l.length = 2 ^ lg i → (∀ e ∈ l, P e) → (G i l).length = 2 ^ lg i ∧ ∀ e ∈ G i l, P e) →
    xs.length = ∏ i, 2 ^ lg i → (∀ e ∈ xs, P e) →
    (flatPass d (fun i => 2 ^ lg i) G x xs).length = ∏ i, 2 ^ lg i ∧ ∀ e ∈ flatPass d (fun i => 2 ^ lg i) G x xs, P e
  | 0, _, _, _, xs, _, hl, hp => ⟨hl, hp⟩
  | d + 1, lg, G, x, xs, hG, hl, hp => by
    set R := ∏ i : Fin d, 2 ^ lg i.succ
    set T0 := 2 ^ lg 0
    have hR : 0 < R := prod_pos_pow _
    have hT0 : 0 < T0 := by positivity
    rw [Fin.prod_univ_succ] at hl
    have hblk : ∀ b, b < T0 → (block R b xs).length = R := fun b hb => length_block _ _ _ T0 hl hb
    have hbp : ∀ b, ∀ e ∈ block R b xs, P e := fun b e he => hp e (List.mem_of_mem_drop (List.mem_of_mem_take he))
    have ih := fun b (hb : b < T0) => flatPass_props P d (fun i => lg i.succ) (fun i => G i.succ) x (block R b xs)
      (fun i l => hG i.succ l) (hblk b hb) (hbp b)
    set W := mapBlocks R (flatPass d (fun i => 2 ^ lg i.succ) (fun i => G i.succ) x) xs
    have hW : W.length = T0 * R := by
      rw [length_mapBlocks R R _ xs (fun b hb => (ih b (by rw [hl, Nat.mul_div_cancel _ hR] at hb; exact hb)).1), hl,
        Nat.mul_div_cancel _ hR]
    have hWp : ∀ e ∈ W, P e := by
      intro e he
      simp only [W, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he
      rw [hl, Nat.mul_div_cancel _ hR] at hb
      exact (ih b hb).2 e he
    set Z := trL T0 R x W
    have hZ : Z.length = R * T0 := length_trL _ _ _ _
    have hZp : ∀ e ∈ Z, P e := fun e he => hWp e (mem_trL _ _ _ _ hW he)
    have hgZ : ∀ b, b < R → (G 0 (block T0 b Z)).length = T0 ∧ ∀ e ∈ G 0 (block T0 b Z), P e := fun b hb =>
      hG 0 _ (length_block _ _ _ R hZ hb) (fun e he => hZp e (List.mem_of_mem_drop (List.mem_of_mem_take he)))
    set Y := mapBlocks T0 (G 0) Z
    have hY : Y.length = R * T0 := by
      rw [length_mapBlocks T0 T0 _ Z (fun b hb => (hgZ b (by rw [hZ, Nat.mul_div_cancel _ hT0] at hb; exact hb)).1), hZ,
        Nat.mul_div_cancel _ hT0]
    have hYp : ∀ e ∈ Y, P e := by
      intro e he
      simp only [Y, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he
      rw [hZ, Nat.mul_div_cancel _ hT0] at hb
      exact (hgZ b hb).2 e he
    refine ⟨?_, fun e he => hYp e (mem_trL _ _ _ _ hY he)⟩
    show (trL R T0 x Y).length = _
    rw [length_trL, Fin.prod_univ_succ]

end IntegerMultBounds.Resampling.ScriptSem
