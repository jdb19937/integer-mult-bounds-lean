module

public import IntegerMultBounds.Resampling.AxisRounds
public import IntegerMultBounds.Resampling.FlatTensor

/-! The tensor driver's field moves on flat bit arrays. An interchange with
an outer prefix `Q · P` acts on each of the `Q` outer blocks
(`swapList_mul`); moving the outermost field inward past the others by
adjacent interchanges is one block transpose (`rotIn_eq_tr2`); and block
transposes and blockwise maps of entries are the same operations on their
bits (`flatten_trL`, `flatten_mapBlocks`). -/

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

/-- An interchange with outer prefix `Q · P` acts on each of the `Q` outer blocks. -/
theorem swapList_mul (Q P H D B : ℕ) (xs : List Bool) (hl : xs.length = Q * (P * H * D * B))
    (hpos : 0 < P * H * D * B) :
    Schoenhage.SwapPrim.swapList (Q * P) H 1 D B xs = mapBlocks (P * H * D * B) (Schoenhage.SwapPrim.swapList P H 1 D B) xs := by
  apply ext_getD' false
  · rw [length_swapList', length_mapBlocks _ (P * D * 1 * H * B) _ _ (fun b _ => length_swapList' _ _ _ _ _ _), hl,
      Nat.mul_div_cancel _ hpos]; ring
  · intro z hz
    rw [length_swapList'] at hz
    obtain ⟨q, z1, hq, hz1, rfl⟩ := decomp2 (show z < Q * (P * D * H * B) by nlinarith)
    obtain ⟨p, z2, hp, hz2, rfl⟩ := decomp2 (show z1 < P * (D * H * B) by nlinarith)
    obtain ⟨d, z3, hd, hz3, rfl⟩ := decomp2 (show z2 < D * (H * B) by nlinarith)
    obtain ⟨h, b, hh, hb, rfl⟩ := decomp2 hz3
    have e1 : q * (P * D * H * B) + (p * (D * H * B) + (d * (H * B) + (h * B + b))) =
        ((((q * P + p) * D + d) * 1 + 0) * H + h) * B + b := by ring
    have hqp : q * P + p < Q * P := by nlinarith
    rw [e1, getD_swapList (Q * P) H 1 D B xs hqp hh (by omega) hd hb]
    have e2 : ((((q * P + p) * D + d) * 1 + 0) * H + h) * B + b =
        q * (P * D * 1 * H * B) + ((((p * D + d) * 1 + 0) * H + h) * B + b) := by ring
    rw [e2, getD_mapBlocks (P * H * D * B) (P * D * 1 * H * B) Q _ xs hpos hl
      (fun _ _ => length_swapList' _ _ _ _ _ _) hq (by nlinarith),
      getD_swapList P H 1 D B _ hp hh (by omega) hd hb,
      getD_block _ _ _ (by
        have h1 : p * H + h < P * H := by nlinarith
        have h2 : (p * H + h) * D + d < P * H * D := by nlinarith
        have h3 : ((p * H + h) * D + d) * B + b < P * H * D * B := by nlinarith
        simpa using h3)]
    congr 1; ring

/-- Move the field of `n` entries, just inside an outer prefix of `Q`, past the fields `gs`
(outer to inner) by adjacent interchanges of blocks of `B` bits. -/
def rotIn (n : ℕ) : ℕ → List ℕ → ℕ → List Bool → List Bool
  | _, [], _, xs => xs
  | Q, g :: gs, B, xs => rotIn n (Q * g) gs B (Schoenhage.SwapPrim.swapList Q n 1 g (B * gs.prod) xs)

theorem length_rotIn (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool), xs.length = Q * n * gs.prod * B →
    (rotIn n Q gs B xs).length = Q * n * gs.prod * B
  | _, [], _, _, h => h
  | Q, g :: gs, B, xs, h => by
    rw [rotIn, length_rotIn n (Q * g) gs B _ (by rw [length_swapList']; ring)]; simp only [List.prod_cons]; ring

theorem rotIn_getD (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool) {q j i b : ℕ},
    q < Q → j < gs.prod → i < n → b < B →
    (rotIn n Q gs B xs).getD (q * (gs.prod * n * B) + (j * n + i) * B + b) false =
      xs.getD (q * (n * gs.prod * B) + (i * gs.prod + j) * B + b) false
  | Q, [], B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_nil] at hj ⊢
    have : j = 0 := by omega
    subst this; simp [rotIn]
  | Q, g :: gs, B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_cons] at hj ⊢
    set R' := gs.prod
    have hR' : 0 < R' := by rcases Nat.eq_zero_or_pos R' with h | h <;> simp_all
    have hg : 0 < g := by rcases Nat.eq_zero_or_pos g with h | h <;> simp_all
    obtain ⟨j1, j2, hj1, hj2, rfl⟩ := decomp2 (show j < g * R' by exact hj)
    have e1 : q * (g * R' * n * B) + ((j1 * R' + j2) * n + i) * B + b =
        (q * g + j1) * (R' * n * B) + (j2 * n + i) * B + b := by ring
    rw [rotIn, e1, rotIn_getD n (Q * g) gs B _ (by nlinarith) hj2 hi hb]
    have e2 : (q * g + j1) * (n * R' * B) + (i * R' + j2) * B + b =
        ((((q * g + j1) * 1 + 0) * n + i) * (B * R') + (j2 * B + b)) := by ring
    have hjb : j2 * B + b < B * R' := by nlinarith
    rw [e2, getD_swapList Q n 1 g (B * R') xs hq hi (by omega) hj1 hjb]
    congr 1; ring

/-- Move the innermost field of `n` entries outward past the fields `gs` (inner to outer), just inside an
outer prefix of `Q`, by adjacent interchanges of blocks of `B` bits. -/
def rotOut (n : ℕ) : ℕ → List ℕ → ℕ → List Bool → List Bool
  | _, [], _, xs => xs
  | Q, g :: gs, B, xs => rotOut n Q gs (g * B) (Schoenhage.SwapPrim.swapList (Q * gs.prod) g 1 n B xs)

theorem rotOut_getD (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool) {q j i b : ℕ},
    q < Q → j < gs.prod → i < n → b < B →
    (rotOut n Q gs B xs).getD (q * (n * gs.prod * B) + (i * gs.prod + j) * B + b) false =
      xs.getD (q * (gs.prod * n * B) + (j * n + i) * B + b) false
  | Q, [], B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_nil] at hj ⊢
    have : j = 0 := by omega
    subst this; simp [rotOut]
  | Q, g :: gs, B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_cons] at hj ⊢
    set R' := gs.prod
    have hR' : 0 < R' := by rcases Nat.eq_zero_or_pos R' with h | h <;> simp_all
    have hg : 0 < g := by rcases Nat.eq_zero_or_pos g with h | h <;> simp_all
    obtain ⟨j', jg, hj', hjg, rfl⟩ := decomp2 (show j < R' * g by rw [mul_comm]; exact hj)
    have e1 : q * (n * (g * R') * B) + (i * (g * R') + (j' * g + jg)) * B + b =
        q * (n * R' * (g * B)) + (i * R' + j') * (g * B) + (jg * B + b) := by ring
    have hjb : jg * B + b < g * B := by nlinarith
    rw [rotOut, e1, rotOut_getD n Q gs (g * B) _ hq hj' hi hjb]
    have e2 : q * (R' * n * (g * B)) + (j' * n + i) * (g * B) + (jg * B + b) =
        ((((q * R' + j') * n + i) * 1 + 0) * g + jg) * B + b := by ring
    have hqj : q * R' + j' < Q * R' := by nlinarith
    rw [e2, getD_swapList (Q * R') g 1 n B xs hqj hjg (by omega) hi hb]
    congr 1; ring

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

theorem mem_mapBlocks (n : ℕ) (g : List α → List α) (hg : ∀ l : List α, ∀ y ∈ g l, y ∈ l) (xs : List α) {e : α}
    (he : e ∈ mapBlocks n g xs) : e ∈ xs := by
  simp only [mapBlocks, List.mem_flatMap] at he
  obtain ⟨b, -, hb⟩ := he
  have := hg _ _ hb
  simp only [block] at this
  exact List.mem_of_mem_drop (List.mem_of_mem_take this)

/-- Moving a field inward on bits is a block transpose of the entries. -/
theorem rotIn_flatten (n Q : ℕ) (gs : List ℕ) (B : ℕ) (es : List (List Bool)) (hw : ∀ e ∈ es, e.length = B)
    (hl : es.length = Q * (n * gs.prod)) (hn : 0 < n) (hR : 0 < gs.prod) :
    rotIn n Q gs B es.flatten = (mapBlocks (n * gs.prod) (trL n gs.prod []) es).flatten := by
  set R := gs.prod
  have hbl : ∀ b, b < Q → (block (n * R) b es).length = n * R := fun b hb => length_block _ _ _ Q hl hb
  have hmap : (mapBlocks (n * R) (trL n R []) es).length = Q * (n * R) := by
    rw [length_mapBlocks (n * R) (R * n) _ _ (fun b _ => length_trL _ _ _ _), hl, Nat.mul_div_cancel _ (by positivity)]
    ring
  have hw' : ∀ e ∈ mapBlocks (n * R) (trL n R []) es, e.length = B := by
    intro e he
    apply hw
    simp only [mapBlocks, List.mem_flatMap, List.mem_range] at he
    obtain ⟨b, hb, he⟩ := he
    rw [hl, Nat.mul_div_cancel _ (by positivity)] at hb
    have := mem_trL n R [] _ (hbl b hb) he
    simp only [block] at this
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have hflat : es.flatten.length = Q * n * R * B := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hw]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, hl]; ring
  have hflat' : (mapBlocks (n * R) (trL n R []) es).flatten.length = Q * n * R * B := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hw']
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, hmap]; ring
  apply ext_getD' false
  · rw [length_rotIn n Q gs B _ hflat, hflat']
  · intro z hz
    rw [length_rotIn n Q gs B _ hflat, show Q * n * R * B = Q * (R * n * B) by ring] at hz
    obtain ⟨q, z1, hq, hz1, rfl⟩ := decomp2 hz
    obtain ⟨jn, b, hjn, hb, rfl⟩ := decomp2 (show z1 < (R * n) * B by nlinarith)
    obtain ⟨j, i, hj, hi, rfl⟩ := decomp2 hjn
    have hiR : i * R + j < n * R := by
      have := Nat.mul_le_mul_right R (show i + 1 ≤ n by omega); rw [Nat.succ_mul] at this; omega
    have hq1 : q * (n * R) + (i * R + j) < Q * (n * R) := by
      have := Nat.mul_le_mul_right (n * R) (show q + 1 ≤ Q by omega); rw [Nat.succ_mul] at this; omega
    have hq2 : q * (R * n) + (j * n + i) < Q * (n * R) := by
      have := Nat.mul_le_mul_right (n * R) (show q + 1 ≤ Q by omega); rw [Nat.succ_mul] at this
      rw [mul_comm R n] at hjn ⊢; omega
    rw [show q * (R * n * B) + ((j * n + i) * B + b) = q * (R * n * B) + (j * n + i) * B + b by ring,
      rotIn_getD n Q gs B _ hq hj hi hb]
    rw [show q * (n * R * B) + (i * R + j) * B + b = (q * (n * R) + (i * R + j)) * B + b by ring,
      getD_flatten_uniform B es hw _ _ (by rw [hl]; exact hq1) hb]
    rw [show q * (R * n * B) + (j * n + i) * B + b = (q * (R * n) + (j * n + i)) * B + b by ring,
      getD_flatten_uniform B _ hw' _ _ (by rw [hmap]; exact hq2) hb]
    congr 1
    rw [getD_mapBlocks (n * R) (R * n) Q _ es (by positivity) hl (fun _ _ => length_trL _ _ _ _) hq hjn,
      getD_trL n R [] _ hi hj, getD_block _ _ _ hiR]

theorem length_rotOut (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool), xs.length = Q * gs.prod * n * B →
    (rotOut n Q gs B xs).length = Q * gs.prod * n * B
  | _, [], _, _, h => h
  | Q, g :: gs, B, xs, h => by
    rw [rotOut, length_rotOut n Q gs (g * B) _ (by rw [length_swapList']; simp only [List.prod_cons] at h ⊢; ring)]
    simp only [List.prod_cons]; ring

/-- Moving a field outward on bits is a block transpose of the entries. -/
theorem rotOut_flatten (n Q : ℕ) (gs : List ℕ) (B : ℕ) (es : List (List Bool)) (hw : ∀ e ∈ es, e.length = B)
    (hl : es.length = Q * (gs.prod * n)) (hn : 0 < n) (hR : 0 < gs.prod) :
    rotOut n Q gs B es.flatten = (mapBlocks (gs.prod * n) (trL gs.prod n []) es).flatten := by
  set R := gs.prod
  have hbl : ∀ b, b < Q → (block (R * n) b es).length = R * n := fun b hb => length_block _ _ _ Q hl hb
  have hmap : (mapBlocks (R * n) (trL R n []) es).length = Q * (R * n) := by
    rw [length_mapBlocks (R * n) (n * R) _ _ (fun b _ => length_trL _ _ _ _), hl, Nat.mul_div_cancel _ (by positivity)]
    ring
  have hw' : ∀ e ∈ mapBlocks (R * n) (trL R n []) es, e.length = B := by
    intro e he
    apply hw
    simp only [mapBlocks, List.mem_flatMap, List.mem_range] at he
    obtain ⟨b, hb, he⟩ := he
    rw [hl, Nat.mul_div_cancel _ (by positivity)] at hb
    have := mem_trL R n [] _ (hbl b hb) he
    simp only [block] at this
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have hflat : es.flatten.length = Q * R * n * B := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hw]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, hl]; ring
  have hflat' : (mapBlocks (R * n) (trL R n []) es).flatten.length = Q * R * n * B := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hw']
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, hmap]; ring
  apply ext_getD' false
  · rw [length_rotOut n Q gs B _ hflat, hflat']
  · intro z hz
    rw [length_rotOut n Q gs B _ hflat, show Q * R * n * B = Q * (n * R * B) by ring] at hz
    obtain ⟨q, z1, hq, hz1, rfl⟩ := decomp2 hz
    obtain ⟨ij, b, hij, hb, rfl⟩ := decomp2 (show z1 < (n * R) * B by nlinarith)
    obtain ⟨i, j, hi, hj, rfl⟩ := decomp2 hij
    have hjn : j * n + i < R * n := by
      have := Nat.mul_le_mul_right n (show j + 1 ≤ R by omega); rw [Nat.succ_mul] at this; omega
    have hq1 : q * (R * n) + (j * n + i) < Q * (R * n) := by
      have := Nat.mul_le_mul_right (R * n) (show q + 1 ≤ Q by omega); rw [Nat.succ_mul] at this; omega
    have hq2 : q * (n * R) + (i * R + j) < Q * (R * n) := by
      have := Nat.mul_le_mul_right (R * n) (show q + 1 ≤ Q by omega); rw [Nat.succ_mul] at this
      rw [mul_comm n R] at hij ⊢; omega
    rw [show q * (n * R * B) + ((i * R + j) * B + b) = q * (n * R * B) + (i * R + j) * B + b by ring,
      rotOut_getD n Q gs B _ hq hj hi hb]
    rw [show q * (R * n * B) + (j * n + i) * B + b = (q * (R * n) + (j * n + i)) * B + b by ring,
      getD_flatten_uniform B es hw _ _ (by rw [hl]; exact hq1) hb]
    rw [show q * (n * R * B) + (i * R + j) * B + b = (q * (n * R) + (i * R + j)) * B + b by ring,
      getD_flatten_uniform B _ hw' _ _ (by rw [hmap]; exact hq2) hb]
    congr 1
    rw [getD_mapBlocks (R * n) (n * R) Q _ es (by positivity) hl (fun _ _ => length_trL _ _ _ _) hq hij,
      getD_trL R n [] _ hj hi, getD_block _ _ _ hjn]

end IntegerMultBounds.Resampling.ScriptSem
