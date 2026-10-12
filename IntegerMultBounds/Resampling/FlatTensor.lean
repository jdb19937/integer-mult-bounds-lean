module

public import IntegerMultBounds.NLogN.ResamplingMultiNumeric
public import Mathlib.Data.List.GetD

/-! Arrays on `∏ ZMod Tᵢ` as flat lists in lexicographic order, axis `0`
outermost (`lexFlat`). The square tensor `tensorZR d T T F` applies the tail
axes block by block and then the head axis to every column; on flat lists the
head axis is a transpose, a map on contiguous lines and a transpose back
(`lexFlat_tensor`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.FlatTensor

open IntegerMultBounds.NLogN

variable {α : Type*}

/-- The flat list of an array, axis `0` outermost. -/
def lexFlat : (d : ℕ) → (T : Fin d → ℕ) → (((i : Fin d) → ZMod (T i)) → α) → List α
  | 0, _, u => [u fun i => i.elim0]
  | d + 1, T, u => (List.range (T 0)).flatMap fun k₀ : ℕ =>
      lexFlat d (fun i => T i.succ) fun j => u (Fin.cons ((k₀ : ℕ) : ZMod (T 0)) j)

theorem length_lexFlat : ∀ (d : ℕ) (T : Fin d → ℕ) (u : ((i : Fin d) → ZMod (T i)) → α),
    (lexFlat d T u).length = ∏ i, T i
  | 0, _, _ => rfl
  | d + 1, T, u => by
    simp only [lexFlat, List.length_flatMap, length_lexFlat d, Fin.prod_univ_succ]
    simp [List.sum_replicate, List.map_const']

/-- One step of the square tensor at a point. -/
theorem tensorZR_succ_apply (d : ℕ) (T : Fin (d + 1) → ℕ) [∀ i, NeZero (T i)]
    (F : (i : Fin (d + 1)) → (ZMod (T i) → ℂ) → (ZMod (T i) → ℂ)) (u : ((i : Fin (d + 1)) → ZMod (T i)) → ℂ)
    (k : (i : Fin (d + 1)) → ZMod (T i)) :
    tensorZR (d + 1) T T F u k =
      F 0 (fun j₀ => tensorZR d (fun i => T i.succ) (fun i => T i.succ) (fun i => F i.succ)
        (fun j' => u (Fin.cons j₀ j')) (Fin.tail k)) (k 0) := rfl

/-- The position of a multi-index in the flat list. -/
def lexIdx : (d : ℕ) → (T : Fin d → ℕ) → ((i : Fin d) → ZMod (T i)) → ℕ
  | 0, _, _ => 0
  | d + 1, T, k => (k 0).val * (∏ i : Fin d, T i.succ) + lexIdx d (fun i => T i.succ) (Fin.tail k)

theorem getD_flatMap_const {β : Type*} (f : ℕ → List β) (n R : ℕ) (hf : ∀ b, b < n → (f b).length = R) (b r : ℕ)
    (hb : b < n) (hr : r < R) (x : β) :
    ((List.range n).flatMap f).getD (b * R + r) x = (f b).getD r x := by
  induction n generalizing b with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl : ((List.range n).flatMap f).length = n * R := by
      rw [List.length_flatMap, List.map_congr_left (g := fun _ => R) (fun c hc => hf c (by simp at hc; omega))]
      simp
    by_cases h : b < n
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith), ih (fun c hc => hf c (by omega)) b h]
    · have hb' : b = n := by omega
      subst hb'
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]

theorem lexIdx_lt : ∀ (d : ℕ) (T : Fin d → ℕ) [∀ i, NeZero (T i)] (k : (i : Fin d) → ZMod (T i)),
    lexIdx d T k < ∏ i, T i
  | 0, _, _, _ => by simp [lexIdx]
  | d + 1, T, _, k => by
    have h1 := lexIdx_lt d (fun i => T i.succ) (Fin.tail k)
    have h0 : (k 0).val < T 0 := ZMod.val_lt (k 0)
    rw [lexIdx, Fin.prod_univ_succ]
    nlinarith

theorem lexFlat_getD : ∀ (d : ℕ) (T : Fin d → ℕ) [∀ i, NeZero (T i)] (u : ((i : Fin d) → ZMod (T i)) → α)
    (k : (i : Fin d) → ZMod (T i)) (x : α), (lexFlat d T u).getD (lexIdx d T k) x = u k
  | 0, _, _, u, k, x => by
    simp only [lexFlat, lexIdx]; simp; congr 1; funext i; exact i.elim0
  | d + 1, T, _, u, k, x => by
    simp only [lexFlat, lexIdx]
    rw [getD_flatMap_const _ (T 0) (∏ i : Fin d, T i.succ) (fun b _ => length_lexFlat _ _ _) _ _ (ZMod.val_lt _)
      (lexIdx_lt _ _ _), lexFlat_getD d _ _ (Fin.tail k)]
    rw [ZMod.natCast_zmod_val, Fin.cons_self_tail]

/-! ### Transposes and blockwise maps on lists -/

theorem getD_ofFn' {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i < n) (x : α) : (List.ofFn f).getD i x = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem div_mod_eq (i M b : ℕ) (hb : b < M) : (i * M + b) / M = i ∧ (i * M + b) % M = b := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- An `M × n` matrix transposed to `n × M`. -/
def trL (M n : ℕ) (x : α) (xs : List α) : List α :=
  List.ofFn fun z : Fin (n * M) => xs.getD (z.val % M * n + z.val / M) x

theorem length_trL (M n : ℕ) (x : α) (xs : List α) : (trL M n x xs).length = n * M := by simp [trL]

theorem getD_trL (M n : ℕ) (x : α) (xs : List α) {i j : ℕ} (hi : i < M) (hj : j < n) :
    (trL M n x xs).getD (j * M + i) x = xs.getD (i * n + j) x := by
  have hz : j * M + i < n * M := by nlinarith
  rw [trL, getD_ofFn' _ _ hz]
  simp only [(div_mod_eq j M i hi).1, (div_mod_eq j M i hi).2]

/-- Block `b` of length `n`. -/
def block (n b : ℕ) (xs : List α) : List α := (xs.drop (b * n)).take n

/-- Apply `g` to every block of length `n`. -/
def mapBlocks (n : ℕ) (g : List α → List α) (xs : List α) : List α :=
  (List.range (xs.length / n)).flatMap fun b => g (block n b xs)

theorem length_mapBlocks (n n' : ℕ) (g : List α → List α) (xs : List α)
    (hg : ∀ b, b < xs.length / n → (g (block n b xs)).length = n') :
    (mapBlocks n g xs).length = xs.length / n * n' := by
  rw [mapBlocks, List.length_flatMap, List.map_congr_left (g := fun _ => n') (fun c hc => hg c (by simp at hc; omega))]
  simp

theorem getD_mapBlocks (n n' N : ℕ) (g : List α → List α) (xs : List α)
    (hn : 0 < n) (hl : xs.length = N * n) (hg : ∀ b, b < N → (g (block n b xs)).length = n') {b j : ℕ} (hb : b < N)
    (hj : j < n') (x : α) :
    (mapBlocks n g xs).getD (b * n' + j) x = (g (block n b xs)).getD j x := by
  rw [mapBlocks, hl, Nat.mul_div_cancel _ hn]
  exact getD_flatMap_const _ N n' (fun b hb => hg b hb) b j hb hj x

theorem getD_block (n b : ℕ) (xs : List α) {j : ℕ} (hj : j < n) (x : α) :
    (block n b xs).getD j x = xs.getD (b * n + j) x := by
  simp only [block, List.getD_eq_getElem?_getD, List.getElem?_take, hj, ite_true, List.getElem?_drop]

/-! ### The flat pass -/

/-- The tail axes block by block, then the head axis: bring it innermost, map its lines, move it back. -/
def flatPass : (d : ℕ) → (T : Fin d → ℕ) → (Fin d → List α → List α) → α → List α → List α
  | 0, _, _, _, xs => xs
  | d + 1, T, G, x, xs =>
    trL (∏ i : Fin d, T i.succ) (T 0) x (mapBlocks (T 0) (G 0)
      (trL (T 0) (∏ i : Fin d, T i.succ) x (mapBlocks (∏ i : Fin d, T i.succ)
        (flatPass d (fun i => T i.succ) (fun i => G i.succ) x) xs)))

/-- A line map from a map on `ZMod n`. -/
def lineOf {n : ℕ} (F : (ZMod n → ℂ) → (ZMod n → ℂ)) (line : List ℂ) : List ℂ :=
  (List.range n).map fun k : ℕ => F (fun j => line.getD j.val 0) ((k : ℕ) : ZMod n)

theorem length_lineOf {n : ℕ} (F : (ZMod n → ℂ) → (ZMod n → ℂ)) (line : List ℂ) : (lineOf F line).length = n := by
  simp [lineOf]

theorem length_flatPass : ∀ (d : ℕ) (T : Fin d → ℕ) [∀ i, NeZero (T i)]
    (F : (i : Fin d) → (ZMod (T i) → ℂ) → (ZMod (T i) → ℂ)) (xs : List ℂ), xs.length = ∏ i, T i →
    (flatPass d T (fun i => lineOf (F i)) 0 xs).length = ∏ i, T i
  | 0, _, _, _, _, h => h
  | d + 1, T, _, F, xs, h => by
    simp only [flatPass, length_trL]; rw [Fin.prod_univ_succ]

/-- Every position below the volume is the position of a multi-index. -/
theorem lexIdx_surj : ∀ (d : ℕ) (T : Fin d → ℕ) [∀ i, NeZero (T i)] (z : ℕ), z < ∏ i, T i →
    ∃ k : (i : Fin d) → ZMod (T i), lexIdx d T k = z
  | 0, _, _, z, h => ⟨fun i => i.elim0, by simp at h; simp [lexIdx, h]⟩
  | d + 1, T, _, z, h => by
    set R := ∏ i : Fin d, T i.succ
    have hR : 0 < R := Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne _)
    rw [Fin.prod_univ_succ] at h
    obtain ⟨k', hk'⟩ := lexIdx_surj d (fun i => T i.succ) (z % R) (Nat.mod_lt _ hR)
    have hq : z / R < T 0 := by rw [Nat.div_lt_iff_lt_mul hR]; exact h
    refine ⟨Fin.cons ((z / R : ℕ) : ZMod (T 0)) k', ?_⟩
    simp only [lexIdx, Fin.cons_zero, Fin.tail_cons, hk']
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq]
    exact Nat.div_add_mod' z R

theorem ext_getD' {l₁ l₂ : List α} (x : α) (hl : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i x = l₂.getD i x) : l₁ = l₂ :=
  List.ext_getElem hl fun i h₁ h₂ => by
    have := h i h₁
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂, Option.getD_some, Option.getD_some] at this

theorem block_lexFlat (d : ℕ) (T : Fin (d + 1) → ℕ) [∀ i, NeZero (T i)] (u : ((i : Fin (d + 1)) → ZMod (T i)) → α)
    (b : ℕ) (hb : b < T 0) (x : α) :
    block (∏ i : Fin d, T i.succ) b (lexFlat (d + 1) T u) =
      lexFlat d (fun i => T i.succ) (fun j => u (Fin.cons ((b : ℕ) : ZMod (T 0)) j)) := by
  have hlen : (lexFlat (d + 1) T u).length = T 0 * ∏ i : Fin d, T i.succ := by
    rw [length_lexFlat, Fin.prod_univ_succ]
  apply ext_getD' x
  · simp only [block, List.length_take, List.length_drop, hlen, length_lexFlat]
    have : (b + 1) * (∏ i : Fin d, T i.succ) ≤ T 0 * ∏ i : Fin d, T i.succ := Nat.mul_le_mul_right _ hb
    rw [Nat.succ_mul] at this; omega
  · intro j hj
    have hjR : j < ∏ i : Fin d, T i.succ := by
      simp only [block, List.length_take] at hj; omega
    rw [getD_block _ _ _ hjR, lexFlat]
    exact getD_flatMap_const _ (T 0) _ (fun b _ => length_lexFlat _ _ _) b j hb hjR x

theorem flatPass_getD : ∀ (d : ℕ) (T : Fin d → ℕ) [∀ i, NeZero (T i)]
    (F : (i : Fin d) → (ZMod (T i) → ℂ) → (ZMod (T i) → ℂ)) (u : ((i : Fin d) → ZMod (T i)) → ℂ)
    (k : (i : Fin d) → ZMod (T i)),
    (flatPass d T (fun i => lineOf (F i)) 0 (lexFlat d T u)).getD (lexIdx d T k) 0 = tensorZR d T T F u k
  | 0, _, _, F, u, k => by
    simp only [flatPass, lexFlat, lexIdx, tensorZR]; simp
  | d + 1, T, _, F, u, k => by
    set R := ∏ i : Fin d, T i.succ with hR
    have hRpos : 0 < R := Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne _)
    have hT0 : 0 < T 0 := Nat.pos_of_ne_zero (NeZero.ne _)
    have hk0 := ZMod.val_lt (k 0)
    have hr := lexIdx_lt d (fun i => T i.succ) (Fin.tail k)
    have hxs : (lexFlat (d + 1) T u).length = T 0 * R := by rw [length_lexFlat, Fin.prod_univ_succ]
    set W := mapBlocks R (flatPass d (fun i => T i.succ) (fun i => lineOf (F i.succ)) 0) (lexFlat (d + 1) T u)
    have hblk : ∀ b, b < T 0 → block R b (lexFlat (d + 1) T u) =
        lexFlat d (fun i => T i.succ) (fun j => u (Fin.cons ((b : ℕ) : ZMod (T 0)) j)) :=
      fun b hb => block_lexFlat d T u b hb 0
    have hgW : ∀ b, b < T 0 → (flatPass d (fun i => T i.succ) (fun i => lineOf (F i.succ)) 0
        (block R b (lexFlat (d + 1) T u))).length = R := fun b hb => by
      rw [hblk b hb]; exact length_flatPass d _ (fun i => F i.succ) _ (length_lexFlat _ _ _)
    set W := mapBlocks R (flatPass d (fun i => T i.succ) (fun i => lineOf (F i.succ)) 0) (lexFlat (d + 1) T u)
    set Z := trL (T 0) R 0 W
    set Y := mapBlocks (T 0) (lineOf (F 0)) Z
    show (trL R (T 0) 0 Y).getD ((k 0).val * R + lexIdx d (fun i => T i.succ) (Fin.tail k)) 0 = _
    rw [getD_trL R (T 0) 0 Y hr hk0,
      getD_mapBlocks (T 0) (T 0) R (lineOf (F 0)) Z hT0 (by rw [length_trL]) (fun b _ => length_lineOf _ _) hr hk0]
    simp only [lineOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk0, Option.map_some,
      Option.getD_some]
    rw [ZMod.natCast_zmod_val, tensorZR_succ_apply]
    congr 1
    funext j
    have hj := ZMod.val_lt j
    rw [← List.getD_eq_getElem?_getD, getD_block _ _ _ hj, getD_trL (T 0) R 0 W hj hr,
      getD_mapBlocks R R (T 0) _ _ hRpos hxs hgW hj hr, hblk _ hj, flatPass_getD d _ (fun i => F i.succ)]
    simp only [ZMod.natCast_zmod_val]

/-- The flat pass computes the square tensor on flat lists. -/
theorem flatPass_lexFlat (d : ℕ) (T : Fin d → ℕ) [∀ i, NeZero (T i)]
    (F : (i : Fin d) → (ZMod (T i) → ℂ) → (ZMod (T i) → ℂ)) (u : ((i : Fin d) → ZMod (T i)) → ℂ) :
    flatPass d T (fun i => lineOf (F i)) 0 (lexFlat d T u) = lexFlat d T (tensorZR d T T F u) := by
  apply ext_getD' 0
  · rw [length_flatPass d T F _ (length_lexFlat _ _ _), length_lexFlat]
  · intro z hz
    rw [length_flatPass d T F _ (length_lexFlat _ _ _)] at hz
    obtain ⟨k, rfl⟩ := lexIdx_surj d T z hz
    rw [flatPass_getD, lexFlat_getD]

end IntegerMultBounds.Resampling.FlatTensor
