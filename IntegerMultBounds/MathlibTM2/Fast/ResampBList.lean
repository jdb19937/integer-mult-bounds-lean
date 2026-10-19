module

public import IntegerMultBounds.MathlibTM2.Node.SwapPass
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-!
# Line maps on box streams

A box array on `∏_{i<d} [0, t_i)` is stored as the stream of its values in address order,
axis `0` most significant (`rsbBox`). A line map along one axis of a list laid out as
`[P] × [H] × [Q]` (`H` the axis, `Q` the stride) is `rsbAxisL P H Q g`: every line
`(p, ·, q)` is replaced by its image under `g`.

* `rsbChunkMap Q n f l`: `f` on each of the `n` consecutive chunks of length `Q`.
* `rsbAxisL_inner`: along the innermost axis (`Q = 1`) the lines are the chunks of length `H`.
* `rsbAxisL_swap`: interchanging the axis `H` with an inner axis `D` across a block `G`
  (`swapList P H G D 1`), mapping the innermost lines, and interchanging back is the line map
  along `H` with stride `G D`.
* `rsbAxisL_box`, `rsbChunkMap_box`: line maps along axis `0` and slicewise maps of box streams.
* `rsbAxesL`: line maps along all axes in the order of `tensorZR`; `rsbAxesL_flat`: on a box
  stream they are the line maps along the axes `d - 1, …, 0` of the whole stream (`rsbFlat`).
* `rsb_swapList_cstream_bits`: the interchange of a coefficient stream, in bits.

The statements and proofs are those of the `Ã` stage (`ResampA` namespace), kept here under
`rsb` names for the `B̃₀` stage.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node


/-! ### Chunks -/

section Chunks

variable {α : Type}

/-- The first `n` chunks of length `Q` of `l`. -/
def rsbChunks (Q n : ℕ) (l : List α) : List (List α) :=
  (List.range n).map fun c => (l.drop (c * Q)).take Q

/-- `f` on each of the first `n` chunks of length `Q`. -/
def rsbChunkMap (Q n : ℕ) (f : List α → List α) (l : List α) : List α :=
  (rsbChunks Q n l).flatMap f

lemma rsbChunks_succ (Q n : ℕ) (l : List α) :
    rsbChunks Q (n + 1) l = rsbChunks Q n l ++ [(l.drop (n * Q)).take Q] := by
  simp [rsbChunks, List.range_succ]

lemma rsbChunk_take {l : List α} {Q n c : ℕ} (hc : c < n) :
    ((l.take (n * Q)).drop (c * Q)).take Q = (l.drop (c * Q)).take Q := by
  have hle : Q ≤ n * Q - c * Q := by
    have : (c + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, one_mul] at this
    omega
  rw [List.drop_take, List.take_take, Nat.min_eq_left hle]

lemma flatten_rsbChunks (Q : ℕ) : ∀ (n : ℕ) (l : List α), l.length = n * Q →
    (rsbChunks Q n l).flatten = l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      rw [Nat.zero_mul, List.length_eq_zero_iff] at hl
      simp [rsbChunks, hl]
  | succ n ih =>
      intro l hl
      have hl' : (l.take (n * Q)).length = n * Q := by
        simp only [List.length_take, hl]
        exact Nat.min_eq_left (Nat.mul_le_mul_right _ (Nat.le_succ n))
      have e : rsbChunks Q n l = rsbChunks Q n (l.take (n * Q)) := by
        simp only [rsbChunks]
        refine List.map_congr_left fun c hc => ?_
        rw [rsbChunk_take (List.mem_range.1 hc)]
      have hd : (l.drop (n * Q)).take Q = l.drop (n * Q) :=
        List.take_of_length_le (by simp [hl, Nat.succ_mul])
      rw [rsbChunks_succ, List.flatten_append, e, ih _ hl', hd]
      simp

lemma length_rsbChunkMap (Q n R : ℕ) (f : List α → List α) (l : List α)
    (hf : ∀ x, (f x).length = R) : (rsbChunkMap Q n f l).length = n * R := by
  simp [rsbChunkMap, List.length_flatMap, hf, rsbChunks, Function.comp_def, List.map_const',
    List.sum_replicate]

end Chunks

/-! ### Line maps along one axis -/

/-- The line maps of one block of `H Q` values: output `h Q + q` is entry `h` of the image of
the line `(·, q)`. -/
def rsbBlockOp (H Q : ℕ) (g : List GaussianInt → List GaussianInt) (b : List GaussianInt) :
    List GaussianInt :=
  (List.range (H * Q)).map fun z =>
    (g ((List.range H).map fun h => b.getD (h * Q + z % Q) 0)).getD (z / Q) 0

/-- The line map `g` along the middle axis of `[P] × [H] × [Q]`. -/
def rsbAxisL (P H Q : ℕ) (g : List GaussianInt → List GaussianInt) (l : List GaussianInt) :
    List GaussianInt :=
  rsbChunkMap (H * Q) P (rsbBlockOp H Q g) l

lemma length_rsbBlockOp (H Q : ℕ) (g : List GaussianInt → List GaussianInt)
    (b : List GaussianInt) : (rsbBlockOp H Q g b).length = H * Q := by
  simp [rsbBlockOp]

lemma length_rsbAxisL (P H Q : ℕ) (g : List GaussianInt → List GaussianInt)
    (l : List GaussianInt) : (rsbAxisL P H Q g l).length = P * (H * Q) :=
  length_rsbChunkMap _ _ _ _ _ (length_rsbBlockOp H Q g)

/-- The line of a block through offset `q`. -/
lemma rsbBlockOp_getD (H Q : ℕ) (g : List GaussianInt → List GaussianInt) (b : List GaussianInt)
    {h q : ℕ} (hh : h < H) (hq : q < Q) :
    (rsbBlockOp H Q g b).getD (h * Q + q) 0 =
      (g ((List.range H).map fun h' => b.getD (h' * Q + q) 0)).getD h 0 := by
  have hz : h * Q + q < H * Q := by nlinarith
  rw [rsbBlockOp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hz]
  simp only [Option.map_some, Option.getD_some]
  rw [show (h * Q + q) % Q = q by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hq],
    show (h * Q + q) / Q = h by rw [Nat.mul_comm, Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt hq, Nat.add_zero]]

/-- Along the innermost axis a block is one line. -/
lemma rsbBlockOp_one (H : ℕ) (g : List GaussianInt → List GaussianInt) (b : List GaussianInt)
    (hb : b.length = H) (hg : (g b).length = H) : rsbBlockOp H 1 g b = g b := by
  apply List.ext_getElem (by simp [length_rsbBlockOp, hg])
  intro z h₁ h₂
  simp only [rsbBlockOp, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.div_one, List.getElem_map,
    List.getElem_range]
  have hl : ((List.range H).map fun h => b.getD h 0) = b := by
    apply List.ext_getElem (by simp [hb])
    intro i hi₁ hi₂
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
  rw [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  rfl

/-- Along the innermost axis the lines are the chunks of length `H`. -/
lemma rsbAxisL_inner (P H : ℕ) (g : List GaussianInt → List GaussianInt) (l : List GaussianInt)
    (hl : l.length = P * H) (hg : ∀ x, x.length = H → (g x).length = H) :
    rsbAxisL P H 1 g l = rsbChunkMap H P g l := by
  unfold rsbAxisL rsbChunkMap
  rw [Nat.mul_one]
  refine List.flatMap_congr fun b hb => ?_
  simp only [rsbChunks, List.mem_map, List.mem_range] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have hbl : ((l.drop (c * H)).take H).length = H := by
    simp only [List.length_take, List.length_drop, hl]
    have : (c + 1) * H ≤ P * H := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, one_mul] at this
    omega
  exact rsbBlockOp_one H g _ hbl (hg _ hbl)

/-! ### Chunkwise maps -/

section ChunkLemmas

variable {α : Type}

lemma rsbChunkMap_eq (Q n : ℕ) (f : List α → List α) (l : List α) :
    rsbChunkMap Q n f l = (List.range n).flatMap fun c => f ((l.drop (c * Q)).take Q) := by
  simp [rsbChunkMap, rsbChunks, List.flatMap_map]

/-- A flatMap over `range (n P)` as a double flatMap. -/
lemma rsb_flatMap_range_mul {β : Type} (n P : ℕ) (F : ℕ → List β) :
    (List.range (n * P)).flatMap F =
      (List.range n).flatMap fun c => (List.range P).flatMap fun p => F (c * P + p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ,
        List.flatMap_append, List.flatMap_map]
      simp

/-- Chunk `c` of a concatenation of blocks of length `Q`. -/
lemma rsb_drop_take_flatten {Q : ℕ} : ∀ (blocks : List (List α)), (∀ b ∈ blocks, b.length = Q) →
    ∀ c, c < blocks.length → ((blocks.flatten).drop (c * Q)).take Q = blocks[c]!
  | [], _, c, hc => by simp at hc
  | b :: bs, h, c, hc => by
      have hb : b.length = Q := h b (by simp)
      cases c with
      | zero =>
          simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons]
          rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
          rfl
      | succ c =>
          simp only [List.flatten_cons, Nat.succ_mul]
          rw [show c * Q + Q = b.length + c * Q by omega, ← List.drop_drop,
            List.drop_left' rfl]
          simpa using rsb_drop_take_flatten bs (fun b' hb' => h b' (by simp [hb'])) c
            (by simpa using hc)

/-- Chunk `c` of a chunkwise map. -/
lemma rsbChunkMap_chunk (Q n : ℕ) (f : List α → List α) (hf : ∀ x, (f x).length = Q)
    (l : List α) {c : ℕ} (hc : c < n) :
    ((rsbChunkMap Q n f l).drop (c * Q)).take Q = f ((l.drop (c * Q)).take Q) := by
  unfold rsbChunkMap
  rw [List.flatMap_def, rsb_drop_take_flatten _ (by simp [hf]) c (by simp [rsbChunks, hc])]
  simp [rsbChunks, hc]

end ChunkLemmas

/-- Block `p` of chunk `c`. -/
lemma rsb_drop_take_drop_take {α : Type} (l : List α) {a b k m : ℕ} (h : k + m ≤ b) :
    (((l.drop a).take b).drop k).take m = (l.drop (a + k)).take m := by
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

/-- Chunkwise line maps are line maps of the whole list. -/
lemma rsbChunkMap_axisL (n P H R : ℕ) (g : List GaussianInt → List GaussianInt)
    (l : List GaussianInt) :
    rsbChunkMap (P * (H * R)) n (rsbAxisL P H R g) l = rsbAxisL (n * P) H R g l := by
  rw [rsbChunkMap_eq, rsbAxisL, rsbChunkMap_eq, rsb_flatMap_range_mul]
  refine List.flatMap_congr fun c hc => ?_
  rw [rsbAxisL, rsbChunkMap_eq]
  refine List.flatMap_congr fun p hp => ?_
  have hp' := List.mem_range.1 hp
  have hle : p * (H * R) + H * R ≤ P * (H * R) := by
    have := Nat.mul_le_mul_right (H * R) hp'
    rw [Nat.succ_mul] at this; exact this
  rw [rsb_drop_take_drop_take l hle]
  congr 3
  ring

/-! ### Interchange of two axes -/

lemma rsb_decomp4 {P H G D z : ℕ} (hz : z < P * H * G * D) :
    ∃ p h γ δ, p < P ∧ h < H ∧ γ < G ∧ δ < D ∧ z = ((p * H + h) * G + γ) * D + δ := by
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; simp at hz
    · exact h
  have hG : 0 < G := by
    rcases Nat.eq_zero_or_pos G with h | h
    · subst h; simp at hz
    · exact h
  have hH : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h | h
    · subst h; simp at hz
    · exact h
  refine ⟨z / D / G / H, z / D / G % H, z / D % G, z % D, ?_, Nat.mod_lt _ hH, Nat.mod_lt _ hG,
    Nat.mod_lt _ hD, ?_⟩
  · apply Nat.div_lt_of_lt_mul
    apply Nat.div_lt_of_lt_mul
    apply Nat.div_lt_of_lt_mul
    calc z < P * H * G * D := hz
      _ = D * (G * (H * P)) := by ring
  · rw [Nat.mul_comm (z / D / G / H) H, Nat.div_add_mod (z / D / G) H,
      Nat.mul_comm (z / D / G) G, Nat.div_add_mod (z / D) G, Nat.mul_comm (z / D) D,
      Nat.div_add_mod z D]

/-- **Moving an axis innermost.** Interchanging the axis `H` with the axis `D` (across the
block `G`), the line map along the now innermost `H`, and the interchange back, together are
the line map along `H` with stride `G D`. -/
theorem rsbAxisL_swap (P H G D : ℕ) (g : List GaussianInt → List GaussianInt)
    (hg : ∀ x, (g x).length = H) (l : List GaussianInt) (hl : l.length = P * H * G * D) :
    swapList P D G H 1 0 (rsbAxisL (P * D * G) H 1 g (swapList P H G D 1 0 l)) =
      rsbAxisL P H (G * D) g l := by
  have hlen₂ : (swapList P H G D 1 0 l).length = P * D * G * H * 1 := by
    simp [swapList]
  have hlen₃ : (rsbAxisL (P * D * G) H 1 g (swapList P H G D 1 0 l)).length =
      P * D * G * H * 1 := by
    rw [length_rsbAxisL]; ring
  apply List.ext_getElem?
  intro z
  by_cases hz : z < P * H * G * D
  · obtain ⟨p, h, γ, δ, hp, hh, hγ, hδ, rfl⟩ := rsb_decomp4 hz
    have e₁ := swapList_getElem? (P := P) (H := D) (G := G) (D := H) (B := 1) 0
      (rsbAxisL (P * D * G) H 1 g (swapList P H G D 1 0 l)) hlen₃ hp hδ hγ hh (Nat.zero_lt_one)
    simp only [Nat.mul_one, Nat.add_zero] at e₁
    rw [e₁]
    -- the right-hand side as a block entry
    have hR : (rsbAxisL P H (G * D) g l)[((p * H + h) * G + γ) * D + δ]? =
        some ((g ((List.range H).map fun h' =>
          l.getD (((p * H + h') * G + γ) * D + δ) 0)).getD h 0) := by
      have hlenR := length_rsbAxisL P H (G * D) g l
      have hidx : ((p * H + h) * G + γ) * D + δ =
          p * (H * (G * D)) + (h * (G * D) + (γ * D + δ)) := by
        ring
      have hlt : ((p * H + h) * G + γ) * D + δ < (rsbAxisL P H (G * D) g l).length := by
        rw [hlenR]
        have := mix_lt (mix_lt (mix_lt hp hh) hγ) hδ
        linarith [show P * H * G * D = P * (H * (G * D)) by ring]
      rw [List.getElem?_eq_getElem hlt]
      congr 1
      rw [← List.getD_eq_getElem _ 0 hlt, rsbAxisL, hidx]
      have hchunk := rsbChunkMap_chunk (H * (G * D)) P (rsbBlockOp H (G * D) g)
        (length_rsbBlockOp H (G * D) g) l hp
      have hin : h * (G * D) + (γ * D + δ) < H * (G * D) := mix_lt hh (mix_lt hγ hδ)
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, ← List.getElem?_take_of_lt hin,
        hchunk, ← List.getD_eq_getElem?_getD,
        rsbBlockOp_getD H (G * D) g _ hh (mix_lt hγ hδ)]
      congr 2
      refine List.map_congr_left fun h' hh' => ?_
      have hh'' := List.mem_range.1 hh'
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt
        (mix_lt hh'' (mix_lt hγ hδ)), List.getElem?_drop]
      congr 2
      ring
    rw [hR]
    -- the left-hand side
    have hlt₃ : ((p * D + δ) * G + γ) * H + h < (rsbAxisL (P * D * G) H 1 g
        (swapList P H G D 1 0 l)).length := by
      rw [hlen₃]
      have := mix_lt (mix_lt (mix_lt hp hδ) hγ) hh
      linarith
    rw [List.getElem?_eq_getElem hlt₃]
    congr 1
    rw [← List.getD_eq_getElem _ 0 hlt₃, rsbAxisL_inner (P * D * G) H g _ (by rw [hlen₂]; ring)
      (fun x _ => hg x)]
    have hc : (p * D + δ) * G + γ < P * D * G := mix_lt (mix_lt hp hδ) hγ
    have hchunk := rsbChunkMap_chunk H (P * D * G) g hg (swapList P H G D 1 0 l) hc
    rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop,
      ← List.getElem?_take_of_lt hh, hchunk, ← List.getD_eq_getElem?_getD]
    congr 2
    have hc' : (((p * D + δ) * G + γ) + 1) * H ≤ P * D * G * H := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at hc'
    apply List.ext_getElem (by
      simp only [List.length_take, List.length_drop, hlen₂, List.length_map, List.length_range]
      omega)
    intro h' h₁ h₂
    have hh' : h' < H := by simpa using h₂
    simp only [List.getElem_map, List.getElem_range]
    have e₂ := swapList_getElem? (P := P) (H := H) (G := G) (D := D) (B := 1) 0 l
      (by rw [hl]; ring) hp hh' hγ hδ (Nat.zero_lt_one)
    simp only [Nat.mul_one, Nat.add_zero] at e₂
    rw [List.getElem_take, List.getElem_drop]
    have hlt₂ : ((p * D + δ) * G + γ) * H + h' < (swapList P H G D 1 0 l).length := by
      rw [hlen₂]
      have := mix_lt (mix_lt (mix_lt hp hδ) hγ) hh'
      linarith
    have e₃ : (swapList P H G D 1 0 l)[((p * D + δ) * G + γ) * H + h'] =
        l.getD (((p * H + h') * G + γ) * D + δ) 0 := by
      have := e₂
      rw [List.getElem?_eq_getElem hlt₂] at this
      rw [List.getD_eq_getElem?_getD, ← this]
      rfl
    rw [← e₃]
  · have hz' : P * H * G * D ≤ z := Nat.le_of_not_lt hz
    have e : P * H * G * D = P * (H * (G * D)) := by ring
    have h1 : (swapList P D G H 1 0 (rsbAxisL (P * D * G) H 1 g
        (swapList P H G D 1 0 l))).length ≤ z := by
      simp only [swapList, List.length_map, List.length_range]; linarith
    have h2 : (rsbAxisL P H (G * D) g l).length ≤ z := by rw [length_rsbAxisL]; linarith
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-! ### Box streams -/

section Box

/-- The stream of an array on `∏_{i<d} [0, t_i)`, axis `0` most significant. -/
def rsbBox {α : Type} : (d : ℕ) → (t : Fin d → ℕ) → (((i : Fin d) → Fin (t i)) → α) → List α
  | 0, _, F => [F fun i => i.elim0]
  | d + 1, t, F => (List.finRange (t 0)).flatMap fun x₀ =>
      rsbBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))

lemma length_rsbBox {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ) (F : ((i : Fin d) → Fin (t i)) → α),
    (rsbBox d t F).length = ∏ i, t i
  | 0, _, _ => by simp [rsbBox]
  | d + 1, t, F => by
      rw [rsbBox, List.length_flatMap, Fin.prod_univ_succ]
      simp only [length_rsbBox d]
      simp [List.sum_replicate]

lemma rsbBox_map {α β : Type} (φ : α → β) : ∀ (d : ℕ) (t : Fin d → ℕ)
    (F : ((i : Fin d) → Fin (t i)) → α), rsbBox d t (fun x => φ (F x)) = (rsbBox d t F).map φ
  | 0, _, _ => by simp [rsbBox]
  | d + 1, t, F => by
      simp only [rsbBox, List.map_flatMap]
      exact List.flatMap_congr fun x₀ _ => rsbBox_map φ d _ _

/-- The chunks of a box stream along axis `0` are the streams of its slices. -/
lemma rsbBox_chunks {α : Type} (d : ℕ) (t : Fin (d + 1) → ℕ)
    (F : ((i : Fin (d + 1)) → Fin (t i)) → α) :
    rsbChunks (∏ i : Fin d, t i.succ) (t 0) (rsbBox (d + 1) t F) =
      (List.finRange (t 0)).map fun x₀ =>
        rsbBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y)) := by
  apply List.ext_getElem (by simp [rsbChunks])
  intro c h₁ h₂
  have hc : c < t 0 := by simpa [rsbChunks] using h₁
  simp only [rsbChunks, List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [rsbBox, List.flatMap_def, rsb_drop_take_flatten _ (by
    intro b hb
    simp only [List.mem_map, List.mem_finRange, true_and] at hb
    obtain ⟨x₀, rfl⟩ := hb
    exact length_rsbBox _ _ _) c (by simpa using hc)]
  simp [hc]

end Box

/-! ### Line maps along all axes -/

/-- Line maps along all axes in the order of `tensorZR`: the axes `1, …, d` slice by slice, then
axis `0`. -/
def rsbAxesL : (d : ℕ) → (t : Fin d → ℕ) → (Fin d → List GaussianInt → List GaussianInt) →
    List GaussianInt → List GaussianInt
  | 0, _, _ => id
  | d + 1, t, g => fun l =>
      rsbAxisL 1 (t 0) (∏ i : Fin d, t i.succ) (g 0)
        (rsbChunkMap (∏ i : Fin d, t i.succ) (t 0)
          (rsbAxesL d (fun i => t i.succ) (fun i => g i.succ)) l)

/-- Entry `x₀ Q + a` of a box stream is entry `a` of the slice `x₀`. -/
lemma rsbBox_getD_succ {α : Type} [Inhabited α] (d : ℕ) (t : Fin (d + 1) → ℕ)
    (F : ((i : Fin (d + 1)) → Fin (t i)) → α) (dflt : α) {x₀ a : ℕ} (hx₀ : x₀ < t 0)
    (ha : a < ∏ i : Fin d, t i.succ) :
    (rsbBox (d + 1) t F).getD (x₀ * (∏ i : Fin d, t i.succ) + a) dflt =
      (rsbBox d (fun i => t i.succ) (fun y => F (Fin.cons ⟨x₀, hx₀⟩ y))).getD a dflt := by
  have h := rsb_drop_take_flatten ((List.finRange (t 0)).map fun x₀ =>
    rsbBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))) (by
      intro b hb
      simp only [List.mem_map, List.mem_finRange, true_and] at hb
      obtain ⟨x₀, rfl⟩ := hb
      exact length_rsbBox _ _ _) x₀ (by simpa using hx₀)
  rw [rsbBox, List.flatMap_def, List.getD_eq_getElem?_getD, ← List.getElem?_drop,
    ← List.getElem?_take_of_lt ha, h]
  simp [hx₀, List.getD_eq_getElem?_getD]

/-- A box stream through one line map along axis `0`. -/
lemma rsbAxisL_box (d : ℕ) (t : Fin (d + 1) → ℕ) (g : List GaussianInt → List GaussianInt)
    (F : ((i : Fin (d + 1)) → Fin (t i)) → GaussianInt) :
    rsbAxisL 1 (t 0) (∏ i : Fin d, t i.succ) g (rsbBox (d + 1) t F) =
      rsbBox (d + 1) t (fun x => (g ((List.finRange (t 0)).map fun j =>
        F (Fin.cons j (Fin.tail x)))).getD (x 0) 0) := by
  set Q := ∏ i : Fin d, t i.succ with hQ
  have hlen : (rsbBox (d + 1) t F).length = t 0 * Q := by
    rw [length_rsbBox, Fin.prod_univ_succ]
  -- the vectors of the slices
  set V : ((i : Fin d) → Fin (t i.succ)) → (Fin (t 0) → GaussianInt) :=
    fun y j => F (Fin.cons j y) with hV
  have hlenV : (rsbBox d (fun i => t i.succ) V).length = Q := length_rsbBox _ _ _
  have hslice : ∀ (j : Fin (t 0)) (a : ℕ),
      (rsbBox d (fun i => t i.succ) (fun y => F (Fin.cons j y))).getD a 0 =
        ((rsbBox d (fun i => t i.succ) V).getD a 0) j := by
    intro j a
    have := rsbBox_map (fun v : Fin (t 0) → GaussianInt => v j) d (fun i => t i.succ) V
    simp only [hV] at this
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (rsbBox d (fun i => t i.succ) V)[a]? <;> rfl
  have e1 : rsbAxisL 1 (t 0) Q g (rsbBox (d + 1) t F) =
      rsbBlockOp (t 0) Q g (rsbBox (d + 1) t F) := by
    rw [rsbAxisL, rsbChunkMap_eq]
    simp [List.take_of_length_le (le_of_eq hlen)]
  rw [e1]
  apply List.ext_getElem
  · rw [length_rsbBlockOp, length_rsbBox, Fin.prod_univ_succ]
  intro z h₁ h₂
  have h₁' := h₁
  rw [length_rsbBlockOp] at h₁'
  have hQ0 : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, Nat.mul_zero] at h₁'; omega
    · exact h
  obtain ⟨x₀, a, hx₀, ha, rfl⟩ : ∃ x₀ a, x₀ < t 0 ∧ a < Q ∧ z = x₀ * Q + a :=
    ⟨z / Q, z % Q, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h₁'), Nat.mod_lt _ hQ0,
      (Nat.div_add_mod' z Q).symm⟩
  rw [← List.getD_eq_getElem _ 0 h₁, rsbBlockOp_getD (t 0) Q g _ hx₀ ha,
    ← List.getD_eq_getElem _ 0 h₂, rsbBox_getD_succ d t _ 0 hx₀ ha]
  simp only [Fin.tail_cons, Fin.cons_zero]
  have hmap := rsbBox_map (fun v : Fin (t 0) → GaussianInt =>
    (g ((List.finRange (t 0)).map v)).getD x₀ 0) d (fun i => t i.succ) V
  simp only [hV] at hmap
  rw [hmap]
  conv_rhs => rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hlenV]; exact ha),
    List.getElem_map]
  congr 2
  apply List.ext_getElem (by simp)
  intro j hj₁ hj₂
  have hj : j < t 0 := by simpa using hj₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [rsbBox_getD_succ d t _ 0 hj ha, hslice ⟨j, hj⟩ a,
    List.getD_eq_getElem _ _ (by rw [hlenV]; exact ha)]
  rfl

/-- A chunkwise map of a box stream acting slice by slice. -/
lemma rsbChunkMap_box (d : ℕ) (t : Fin (d + 1) → ℕ) (f : List GaussianInt → List GaussianInt)
    (F G : ((i : Fin (d + 1)) → Fin (t i)) → GaussianInt)
    (h : ∀ x₀ : Fin (t 0), f (rsbBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))) =
      rsbBox d (fun i => t i.succ) (fun y => G (Fin.cons x₀ y))) :
    rsbChunkMap (∏ i : Fin d, t i.succ) (t 0) f (rsbBox (d + 1) t F) = rsbBox (d + 1) t G := by
  rw [rsbChunkMap, rsbBox_chunks, List.flatMap_map, rsbBox]
  exact List.flatMap_congr fun x₀ _ => h x₀

/-! ### The axes one at a time -/

/-- The product of the sizes of the axes before `i`. -/
def rsbPre {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : ℕ := ((List.ofFn t).take i).prod

/-- The stride of axis `i`: the product of the sizes of the axes after `i`. -/
def rsbSuf {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : ℕ := ((List.ofFn t).drop (i + 1)).prod

/-- The line map along axis `i` of the whole box stream. -/
def rsbAxisOp {d : ℕ} (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (i : Fin d) : List GaussianInt → List GaussianInt :=
  rsbAxisL (rsbPre t i) (t i) (rsbSuf t i) (g i)

/-- The line maps along the axes `i, …, d - 1`, the last axis first. -/
def rsbFlat (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt) (i : ℕ)
    (l : List GaussianInt) : List GaussianInt :=
  ((List.finRange d).drop i).foldr (fun j acc => rsbAxisOp t g j acc) l

lemma rsbFlat_ge (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    {i : ℕ} (hi : d ≤ i) (l : List GaussianInt) : rsbFlat d t g i l = l := by
  rw [rsbFlat, List.drop_eq_nil_of_le (by rw [List.length_finRange]; exact hi)]
  rfl

lemma rsbFlat_lt (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    {i : ℕ} (hi : i < d) (l : List GaussianInt) :
    rsbFlat d t g i l = rsbAxisOp t g ⟨i, hi⟩ (rsbFlat d t g (i + 1) l) := by
  rw [rsbFlat, List.drop_eq_getElem_cons (by simpa using hi)]
  simp [rsbFlat]

lemma rsbPre_succ {d : ℕ} (t : Fin (d + 1) → ℕ) (i : ℕ) :
    rsbPre t (i + 1) = t 0 * rsbPre (fun j : Fin d => t j.succ) i := by
  simp [rsbPre, List.ofFn_succ]

lemma rsbPre_zero {d : ℕ} (t : Fin d → ℕ) : rsbPre t 0 = 1 := by simp [rsbPre]

lemma rsbSuf_succ {d : ℕ} (t : Fin (d + 1) → ℕ) (i : ℕ) :
    rsbSuf t (i + 1) = rsbSuf (fun j : Fin d => t j.succ) i := by
  simp [rsbSuf, List.ofFn_succ]

lemma rsbSuf_zero {d : ℕ} (t : Fin (d + 1) → ℕ) : rsbSuf t 0 = ∏ i : Fin d, t i.succ := by
  simp [rsbSuf, List.ofFn_succ, List.prod_ofFn]

/-- Before, along, and after axis `i`: the whole box. -/
lemma rsbPre_mul {d : ℕ} (t : Fin d → ℕ) (i : Fin d) :
    rsbPre t i * (t i * rsbSuf t i) = ∏ j, t j := by
  have h1 := List.prod_take_mul_prod_drop (List.ofFn t) i
  have h2 : (List.ofFn t).drop i = t i :: (List.ofFn t).drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (by simp)]; simp
  rw [← List.prod_ofFn, ← h1, h2, List.prod_cons, rsbPre, rsbSuf]

lemma rsbChunkMap_congr {α : Type} {Q n : ℕ} {f f' : List α → List α}
    (h : ∀ x, x.length = Q → f x = f' x) {l : List α} (hl : l.length = n * Q) :
    rsbChunkMap Q n f l = rsbChunkMap Q n f' l := by
  rw [rsbChunkMap_eq, rsbChunkMap_eq]
  refine List.flatMap_congr fun c hc => h _ ?_
  have hc' := List.mem_range.1 hc
  simp only [List.length_take, List.length_drop, hl]
  have : (c + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hc'
  rw [Nat.succ_mul] at this
  omega

lemma rsbChunkMap_comp' {α : Type} (Q n : ℕ) (f f' : List α → List α)
    (hf' : ∀ x, x.length = Q → (f' x).length = Q) (l : List α) (hl : l.length = n * Q) :
    rsbChunkMap Q n f (rsbChunkMap Q n f' l) = rsbChunkMap Q n (f ∘ f') l := by
  have hlen : ∀ c, c < n → ((l.drop (c * Q)).take Q).length = Q := by
    intro c hc
    simp only [List.length_take, List.length_drop, hl]
    have : (c + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at this
    omega
  conv_lhs => rw [rsbChunkMap_eq]
  conv_rhs => rw [rsbChunkMap_eq]
  refine List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.1 hc
  have h := rsb_drop_take_flatten ((rsbChunks Q n l).map f') (by
    intro b hb
    simp only [List.mem_map, rsbChunks, List.mem_range] at hb
    obtain ⟨_, ⟨c', hc'', rfl⟩, rfl⟩ := hb
    exact hf' _ (hlen c' hc'')) c (by simp [rsbChunks, hc'])
  rw [rsbChunkMap, List.flatMap_def, h]
  simp [rsbChunks, hc']

/-- The chunkwise line maps along the axes of the slices are line maps of the whole box. -/
lemma rsbChunkMap_foldr {d : ℕ} (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (n : ℕ) : ∀ (is : List (Fin d)) (l : List GaussianInt), l.length = n * ∏ j, t j →
      rsbChunkMap (∏ j, t j) n (fun x => is.foldr (fun (j : Fin d) acc => rsbAxisOp t g j acc) x)
        l = is.foldr (fun (j : Fin d) acc =>
          rsbAxisL (n * rsbPre t (j : ℕ)) (t j) (rsbSuf t (j : ℕ)) (g j) acc) l
  | [], l, hl => by
      simp only [List.foldr_nil]
      rw [rsbChunkMap, List.flatMap_id']
      exact flatten_rsbChunks _ n l hl
  | j :: is, l, hl => by
      simp only [List.foldr_cons]
      have hc := rsbChunkMap_comp' (∏ j, t j) n (rsbAxisOp t g j)
        (fun x => is.foldr (fun (j : Fin d) acc => rsbAxisOp t g j acc) x) (by
          intro x hx
          cases is with
          | nil => simpa using hx
          | cons k is => simp [rsbAxisOp, length_rsbAxisL, rsbPre_mul]) l hl
      rw [← show (rsbAxisOp t g j ∘ fun x => is.foldr (fun (j : Fin d) acc =>
        rsbAxisOp t g j acc) x) = fun x => rsbAxisOp t g j (is.foldr (fun (j : Fin d) acc =>
          rsbAxisOp t g j acc) x) from rfl, ← hc, rsbChunkMap_foldr t g n is l hl]
      rw [rsbAxisOp, ← rsbPre_mul t j, rsbChunkMap_axisL]

/-- **The axes one at a time.** On a box stream, the line maps along all axes in the order of
`tensorZR` are the line maps along the axes `d - 1, …, 0` of the whole stream. -/
theorem rsbAxesL_flat : ∀ (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (l : List GaussianInt), l.length = ∏ i, t i → rsbAxesL d t g l = rsbFlat d t g 0 l
  | 0, _, _, l, _ => by simp [rsbAxesL, rsbFlat]
  | d + 1, t, g, l, hl => by
      have hl' : l.length = t 0 * ∏ i : Fin d, t i.succ := by rw [hl, Fin.prod_univ_succ]
      rw [rsbFlat, List.drop_zero, List.finRange_succ, List.foldr_cons, List.foldr_map]
      show rsbAxisL 1 (t 0) (∏ i : Fin d, t i.succ) (g 0) (rsbChunkMap (∏ i : Fin d, t i.succ)
        (t 0) (rsbAxesL d (fun i => t i.succ) (fun i => g i.succ)) l) = _
      rw [rsbChunkMap_congr (f' := fun x => rsbFlat d (fun i => t i.succ) (fun i => g i.succ) 0 x)
        (fun x hx => rsbAxesL_flat d _ _ x hx) hl']
      simp only [rsbFlat, List.drop_zero]
      rw [rsbChunkMap_foldr (fun i => t i.succ) (fun i => g i.succ) (t 0) _ l hl']
      simp only [rsbAxisOp, Fin.val_zero, rsbPre_zero, rsbSuf_zero, Fin.val_succ, rsbPre_succ,
        rsbSuf_succ]


/-! ### Interchanges of lists of records -/

lemma rsb_decomp5 {P D G H B z : ℕ} (hz : z < P * D * G * H * B) :
    ∃ p d g h b, p < P ∧ d < D ∧ g < G ∧ h < H ∧ b < B ∧
      z = (((p * D + d) * G + g) * H + h) * B + b := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hz
    · exact h
  have hz' : z / B < P * D * G * H := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hz)
  obtain ⟨p, d, g, h, hp, hd, hg, hh, he⟩ := rsb_decomp4 hz'
  exact ⟨p, d, g, h, z % B, hp, hd, hg, hh, Nat.mod_lt _ hB, by
    rw [← he, Nat.div_add_mod']⟩

lemma rsb_length_swapList {α : Type} (P H G D B : ℕ) (dflt : α) (l : List α) :
    (swapList P H G D B dflt l).length = P * D * G * H * B := by
  simp [swapList]

/-- The default element of an interchange of a list of the right length is irrelevant. -/
lemma rsb_swapList_dflt {α : Type} (P H G D B : ℕ) (d₁ d₂ : α) (l : List α)
    (hl : l.length = P * H * G * D * B) : swapList P H G D B d₁ l = swapList P H G D B d₂ l := by
  apply List.ext_getElem?
  intro z
  by_cases hz : z < P * D * G * H * B
  · obtain ⟨p, d, g, h, b, hp, hd, hg, hh, hb, rfl⟩ := rsb_decomp5 hz
    rw [swapList_getElem? d₁ l hl hp hh hg hd hb, swapList_getElem? d₂ l hl hp hh hg hd hb]
  · rw [List.getElem?_eq_none (by rw [rsb_length_swapList]; omega),
      List.getElem?_eq_none (by rw [rsb_length_swapList]; omega)]

lemma rsb_swapList_map {α β : Type} (f : α → β) (P H G D B : ℕ) (a : α) (l : List α) :
    swapList P H G D B (f a) (l.map f) = (swapList P H G D B a l).map f := by
  simp [swapList, List.getD_eq_getElem?_getD, List.getElem?_map]

/-- The interchange of a concatenation of blocks of `B` symbols is the concatenation of the
interchanged blocks. -/
lemma rsb_swapList_flatten {α : Type} (P H G D B : ℕ) (dflt : α) (blocks : List (List α))
    (hl : blocks.length = P * H * G * D) (hB : ∀ b ∈ blocks, b.length = B) :
    swapList P H G D B dflt blocks.flatten = (swapList P H G D 1 [] blocks).flatten := by
  have hlf : blocks.flatten.length = P * H * G * D * B := by
    rw [length_flatten_uniform _ hB, hl]
  have hl1 : blocks.length = P * H * G * D * 1 := by rw [hl, Nat.mul_one]
  have hmem : ∀ x ∈ swapList P H G D 1 [] blocks, x.length = B := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < P * D * G * H * 1 := by rwa [rsb_length_swapList] at hi
    obtain ⟨p, d, g, h, b, hp, hd, hg, hh, hb, rfl⟩ := rsb_decomp5 hi'
    have e := swapList_getElem? [] blocks hl1 hp hh hg hd hb
    rw [List.getElem?_eq_getElem hi] at e
    have hlt : (((p * H + h) * G + g) * D + d) * 1 + b < blocks.length := by
      rw [hl1]; exact mix_lt (mix_lt (mix_lt (mix_lt hp hh) hg) hd) hb
    rw [List.getElem?_eq_getElem hlt] at e
    rw [Option.some_inj.1 e]
    exact hB _ (List.getElem_mem _)
  apply List.ext_getElem?
  intro z
  by_cases hz : z < P * D * G * H * B
  · obtain ⟨p, d, g, h, b, hp, hd, hg, hh, hb, rfl⟩ := rsb_decomp5 hz
    rw [swapList_getElem? dflt _ hlf hp hh hg hd hb, flatten_getElem?_uniform _ hB _ _ hb,
      flatten_getElem?_uniform _ hmem _ _ hb]
    have e := swapList_getElem? [] blocks hl1 hp hh hg hd (Nat.zero_lt_one)
    simp only [Nat.mul_one, Nat.add_zero] at e
    rw [e]
  · rw [List.getElem?_eq_none (by rw [rsb_length_swapList]; omega), List.getElem?_eq_none]
    rw [length_flatten_uniform _ hmem, rsb_length_swapList]
    nlinarith

/-- The interchange of a coefficient stream, in bits. -/
lemma rsb_swapList_cstream_bits {A : ℕ} (P H G D w : ℕ) (L : List GaussianInt)
    (hL : L.length = P * H * G * D) :
    swapList P H G D (3 * w) blank (toBits (cstream A w L)) =
      toBits (cstream A w (swapList P H G D 1 0 L)) := by
  have hcs : ∀ L' : List GaussianInt, cstream A w L' = (L'.map (csyms A w)).flatten := by
    intro L'; simp [cstream, List.flatMap_def]
  rw [hcs, hcs, toBits_flatten, toBits_flatten,
    rsb_swapList_flatten P H G D (3 * w) blank _ (by simp [hL]) (by simp [length_toBits, csyms]),
    List.map_map, List.map_map]
  congr 1
  rw [rsb_swapList_dflt P H G D 1 [] ((toBits ∘ csyms A w) 0) _ (by simp [hL]),
    rsb_swapList_map (toBits ∘ csyms A w)]

lemma rsb_pairSym_lt_eight {A : ℕ} (hA : 4 ≤ A) (a b : Bool) : (pairSym A a b).val < 8 := by
  rw [pairSym_val hA]; cases a <;> cases b <;> simp

lemma rsb_cstream_lt_eight {A w : ℕ} (hA : 4 ≤ A) (L : List GaussianInt) :
    ∀ s ∈ cstream A w L, s.val < 8 := by
  intro s hs
  simp only [cstream, List.mem_flatMap, csyms, coeffSyms, List.mem_ofFn] at hs
  obtain ⟨_, _, t, rfl⟩ := hs
  exact rsb_pairSym_lt_eight hA _ _

/-- The step bound of one interchange: `c` steps of the interchange machine, `sb` symbols on the
bank, `n` stream symbols. -/
noncomputable def rsbSwapCost (T t₀ c sb n : ℕ) : ℕ :=
  (T + 12 * swapT t₀ + 5) * c + 6 * sb + 34 * n + 2 * T + 6 * swapT t₀ + 23

end IntegerMultBounds.MathlibTM2.Fast
