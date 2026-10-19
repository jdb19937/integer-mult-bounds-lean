module

public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import IntegerMultBounds.NLogN.ResamplingMultiNumeric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import IntegerMultBounds.MathlibTM2.Fast.CMul

/-!
# Line maps on box streams

A box array on `∏_{i<d} [0, t_i)` is stored as the stream of its values in address order,
axis `0` most significant (`rsaBox`). A line map along one axis of a list laid out as
`[P] × [H] × [Q]` (`H` the axis, `Q` the stride) is `rsaAxisL P H Q g`: every line
`(p, ·, q)` is replaced by its image under `g`.

* `rsaChunkMap Q n f l`: `f` on each of the `n` consecutive chunks of length `Q`.
* `rsaAxisL_inner`: along the innermost axis (`Q = 1`) the lines are the chunks of length `H`.
* `rsaChunkMap_axisL`: chunkwise line maps are line maps of the whole list.
* `rsaAxisL_swap`: interchanging the axis `H` with an inner axis `D` across a block `G`
  (`swapList P H G D 1`), mapping the innermost lines, and interchanging back is the line map
  along `H` with stride `G D`.
* `rsaBox d t F` and the tensor `rsa_tensor`: for line maps `g i` related to the numeric maps
  `A i` (`RsaLineRel`), the line maps along all axes, in the order of `tensorZR` (last axis
  first), turn the padded stream of the numerators of `u` into the stream of the numerators of
  `tensorZR d M t A u`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds.MathlibTM2.Host

/-! ### Chunks -/

section Chunks

variable {α : Type}

/-- The first `n` chunks of length `Q` of `l`. -/
def rsaChunks (Q n : ℕ) (l : List α) : List (List α) :=
  (List.range n).map fun c => (l.drop (c * Q)).take Q

/-- `f` on each of the first `n` chunks of length `Q`. -/
def rsaChunkMap (Q n : ℕ) (f : List α → List α) (l : List α) : List α :=
  (rsaChunks Q n l).flatMap f

lemma rsaChunks_succ (Q n : ℕ) (l : List α) :
    rsaChunks Q (n + 1) l = rsaChunks Q n l ++ [(l.drop (n * Q)).take Q] := by
  simp [rsaChunks, List.range_succ]

lemma rsaChunk_take {l : List α} {Q n c : ℕ} (hc : c < n) :
    ((l.take (n * Q)).drop (c * Q)).take Q = (l.drop (c * Q)).take Q := by
  have hle : Q ≤ n * Q - c * Q := by
    have : (c + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, one_mul] at this
    omega
  rw [List.drop_take, List.take_take, Nat.min_eq_left hle]

lemma flatten_rsaChunks (Q : ℕ) : ∀ (n : ℕ) (l : List α), l.length = n * Q →
    (rsaChunks Q n l).flatten = l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      rw [Nat.zero_mul, List.length_eq_zero_iff] at hl
      simp [rsaChunks, hl]
  | succ n ih =>
      intro l hl
      have hl' : (l.take (n * Q)).length = n * Q := by
        simp only [List.length_take, hl]
        exact Nat.min_eq_left (Nat.mul_le_mul_right _ (Nat.le_succ n))
      have e : rsaChunks Q n l = rsaChunks Q n (l.take (n * Q)) := by
        simp only [rsaChunks]
        refine List.map_congr_left fun c hc => ?_
        rw [rsaChunk_take (List.mem_range.1 hc)]
      have hd : (l.drop (n * Q)).take Q = l.drop (n * Q) :=
        List.take_of_length_le (by simp [hl, Nat.succ_mul])
      rw [rsaChunks_succ, List.flatten_append, e, ih _ hl', hd]
      simp

lemma length_rsaChunkMap (Q n R : ℕ) (f : List α → List α) (l : List α)
    (hf : ∀ x, (f x).length = R) : (rsaChunkMap Q n f l).length = n * R := by
  simp [rsaChunkMap, List.length_flatMap, hf, rsaChunks, Function.comp_def, List.map_const',
    List.sum_replicate]

end Chunks

/-! ### Line maps along one axis -/

/-- The line maps of one block of `H Q` values: output `h Q + q` is entry `h` of the image of
the line `(·, q)`. -/
def rsaBlockOp (H Q : ℕ) (g : List GaussianInt → List GaussianInt) (b : List GaussianInt) :
    List GaussianInt :=
  (List.range (H * Q)).map fun z =>
    (g ((List.range H).map fun h => b.getD (h * Q + z % Q) 0)).getD (z / Q) 0

/-- The line map `g` along the middle axis of `[P] × [H] × [Q]`. -/
def rsaAxisL (P H Q : ℕ) (g : List GaussianInt → List GaussianInt) (l : List GaussianInt) :
    List GaussianInt :=
  rsaChunkMap (H * Q) P (rsaBlockOp H Q g) l

lemma length_rsaBlockOp (H Q : ℕ) (g : List GaussianInt → List GaussianInt)
    (b : List GaussianInt) : (rsaBlockOp H Q g b).length = H * Q := by
  simp [rsaBlockOp]

lemma length_rsaAxisL (P H Q : ℕ) (g : List GaussianInt → List GaussianInt)
    (l : List GaussianInt) : (rsaAxisL P H Q g l).length = P * (H * Q) :=
  length_rsaChunkMap _ _ _ _ _ (length_rsaBlockOp H Q g)

/-- The line of a block through offset `q`. -/
lemma rsaBlockOp_getD (H Q : ℕ) (g : List GaussianInt → List GaussianInt) (b : List GaussianInt)
    {h q : ℕ} (hh : h < H) (hq : q < Q) :
    (rsaBlockOp H Q g b).getD (h * Q + q) 0 =
      (g ((List.range H).map fun h' => b.getD (h' * Q + q) 0)).getD h 0 := by
  have hz : h * Q + q < H * Q := by nlinarith
  rw [rsaBlockOp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hz]
  simp only [Option.map_some, Option.getD_some]
  rw [show (h * Q + q) % Q = q by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hq],
    show (h * Q + q) / Q = h by rw [Nat.mul_comm, Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt hq, Nat.add_zero]]

/-- Along the innermost axis a block is one line. -/
lemma rsaBlockOp_one (H : ℕ) (g : List GaussianInt → List GaussianInt) (b : List GaussianInt)
    (hb : b.length = H) (hg : (g b).length = H) : rsaBlockOp H 1 g b = g b := by
  apply List.ext_getElem (by simp [length_rsaBlockOp, hg])
  intro z h₁ h₂
  simp only [rsaBlockOp, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.div_one, List.getElem_map,
    List.getElem_range]
  have hl : ((List.range H).map fun h => b.getD h 0) = b := by
    apply List.ext_getElem (by simp [hb])
    intro i hi₁ hi₂
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
  rw [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  rfl

/-- Along the innermost axis the lines are the chunks of length `H`. -/
lemma rsaAxisL_inner (P H : ℕ) (g : List GaussianInt → List GaussianInt) (l : List GaussianInt)
    (hl : l.length = P * H) (hg : ∀ x, x.length = H → (g x).length = H) :
    rsaAxisL P H 1 g l = rsaChunkMap H P g l := by
  unfold rsaAxisL rsaChunkMap
  rw [Nat.mul_one]
  refine List.flatMap_congr fun b hb => ?_
  simp only [rsaChunks, List.mem_map, List.mem_range] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have hbl : ((l.drop (c * H)).take H).length = H := by
    simp only [List.length_take, List.length_drop, hl]
    have : (c + 1) * H ≤ P * H := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, one_mul] at this
    omega
  exact rsaBlockOp_one H g _ hbl (hg _ hbl)

/-! ### Chunkwise maps -/

section ChunkLemmas

variable {α : Type}

lemma rsaChunkMap_eq (Q n : ℕ) (f : List α → List α) (l : List α) :
    rsaChunkMap Q n f l = (List.range n).flatMap fun c => f ((l.drop (c * Q)).take Q) := by
  simp [rsaChunkMap, rsaChunks, List.flatMap_map]

/-- A flatMap over `range (n P)` as a double flatMap. -/
lemma rsa_flatMap_range_mul {β : Type} (n P : ℕ) (F : ℕ → List β) :
    (List.range (n * P)).flatMap F =
      (List.range n).flatMap fun c => (List.range P).flatMap fun p => F (c * P + p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ,
        List.flatMap_append, List.flatMap_map]
      simp

/-- Chunk `c` of a concatenation of blocks of length `Q`. -/
lemma rsa_drop_take_flatten {Q : ℕ} : ∀ (blocks : List (List α)), (∀ b ∈ blocks, b.length = Q) →
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
          simpa using rsa_drop_take_flatten bs (fun b' hb' => h b' (by simp [hb'])) c
            (by simpa using hc)

/-- Chunk `c` of a chunkwise map. -/
lemma rsaChunkMap_chunk (Q n : ℕ) (f : List α → List α) (hf : ∀ x, (f x).length = Q)
    (l : List α) {c : ℕ} (hc : c < n) :
    ((rsaChunkMap Q n f l).drop (c * Q)).take Q = f ((l.drop (c * Q)).take Q) := by
  unfold rsaChunkMap
  rw [List.flatMap_def, rsa_drop_take_flatten _ (by simp [hf]) c (by simp [rsaChunks, hc])]
  simp [rsaChunks, hc]

end ChunkLemmas

/-- Block `p` of chunk `c`. -/
lemma rsa_drop_take_drop_take {α : Type} (l : List α) {a b k m : ℕ} (h : k + m ≤ b) :
    (((l.drop a).take b).drop k).take m = (l.drop (a + k)).take m := by
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

/-- Chunkwise line maps are line maps of the whole list. -/
lemma rsaChunkMap_axisL (n P H R : ℕ) (g : List GaussianInt → List GaussianInt)
    (l : List GaussianInt) :
    rsaChunkMap (P * (H * R)) n (rsaAxisL P H R g) l = rsaAxisL (n * P) H R g l := by
  rw [rsaChunkMap_eq, rsaAxisL, rsaChunkMap_eq, rsa_flatMap_range_mul]
  refine List.flatMap_congr fun c hc => ?_
  rw [rsaAxisL, rsaChunkMap_eq]
  refine List.flatMap_congr fun p hp => ?_
  have hp' := List.mem_range.1 hp
  have hle : p * (H * R) + H * R ≤ P * (H * R) := by
    have := Nat.mul_le_mul_right (H * R) hp'
    rw [Nat.succ_mul] at this; exact this
  rw [rsa_drop_take_drop_take l hle]
  congr 3
  ring

/-! ### Interchange of two axes -/

lemma rsa_decomp4 {P H G D z : ℕ} (hz : z < P * H * G * D) :
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
theorem rsaAxisL_swap (P H G D : ℕ) (g : List GaussianInt → List GaussianInt)
    (hg : ∀ x, (g x).length = H) (l : List GaussianInt) (hl : l.length = P * H * G * D) :
    swapList P D G H 1 0 (rsaAxisL (P * D * G) H 1 g (swapList P H G D 1 0 l)) =
      rsaAxisL P H (G * D) g l := by
  have hlen₂ : (swapList P H G D 1 0 l).length = P * D * G * H * 1 := by
    simp [swapList]
  have hlen₃ : (rsaAxisL (P * D * G) H 1 g (swapList P H G D 1 0 l)).length =
      P * D * G * H * 1 := by
    rw [length_rsaAxisL]; ring
  apply List.ext_getElem?
  intro z
  by_cases hz : z < P * H * G * D
  · obtain ⟨p, h, γ, δ, hp, hh, hγ, hδ, rfl⟩ := rsa_decomp4 hz
    have e₁ := swapList_getElem? (P := P) (H := D) (G := G) (D := H) (B := 1) 0
      (rsaAxisL (P * D * G) H 1 g (swapList P H G D 1 0 l)) hlen₃ hp hδ hγ hh (Nat.zero_lt_one)
    simp only [Nat.mul_one, Nat.add_zero] at e₁
    rw [e₁]
    -- the right-hand side as a block entry
    have hR : (rsaAxisL P H (G * D) g l)[((p * H + h) * G + γ) * D + δ]? =
        some ((g ((List.range H).map fun h' =>
          l.getD (((p * H + h') * G + γ) * D + δ) 0)).getD h 0) := by
      have hlenR := length_rsaAxisL P H (G * D) g l
      have hidx : ((p * H + h) * G + γ) * D + δ = p * (H * (G * D)) + (h * (G * D) + (γ * D + δ)) := by
        ring
      have hlt : ((p * H + h) * G + γ) * D + δ < (rsaAxisL P H (G * D) g l).length := by
        rw [hlenR]
        have := mix_lt (mix_lt (mix_lt hp hh) hγ) hδ
        linarith [show P * H * G * D = P * (H * (G * D)) by ring]
      rw [List.getElem?_eq_getElem hlt]
      congr 1
      rw [← List.getD_eq_getElem _ 0 hlt, rsaAxisL, hidx]
      have hchunk := rsaChunkMap_chunk (H * (G * D)) P (rsaBlockOp H (G * D) g)
        (length_rsaBlockOp H (G * D) g) l hp
      have hin : h * (G * D) + (γ * D + δ) < H * (G * D) := mix_lt hh (mix_lt hγ hδ)
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, ← List.getElem?_take_of_lt hin,
        hchunk, ← List.getD_eq_getElem?_getD,
        rsaBlockOp_getD H (G * D) g _ hh (mix_lt hγ hδ)]
      congr 2
      refine List.map_congr_left fun h' hh' => ?_
      have hh'' := List.mem_range.1 hh'
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt
        (mix_lt hh'' (mix_lt hγ hδ)), List.getElem?_drop]
      congr 2
      ring
    rw [hR]
    -- the left-hand side
    have hlt₃ : ((p * D + δ) * G + γ) * H + h < (rsaAxisL (P * D * G) H 1 g
        (swapList P H G D 1 0 l)).length := by
      rw [hlen₃]
      have := mix_lt (mix_lt (mix_lt hp hδ) hγ) hh
      linarith
    rw [List.getElem?_eq_getElem hlt₃]
    congr 1
    rw [← List.getD_eq_getElem _ 0 hlt₃, rsaAxisL_inner (P * D * G) H g _ (by rw [hlen₂]; ring)
      (fun x _ => hg x)]
    have hc : (p * D + δ) * G + γ < P * D * G := mix_lt (mix_lt hp hδ) hγ
    have hchunk := rsaChunkMap_chunk H (P * D * G) g hg (swapList P H G D 1 0 l) hc
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
    have h1 : (swapList P D G H 1 0 (rsaAxisL (P * D * G) H 1 g
        (swapList P H G D 1 0 l))).length ≤ z := by
      simp only [swapList, List.length_map, List.length_range]; linarith
    have h2 : (rsaAxisL P H (G * D) g l).length ≤ z := by rw [length_rsaAxisL]; linarith
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-! ### Box streams -/

section Box

/-- The stream of an array on `∏_{i<d} [0, t_i)`, axis `0` most significant. -/
def rsaBox {α : Type} : (d : ℕ) → (t : Fin d → ℕ) → (((i : Fin d) → Fin (t i)) → α) → List α
  | 0, _, F => [F fun i => i.elim0]
  | d + 1, t, F => (List.finRange (t 0)).flatMap fun x₀ =>
      rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))

lemma length_rsaBox {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ) (F : ((i : Fin d) → Fin (t i)) → α),
    (rsaBox d t F).length = ∏ i, t i
  | 0, _, _ => by simp [rsaBox]
  | d + 1, t, F => by
      rw [rsaBox, List.length_flatMap, Fin.prod_univ_succ]
      simp only [length_rsaBox d]
      simp [List.sum_replicate]

lemma rsaBox_map {α β : Type} (φ : α → β) : ∀ (d : ℕ) (t : Fin d → ℕ)
    (F : ((i : Fin d) → Fin (t i)) → α), rsaBox d t (fun x => φ (F x)) = (rsaBox d t F).map φ
  | 0, _, _ => by simp [rsaBox]
  | d + 1, t, F => by
      simp only [rsaBox, List.map_flatMap]
      exact List.flatMap_congr fun x₀ _ => rsaBox_map φ d _ _

/-- The chunks of a box stream along axis `0` are the streams of its slices. -/
lemma rsaBox_chunks {α : Type} (d : ℕ) (t : Fin (d + 1) → ℕ)
    (F : ((i : Fin (d + 1)) → Fin (t i)) → α) :
    rsaChunks (∏ i : Fin d, t i.succ) (t 0) (rsaBox (d + 1) t F) =
      (List.finRange (t 0)).map fun x₀ => rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y)) := by
  apply List.ext_getElem (by simp [rsaChunks])
  intro c h₁ h₂
  have hc : c < t 0 := by simpa [rsaChunks] using h₁
  simp only [rsaChunks, List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [rsaBox, List.flatMap_def, rsa_drop_take_flatten _ (by
    intro b hb
    simp only [List.mem_map, List.mem_finRange, true_and] at hb
    obtain ⟨x₀, rfl⟩ := hb
    exact length_rsaBox _ _ _) c (by simpa using hc)]
  simp [hc]

end Box

/-! ### Line maps along all axes -/

/-- Line maps along all axes in the order of `tensorZR`: the axes `1, …, d` slice by slice, then
axis `0`. -/
def rsaAxesL : (d : ℕ) → (t : Fin d → ℕ) → (Fin d → List GaussianInt → List GaussianInt) →
    List GaussianInt → List GaussianInt
  | 0, _, _ => id
  | d + 1, t, g => fun l =>
      rsaAxisL 1 (t 0) (∏ i : Fin d, t i.succ) (g 0)
        (rsaChunkMap (∏ i : Fin d, t i.succ) (t 0)
          (rsaAxesL d (fun i => t i.succ) (fun i => g i.succ)) l)

/-- The integer line map `g` on padded lines of `t` records gives the numerators at scale `qo`
of the numeric map `A` on the lines whose first `M` records are the numerators at scale `qi`. -/
structure RsaLineRel (M t : ℕ) (A : (ZMod M → ℂ) → ZMod t → ℂ)
    (g : List GaussianInt → List GaussianInt) (qi qo : ℕ) : Prop where
  len : ∀ N, (g N).length = t
  num : ∀ (N : List GaussianInt) (v : ZMod M → ℂ), N.length = t →
    (∀ j : ZMod M, v j = GaussianInt.toComplex (N.getD j.val 0) / 2 ^ qi) →
      ∀ k : ℕ, k < t → A v (k : ZMod t) = GaussianInt.toComplex ((g N).getD k 0) / 2 ^ qo

/-- Entry `x₀ Q + a` of a box stream is entry `a` of the slice `x₀`. -/
lemma rsaBox_getD_succ {α : Type} [Inhabited α] (d : ℕ) (t : Fin (d + 1) → ℕ)
    (F : ((i : Fin (d + 1)) → Fin (t i)) → α) (dflt : α) {x₀ a : ℕ} (hx₀ : x₀ < t 0)
    (ha : a < ∏ i : Fin d, t i.succ) :
    (rsaBox (d + 1) t F).getD (x₀ * (∏ i : Fin d, t i.succ) + a) dflt =
      (rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons ⟨x₀, hx₀⟩ y))).getD a dflt := by
  have h := rsa_drop_take_flatten ((List.finRange (t 0)).map fun x₀ =>
    rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))) (by
      intro b hb
      simp only [List.mem_map, List.mem_finRange, true_and] at hb
      obtain ⟨x₀, rfl⟩ := hb
      exact length_rsaBox _ _ _) x₀ (by simpa using hx₀)
  rw [rsaBox, List.flatMap_def, List.getD_eq_getElem?_getD, ← List.getElem?_drop,
    ← List.getElem?_take_of_lt ha, h]
  simp [hx₀, List.getD_eq_getElem?_getD]

/-- A box stream through one line map along axis `0`. -/
lemma rsaAxisL_box (d : ℕ) (t : Fin (d + 1) → ℕ) (g : List GaussianInt → List GaussianInt)
    (F : ((i : Fin (d + 1)) → Fin (t i)) → GaussianInt) :
    rsaAxisL 1 (t 0) (∏ i : Fin d, t i.succ) g (rsaBox (d + 1) t F) =
      rsaBox (d + 1) t (fun x => (g ((List.finRange (t 0)).map fun j =>
        F (Fin.cons j (Fin.tail x)))).getD (x 0) 0) := by
  set Q := ∏ i : Fin d, t i.succ with hQ
  have hlen : (rsaBox (d + 1) t F).length = t 0 * Q := by
    rw [length_rsaBox, Fin.prod_univ_succ]
  -- the vectors of the slices
  set V : ((i : Fin d) → Fin (t i.succ)) → (Fin (t 0) → GaussianInt) :=
    fun y j => F (Fin.cons j y) with hV
  have hlenV : (rsaBox d (fun i => t i.succ) V).length = Q := length_rsaBox _ _ _
  have hslice : ∀ (j : Fin (t 0)) (a : ℕ),
      (rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons j y))).getD a 0 =
        ((rsaBox d (fun i => t i.succ) V).getD a 0) j := by
    intro j a
    have := rsaBox_map (fun v : Fin (t 0) → GaussianInt => v j) d (fun i => t i.succ) V
    simp only [hV] at this
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (rsaBox d (fun i => t i.succ) V)[a]? <;> rfl
  have e1 : rsaAxisL 1 (t 0) Q g (rsaBox (d + 1) t F) = rsaBlockOp (t 0) Q g (rsaBox (d + 1) t F) := by
    rw [rsaAxisL, rsaChunkMap_eq]
    simp [List.take_of_length_le (le_of_eq hlen)]
  rw [e1]
  apply List.ext_getElem
  · rw [length_rsaBlockOp, length_rsaBox, Fin.prod_univ_succ]
  intro z h₁ h₂
  have h₁' := h₁
  rw [length_rsaBlockOp] at h₁'
  have hQ0 : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, Nat.mul_zero] at h₁'; omega
    · exact h
  obtain ⟨x₀, a, hx₀, ha, rfl⟩ : ∃ x₀ a, x₀ < t 0 ∧ a < Q ∧ z = x₀ * Q + a :=
    ⟨z / Q, z % Q, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h₁'), Nat.mod_lt _ hQ0,
      (Nat.div_add_mod' z Q).symm⟩
  rw [← List.getD_eq_getElem _ 0 h₁, rsaBlockOp_getD (t 0) Q g _ hx₀ ha,
    ← List.getD_eq_getElem _ 0 h₂, rsaBox_getD_succ d t _ 0 hx₀ ha]
  simp only [Fin.tail_cons, Fin.cons_zero]
  have hmap := rsaBox_map (fun v : Fin (t 0) → GaussianInt =>
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
  rw [rsaBox_getD_succ d t _ 0 hj ha, hslice ⟨j, hj⟩ a,
    List.getD_eq_getElem _ _ (by rw [hlenV]; exact ha)]
  rfl

/-- A chunkwise map of a box stream acting slice by slice. -/
lemma rsaChunkMap_box (d : ℕ) (t : Fin (d + 1) → ℕ) (f : List GaussianInt → List GaussianInt)
    (F G : ((i : Fin (d + 1)) → Fin (t i)) → GaussianInt)
    (h : ∀ x₀ : Fin (t 0), f (rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))) =
      rsaBox d (fun i => t i.succ) (fun y => G (Fin.cons x₀ y))) :
    rsaChunkMap (∏ i : Fin d, t i.succ) (t 0) f (rsaBox (d + 1) t F) = rsaBox (d + 1) t G := by
  rw [rsaChunkMap, rsaBox_chunks, List.flatMap_map, rsaBox]
  exact List.flatMap_congr fun x₀ _ => h x₀

open IntegerMultBounds.NLogN in
/-- **Line maps along all axes compute `tensorZR`.** Let `F` be the padded stream of the
numerators of `u` at scale `qi` (zero where some coordinate `x i ≥ M i`) and let every line
map `g i` give the numerators of `A i` (`RsaLineRel`), at input scale `qi` for the axis
processed first (`i = d - 1`) and `qo` for the others, output scale `qo`. Then the line maps
along all axes turn `rsaBox d t F` into the stream of an array `G` of numerators of
`tensorZR d M t A u` at scale `qo` (`qi` when `d = 0`). -/
theorem rsa_tensor : ∀ (d : ℕ) (M t : Fin d → ℕ) [∀ i, NeZero (M i)] [∀ i, NeZero (t i)]
    (_ : ∀ i, M i ≤ t i) (A : (i : Fin d) → (ZMod (M i) → ℂ) → ZMod (t i) → ℂ)
    (g : Fin d → List GaussianInt → List GaussianInt) (qi qo : ℕ)
    (_ : ∀ i : Fin d, RsaLineRel (M i) (t i) (A i) (g i)
      (if (i : ℕ) + 1 = d then qi else qo) qo)
    (u : ((i : Fin d) → ZMod (M i)) → ℂ) (F : ((i : Fin d) → Fin (t i)) → GaussianInt)
    (_ : ∀ x : (i : Fin d) → Fin (t i), (∀ i, (x i : ℕ) < M i) →
      u (fun i => ((x i : ℕ) : ZMod (M i))) = GaussianInt.toComplex (F x) / 2 ^ qi)
    (_ : ∀ x : (i : Fin d) → Fin (t i), (∃ i, M i ≤ x i) → F x = 0),
    ∃ G : ((i : Fin d) → Fin (t i)) → GaussianInt,
      (∀ x : (i : Fin d) → Fin (t i), tensorZR d M t A u (fun i => ((x i : ℕ) : ZMod (t i))) =
        GaussianInt.toComplex (G x) / 2 ^ (if d = 0 then qi else qo)) ∧
      rsaAxesL d t g (rsaBox d t F) = rsaBox d t G
  | 0, M, t, _, _, _, A, g, qi, qo, _, u, F, hF, _ => by
      refine ⟨F, fun x => ?_, rfl⟩
      have h := hF x (fun i => i.elim0)
      have e : (fun i => ((x i : ℕ) : ZMod (M i))) = fun i => i.elim0 := funext fun i => i.elim0
      rw [e] at h
      simpa [tensorZR] using h
  | d + 1, M, t, _, _, hMt, A, g, qi, qo, hA, u, F, hF, hF0 => by
      set Q := ∏ i : Fin d, t i.succ with hQ
      set σ := if d = 0 then qi else qo with hσ
      have hA' : ∀ i : Fin d, RsaLineRel (M i.succ) (t i.succ) (A i.succ) (g i.succ)
          (if (i : ℕ) + 1 = d then qi else qo) qo := by
        intro i
        have := hA i.succ
        simpa using this
      have key : ∀ x₀ : Fin (t 0), ∃ G' : ((i : Fin d) → Fin (t i.succ)) → GaussianInt,
          (∀ y : (i : Fin d) → Fin (t i.succ), (x₀ : ℕ) < M 0 →
            tensorZR d (fun i => M i.succ) (fun i => t i.succ) (fun i => A i.succ)
              (fun j' => u (Fin.cons (((x₀ : ℕ) : ZMod (M 0))) j'))
              (fun i => ((y i : ℕ) : ZMod (t i.succ))) = GaussianInt.toComplex (G' y) / 2 ^ σ) ∧
          rsaAxesL d (fun i => t i.succ) (fun i => g i.succ)
            (rsaBox d (fun i => t i.succ) (fun y => F (Fin.cons x₀ y))) =
            rsaBox d (fun i => t i.succ) G' := by
        intro x₀
        by_cases hx : (x₀ : ℕ) < M 0
        · obtain ⟨G', h1, h2⟩ := rsa_tensor d (fun i => M i.succ) (fun i => t i.succ)
            (fun i => hMt i.succ) (fun i => A i.succ) (fun i => g i.succ) qi qo hA'
            (fun j' => u (Fin.cons (((x₀ : ℕ) : ZMod (M 0))) j')) (fun y => F (Fin.cons x₀ y))
            (fun y hy => by
              have hv : ∀ i : Fin (d + 1),
                  ((Fin.cons x₀ y : (i : Fin (d + 1)) → Fin (t i)) i : ℕ) < M i := by
                intro i
                refine Fin.cases ?_ (fun i => ?_) i
                · simpa using hx
                · simpa using hy i
              have := hF (Fin.cons x₀ y) hv
              rw [← this]
              congr 1
              funext i
              refine Fin.cases ?_ (fun i => ?_) i <;> simp)
            (fun y ⟨i, hi⟩ => hF0 (Fin.cons x₀ y) ⟨i.succ, by simpa using hi⟩)
          exact ⟨G', fun y _ => h1 y, h2⟩
        · obtain ⟨G', _, h2⟩ := rsa_tensor d (fun i => M i.succ) (fun i => t i.succ)
            (fun i => hMt i.succ) (fun i => A i.succ) (fun i => g i.succ) qi qo hA'
            (fun _ => 0) (fun y => F (Fin.cons x₀ y))
            (fun y _ => by
              rw [hF0 (Fin.cons x₀ y) ⟨0, by simpa using Nat.le_of_not_lt hx⟩]
              simp)
            (fun y ⟨i, hi⟩ => hF0 (Fin.cons x₀ y) ⟨i.succ, by simpa using hi⟩)
          exact ⟨G', fun y h => absurd h hx, h2⟩
      choose Gs hGs using key
      set Gm : ((i : Fin (d + 1)) → Fin (t i)) → GaussianInt := fun x => Gs (x 0) (Fin.tail x)
        with hGm
      have hchunk : rsaChunkMap Q (t 0) (rsaAxesL d (fun i => t i.succ) (fun i => g i.succ))
          (rsaBox (d + 1) t F) = rsaBox (d + 1) t Gm :=
        rsaChunkMap_box d t _ F Gm (fun x₀ => by
          rw [(hGs x₀).2]
          simp [hGm])
      refine ⟨fun x => (g 0 ((List.finRange (t 0)).map fun j =>
        Gm (Fin.cons j (Fin.tail x)))).getD (x 0) 0, fun x => ?_, ?_⟩
      · -- the numerators
        set N := (List.finRange (t 0)).map fun j => Gm (Fin.cons j (Fin.tail x)) with hN
        have hv : ∀ j₀ : ZMod (M 0),
            tensorZR d (fun i => M i.succ) (fun i => t i.succ) (fun i => A i.succ)
              (fun j' => u (Fin.cons j₀ j')) (fun i => ((x i.succ : ℕ) : ZMod (t i.succ))) =
            GaussianInt.toComplex (N.getD j₀.val 0) / 2 ^ (if ((0 : Fin (d + 1)) : ℕ) + 1 = d + 1
              then qi else qo) := by
          intro j₀
          have hj : j₀.val < t 0 := lt_of_lt_of_le (ZMod.val_lt j₀) (hMt 0)
          have h1 := (hGs ⟨j₀.val, hj⟩).1 (Fin.tail x) (ZMod.val_lt j₀)
          simp only [ZMod.natCast_val, ZMod.cast_id', id] at h1
          have e : (if ((0 : Fin (d + 1)) : ℕ) + 1 = d + 1 then qi else qo) = σ := by simp [hσ]
          rw [e]
          rw [show (fun i : Fin d => ((x i.succ : ℕ) : ZMod (t i.succ))) =
            fun i => (((Fin.tail x) i : ℕ) : ZMod (t i.succ)) from rfl, h1]
          congr 2
          rw [hN, List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map,
            List.getElem_finRange]
          simp [hGm]
        have h := (hA 0).num N _ (by simp [hN]) hv (x 0) (x 0).isLt
        have hT : tensorZR (d + 1) M t A u (fun i => ((x i : ℕ) : ZMod (t i))) =
            A 0 (fun j₀ : ZMod (M 0) => tensorZR d (fun i => M i.succ) (fun i => t i.succ)
              (fun i => A i.succ) (fun j' => u (Fin.cons j₀ j'))
              (fun i => ((x i.succ : ℕ) : ZMod (t i.succ)))) ((x 0 : ℕ) : ZMod (t 0)) := rfl
        rw [hT, h]
        simp [hN]
      · show rsaAxisL 1 (t 0) Q (g 0) (rsaChunkMap Q (t 0)
          (rsaAxesL d (fun i => t i.succ) (fun i => g i.succ)) (rsaBox (d + 1) t F)) = _
        rw [hchunk, rsaAxisL_box]

/-! ### The axes one at a time -/

/-- The product of the sizes of the axes before `i`. -/
def rsaPre {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : ℕ := ((List.ofFn t).take i).prod

/-- The stride of axis `i`: the product of the sizes of the axes after `i`. -/
def rsaSuf {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : ℕ := ((List.ofFn t).drop (i + 1)).prod

/-- The line map along axis `i` of the whole box stream. -/
def rsaAxisOp {d : ℕ} (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (i : Fin d) : List GaussianInt → List GaussianInt :=
  rsaAxisL (rsaPre t i) (t i) (rsaSuf t i) (g i)

/-- The line maps along the axes `i, …, d - 1`, the last axis first. -/
def rsaFlat (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt) (i : ℕ)
    (l : List GaussianInt) : List GaussianInt :=
  ((List.finRange d).drop i).foldr (fun j acc => rsaAxisOp t g j acc) l

lemma rsaFlat_ge (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    {i : ℕ} (hi : d ≤ i) (l : List GaussianInt) : rsaFlat d t g i l = l := by
  rw [rsaFlat, List.drop_eq_nil_of_le (by rw [List.length_finRange]; exact hi)]
  rfl

lemma rsaFlat_lt (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    {i : ℕ} (hi : i < d) (l : List GaussianInt) :
    rsaFlat d t g i l = rsaAxisOp t g ⟨i, hi⟩ (rsaFlat d t g (i + 1) l) := by
  rw [rsaFlat, List.drop_eq_getElem_cons (by simpa using hi)]
  simp [rsaFlat]

lemma rsaPre_succ {d : ℕ} (t : Fin (d + 1) → ℕ) (i : ℕ) :
    rsaPre t (i + 1) = t 0 * rsaPre (fun j : Fin d => t j.succ) i := by
  simp [rsaPre, List.ofFn_succ]

lemma rsaPre_zero {d : ℕ} (t : Fin d → ℕ) : rsaPre t 0 = 1 := by simp [rsaPre]

lemma rsaSuf_succ {d : ℕ} (t : Fin (d + 1) → ℕ) (i : ℕ) :
    rsaSuf t (i + 1) = rsaSuf (fun j : Fin d => t j.succ) i := by
  simp [rsaSuf, List.ofFn_succ]

lemma rsaSuf_zero {d : ℕ} (t : Fin (d + 1) → ℕ) : rsaSuf t 0 = ∏ i : Fin d, t i.succ := by
  simp [rsaSuf, List.ofFn_succ, List.prod_ofFn]

/-- Before, along, and after axis `i`: the whole box. -/
lemma rsaPre_mul {d : ℕ} (t : Fin d → ℕ) (i : Fin d) :
    rsaPre t i * (t i * rsaSuf t i) = ∏ j, t j := by
  have h1 := List.prod_take_mul_prod_drop (List.ofFn t) i
  have h2 : (List.ofFn t).drop i = t i :: (List.ofFn t).drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (by simp)]; simp
  rw [← List.prod_ofFn, ← h1, h2, List.prod_cons, rsaPre, rsaSuf]

lemma rsaChunkMap_congr {α : Type} {Q n : ℕ} {f f' : List α → List α}
    (h : ∀ x, x.length = Q → f x = f' x) {l : List α} (hl : l.length = n * Q) :
    rsaChunkMap Q n f l = rsaChunkMap Q n f' l := by
  rw [rsaChunkMap_eq, rsaChunkMap_eq]
  refine List.flatMap_congr fun c hc => h _ ?_
  have hc' := List.mem_range.1 hc
  simp only [List.length_take, List.length_drop, hl]
  have : (c + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hc'
  rw [Nat.succ_mul] at this
  omega

lemma rsaChunkMap_comp' {α : Type} (Q n : ℕ) (f f' : List α → List α)
    (hf' : ∀ x, x.length = Q → (f' x).length = Q) (l : List α) (hl : l.length = n * Q) :
    rsaChunkMap Q n f (rsaChunkMap Q n f' l) = rsaChunkMap Q n (f ∘ f') l := by
  have hlen : ∀ c, c < n → ((l.drop (c * Q)).take Q).length = Q := by
    intro c hc
    simp only [List.length_take, List.length_drop, hl]
    have : (c + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at this
    omega
  conv_lhs => rw [rsaChunkMap_eq]
  conv_rhs => rw [rsaChunkMap_eq]
  refine List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.1 hc
  have h := rsa_drop_take_flatten ((rsaChunks Q n l).map f') (by
    intro b hb
    simp only [List.mem_map, rsaChunks, List.mem_range] at hb
    obtain ⟨_, ⟨c', hc'', rfl⟩, rfl⟩ := hb
    exact hf' _ (hlen c' hc'')) c (by simp [rsaChunks, hc'])
  rw [rsaChunkMap, List.flatMap_def, h]
  simp [rsaChunks, hc']

/-- The chunkwise line maps along the axes of the slices are line maps of the whole box. -/
lemma rsaChunkMap_foldr {d : ℕ} (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (n : ℕ) : ∀ (is : List (Fin d)) (l : List GaussianInt), l.length = n * ∏ j, t j →
      rsaChunkMap (∏ j, t j) n (fun x => is.foldr (fun (j : Fin d) acc => rsaAxisOp t g j acc) x)
        l = is.foldr (fun (j : Fin d) acc =>
          rsaAxisL (n * rsaPre t (j : ℕ)) (t j) (rsaSuf t (j : ℕ)) (g j) acc) l
  | [], l, hl => by
      simp only [List.foldr_nil]
      rw [rsaChunkMap, List.flatMap_id']
      exact flatten_rsaChunks _ n l hl
  | j :: is, l, hl => by
      simp only [List.foldr_cons]
      have hc := rsaChunkMap_comp' (∏ j, t j) n (rsaAxisOp t g j)
        (fun x => is.foldr (fun (j : Fin d) acc => rsaAxisOp t g j acc) x) (by
          intro x hx
          cases is with
          | nil => simpa using hx
          | cons k is => simp [rsaAxisOp, length_rsaAxisL, rsaPre_mul]) l hl
      rw [← show (rsaAxisOp t g j ∘ fun x => is.foldr (fun (j : Fin d) acc =>
        rsaAxisOp t g j acc) x) = fun x => rsaAxisOp t g j (is.foldr (fun (j : Fin d) acc =>
          rsaAxisOp t g j acc) x) from rfl, ← hc, rsaChunkMap_foldr t g n is l hl]
      rw [rsaAxisOp, ← rsaPre_mul t j, rsaChunkMap_axisL]

/-- **The axes one at a time.** On a box stream, the line maps along all axes in the order of
`tensorZR` are the line maps along the axes `d - 1, …, 0` of the whole stream. -/
theorem rsaAxesL_flat : ∀ (d : ℕ) (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (l : List GaussianInt), l.length = ∏ i, t i → rsaAxesL d t g l = rsaFlat d t g 0 l
  | 0, _, _, l, _ => by simp [rsaAxesL, rsaFlat]
  | d + 1, t, g, l, hl => by
      have hl' : l.length = t 0 * ∏ i : Fin d, t i.succ := by rw [hl, Fin.prod_univ_succ]
      rw [rsaFlat, List.drop_zero, List.finRange_succ, List.foldr_cons, List.foldr_map]
      show rsaAxisL 1 (t 0) (∏ i : Fin d, t i.succ) (g 0) (rsaChunkMap (∏ i : Fin d, t i.succ)
        (t 0) (rsaAxesL d (fun i => t i.succ) (fun i => g i.succ)) l) = _
      rw [rsaChunkMap_congr (f' := fun x => rsaFlat d (fun i => t i.succ) (fun i => g i.succ) 0 x)
        (fun x hx => rsaAxesL_flat d _ _ x hx) hl']
      simp only [rsaFlat, List.drop_zero]
      rw [rsaChunkMap_foldr (fun i => t i.succ) (fun i => g i.succ) (t 0) _ l hl']
      simp only [rsaAxisOp, Fin.val_zero, rsaPre_zero, rsaSuf_zero, Fin.val_succ, rsaPre_succ,
        rsaSuf_succ]

end IntegerMultBounds.MathlibTM2.Fast.ResampA
