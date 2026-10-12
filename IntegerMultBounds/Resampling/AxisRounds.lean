module

public import IntegerMultBounds.Schoenhage.SwapPrim

/-! Flat arrays of `B`-bit blocks in lexicographic order, and the field moves
of the tensor driver. `tr2 M n B` transposes an `M × n` matrix of blocks; the
interchange of two adjacent fields (`SwapPrim.swapList` with `G = 1`) is a
`tr2` inside every outer block (`swapList_blocks`); moving the innermost field
past all the others by adjacent interchanges is one `tr2` (`rot_eq_tr2`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.AxisRounds

open IntegerMultBounds.Machine IntegerMultBounds.Schoenhage

/-- The `M × n` matrix of `B`-bit blocks transposed to `n × M`. -/
def tr2 (M n B : ℕ) (xs : List Bool) : List Bool :=
  List.ofFn fun z : Fin (n * M * B) => xs.getD (((z / B) % M * n + z / B / M) * B + z % B) false

theorem length_tr2 (M n B : ℕ) (xs : List Bool) : (tr2 M n B xs).length = n * M * B := by simp [tr2]

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) : (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem idx_div (i B b : ℕ) (hb : b < B) : (i * B + b) / B = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]

theorem idx_mod (i B b : ℕ) (hb : b < B) : (i * B + b) % B = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem getD_tr2 (M n B : ℕ) (xs : List Bool) {i j b : ℕ} (hi : i < M) (hj : j < n) (hb : b < B) :
    (tr2 M n B xs).getD ((j * M + i) * B + b) false = xs.getD ((i * n + j) * B + b) false := by
  have hz : (j * M + i) * B + b < n * M * B := by
    have : j * M + i < n * M := by nlinarith
    nlinarith
  rw [tr2, getD_ofFn _ _ hz]
  simp only [idx_div _ _ _ hb, idx_mod _ _ _ hb, idx_div _ _ _ hi, idx_mod _ _ _ hi]

theorem getD_swapList (P H G D B : ℕ) (xs : List Bool) {p h g d b : ℕ} (hp : p < P) (hh : h < H) (hg : g < G)
    (hd : d < D) (hb : b < B) :
    (SwapPrim.swapList P H G D B xs).getD ((((p * D + d) * G + g) * H + h) * B + b) false =
      xs.getD ((((p * H + h) * G + g) * D + d) * B + b) false := by
  have e := BinaryAdjacentWidthInterchange.transpose_entry
    (id : Fin (BinaryAdjacentWidthInterchange.volume P H G D B) → _) ⟨p, hp⟩ ⟨h, hh⟩ ⟨g, hg⟩ ⟨d, hd⟩ ⟨b, hb⟩
  have v1 : (BinaryAdjacentWidthInterchange.index (⟨p, hp⟩ : Fin P) (⟨d, hd⟩ : Fin D) (⟨g, hg⟩ : Fin G)
      (⟨h, hh⟩ : Fin H) (⟨b, hb⟩ : Fin B)).val = (((p * D + d) * G + g) * H + h) * B + b := by
    simp [BinaryAdjacentWidthInterchange.index, RecursiveInterchangeRows.pack, finProdFinEquiv]; ring
  have v2 : (BinaryAdjacentWidthInterchange.index (⟨p, hp⟩ : Fin P) (⟨h, hh⟩ : Fin H) (⟨g, hg⟩ : Fin G)
      (⟨d, hd⟩ : Fin D) (⟨b, hb⟩ : Fin B)).val = (((p * H + h) * G + g) * D + d) * B + b := by
    simp [BinaryAdjacentWidthInterchange.index, RecursiveInterchangeRows.pack, finProdFinEquiv]; ring
  rw [← v1, ← v2]
  unfold SwapPrim.swapList
  rw [getD_ofFn _ _ (Fin.isLt _)]
  simp only [Fin.eta, e, id]

theorem ext_getD {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i false = l₂.getD i false) : l₁ = l₂ :=
  List.ext_getElem hl fun i h₁ h₂ => by
    have := h i h₁
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂, Option.getD_some, Option.getD_some] at this

theorem length_swapList (P H G D B : ℕ) (xs : List Bool) :
    (SwapPrim.swapList P H G D B xs).length = P * D * G * H * B := by
  simp [SwapPrim.swapList, BinaryAdjacentWidthInterchange.volume]

/-- Move the innermost field (`n` entries) past the fields `gs`, innermost first, by adjacent
interchanges of blocks of `B` bits. -/
def rot : List ℕ → ℕ → ℕ → List Bool → List Bool
  | [], _, _, xs => xs
  | g :: gs, n, B, xs => rot gs n (g * B) (SwapPrim.swapList gs.prod g 1 n B xs)

theorem rot_eq_tr2 : ∀ (gs : List ℕ) (n B : ℕ) (xs : List Bool), xs.length = gs.prod * n * B →
    rot gs n B xs = tr2 gs.prod n B xs
  | [], n, B, xs, hl => by
    simp only [rot, List.prod_nil, one_mul] at hl ⊢
    apply ext_getD (by rw [length_tr2, hl]; ring)
    intro z hz
    rw [hl] at hz
    have hB : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; simp at hz)
    have hzB : z / B < n := by rw [Nat.div_lt_iff_lt_mul hB]; exact hz
    have e : z = (z / B * 1 + 0) * B + z % B := by rw [mul_one, add_zero, Nat.div_add_mod']
    rw [e, getD_tr2 1 n B xs (by omega) hzB (Nat.mod_lt _ hB)]
    simp
  | g :: gs, n, B, xs, hl => by
    have hlen : (SwapPrim.swapList gs.prod g 1 n B xs).length = gs.prod * n * (g * B) := by
      rw [length_swapList]; ring
    rw [rot, rot_eq_tr2 gs n (g * B) _ hlen]
    apply ext_getD (by simp [length_tr2, List.prod_cons]; ring)
    intro z hz
    rw [length_tr2] at hz
    have hB : 0 < B := by rcases Nat.eq_zero_or_pos B with h | h <;> simp_all
    have hg : 0 < g := by rcases Nat.eq_zero_or_pos g with h | h <;> simp_all
    have hQ : 0 < gs.prod := by rcases Nat.eq_zero_or_pos gs.prod with h | h <;> simp_all
    set Q := gs.prod
    -- output index z = (j * Q + q) * (g * B) + (ig * B + b)
    set j := z / (g * B) / Q
    set q := z / (g * B) % Q
    set ig := z % (g * B) / B
    set b := z % (g * B) % B
    have hj : j < n := by
      simp only [j]; rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
      calc z < n * Q * (g * B) := hz
        _ = n * (g * B * Q) := by ring
    have hq : q < Q := Nat.mod_lt _ hQ
    have hig : ig < g := by simp only [ig]; rw [Nat.div_lt_iff_lt_mul hB]; exact Nat.mod_lt _ (by positivity)
    have hb : b < B := Nat.mod_lt _ hB
    have hz1 : z = (j * Q + q) * (g * B) + (ig * B + b) := by
      rw [Nat.div_add_mod' (z % (g * B)) B, Nat.div_add_mod' (z / (g * B)) Q, Nat.div_add_mod' z (g * B)]
    have hz2 : z = (j * (g * Q) + (q * g + ig)) * B + b := by rw [hz1]; ring
    have hgB : ig * B + b < g * B := by nlinarith
    have hm : q * g + ig < g * Q := by nlinarith
    rw [List.prod_cons]
    conv_lhs => rw [hz1]
    conv_rhs => rw [hz2]
    rw [getD_tr2 Q n (g * B) _ hq hj hgB, getD_tr2 (g * Q) n B xs hm hj hb]
    have e1 : (q * n + j) * (g * B) + (ig * B + b) = (((q * n + j) * 1 + 0) * g + ig) * B + b := by ring
    rw [e1, getD_swapList Q g 1 n B xs hq hig (by omega) hj hb]
    congr 1; ring

end IntegerMultBounds.Resampling.AxisRounds
