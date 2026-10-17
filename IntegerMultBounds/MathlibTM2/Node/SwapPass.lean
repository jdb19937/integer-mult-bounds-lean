module

public import IntegerMultBounds.MathlibTM2.Node.Rect
public import IntegerMultBounds.MathlibTM2.Host.PlacedSwap
public import IntegerMultBounds.Machine.BinaryInterchangeBudget
import Mathlib.Tactic.Positivity.Finset

/-!
# The field-swap pass

`swapPass` is the host program for one instruction `Instr.swap a b` (`a ≠ b`) of the packed
program on a record stream. The stream register `str` holds the records of the rectangle
`[N₀] × [2^L] × [N₁] × [2^L] × [N₂] × [2^L] × [N₃]` in rank order, each a list of `B` symbols of
value below `8`. The pass
1. replaces every symbol by its three bits, least significant first, moving the stream onto the
   register `tmp` (`toBitsPass`; the move reverses the list);
2. moves the bits to the payload register `ι (reg pay)` of the placed interchange machine
   (`moveR`, which restores the order);
3. runs the vendored interchange `placedSwapProg` on the layout `[P] × [2^L] × [G] × [2^L] × [B']`
   with `(P, G, R) = swapDims a b` and `B' = R * (3 * B)`: the two `2^L` axes are the exchanged
   chunks, `G` the block between them, `B'` the bits of the `R` records below the second chunk;
4. moves the result back to `tmp` and packs every three bits into one symbol on `str`
   (`ofBitsPass`).

`swapList_moveRecs` identifies the list interchange with `moveRecs (rankPerm [.swap a b])` for
records of any uniform length, and `swapList_toBits` transfers it to bit streams. `swapPass_exec`
states the exact effect of the pass and a step bound in terms of `BinaryInterchangeRun.cost`;
`swapPass_exec_le` bounds that cost with `BinaryInterchangeRun.uniform_bound`.

The caller fills the five header registers with the canonical counters of `(P, G, B', L, L)`;
the pass leaves them unchanged.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Layer.PackedXor IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2


section Bits

variable {A : ℕ}

/-- The three bit symbols of the value of `x`, least significant first. -/
def bits3 (x : Fin (A + 4)) : List (Fin (A + 4)) :=
  [bitSymbol (x.val.testBit 0), bitSymbol (x.val.testBit 1), bitSymbol (x.val.testBit 2)]

/-- Every symbol of a list replaced by its three bits, least significant first. -/
def toBits (l : List (Fin (A + 4))) : List (Fin (A + 4)) := l.flatMap bits3

@[simp] lemma length_bits3 (x : Fin (A + 4)) : (bits3 x).length = 3 := rfl

@[simp] lemma toBits_nil : toBits ([] : List (Fin (A + 4))) = [] := rfl

lemma toBits_cons (x : Fin (A + 4)) (l : List (Fin (A + 4))) :
    toBits (x :: l) = bits3 x ++ toBits l := by
  simp [toBits]

lemma length_toBits (l : List (Fin (A + 4))) : (toBits l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [toBits_cons, List.length_append, ih]; simp; omega

lemma toBits_flatten (l : List (List (Fin (A + 4)))) :
    toBits l.flatten = (l.map toBits).flatten := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [toBits, List.flatMap_append] at ih ⊢; exact ih

lemma reverse_toBits (l : List (Fin (A + 4))) :
    (toBits l).reverse = l.reverse.flatMap (fun x => (bits3 x).reverse) := by
  simp [toBits, List.reverse_flatMap]; rfl

lemma mem_toBits {l : List (Fin (A + 4))} {s : Fin (A + 4)} (hs : s ∈ toBits l) :
    ∃ b, s = bitSymbol b := by
  simp only [toBits, List.mem_flatMap, bits3, List.mem_cons, List.not_mem_nil, or_false] at hs
  obtain ⟨x, _, h | h | h⟩ := hs <;> exact ⟨_, h⟩

/-- The bit read from a popped symbol: `1` for `bitSymbol true`, `0` otherwise. -/
def bitVal (o : Option (Fin (A + 4))) : ℕ := if o = some (bitSymbol true) then 1 else 0

/-- Append a popped bit below the accumulated value `acc` (bits arrive most significant
first). -/
def shiftBit (acc o : Option (Fin (A + 4))) : Option (Fin (A + 4)) :=
  some ⟨(2 * (acc.getD blank).val + bitVal o) % (A + 4), Nat.mod_lt _ (by omega)⟩

lemma bitVal_bitSymbol (b : Bool) : bitVal (some (bitSymbol b : Fin (A + 4))) = b.toNat := by
  cases b <;> simp [bitVal, bitSymbol, Fin.ext_iff]

/-- Reading the three bits of `x`, most significant first, recovers `x`. -/
lemma shiftBit_bits3 (x : Fin (A + 4)) (hx : x.val < 8) :
    shiftBit (shiftBit (shiftBit none (some (bitSymbol (x.val.testBit 2))))
      (some (bitSymbol (x.val.testBit 1)))) (some (bitSymbol (x.val.testBit 0))) = some x := by
  simp only [shiftBit, bitVal_bitSymbol, Option.getD_none, Option.getD_some, Option.some.injEq]
  apply Fin.ext
  simp only [blank]
  obtain ⟨n, hn⟩ := x
  simp only at hx ⊢
  have h4 : ∀ m < 4, m % (A + 4) = m := fun m hm => Nat.mod_eq_of_lt (by omega)
  have key : 2 * (2 * (n.testBit 2).toNat + (n.testBit 1).toNat) + (n.testBit 0).toNat = n := by
    interval_cases n <;> decide
  have hb : ∀ b : Bool, b.toNat < 2 := fun b => by cases b <;> decide
  have e1 := hb (n.testBit 2)
  have e2 := hb (n.testBit 1)
  rw [h4 (2 * 0 + _) (by omega), h4 (2 * (2 * 0 + _) + _) (by omega)]
  rw [Nat.mul_zero, Nat.zero_add, key, Nat.mod_eq_of_lt hn]

end Bits

section Flatten

variable {α : Type*}

/-- Length of a flattened list of lists of length `R`. -/
lemma length_flatten_uniform {R : ℕ} : ∀ (l : List (List α)), (∀ x ∈ l, x.length = R) →
    l.flatten.length = l.length * R
  | [], _ => by simp
  | x :: l, h => by
      rw [List.flatten_cons, List.length_append, h x (by simp),
        length_flatten_uniform l (fun y hy => h y (by simp [hy])), List.length_cons]
      ring

/-- Entry `i` of list `r` in a flattened list of lists of length `R`. -/
lemma flatten_getElem?_uniform {R : ℕ} : ∀ (l : List (List α)), (∀ x ∈ l, x.length = R) →
    ∀ r i, i < R → l.flatten[r * R + i]? = l[r]?.bind (·[i]?)
  | [], _, r, i, _ => by simp
  | x :: l, h, r, i, hi => by
      have hx := h x (by simp)
      rw [List.flatten_cons]
      cases r with
      | zero =>
          rw [List.getElem?_append_left (by rw [hx]; omega)]
          simp
      | succ r =>
          rw [List.getElem?_append_right (by rw [hx]; nlinarith), hx,
            show (r + 1) * R + i - R = r * R + i by rw [Nat.succ_mul]; omega,
            flatten_getElem?_uniform l (fun y hy => h y (by simp [hy])) r i hi]
          simp

end Flatten

section Interchange

variable (N₀ N₁ N₂ N₃ L K ρ n : ℕ)

/-- Interchange dimensions `(P, G, R)` for exchanging the chunk slots `a ≠ b`: `P` outer
blocks, `G` middle blocks between the two exchanged chunks, `R` records per inner block. -/
def swapDims (a b : Fin 3) : ℕ × ℕ × ℕ :=
  if a ≠ 2 ∧ b ≠ 2 then (N₀, N₁, N₂ * 2 ^ L * N₃)
  else if a ≠ 0 ∧ b ≠ 0 then (N₀ * 2 ^ L * N₁, N₂, N₃)
  else (N₀, N₁ * 2 ^ L * N₂, N₃)

lemma swapDims_comm (a b : Fin 3) :
    swapDims N₀ N₁ N₂ N₃ L a b = swapDims N₀ N₁ N₂ N₃ L b a := by
  unfold swapDims
  simp only [and_comm]

/-- The interchange layout has `R` cells per record. -/
lemma swapDims_vol (a b : Fin 3) (hab : a ≠ b) (R : ℕ) :
    (swapDims N₀ N₁ N₂ N₃ L a b).1 * 2 ^ L * (swapDims N₀ N₁ N₂ N₃ L a b).2.1 * 2 ^ L *
      ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) = rectSize N₀ N₁ N₂ N₃ L * R := by
  fin_cases a <;> fin_cases b <;> simp at hab <;> simp [swapDims, rectSize] <;> ring

/-- The instruction `swap a b` on ranks. -/
lemma rankPerm_swap (a b : Fin 3) (p : Addr N₀ N₁ N₂ N₃ L) :
    rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b] (rankEquiv N₀ N₁ N₂ N₃ L p) =
      rankEquiv N₀ N₁ N₂ N₃ L (p.1, p.2 ∘ Equiv.swap a b) := by
  simp only [rankPerm, progPerm, instrPerm, liftA, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.trans_refl, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  congr 2

/-- Index arithmetic of `swap a b`: a bit at offset `i` of the record at address `p` sits at
source cell `(q, h, g, d, e)` of the interchange, and the moved record at target cell
`(q, d, g, h, e)`. -/
lemma swap_index (a b : Fin 3) (hab : a ≠ b) (R i : ℕ) (hi : i < R) (p : Addr N₀ N₁ N₂ N₃ L) :
    ∃ q h g d e, q < (swapDims N₀ N₁ N₂ N₃ L a b).1 ∧ h < 2 ^ L ∧
      g < (swapDims N₀ N₁ N₂ N₃ L a b).2.1 ∧ d < 2 ^ L ∧
      e < (swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R ∧
      rank N₀ N₁ N₂ N₃ L p * R + i = (((q * 2 ^ L + h) * (swapDims N₀ N₁ N₂ N₃ L a b).2.1 + g) *
        2 ^ L + d) * ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) + e ∧
      rank N₀ N₁ N₂ N₃ L (p.1, p.2 ∘ Equiv.swap a b) * R + i =
        (((q * 2 ^ L + d) * (swapDims N₀ N₁ N₂ N₃ L a b).2.1 + g) * 2 ^ L + h) *
          ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) + e := by
  obtain ⟨⟨s₀, s₁, s₂, s₃⟩, c⟩ := p
  have c0 := (c 0).isLt
  have c1 := (c 1).isLt
  have c2 := (c 2).isLt
  have e01 : ∀ e : Equiv.Perm (Fin 3), e = Equiv.swap 0 1 →
      (c ∘ e) 0 = c 1 ∧ (c ∘ e) 1 = c 0 ∧ (c ∘ e) 2 = c 2 := by
    rintro e rfl; simp [Equiv.swap_apply_of_ne_of_ne]
  have e12 : ∀ e : Equiv.Perm (Fin 3), e = Equiv.swap 1 2 →
      (c ∘ e) 0 = c 0 ∧ (c ∘ e) 1 = c 2 ∧ (c ∘ e) 2 = c 1 := by
    rintro e rfl; simp [Equiv.swap_apply_of_ne_of_ne]
  have e02 : ∀ e : Equiv.Perm (Fin 3), e = Equiv.swap 0 2 →
      (c ∘ e) 0 = c 2 ∧ (c ∘ e) 1 = c 1 ∧ (c ∘ e) 2 = c 0 := by
    rintro e rfl; simp [Equiv.swap_apply_of_ne_of_ne]
  -- the three unordered pairs
  have h01 : ∀ e : Equiv.Perm (Fin 3), e = Equiv.swap 0 1 →
      ∃ q h g d f, q < N₀ ∧ h < 2 ^ L ∧ g < N₁ ∧ d < 2 ^ L ∧ f < N₂ * 2 ^ L * N₃ * R ∧
        rank N₀ N₁ N₂ N₃ L ((s₀, s₁, s₂, s₃), c) * R + i =
          (((q * 2 ^ L + h) * N₁ + g) * 2 ^ L + d) * (N₂ * 2 ^ L * N₃ * R) + f ∧
        rank N₀ N₁ N₂ N₃ L ((s₀, s₁, s₂, s₃), c ∘ e) * R + i =
          (((q * 2 ^ L + d) * N₁ + g) * 2 ^ L + h) * (N₂ * 2 ^ L * N₃ * R) + f := by
    intro e he
    obtain ⟨k0, k1, k2⟩ := e01 e he
    refine ⟨s₀, c 0, s₁, c 1, ((s₂ * 2 ^ L + c 2) * N₃ + s₃) * R + i, s₀.isLt, c0, s₁.isLt, c1,
      mix_lt (mix_lt (mix_lt s₂.isLt c2) s₃.isLt) hi, ?_, ?_⟩
    · simp only [rank]; ring
    · simp only [rank, k0, k1, k2]; ring
  have h12 : ∀ e : Equiv.Perm (Fin 3), e = Equiv.swap 1 2 →
      ∃ q h g d f, q < N₀ * 2 ^ L * N₁ ∧ h < 2 ^ L ∧ g < N₂ ∧ d < 2 ^ L ∧ f < N₃ * R ∧
        rank N₀ N₁ N₂ N₃ L ((s₀, s₁, s₂, s₃), c) * R + i =
          (((q * 2 ^ L + h) * N₂ + g) * 2 ^ L + d) * (N₃ * R) + f ∧
        rank N₀ N₁ N₂ N₃ L ((s₀, s₁, s₂, s₃), c ∘ e) * R + i =
          (((q * 2 ^ L + d) * N₂ + g) * 2 ^ L + h) * (N₃ * R) + f := by
    intro e he
    obtain ⟨k0, k1, k2⟩ := e12 e he
    refine ⟨(s₀ * 2 ^ L + c 0) * N₁ + s₁, c 1, s₂, c 2, s₃ * R + i,
      mix_lt (mix_lt s₀.isLt c0) s₁.isLt, c1, s₂.isLt, c2, mix_lt s₃.isLt hi, ?_, ?_⟩
    · simp only [rank]; ring
    · simp only [rank, k0, k1, k2]; ring
  have h02 : ∀ e : Equiv.Perm (Fin 3), e = Equiv.swap 0 2 →
      ∃ q h g d f, q < N₀ ∧ h < 2 ^ L ∧ g < N₁ * 2 ^ L * N₂ ∧ d < 2 ^ L ∧ f < N₃ * R ∧
        rank N₀ N₁ N₂ N₃ L ((s₀, s₁, s₂, s₃), c) * R + i =
          (((q * 2 ^ L + h) * (N₁ * 2 ^ L * N₂) + g) * 2 ^ L + d) * (N₃ * R) + f ∧
        rank N₀ N₁ N₂ N₃ L ((s₀, s₁, s₂, s₃), c ∘ e) * R + i =
          (((q * 2 ^ L + d) * (N₁ * 2 ^ L * N₂) + g) * 2 ^ L + h) * (N₃ * R) + f := by
    intro e he
    obtain ⟨k0, k1, k2⟩ := e02 e he
    refine ⟨s₀, c 0, (s₁ * 2 ^ L + c 1) * N₂ + s₂, c 2, s₃ * R + i,
      s₀.isLt, c0, mix_lt (mix_lt s₁.isLt c1) s₂.isLt, c2, mix_lt s₃.isLt hi, ?_, ?_⟩
    · simp only [rank]; ring
    · simp only [rank, k0, k1, k2]; ring
  fin_cases a <;> fin_cases b <;> simp at hab <;>
    simp (config := { decide := true }) only [swapDims, ite_true, ite_false]
  · exact h01 _ rfl
  · exact h02 _ rfl
  · exact h01 _ (Equiv.swap_comm _ _)
  · exact h12 _ rfl
  · exact h02 _ (Equiv.swap_comm _ _)
  · exact h12 _ (Equiv.swap_comm _ _)

/-- The list interchange with the dimensions `swapDims a b` moves the records of a stream as the
instruction `swap a b` does. -/
theorem swapList_moveRecs {α : Type*} (dflt : α) (a b : Fin 3) (hab : a ≠ b) (R : ℕ)
    (l : List (List α)) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L) (hR : ∀ x ∈ l, x.length = R) :
    swapList (swapDims N₀ N₁ N₂ N₃ L a b).1 (2 ^ L) (swapDims N₀ N₁ N₂ N₃ L a b).2.1 (2 ^ L)
        ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) dflt l.flatten =
      (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b]) l).flatten := by
  set π := rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b] with hπdef
  have hvol := swapDims_vol N₀ N₁ N₂ N₃ L a b hab R
  have hmem : ∀ x ∈ moveRecs π l, x.length = R := by
    intro x hx
    simp only [moveRecs, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    apply hR
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact (π.symm j).isLt)]
    exact List.getElem_mem _
  have hlen₀ : l.flatten.length = (swapDims N₀ N₁ N₂ N₃ L a b).1 * 2 ^ L *
      (swapDims N₀ N₁ N₂ N₃ L a b).2.1 * 2 ^ L * ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) := by
    rw [length_flatten_uniform _ hR, hl, hvol]
  have hlen₁ : (swapList (swapDims N₀ N₁ N₂ N₃ L a b).1 (2 ^ L) (swapDims N₀ N₁ N₂ N₃ L a b).2.1
      (2 ^ L) ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) dflt l.flatten).length =
      rectSize N₀ N₁ N₂ N₃ L * R := by
    rw [swapList, List.length_map, List.length_range, ← hvol]
  have hlen₂ : (moveRecs π l).flatten.length = rectSize N₀ N₁ N₂ N₃ L * R := by
    rw [length_flatten_uniform _ hmem, length_moveRecs]
  apply List.ext_getElem?
  intro z
  by_cases hz : z < rectSize N₀ N₁ N₂ N₃ L * R
  · have hR0 : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h | h
      · rw [h, Nat.mul_zero] at hz; omega
      · exact h
    obtain ⟨q, i, hi, hq, rfl⟩ : ∃ q i, i < R ∧ q < rectSize N₀ N₁ N₂ N₃ L ∧ z = q * R + i :=
      ⟨z / R, z % R, Nat.mod_lt _ hR0, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]),
        (Nat.div_add_mod' z R).symm⟩
    set r := π.symm ⟨q, hq⟩ with hr
    set p := (rankEquiv N₀ N₁ N₂ N₃ L).symm r with hp
    have hπ : π (rankEquiv N₀ N₁ N₂ N₃ L p) = ⟨q, hq⟩ := by simp [p, r]
    rw [hπdef, rankPerm_swap] at hπ
    have hq' : rank N₀ N₁ N₂ N₃ L (p.1, p.2 ∘ Equiv.swap a b) = q := by
      rw [← rankEquiv_val, hπ]
    have hrp : rank N₀ N₁ N₂ N₃ L p = r.val := by
      rw [← rankEquiv_val]; simp [p]
    obtain ⟨q₁, h, g, d, e, b1, b2, b3, b4, b5, hs, ht⟩ :=
      swap_index N₀ N₁ N₂ N₃ L a b hab R i hi p
    have hrl : r.val < l.length := by rw [hl]; exact r.isLt
    have e₁ : (swapList (swapDims N₀ N₁ N₂ N₃ L a b).1 (2 ^ L) (swapDims N₀ N₁ N₂ N₃ L a b).2.1
        (2 ^ L) ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * R) dflt l.flatten)[q * R + i]? =
        l[r.val]?.bind (·[i]?) := by
      rw [← hq', ht, swapList_getElem? dflt l.flatten hlen₀ b1 b2 b3 b4 b5, ← hs,
        flatten_getElem?_uniform _ hR _ _ hi, hrp]
    have e₂ : (moveRecs π l).flatten[q * R + i]? = l[r.val]?.bind (·[i]?) := by
      rw [flatten_getElem?_uniform _ hmem _ _ hi]
      simp only [moveRecs, List.getElem?_ofFn, hq, dite_true, List.getElem?_eq_getElem hrl,
        Option.bind_some]
      rw [List.getD_eq_getElem _ _ hrl]
    rw [e₁, e₂]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- `swapList_moveRecs` on bit streams: the interchange of the bits of a record stream is the
bit stream of the moved records. -/
theorem swapList_toBits {A : ℕ} (a b : Fin 3) (hab : a ≠ b) (B : ℕ)
    (l : List (List (Fin (A + 4)))) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hB : ∀ x ∈ l, x.length = B) :
    swapList (swapDims N₀ N₁ N₂ N₃ L a b).1 (2 ^ L) (swapDims N₀ N₁ N₂ N₃ L a b).2.1 (2 ^ L)
        ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * (3 * B)) blank (toBits l.flatten) =
      toBits (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b]) l).flatten := by
  have hmap : (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b]) l).map toBits =
      moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b]) (l.map toBits) := by
    simp only [moveRecs, List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[(rankPerm N₀ N₁ N₂ N₃ L K ρ n [.swap a b]).symm j]? <;> rfl
  rw [toBits_flatten, toBits_flatten, hmap]
  apply swapList_moveRecs N₀ N₁ N₂ N₃ L K ρ n blank a b hab (3 * B) (l.map toBits)
    (by rw [List.length_map, hl])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rw [length_toBits, hB y hy]

end Interchange

section Passes

variable {T Q A : ℕ} {U : Type} {F : Type} (body : F → Pr F T Q A U)

/-- Registers after emptying register `i` and pushing the list `w` onto register `j`. -/
def pushedR (R : Fin T → List (Fin (A + 4))) (i j : Fin T) (w : List (Fin (A + 4))) :
    Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R i []) j (w ++ R j)

/-- One step of `toBitsPass`: pop a symbol of register `i`, push its three bits onto register `j`,
least significant first. -/
def toBitsStep (i j : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push (.rt j) (fun v => bitSymbol ((v.sym.getD blank).val.testBit 0))
      (.push (.rt j) (fun v => bitSymbol ((v.sym.getD blank).val.testBit 1))
        (.push (.rt j) (fun v => bitSymbol ((v.sym.getD blank).val.testBit 2)) (peekR i))))

/-- Move register `i` onto register `j`, replacing each symbol by its three bits. -/
def toBitsPass (i j : Fin T) : Pr F T Q A U := whileR i (toBitsStep i j)

/-- The loop of `toBitsPass`. -/
theorem toBitsPass_loop (i j : Fin T) (hij : i ≠ j) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R i = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (toBitsStep i j))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := pushedR S.R i j (toBits l).reverse }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with R := pushedR S.R i j (toBits []).reverse } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [pushedR]
          · by_cases hk' : k = i
            · subst hk'; simp [pushedR, hk, hS]
            · simp [pushedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      set R₁ := Function.update (Function.update S.R i rest) j ((bits3 e).reverse ++ S.R j)
        with hR₁
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := R₁ } (by simp [hR₁, Function.update_of_ne hij]) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (toBitsStep i j : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome } { S with R := R₁ } := by
        simp [toBitsStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm, bits3, hR₁]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (toBitsStep i j) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [pushedR, hR₁, toBits_cons]
      · by_cases hk' : k = i
        · subst hk'; simp [pushedR, hR₁, hk]
        · simp [pushedR, hR₁, hk, hk']

/-- `toBitsPass i j` empties register `i` and pushes the reversed bit list of its content onto
register `j`. -/
theorem toBitsPass_exec (i j : Fin T) (hij : i ≠ j) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (toBitsPass i j) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with R := pushedR S.R i j (toBits (S.R i)).reverse }) := by
  obtain ⟨v', hu, he⟩ := toBitsPass_loop body i j hij (S.R i)
    { v with flag := (S.R i).head?.isSome } S rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S))
    he) (by ring) rfl⟩

/-- One step of `ofBitsPass`: pop three bits of register `i`, most significant first, and push the
symbol of their value onto register `j`. -/
def ofBitsStep (i j : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := shiftBit none o })
    (.pop (.rt i) (fun v o => { v with sym := shiftBit v.sym o })
      (.pop (.rt i) (fun v o => { v with sym := shiftBit v.sym o })
        (.push (.rt j) (fun v => v.sym.getD blank) (peekR i))))

/-- Move register `i` onto register `j`, replacing each triple of bits by the symbol of their
value; inverse to `toBitsPass` on symbols of value below `8`. -/
def ofBitsPass (i j : Fin T) : Pr F T Q A U := whileR i (ofBitsStep i j)

/-- The loop of `ofBitsPass`. -/
theorem ofBitsPass_loop (i j : Fin T) (hij : i ≠ j) :
    ∀ (m : List (Fin (A + 4))), (∀ x ∈ m, x.val < 8) → ∀ (v : HS T Q A U) (S : Stacks T A),
      S.R i = m.flatMap (fun x => (bits3 x).reverse) → v.flag = (S.R i).head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (ofBitsStep i j))) (mk v S) (2 * m.length + 1)
          (mk v' { S with R := pushedR S.R i j m.reverse }) := by
  intro m
  induction m with
  | nil =>
      intro _ v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with R := pushedR S.R i j ([] : List (Fin (A + 4))).reverse } : Stacks T A) =
          S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [pushedR]
          · by_cases hk' : k = i
            · subst hk'; simp [pushedR, hk, hS]
            · simp [pushedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa [hS] using hf)
  | cons e rest ih =>
      intro hm v S hS hf
      have he8 : e.val < 8 := hm e (by simp)
      set R₁ := Function.update (Function.update S.R i (rest.flatMap fun x => (bits3 x).reverse))
        j (e :: S.R j) with hR₁
      obtain ⟨v', hu, he⟩ := ih (fun x hx => hm x (by simp [hx]))
        { v with sym := some e, flag := (rest.flatMap fun x => (bits3 x).reverse).head?.isSome }
        { S with R := R₁ } (by simp [hR₁, Function.update_of_ne hij])
        (by simp [hR₁, Function.update_of_ne hij])
      refine ⟨v', hu, ?_⟩
      have hrun : (ofBitsStep i j : Act T Q A U).run (mk v S) =
          mk { v with
              sym := some e
              flag := (rest.flatMap fun x => (bits3 x).reverse).head?.isSome }
            { S with R := R₁ } := by
        set b₀ : Fin (A + 4) := bitSymbol (e.val.testBit 0) with hb₀
        set b₁ : Fin (A + 4) := bitSymbol (e.val.testBit 1) with hb₁
        set b₂ : Fin (A + 4) := bitSymbol (e.val.testBit 2) with hb₂
        set w := rest.flatMap fun x => (bits3 x).reverse with hw
        have hh : shiftBit (shiftBit (shiftBit none (some b₂)) (some b₁)) (some b₀) = some e :=
          shiftBit_bits3 e he8
        have hS' : S.R i = b₂ :: b₁ :: b₀ :: w := by rw [hS]; rfl
        simp [ofBitsStep, peekR, Action.run, hS', update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm, hR₁, hh]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        (by rw [mk_var, hf, hS]; simp [bits3])
        (hrun ▸ Exec.act (body := body) (ofBitsStep i j) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [pushedR, hR₁]
      · by_cases hk' : k = i
        · subst hk'; simp [pushedR, hR₁, hk]
        · simp [pushedR, hR₁, hk, hk']

/-- `ofBitsPass i j` on register `i` holding the reversed bit list of `m` empties register `i`
and pushes `m` onto register `j`. -/
theorem ofBitsPass_exec (i j : Fin T) (hij : i ≠ j) (m : List (Fin (A + 4)))
    (hm : ∀ x ∈ m, x.val < 8) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R i = (toBits m).reverse) :
    ∃ v', v'.user = v.user ∧
      Exec body (ofBitsPass i j) (mk v S) (2 * m.length + 2)
        (mk v' { S with R := pushedR S.R i j m }) := by
  rw [reverse_toBits] at hS
  obtain ⟨v', hu, he⟩ := ofBitsPass_loop body i j hij m.reverse (by simpa using hm)
    { v with flag := (S.R i).head?.isSome } S hS rfl
  rw [List.reverse_reverse, List.length_reverse] at he
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S))
    he) (by ring) rfl⟩

end Passes

section Pass

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Every record of a moved stream is a record of the original stream. -/
lemma mem_moveRecs {α : Type*} {M : ℕ} (π : Equiv.Perm (Fin M)) {l : List (List α)}
    (hl : l.length = M) {x : List α} (hx : x ∈ moveRecs π l) : x ∈ l := by
  simp only [moveRecs, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact (π.symm j).isLt)]
  exact List.getElem_mem _

/-- A list of bit symbols of length `V` as a bit vector. -/
lemma exists_ofFn_bits {A : ℕ} (l : List (Fin (A + 4))) (hl : ∀ s ∈ l, ∃ b, s = bitSymbol b)
    {V : ℕ} (hV : l.length = V) : ∃ x : Fin V → Bool, l = List.ofFn fun i => bitSymbol (x i) := by
  subst hV
  refine ⟨fun i => decide (l[i] = bitSymbol true), ?_⟩
  apply List.ext_getElem (by simp)
  intro z h₁ _
  have key : ∀ s : Fin (A + 4), (∃ b, s = bitSymbol b) →
      s = bitSymbol (decide (s = bitSymbol true)) := by
    rintro s ⟨b, rfl⟩
    cases b <;> simp [bitSymbol, Fin.ext_iff]
  simp only [List.getElem_ofFn]
  exact key _ (hl _ (List.getElem_mem h₁))

section Params

variable (N₀ N₁ N₂ N₃ L : ℕ)

/-- The interchange dimensions are positive. -/
lemma swapDims_pos (a b : Fin 3) (h₀ : 0 < N₀) (h₁ : 0 < N₁) (h₂ : 0 < N₂) (h₃ : 0 < N₃) :
    0 < (swapDims N₀ N₁ N₂ N₃ L a b).1 ∧ 0 < (swapDims N₀ N₁ N₂ N₃ L a b).2.1 ∧
      0 < (swapDims N₀ N₁ N₂ N₃ L a b).2.2 := by
  unfold swapDims
  split_ifs <;> exact ⟨by positivity, by positivity, by positivity⟩

end Params

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The host program for the instruction `swap a b` on the stream register `str`: expand the
stream to bits on `tmp`, move them to the payload register `ι (reg pay)`, run the placed
interchange, move the result back to `tmp`, and pack it onto `str`. The interchange dimensions
come from the five header registers, so the program itself does not depend on `a` and `b`. -/
def swapPass (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι)
    (hT : swapT t₀ ≤ T) (str tmp : Fin T) : Pr F T Q (prime + K) U :=
  .seq (toBitsPass str tmp)
    (.seq (moveR tmp (ι (reg pay)) id)
      (.seq (placedSwapProg hd pay hi hQ ι hι hT)
        (.seq (moveR (ι (reg pay)) tmp id) (ofBitsPass tmp str))))

/-- Running `swapPass` for `swap a b`.

Register interface: `ι` places the interchange bank (caller registers `ι (reg i)`, `i < t₀`,
private registers `ι j`, `t₀ ≤ j`); `str` (the stream) and `tmp` are distinct registers outside
the placement. Before the pass every left stack is empty, `str` holds `l.flatten`, `tmp`, the
payload register and the private registers are empty, header register `ι (reg (hd k))` holds
`separator :: (hs k).map bitSymbol` for canonical counters `hs k` of
`values P G B' L L k = ![P, G, B', L, L] k`, and every other caller register holds non-blank
symbols of the vendored alphabet.

Afterwards `str` holds the moved stream and every other stack, header registers included, is as
before. The step bound is `T + 12 * swapT t₀ + 5` host steps per step of the interchange
machine (simulation and normalization of the placed registers), `6` steps per symbol initially on
the placed registers, `34` steps per stream symbol for the conversions and moves, and a term
linear in the tape counts. -/
theorem swapPass_exec (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j, ι j ≠ str) (htmp : ∀ j, ι j ≠ tmp)
    (N₀ N₁ N₂ N₃ L Kc ρ n B : ℕ) (a b : Fin 3) (hab : a ≠ b)
    (h₀ : 0 < N₀) (h₁ : 0 < N₁) (h₂ : 0 < N₂) (h₃ : 0 < N₃) (hB : 0 < B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values
      (swapDims N₀ N₁ N₂ N₃ L a b).1 (swapDims N₀ N₁ N₂ N₃ L a b).2.1
      ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * (3 * B)) L L k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ y, S.L y = [])
    (hR : S.R str = l.flatten) (htmp0 : S.R tmp = []) (hpay0 : S.R (ι (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T + 12 * swapT t₀ + 5) * BinaryInterchangeRun.cost (swapDims N₀ N₁ N₂ N₃ L a b).1
          (swapDims N₀ N₁ N₂ N₃ L a b).2.1 ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * (3 * B)) L L hs +
        6 * ∑ j, (S.R (ι j)).length + 34 * (rectSize N₀ N₁ N₂ N₃ L * B) + 2 * T +
        6 * swapT t₀ + 23 ∧
      Exec body (swapPass hd pay hi hQ ι hι hT str tmp) (mk v S) m
        (mk v' { S with
          R := Function.update S.R str
            (moveRecs (rankPerm N₀ N₁ N₂ N₃ L Kc ρ n [.swap a b]) l).flatten }) := by
  classical
  set M := rectSize N₀ N₁ N₂ N₃ L with hM
  set π := rankPerm N₀ N₁ N₂ N₃ L Kc ρ n [.swap a b] with hπ
  set P := (swapDims N₀ N₁ N₂ N₃ L a b).1 with hP
  set G := (swapDims N₀ N₁ N₂ N₃ L a b).2.1 with hG
  set B' := (swapDims N₀ N₁ N₂ N₃ L a b).2.2 * (3 * B) with hB'
  set w := l.flatten with hw
  set w' := (moveRecs π l).flatten with hw'
  set pr := ι (reg pay) with hpr
  have hpay_str : pr ≠ str := hstr _
  have hpay_tmp : pr ≠ tmp := htmp _
  -- lengths
  have hwlen : w.length = M * B := by rw [hw, length_flatten_uniform _ hlB, hl]
  have hw'len : w'.length = M * B := by
    rw [hw', length_flatten_uniform _ (fun x hx => hlB x (mem_moveRecs π hl hx)), length_moveRecs]
  have hvol : P * 2 ^ L * G * 2 ^ L * B' = M * (3 * B) :=
    swapDims_vol N₀ N₁ N₂ N₃ L a b hab (3 * B)
  have hpos := swapDims_pos N₀ N₁ N₂ N₃ L a b h₀ h₁ h₂ h₃
  have hPpos : 0 < P := hpos.1
  have hGpos : 0 < G := hpos.2.1
  have hBpos : 0 < B' := Nat.mul_pos hpos.2.2 (by omega)
  -- the bit streams
  have hswap : swapList P (2 ^ L) G (2 ^ L) B' blank (toBits w) = toBits w' :=
    swapList_toBits N₀ N₁ N₂ N₃ L Kc ρ n a b hab B l hl hlB
  have h8' : ∀ s ∈ w', s.val < 8 := by
    intro s hs'
    obtain ⟨x, hx, hsx⟩ := List.mem_flatten.1 hs'
    exact h8 x (mem_moveRecs π hl hx) s hsx
  have hhd_pay : ∀ k, hd k ≠ pay := by
    intro k hk
    have h' := hhdr k
    rw [hk, hpay0] at h'
    exact List.cons_ne_nil _ _ h'.symm
  have hreg_pay : ∀ j : Fin (swapT t₀), j ≠ reg pay → ι j ≠ pr := fun j hj h' => hj (hι h')
  -- step 1: expand the stream to bits on `tmp`
  obtain ⟨v₁, hu₁, he₁⟩ := toBitsPass_exec body str tmp hst v S
  set S₁ : Stacks T (prime + K) := { S with R := pushedR S.R str tmp (toBits (S.R str)).reverse }
    with hS₁
  -- step 2: move the bits to the payload register
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp pr hpay_tmp.symm id v₁ S₁
  set S₂ : Stacks T (prime + K) := { S₁ with R := movedR S₁.R tmp pr id (S₁.R tmp) } with hS₂
  have hS₁tmp : S₁.R tmp = (toBits w).reverse := by
    show pushedR S.R str tmp (toBits (S.R str)).reverse tmp = _
    rw [pushedR, Function.update_self, hR, htmp0, List.append_nil]
  have hS₁pr : S₁.R pr = [] := by
    show pushedR S.R str tmp (toBits (S.R str)).reverse pr = _
    rw [pushedR, Function.update_of_ne hpay_tmp, Function.update_of_ne hpay_str, hpay0]
  have hS₂pr : S₂.R pr = toBits w := by
    show movedR S₁.R tmp pr id (S₁.R tmp) pr = _
    rw [movedR, Function.update_self, hS₁tmp, hS₁pr, List.map_id, List.reverse_reverse,
      List.append_nil]
  have hS₂oth : ∀ y, y ≠ pr → y ≠ str → y ≠ tmp → S₂.R y = S.R y := by
    intro y h₁' h₂' h₃'
    simp [hS₂, movedR, hS₁, pushedR, h₁', h₂', h₃']
  have hS₂str : S₂.R str = [] := by
    simp [hS₂, movedR, hS₁, pushedR, hst, Ne.symm hpay_str]
  have hS₂tmp : S₂.R tmp = [] := by
    simp [hS₂, movedR, hS₁, pushedR, Ne.symm hpay_tmp]
  have hS₂ι : ∀ j, j ≠ reg pay → S₂.R (ι j) = S.R (ι j) := fun j hj =>
    hS₂oth _ (hreg_pay j hj) (hstr j) (htmp j)
  -- step 3: the placed interchange
  have hblen :
      (toBits w).length = BinaryAdjacentWidthInterchange.volume P (2 ^ L) G (2 ^ L) B' := by
    rw [length_toBits, hwlen, BinaryAdjacentWidthInterchange.volume, hvol]; ring
  obtain ⟨x, hx⟩ := exists_ofFn_bits (toBits w) (fun s hs' => mem_toBits hs') hblen
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := placedSwapProg_exec body hd pay hi hQ ι hι hT P G B' L L hs
    (Nat.le_succ L) (Nat.le_succ L) hv hc hPpos hGpos hBpos x v₂ S₂ hL
    (fun j hj => by
      rw [hS₂ι j (fun h' => by rw [h', reg_val] at hj; exact absurd pay.isLt (by omega))]
      exact hpriv j hj)
    (fun k => by
      rw [hS₂ι _ (fun h' => hhd_pay k (BinaryInterchangeRun.slot_injective h'))]
      exact hhdr k)
    (by rw [hS₂pr, ← hx])
    (fun i hip hk => by
      rw [hS₂ι _ (fun h' => hip (BinaryInterchangeRun.slot_injective h'))]
      exact hother i hip hk)
  set S₃ : Stacks T (prime + K) := { S₂ with
    L := fun _ => []
    R := Function.update S₂.R pr (swapList P (2 ^ L) G (2 ^ L) B' blank (S₂.R pr)) } with hS₃
  have hS₃pr : S₃.R pr = toBits w' := by
    show Function.update S₂.R pr (swapList P (2 ^ L) G (2 ^ L) B' blank (S₂.R pr)) pr = _
    rw [Function.update_self, hS₂pr, hswap]
  -- step 4: move the interchanged bits back to `tmp`
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body pr tmp hpay_tmp id v₃ S₃
  set S₄ : Stacks T (prime + K) := { S₃ with R := movedR S₃.R pr tmp id (S₃.R pr) } with hS₄
  have hS₃tmp : S₃.R tmp = [] := by
    show Function.update S₂.R pr (swapList P (2 ^ L) G (2 ^ L) B' blank (S₂.R pr)) tmp = _
    rw [Function.update_of_ne (Ne.symm hpay_tmp), hS₂tmp]
  have hS₄tmp : S₄.R tmp = (toBits w').reverse := by
    show movedR S₃.R pr tmp id (S₃.R pr) tmp = _
    rw [movedR, Function.update_self, hS₃pr, hS₃tmp, List.map_id, List.append_nil]
  -- step 5: pack the bits onto the stream register
  obtain ⟨v₅, hu₅, he₅⟩ := ofBitsPass_exec body tmp str hst.symm w' h8' v₄ S₄ hS₄tmp
  -- the sum over the placed registers
  have hsum : ∑ j, (S₂.R (ι j)).length ≤ ∑ j, (S.R (ι j)).length + 3 * (M * B) := by
    have hpt : ∀ j, (S₂.R (ι j)).length ≤
        (S.R (ι j)).length + if j = reg pay then 3 * (M * B) else 0 := by
      intro j
      by_cases hj : j = reg pay
      · subst hj
        simp only [↓reduceIte]
        rw [← hpr, hS₂pr, length_toBits, hwlen]
        omega
      · simp only [hj, ↓reduceIte]
        rw [hS₂ι j hj]
        omega
    calc ∑ j, (S₂.R (ι j)).length
        ≤ ∑ j, ((S.R (ι j)).length + if j = reg pay then 3 * (M * B) else 0) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ = ∑ j, (S.R (ι j)).length + 3 * (M * B) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
  refine ⟨v₅, _, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))) rfl ?_⟩
  · have e₁ : (S.R str).length = M * B := by rw [hR, hwlen]
    have e₂ : (S₁.R tmp).length = 3 * (M * B) := by
      rw [hS₁tmp, List.length_reverse, length_toBits, hwlen]
    have e₄ : (S₃.R pr).length = 3 * (M * B) := by
      rw [hS₃pr, length_toBits, hw'len]
    rw [e₁, e₂, e₄, hw'len]
    nlinarith [hm₃, hsum]
  · congr 1
    refine Stacks.ext rfl rfl ?_ ?_
    · funext y
      exact (hL y).symm
    · funext y
      by_cases hy₁ : y = str
      · subst hy₁
        simp [pushedR, hst, hS₄, movedR, hS₃, Ne.symm hpay_str, hS₂str]
      · by_cases hy₂ : y = tmp
        · subst hy₂
          simp [pushedR, hy₁, htmp0]
        · by_cases hy₃ : y = pr
          · subst hy₃
            simp [pushedR, hy₁, hy₂, hS₄, movedR, hpay0]
          · simp [pushedR, hy₁, hy₂, hy₃, hS₄, movedR, hS₃, hS₂oth y hy₃ hy₁ hy₂]

/-- The constant of the vendored interchange time bound `BinaryInterchangeRun.uniform_bound`. -/
def swapConst : ℝ := Classical.choose BinaryInterchangeRun.uniform_bound

lemma swapConst_pos : 0 < swapConst := (Classical.choose_spec BinaryInterchangeRun.uniform_bound).1

/-- Transfer a step count bound `k * c + r` with `c ≤ C * (3 * V) * F` to the reals. -/
lemma cast_time_bound {m k c r : ℕ} {C V F : ℝ} (hm : m ≤ k * c + r)
    (hc : (c : ℝ) ≤ C * (3 * V) * F) :
    (m : ℝ) ≤ 3 * C * k * V * F + r := by
  have h₁ : (m : ℝ) ≤ k * c + r := by exact_mod_cast hm
  have h₂ := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) k)
  nlinarith

/-- `swapPass_exec` with the interchange cost bounded by `BinaryInterchangeRun.uniform_bound`. -/
theorem swapPass_exec_le (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j, ι j ≠ str) (htmp : ∀ j, ι j ≠ tmp)
    (N₀ N₁ N₂ N₃ L Kc ρ n B : ℕ) (a b : Fin 3) (hab : a ≠ b)
    (h₀ : 0 < N₀) (h₁ : 0 < N₁) (h₂ : 0 < N₂) (h₃ : 0 < N₃) (hB : 0 < B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values
      (swapDims N₀ N₁ N₂ N₃ L a b).1 (swapDims N₀ N₁ N₂ N₃ L a b).2.1
      ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * (3 * B)) L L k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ y, S.L y = [])
    (hR : S.R str = l.flatten) (htmp0 : S.R tmp = []) (hpay0 : S.R (ι (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ 3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (rectSize N₀ N₁ N₂ N₃ L * B : ℕ) *
          ((max 1 L : ℕ) : ℝ) ^ Parameters.tau +
        (6 * ∑ j, (S.R (ι j)).length + 34 * (rectSize N₀ N₁ N₂ N₃ L * B) + 2 * T +
          6 * swapT t₀ + 23 : ℕ) ∧
      Exec body (swapPass hd pay hi hQ ι hι hT str tmp) (mk v S) m
        (mk v' { S with
          R := Function.update S.R str
            (moveRecs (rankPerm N₀ N₁ N₂ N₃ L Kc ρ n [.swap a b]) l).flatten }) := by
  obtain ⟨v', m, hu, hm, he⟩ := swapPass_exec body hd pay hi hQ ι hι hT str tmp hst hstr htmp
    N₀ N₁ N₂ N₃ L Kc ρ n B a b hab h₀ h₁ h₂ h₃ hB l hl hlB h8 hs hv hc v S hL hR htmp0 hpay0
    hpriv hhdr hother
  refine ⟨v', m, hu, ?_, he⟩
  have hpos := swapDims_pos N₀ N₁ N₂ N₃ L a b h₀ h₁ h₂ h₃
  have hC := (Classical.choose_spec BinaryInterchangeRun.uniform_bound).2
    (swapDims N₀ N₁ N₂ N₃ L a b).1 (swapDims N₀ N₁ N₂ N₃ L a b).2.1
    ((swapDims N₀ N₁ N₂ N₃ L a b).2.2 * (3 * B)) L L hs hpos.1 hpos.2.1
    (Nat.mul_pos hpos.2.2 (by omega)) (Nat.le_succ L) (Nat.le_succ L) hv hc
  rw [max_self, BinaryAdjacentWidthInterchange.volume,
    swapDims_vol N₀ N₁ N₂ N₃ L a b hab (3 * B)] at hC
  have hvol : ((rectSize N₀ N₁ N₂ N₃ L * (3 * B) : ℕ) : ℝ) =
      3 * ((rectSize N₀ N₁ N₂ N₃ L * B : ℕ) : ℝ) := by
    push_cast; ring
  rw [hvol] at hC
  exact cast_time_bound (hm.trans (le_of_eq (by ring))) hC

end

end Pass

end IntegerMultBounds.MathlibTM2.Node
