module

public import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# The rectangular interchange on lists

`swapList P H G D B dflt l` interchanges a list laid out as `[P]×[H]×[G]×[D]×[B]` (row-major, `P`
outermost) into `[P]×[D]×[G]×[H]×[B]`; `swapList_getElem?` states it with explicit index
arithmetic.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

/-- Source offset of the cell at target offset `z` when `[P]×[H]×[G]×[D]×[B]` (row-major, `P`
outermost) is interchanged into `[P]×[D]×[G]×[H]×[B]`. -/
def swapSrc (H G D B z : ℕ) : ℕ :=
  (((z / B / H / G / D * H + z / B % H) * G + z / B / H % G) * D + z / B / H / G % D) * B + z % B

/-- The interchange of a list laid out as `[P]×[H]×[G]×[D]×[B]` into `[P]×[D]×[G]×[H]×[B]`;
`dflt` fills offsets beyond the list. -/
def swapList {α : Type*} (P H G D B : ℕ) (dflt : α) (l : List α) : List α :=
  (List.range (P * D * G * H * B)).map fun z => l.getD (swapSrc H G D B z) dflt

lemma div_mod_mix {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := by omega
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma mix_lt {a b A n : ℕ} (ha : a < A) (hb : b < n) : a * n + b < A * n := by
  have : (a + 1) * n ≤ A * n := Nat.mul_le_mul_right _ ha
  nlinarith

/-- Entry of the interchanged list: target cell `(p, d, g, h, b)` holds source cell
`(p, h, g, d, b)`. -/
theorem swapList_getElem? {α : Type*} {P H G D B : ℕ} (dflt : α) (l : List α)
    (hl : l.length = P * H * G * D * B) {p h g d b : ℕ}
    (hp : p < P) (hh : h < H) (hg : g < G) (hd : d < D) (hb : b < B) :
    (swapList P H G D B dflt l)[(((p * D + d) * G + g) * H + h) * B + b]? =
      l[(((p * H + h) * G + g) * D + d) * B + b]? := by
  have hz : (((p * D + d) * G + g) * H + h) * B + b < P * D * G * H * B :=
    mix_lt (mix_lt (mix_lt (mix_lt hp hd) hg) hh) hb
  have hs : (((p * H + h) * G + g) * D + d) * B + b < l.length :=
    hl ▸ mix_lt (mix_lt (mix_lt (mix_lt hp hh) hg) hd) hb
  rw [swapList, List.getElem?_map, List.getElem?_range hz, Option.map_some]
  have hsrc : swapSrc H G D B ((((p * D + d) * G + g) * H + h) * B + b) =
      (((p * H + h) * G + g) * D + d) * B + b := by
    unfold swapSrc
    rw [(div_mod_mix hb).1, (div_mod_mix hb).2, (div_mod_mix hh).1, (div_mod_mix hh).2,
      (div_mod_mix hg).1, (div_mod_mix hg).2, (div_mod_mix hd).1, (div_mod_mix hd).2]
  rw [hsrc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
  rfl

end IntegerMultBounds.MathlibTM2.Host
