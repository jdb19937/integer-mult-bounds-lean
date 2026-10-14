module

public import IntegerMultBounds.Schoenhage.SwapPrim

/-! The interchange of two address fields of a flat bit array as an index map
(`getD_swapList`), with its length (`length_swapList`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.AxisRounds

open IntegerMultBounds.Machine IntegerMultBounds.Schoenhage

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) : (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

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


end IntegerMultBounds.Resampling.AxisRounds
