module

public import IntegerMultBounds.Resampling.Script

/-! Axis exposure by one nonadjacent interchange (the repository's audited
routing note): swap the axis with the innermost field across the gap of the
fields between, map the lines, swap back. On entry lists the interchange is
`swapE` (`swapList_flatten`), and the sandwich on a block equals the head-axis
step of the flat pass (`sandwich_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.Sandwich
noncomputable section

open Machine Schoenhage ScriptSem FlatTensor AxisRounds

/-- The interchange of the fields `H` and `D` across a gap `G` inside an outer prefix `P`, on entries. -/
def swapE (P H G D : ℕ) (es : List (List Bool)) : List (List Bool) :=
  List.ofFn fun z : Fin (P * D * G * H) =>
    es.getD ((((z.val / H / G / D) * H + z.val % H) * G + z.val / H % G) * D + z.val / H / G % D) []

theorem length_swapE (P H G D : ℕ) (es : List (List Bool)) : (swapE P H G D es).length = P * D * G * H := by
  simp [swapE]

theorem getD_swapE (P H G D : ℕ) (es : List (List Bool)) {p h g d : ℕ} (hp : p < P) (hh : h < H) (hg : g < G)
    (hd : d < D) :
    (swapE P H G D es).getD (((p * D + d) * G + g) * H + h) [] = es.getD (((p * H + h) * G + g) * D + d) [] := by
  have hz : ((p * D + d) * G + g) * H + h < P * D * G * H := by
    have h1 : p * D + d < P * D := by nlinarith
    have h2 : (p * D + d) * G + g < P * D * G := by nlinarith
    nlinarith
  rw [swapE, getD_ofFn' _ _ hz]
  simp only [(div_mod_eq _ _ _ hh).1, (div_mod_eq _ _ _ hh).2, (div_mod_eq _ _ _ hg).1, (div_mod_eq _ _ _ hg).2,
    (div_mod_eq _ _ _ hd).1, (div_mod_eq _ _ _ hd).2]

theorem decomp4 {z P D G H : ℕ} (hz : z < P * D * G * H) :
    ∃ p d g h, p < P ∧ d < D ∧ g < G ∧ h < H ∧ z = ((p * D + d) * G + g) * H + h := by
  obtain ⟨pdg, h, h1, hh, rfl⟩ := decomp2 hz
  obtain ⟨pd, g, h2, hg, rfl⟩ := decomp2 h1
  obtain ⟨p, d, hp, hd, rfl⟩ := decomp2 h2
  exact ⟨p, d, g, h, hp, hd, hg, hh, rfl⟩

theorem mem_swapE (P H G D : ℕ) (es : List (List Bool)) (hl : es.length = P * H * G * D) {e : List Bool}
    (he : e ∈ swapE P H G D es) : e ∈ es := by
  rw [swapE, List.mem_ofFn] at he
  obtain ⟨z, rfl⟩ := he
  obtain ⟨p, d, g, h, hp, hd, hg, hh, hz⟩ := decomp4 z.isLt
  simp only [hz, (div_mod_eq _ _ _ hh).1, (div_mod_eq _ _ _ hh).2, (div_mod_eq _ _ _ hg).1, (div_mod_eq _ _ _ hg).2,
    (div_mod_eq _ _ _ hd).1, (div_mod_eq _ _ _ hd).2]
  have hi : ((p * H + h) * G + g) * D + d < es.length := by
    rw [hl]
    have h1 : p * H + h < P * H := by nlinarith
    have h2 : (p * H + h) * G + g < P * H * G := by nlinarith
    nlinarith
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

/-- The bit-level interchange of whole entries is `swapE`. -/
theorem swapList_flatten (P H G D B : ℕ) (es : List (List Bool)) (hw : ∀ e ∈ es, e.length = B)
    (hl : es.length = P * H * G * D) :
    SwapPrim.swapList P H G D B es.flatten = (swapE P H G D es).flatten := by
  have hw' : ∀ e ∈ swapE P H G D es, e.length = B := fun e he => hw e (mem_swapE P H G D es hl he)
  have hL : (swapE P H G D es).flatten.length = P * D * G * H * B := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hw']
    simp [length_swapE]
  apply ext_getD' false
  · rw [length_swapList', hL]
  · intro z hz
    rw [length_swapList'] at hz
    obtain ⟨e, b, he, hb, rfl⟩ := decomp2 hz
    obtain ⟨p, d, g, h, hp, hd, hg, hh, rfl⟩ := decomp4 he
    rw [getD_swapList P H G D B _ hp hh hg hd hb,
      getD_flatten_uniform B _ hw' _ _ (by rw [length_swapE]; exact he) hb, getD_swapE P H G D es hp hh hg hd]
    have hi : ((p * H + h) * G + g) * D + d < es.length := by
      rw [hl]
      have h1 : p * H + h < P * H := by nlinarith
      have h2 : (p * H + h) * G + g < P * H * G := by nlinarith
      nlinarith
    rw [getD_flatten_uniform B es hw _ _ hi hb]

/-- Swapping an axis with the innermost field, mapping lines and swapping back is the head-axis step of the
flat pass in every outer block. -/
theorem sandwich_eq (Q T0 Gm D : ℕ) (g : List (List Bool) → List (List Bool)) (es : List (List Bool))
    (hl : es.length = Q * (T0 * (Gm * D))) (hT0 : 0 < T0) (hGm : 0 < Gm) (hD : 0 < D)
    (hg : ∀ l : List (List Bool), l.length = T0 → (g l).length = T0) :
    swapE Q D Gm T0 (mapBlocks T0 g (swapE Q T0 Gm D es)) =
      mapBlocks (T0 * (Gm * D)) (fun blk => trL (Gm * D) T0 [] (mapBlocks T0 g (trL T0 (Gm * D) [] blk))) es := by
  set X := swapE Q T0 Gm D es
  have hX : X.length = Q * D * Gm * T0 := length_swapE _ _ _ _ _
  have hXb : ∀ bi, bi < Q * D * Gm → (block T0 bi X).length = T0 := fun bi hb =>
    length_block T0 bi X (Q * D * Gm) hX hb
  set Y := mapBlocks T0 g X
  have hY : Y.length = Q * D * Gm * T0 := by
    rw [length_mapBlocks T0 T0 g X (fun b hb => hg _ (hXb b (by rw [hX, Nat.mul_div_cancel _ hT0] at hb; exact hb))),
      hX, Nat.mul_div_cancel _ hT0]
  have hN : 0 < T0 * (Gm * D) := by positivity
  set f := fun blk : List (List Bool) => trL (Gm * D) T0 [] (mapBlocks T0 g (trL T0 (Gm * D) [] blk))
  have hf : ∀ b, b < Q → (f (block (T0 * (Gm * D)) b es)).length = T0 * (Gm * D) := fun b _ => by
    simp only [f, length_trL]; try ring
  have hR : (mapBlocks (T0 * (Gm * D)) f es).length = Q * (T0 * (Gm * D)) := by
    rw [length_mapBlocks _ (T0 * (Gm * D)) f es (fun b hb => hf b (by rw [hl, Nat.mul_div_cancel _ hN] at hb; exact hb)),
      hl, Nat.mul_div_cancel _ hN]
  apply ext_getD' []
  · rw [length_swapE, hR]; ring
  · intro z hz
    rw [length_swapE] at hz
    obtain ⟨q, a, gg, c, hq, ha, hgg, hc, rfl⟩ := decomp4 hz
    -- left: the outer swap, then the line map
    have hbi : (q * D + c) * Gm + gg < Q * D * Gm := by
      have h1 : q * D + c < Q * D := by nlinarith
      nlinarith
    rw [getD_swapE Q D Gm T0 _ hq hc hgg ha,
      getD_mapBlocks T0 T0 (Q * D * Gm) g X hT0 hX (fun b hb => hg _ (hXb b hb)) hbi ha]
    -- right: the block, then the transposes
    have hin : a * (Gm * D) + (gg * D + c) < T0 * (Gm * D) := by
      have : gg * D + c < Gm * D := by nlinarith
      nlinarith
    rw [show ((q * T0 + a) * Gm + gg) * D + c = q * (T0 * (Gm * D)) + (a * (Gm * D) + (gg * D + c)) by ring,
      getD_mapBlocks _ (T0 * (Gm * D)) Q f es hN hl hf hq hin]
    have hbq : (block (T0 * (Gm * D)) q es).length = T0 * (Gm * D) := length_block _ _ _ Q hl hq
    have hcol : gg * D + c < Gm * D := by nlinarith
    simp only [f]
    rw [getD_trL (Gm * D) T0 [] _ hcol ha]
    have hZ : (trL T0 (Gm * D) [] (block (T0 * (Gm * D)) q es)).length = Gm * D * T0 := length_trL _ _ _ _
    rw [getD_mapBlocks T0 T0 (Gm * D) g _ hT0 hZ (fun b hb => hg _ (length_block _ _ _ (Gm * D) hZ hb)) hcol ha]
    congr 2
    apply ext_getD' []
    · rw [hXb _ hbi, length_block _ _ _ (Gm * D) hZ hcol]
    · intro j hj
      rw [hXb _ hbi] at hj
      rw [getD_block _ _ _ hj, getD_block _ _ _ hj, getD_swapE Q T0 Gm D es hq hj hgg hc,
        getD_trL T0 (Gm * D) [] _ hj hcol, getD_block _ _ _ (by nlinarith)]
      congr 1; ring

end
end IntegerMultBounds.Resampling.Sandwich
