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

open Machine Schoenhage ScriptSem FlatTensor AxisRounds AxisDriver Script

variable {E : ℕ}

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

/-! ### The script -/

theorem trL_one_left {α : Type*} (n : ℕ) (x : α) (xs : List α) (hl : xs.length = n) : trL 1 n x xs = xs := by
  apply ext_getD' x
  · rw [length_trL, hl, mul_one]
  · intro j hj
    rw [length_trL, mul_one] at hj
    have := getD_trL 1 n x xs (i := 0) (j := j) one_pos hj
    simpa using this

theorem trL_one_right {α : Type*} (M : ℕ) (x : α) (xs : List α) (hl : xs.length = M) : trL M 1 x xs = xs := by
  apply ext_getD' x
  · rw [length_trL, hl, one_mul]
  · intro i hi
    rw [length_trL, one_mul] at hi
    have := getD_trL M 1 x xs (i := i) (j := 0) hi one_pos
    simpa using this

/-- The records for the head axis: alone it needs no move; otherwise swap it with the innermost field, its
record, swap back. -/
def headRecs (B : ℕ) : (d : ℕ) → (Fin (d + 1) → ℕ) → ℕ → List (List Bool) → List Rec
  | 0, _, _, ws => [.axis ws]
  | d + 1, lg, Q, ws =>
    [.swap (swapHdrsG Q ((∏ i : Fin (d + 1), 2 ^ lg i.succ) / 2 ^ lg (Fin.last (d + 1))) (lg 0)
        (lg (Fin.last (d + 1))) B),
      .axis ws,
      .swap (swapHdrsG Q ((∏ i : Fin (d + 1), 2 ^ lg i.succ) / 2 ^ lg (Fin.last (d + 1)))
        (lg (Fin.last (d + 1))) (lg 0) B)]

/-- The tensor script with one interchange each way per axis: the tail axes, then the head axis. -/
def sScript (B : ℕ) : (d : ℕ) → (Fin d → ℕ) → ℕ → (Fin d → List (List Bool)) → List Rec
  | 0, _, _, _ => []
  | d + 1, lg, Q, aw => sScript B d (fun i => lg i.succ) (Q * 2 ^ lg 0) (fun i => aw i.succ) ++ headRecs B d lg Q (aw 0)

theorem last_dvd_prod (d : ℕ) (lg : Fin (d + 2) → ℕ) :
    (∏ i : Fin (d + 1), 2 ^ lg i.succ) = (∏ i : Fin (d + 1), 2 ^ lg i.succ) / 2 ^ lg (Fin.last (d + 1)) *
      2 ^ lg (Fin.last (d + 1)) := by
  rw [Nat.div_mul_cancel]
  exact Finset.dvd_prod_of_mem (fun i : Fin (d + 1) => 2 ^ lg i.succ) (Finset.mem_univ (Fin.last d)) |>.trans
    (by rfl) |> fun h => by simpa [Fin.succ_last] using h

theorem lenFlat (B : ℕ) (es : List (List Bool)) (h : ∀ e ∈ es, e.length = B) :
    es.flatten.length = es.length * B := by
  rw [List.length_flatten, List.map_congr_left (g := fun _ => B) h]; simp

theorem flatMap_congr2 {β γ : Type*} {f g : β → List γ} : ∀ l : List β, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons]; rw [h x (by simp), flatMap_congr2 l (fun y hy => h y (by simp [hy]))]

theorem mapBlocks_congr {α : Type*} (n : ℕ) (f g : List α → List α) (xs : List α)
    (h : ∀ b, b < xs.length / n → f (block n b xs) = g (block n b xs)) : mapBlocks n f xs = mapBlocks n g xs := by
  unfold mapBlocks
  exact flatMap_congr2 _ fun b hb => h b (List.mem_range.mp hb)

theorem headRecs_spec (S : AxisSpec E) (B NT : ℕ) (hB : 0 < B) (d : ℕ) (lg : Fin (d + 1) → ℕ) (Q : ℕ)
    (ws : List (List Bool)) (G0 : List (List Bool) → List (List Bool)) (es : List (List Bool))
    (hlg : ∀ i j, lg i ≤ lg j + 1)
    (hGl : ∀ l : List (List Bool), l.length = 2 ^ lg 0 → (G0 l).length = 2 ^ lg 0)
    (hGw : ∀ l : List (List Bool), l.length = 2 ^ lg 0 → (∀ e ∈ l, e.length = B) → ∀ e ∈ G0 l, e.length = B)
    (hax : ∀ xs : List (List Bool), xs.length = NT → (∀ e ∈ xs, e.length = B) →
      ws.length = S.regs.length ∧ S.Good ws xs.flatten ∧ S.f ws xs.flatten = (mapBlocks (2 ^ lg 0) G0 xs).flatten)
    (hQ : 0 < Q) (hNT : Q * (2 ^ lg 0 * ∏ i : Fin d, 2 ^ lg i.succ) = NT) (hl : es.length = NT)
    (hw : ∀ e ∈ es, e.length = B) :
    Valid S (headRecs B d lg Q ws) es.flatten ∧
      result S (headRecs B d lg Q ws) es.flatten =
        (mapBlocks (2 ^ lg 0 * ∏ i : Fin d, 2 ^ lg i.succ) (fun blk => trL (∏ i : Fin d, 2 ^ lg i.succ) (2 ^ lg 0) []
          (mapBlocks (2 ^ lg 0) G0 (trL (2 ^ lg 0) (∏ i : Fin d, 2 ^ lg i.succ) [] blk))) es).flatten ∧
      ∀ Ka Ks : ℕ,
        (∀ xs : List (List Bool), xs.length = NT → (∀ e ∈ xs, e.length = B) → axisCost S ws xs.flatten ≤ Ka) →
        (∀ (P G h d' : ℕ) (A : List Bool), A.length = NT * B → (∃ i, h = lg i) → (∃ j, d' = lg j) →
          swapCost (swapHdrsG P G h d' B) A ≤ Ks) →
        driveCost S (headRecs B d lg Q ws) es.flatten ≤ Ka + 3 + 2 * (Ks + 3) := by
  have hT0 : 0 < 2 ^ lg 0 := by positivity
  cases d with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hNT ⊢
    have hl' : es.length = Q * 2 ^ lg 0 := by rw [hl, ← hNT]
    obtain ⟨h1, h2, h3⟩ := hax es hl hw
    refine ⟨⟨h1, h2, trivial⟩, ?_, ?_⟩
    swap
    · intro Ka Ks hKa _
      have := hKa es hl hw
      simp only [headRecs, driveCost]; omega
    simp only [headRecs, result]
    rw [h3]
    congr 1
    rw [mapBlocks_nest (2 ^ lg 0) 1 Q (G0) es [] hT0 one_pos (by rw [hl']; ring) hGl, one_mul]
    apply mapBlocks_congr
    intro b hb
    rw [hl', Nat.mul_div_cancel _ hT0] at hb
    have hbl := length_block (2 ^ lg 0) b es Q hl' hb
    rw [trL_one_right _ _ _ hbl]
    rw [trL_one_left _ _ _ (by
      rw [length_mapBlocks _ (2 ^ lg 0) _ _ (fun c hc => hGl _ (length_block _ _ _ 1 (by rw [hbl, one_mul])
        (by rw [hbl, Nat.div_self hT0] at hc; exact hc))), hbl, Nat.div_self hT0, one_mul])]
  | succ d =>
    set T0 := 2 ^ lg 0
    set R := ∏ i : Fin (d + 1), 2 ^ lg i.succ
    set hlast := lg (Fin.last (d + 1))
    set D := 2 ^ hlast
    set Gm := R / D
    have hRGD : R = Gm * D := last_dvd_prod d lg
    have hR : 0 < R := prod_pos_pow _
    have hD : 0 < D := by positivity
    have hGm : 0 < Gm := Nat.div_pos (by rw [hRGD]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (by
      intro h; rw [h, zero_mul] at hRGD; omega))) hD
    have hl' : es.length = Q * T0 * Gm * D := by rw [hl, ← hNT, hRGD]; ring
    have hflat : es.flatten.length = Q * 2 ^ lg 0 * Gm * 2 ^ hlast * B := by
      rw [lenFlat B es hw, hl']
    obtain ⟨p1, f1⟩ := swapRecG_spec Q Gm (lg 0) hlast B es.flatten hQ hGm hB (hlg _ _) (hlg _ _) hflat
    rw [swapList_flatten Q T0 Gm D B es hw hl'] at f1
    set es2 := swapE Q T0 Gm D es
    have hes2 : es2.length = NT := by rw [length_swapE, ← hl, hl']; ring
    have hes2w : ∀ e ∈ es2, e.length = B := fun e he => hw e (mem_swapE Q T0 Gm D es hl' he)
    obtain ⟨a1, a2, a3⟩ := hax es2 hes2 hes2w
    set es3 := mapBlocks T0 G0 es2
    have hdivT : es2.length / T0 = Q * D * Gm := by rw [length_swapE, Nat.mul_div_cancel _ (by positivity)]
    have hes3 : es3.length = Q * D * Gm * T0 := by
      rw [length_mapBlocks T0 T0 G0 es2 (fun b hb => hGl _ (length_block _ _ _ (Q * D * Gm) (length_swapE _ _ _ _ _)
        (hdivT ▸ hb))), hdivT]
    have hes3w : ∀ e ∈ es3, e.length = B := by
      intro e he; simp only [es3, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he
      rw [hdivT] at hb
      exact hGw _ (length_block _ _ _ (Q * D * Gm) (length_swapE _ _ _ _ _) hb)
        (fun e' he' => hes2w e' (List.mem_of_mem_drop (List.mem_of_mem_take he'))) e he
    have hflat3 : es3.flatten.length = Q * 2 ^ hlast * Gm * 2 ^ lg 0 * B := by
      rw [lenFlat B es3 hes3w, hes3]
    obtain ⟨p2, f2⟩ := swapRecG_spec Q Gm hlast (lg 0) B es3.flatten hQ hGm hB (hlg _ _) (hlg _ _) hflat3
    rw [swapList_flatten Q D Gm T0 B es3 hes3w (by rw [hes3])] at f2
    have hsw := sandwich_eq Q T0 Gm D G0 es (by rw [hl']; ring) (by positivity) hGm hD hGl
    refine ⟨⟨rfl, p1, by rw [f1]; exact ⟨a1, a2, by rw [a3]; exact ⟨rfl, p2, trivial⟩⟩⟩, ?_, ?_⟩
    · simp only [headRecs, result]
      rw [f1, a3, f2, hsw, ← hRGD]
    · intro Ka Ks hKa hKs
      have c1 := hKs Q Gm (lg 0) hlast es.flatten (by rw [lenFlat B es hw, hl]) ⟨0, rfl⟩ ⟨_, rfl⟩
      have c2 := hKa es2 hes2 hes2w
      have c3 := hKs Q Gm hlast (lg 0) es3.flatten (by rw [lenFlat B es3 hes3w, hes3, ← hes2, length_swapE])
        ⟨_, rfl⟩ ⟨0, rfl⟩
      have hh : headRecs B (d + 1) lg Q ws = [.swap (swapHdrsG Q Gm (lg 0) hlast B), .axis ws,
          .swap (swapHdrsG Q Gm hlast (lg 0) B)] := rfl
      rw [hh]
      simp only [driveCost]
      rw [f1, a3]
      omega

theorem sScript_spec (S : AxisSpec E) (B NT : ℕ) (hB : 0 < B) : ∀ (d : ℕ) (lg : Fin d → ℕ) (Q : ℕ)
    (aw : Fin d → List (List Bool)) (G : Fin d → List (List Bool) → List (List Bool)) (es : List (List Bool)),
    (∀ i j, lg i ≤ lg j + 1) →
    (∀ i (l : List (List Bool)), l.length = 2 ^ lg i → (G i l).length = 2 ^ lg i) →
    (∀ i (l : List (List Bool)), l.length = 2 ^ lg i → (∀ e ∈ l, e.length = B) → ∀ e ∈ G i l, e.length = B) →
    (∀ i (xs : List (List Bool)), xs.length = NT → (∀ e ∈ xs, e.length = B) →
      (aw i).length = S.regs.length ∧ S.Good (aw i) xs.flatten ∧
      S.f (aw i) xs.flatten = (mapBlocks (2 ^ lg i) (G i) xs).flatten) →
    0 < Q → Q * ∏ i, 2 ^ lg i = NT → es.length = NT → (∀ e ∈ es, e.length = B) →
    Valid S (sScript B d lg Q aw) es.flatten ∧
      result S (sScript B d lg Q aw) es.flatten =
        (mapBlocks (∏ i, 2 ^ lg i) (flatPass d (fun i => 2 ^ lg i) G []) es).flatten ∧
      ∀ (Ka : Fin d → ℕ) (Ks : ℕ),
        (∀ i (xs : List (List Bool)), xs.length = NT → (∀ e ∈ xs, e.length = B) →
          axisCost S (aw i) xs.flatten ≤ Ka i) →
        (∀ (P G h d' : ℕ) (A : List Bool), A.length = NT * B → (∃ i, h = lg i) → (∃ j, d' = lg j) →
          swapCost (swapHdrsG P G h d' B) A ≤ Ks) →
        driveCost S (sScript B d lg Q aw) es.flatten ≤ (∑ i, Ka i) + d * (3 + 2 * (Ks + 3))
  | 0, lg, Q, aw, G, es, _, _, _, _, hQ, hNT, hl, hw => by
    refine ⟨trivial, ?_, fun _ _ _ _ => by simp [sScript, driveCost]⟩
    simp only [sScript, result, Finset.univ_eq_empty, Finset.prod_empty]
    congr 1
    have hb1 : ∀ b, b < es.length → (flatPass 0 (fun i => 2 ^ lg i) G [] (block 1 b es)).length = 1 :=
      fun b hb => length_block 1 b es es.length (by ring) hb
    apply ext_getD' []
    · rw [length_mapBlocks 1 1 _ _ (fun b hb => hb1 b (by simpa using hb))]; simp
    · intro z hz
      have := getD_mapBlocks 1 1 es.length _ es one_pos (by ring) hb1 hz one_pos []
      simp only [mul_one, add_zero] at this
      rw [this, show flatPass 0 (fun i => 2 ^ lg i) G [] (block 1 z es) = block 1 z es from rfl,
        getD_block _ _ _ one_pos]
      simp
  | d + 1, lg, Q, aw, G, es, hlg, hGl, hGw, hax, hQ, hNT, hl, hw => by
    set T0 := 2 ^ lg 0
    set R := ∏ i : Fin d, 2 ^ lg i.succ
    have hR : 0 < R := prod_pos_pow _
    have hT0 : 0 < T0 := by positivity
    have hprod : ∏ i : Fin (d + 1), 2 ^ lg i = T0 * R := Fin.prod_univ_succ _
    have hl' : es.length = Q * (T0 * R) := by rw [hl, ← hNT, hprod]
    -- 1. the tail axes
    obtain ⟨v1, r1, k1⟩ := sScript_spec S B NT hB d (fun i => lg i.succ) (Q * T0) (fun i => aw i.succ)
      (fun i => G i.succ) es (fun i j => hlg _ _) (fun i l => hGl i.succ l) (fun i l => hGw i.succ l)
      (fun i xs => hax i.succ xs) (by positivity) (by rw [← hNT, hprod]; ring) hl hw
    set φ := flatPass d (fun i => 2 ^ lg i.succ) (fun i => G i.succ) ([] : List Bool)
    have hφ : ∀ l : List (List Bool), l.length = R → (φ l).length = R := fun l hl =>
      (flatPass_props (fun _ => True) d (fun i => lg i.succ) (fun i => G i.succ) [] l
        (fun i l' hl' _ => ⟨hGl i.succ l' hl', fun _ _ => trivial⟩) hl (fun _ _ => trivial)).1
    set es1 := mapBlocks R φ es
    have hdivR : es.length / R = Q * T0 := by rw [hl', show Q * (T0 * R) = Q * T0 * R by ring, Nat.mul_div_cancel _ hR]
    have hfp := fun b (hb : b < Q * T0) => flatPass_props (fun e : List Bool => e.length = B) d
      (fun i => lg i.succ) (fun i => G i.succ) [] (block R b es) (fun i l h1 h2 => ⟨hGl i.succ l h1, hGw i.succ l h1 h2⟩)
      (length_block _ _ _ (Q * T0) (by rw [hl']; ring) hb)
      (fun e he => hw e (List.mem_of_mem_drop (List.mem_of_mem_take he)))
    have hes1 : es1.length = Q * (T0 * R) := by
      rw [length_mapBlocks R R _ es (fun b hb => (hfp b (hdivR ▸ hb)).1), hdivR]; ring
    have hes1w : ∀ e ∈ es1, e.length = B := by
      intro e he; simp only [es1, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he; exact (hfp b (hdivR ▸ hb)).2 e he
    have e1 : es1 = mapBlocks (T0 * R) (mapBlocks R φ) es :=
      mapBlocks_nest R T0 Q φ es [] hR hT0 hl' (fun l hl => hφ l hl)
    -- the head step on each block
    set head := fun blk : List (List Bool) => trL R T0 [] (mapBlocks T0 (G 0) (trL T0 R [] blk))
    have hfinal : (mapBlocks (T0 * R) head es1) = mapBlocks (T0 * R) (flatPass (d + 1) (fun i => 2 ^ lg i) G []) es := by
      rw [e1, mapBlocks_comp (T0 * R) Q head (mapBlocks R φ) es [] (by positivity) hl'
        (fun l hl => by
          rw [length_mapBlocks R R φ l (fun b hb => hφ _ (length_block _ _ _ T0 (by rw [hl])
            (by rw [hl, Nat.mul_div_cancel _ hR] at hb; exact hb))), hl,
            Nat.mul_div_cancel _ hR])
        (fun l _ => by simp only [head, length_trL]; try ring)]
      rfl
    obtain ⟨vh, rh, kh⟩ := headRecs_spec S B NT hB d lg Q (aw 0) (G 0) es1 hlg (hGl 0) (hGw 0) (hax 0) hQ
      (by rw [← hNT, hprod]) (by rw [hes1, ← hNT, hprod]) hes1w
    have hscr : sScript B (d + 1) lg Q aw = sScript B d (fun i => lg i.succ) (Q * T0) (fun i => aw i.succ) ++
        headRecs B d lg Q (aw 0) := rfl
    rw [hscr]
    refine ⟨valid_append S _ _ _ v1 (by rw [r1]; exact vh), ?_, ?_⟩
    · rw [result_append, r1, rh, hfinal, hprod]
    · intro Ka Ks hKa hKs
      have h1 := k1 (fun i => Ka i.succ) Ks (fun i xs h1 h2 => hKa i.succ xs h1 h2)
        (fun P G' h d' A hA ⟨i, hi⟩ ⟨j, hj⟩ => hKs P G' h d' A hA ⟨i.succ, hi⟩ ⟨j.succ, hj⟩)
      have h2 := kh (Ka 0) Ks (hKa 0) hKs
      rw [driveCost_append, r1, Fin.sum_univ_succ]
      nlinarith

end
end IntegerMultBounds.Resampling.Sandwich
