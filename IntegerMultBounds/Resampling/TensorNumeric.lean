module

public import IntegerMultBounds.Resampling.LineNumeric

/-! The tensor driver's output decoded. Decoding commutes with the flat
pass when every line map does on good lines (`flatPass_map`); with the
expansion line maps the decoded result is the tensor of the floored tabled
`Ã` maps on the flat array (`expand_tensor`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.TensorNumeric
noncomputable section

open Machine Schoenhage FlatTensor ScriptSem LineMaps PaddedTensor FloorStep LineNumeric
open IntegerMultBounds.NLogN (tensorZR)

variable {α β : Type*}

theorem trL_map (M n : ℕ) (f : α → β) (x : α) (xs : List α) :
    (trL M n x xs).map f = trL M n (f x) (xs.map f) := by
  simp only [trL, List.map_ofFn]
  congr 1; funext z
  simp [List.getD_eq_getElem?_getD]

theorem block_map (n b : ℕ) (f : α → β) (xs : List α) : block n b (xs.map f) = (block n b xs).map f := by
  simp [block, List.map_drop, List.map_take]

theorem mapBlocks_map (n : ℕ) (f : α → β) (g : List α → List α) (g' : List β → List β) (xs : List α)
    (h : ∀ b, b < xs.length / n → (g (block n b xs)).map f = g' ((block n b xs).map f)) :
    (mapBlocks n g xs).map f = mapBlocks n g' (xs.map f) := by
  simp only [mapBlocks, List.map_flatMap, List.length_map]
  apply LineMaps.flatMap_congr'
  intro b hb
  rw [h b (List.mem_range.mp hb), block_map]

theorem flatPass_map (P : α → Prop) (f : α → β) : ∀ (d : ℕ) (lg : Fin d → ℕ) (G : Fin d → List α → List α)
    (G' : Fin d → List β → List β) (x : α) (xs : List α),
    (∀ i (l : List α), l.length = 2 ^ lg i → (∀ e ∈ l, P e) →
      (G i l).length = 2 ^ lg i ∧ (∀ e ∈ G i l, P e) ∧ (G i l).map f = G' i (l.map f)) →
    xs.length = ∏ i, 2 ^ lg i → (∀ e ∈ xs, P e) →
    (flatPass d (fun i => 2 ^ lg i) G x xs).map f = flatPass d (fun i => 2 ^ lg i) G' (f x) (xs.map f)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | d + 1, lg, G, G', x, xs, hG, hl, hp => by
    set R := ∏ i : Fin d, 2 ^ lg i.succ
    set T0 := 2 ^ lg 0
    have hR : 0 < R := prod_pos_pow _
    have hT0 : 0 < T0 := by positivity
    rw [Fin.prod_univ_succ] at hl
    have hblk : ∀ b, b < T0 → (block R b xs).length = R := fun b hb => length_block _ _ _ T0 hl hb
    have hbp : ∀ b, ∀ e ∈ block R b xs, P e := fun b e he => hp e (List.mem_of_mem_drop (List.mem_of_mem_take he))
    have hGp : ∀ i (l : List α), l.length = 2 ^ lg i → (∀ e ∈ l, P e) →
        (G i l).length = 2 ^ lg i ∧ ∀ e ∈ G i l, P e := fun i l h1 h2 => ⟨(hG i l h1 h2).1, (hG i l h1 h2).2.1⟩
    have ih := fun b (hb : b < T0) => flatPass_props P d (fun i => lg i.succ) (fun i => G i.succ) x (block R b xs)
      (fun i l => hGp i.succ l) (hblk b hb) (hbp b)
    have hdivR : xs.length / R = T0 := by rw [hl, Nat.mul_div_cancel _ hR]
    set W := mapBlocks R (flatPass d (fun i => 2 ^ lg i.succ) (fun i => G i.succ) x) xs
    have hW : W.length = T0 * R := by
      rw [length_mapBlocks R R _ xs (fun b hb => (ih b (hdivR ▸ hb)).1), hdivR]
    have hWp : ∀ e ∈ W, P e := by
      intro e he
      simp only [W, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he
      exact (ih b (hdivR ▸ hb)).2 e he
    set Z := trL T0 R x W
    have hZ : Z.length = R * T0 := length_trL _ _ _ _
    have hZp : ∀ e ∈ Z, P e := fun e he => hWp e (mem_trL _ _ _ _ hW he)
    have hdivT : Z.length / T0 = R := by rw [hZ, Nat.mul_div_cancel _ hT0]
    show (trL R T0 x (mapBlocks T0 (G 0) Z)).map f =
      trL R T0 (f x) (mapBlocks T0 (G' 0) (trL T0 R (f x) (mapBlocks R
        (flatPass d (fun i => 2 ^ lg i.succ) (fun i => G' i.succ) (f x)) (xs.map f))))
    rw [trL_map, mapBlocks_map T0 f (G 0) (G' 0) Z (fun b hb => (hG 0 _ (length_block _ _ _ R hZ (hdivT ▸ hb))
      (fun e he => hZp e (List.mem_of_mem_drop (List.mem_of_mem_take he)))).2.2), trL_map,
      mapBlocks_map R f _ _ xs (fun b hb => flatPass_map P f d (fun i => lg i.succ) (fun i => G i.succ)
        (fun i => G' i.succ) x _ (fun i l => hG i.succ l) (hblk b (hdivR ▸ hb)) (hbp b))]

/-- The floored tabled `Ã` from length `s` to `t`. -/
def floorAt (s t m α p : ℕ) (u : ZMod s → ℂ) : ZMod t → ℂ :=
  floorV p (NLogN.resampANum s t m (WindowSum.termW p fun k j => (WeightTable.tableA s t α p k j : ℝ) / 2 ^ p) u)

instance pow_neZero {d : ℕ} (lg : Fin d → ℕ) (i : Fin d) : NeZero (2 ^ lg i) := ⟨by positivity⟩

theorem floorA_ball (s t m α p : ℕ) [NeZero s] [NeZero t] (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hm : p * α ^ 2 ≤ m ^ 2)
    (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p) (v : ZMod t → ℂ) (hv : ‖v‖ ≤ 1) :
    ‖floorA s t m α p v‖ ≤ 1 := by
  have hαr : (2 : ℝ) ≤ α := by exact_mod_cast hα
  have hαpr : (α : ℝ) ^ 2 ≤ p := by exact_mod_cast hαp
  have hmr : (p : ℝ) * (α : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hm
  obtain ⟨-, -, hball⟩ := floorA_tabled (s := s) (t := t) hαr hαpr hmr hm1 hmp hp (WeightTable.tableA s t α p)
    (fun k j => WeightTable.tableA_err s t α p hp hα k j)
  refine hball _ ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun ℓ => ?_)
  exact (norm_le_pi_norm v _).trans hv

theorem expand_tensor (d : ℕ) (lg : Fin d → ℕ) (S : Fin d → ℕ) [∀ i, NeZero (S i)] (m α p w W : ℕ)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hm : p * α ^ 2 ≤ m ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (hw : p + 2 ≤ w) (hwW : w + 1 ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hS : ∀ i, S i ≤ 2 ^ lg i) (es : List (List Bool))
    (hes : ∀ e ∈ es, e.length = 2 * w ∧ ‖decE w p e‖ ≤ 1) (hl : es.length = ∏ i, 2 ^ lg i)
    (u : ((i : Fin d) → ZMod (2 ^ lg i)) → ℂ) (hu : es.map (decE w p) = lexFlat d (fun i => 2 ^ lg i) u) :
    (flatPass d (fun i => 2 ^ lg i)
      (fun i => lineA (TabATape.tabA (S i) (2 ^ lg i) m α p w (2 ^ lg i * (2 * m + 1))) (S i) (2 ^ lg i) m p w W)
      [] es).map (decE w p) =
      lexFlat d (fun i => 2 ^ lg i) (tensorZR d S (fun i => 2 ^ lg i) (fun i => floorAt (S i) (2 ^ lg i) m α p)
        (restrD S (fun i => 2 ^ lg i) u)) := by
  rw [flatPass_map (fun e => e.length = 2 * w ∧ ‖decE w p e‖ ≤ 1) (decE w p) d lg _
    (fun i => lineOf (floorA (S i) (2 ^ lg i) m α p)) [] es ?_ hl hes, decE_nil, hu,
    flatPass_lexFlat d (fun i => 2 ^ lg i) (fun i => floorA (S i) (2 ^ lg i) m α p) u]
  · congr 1
    exact tensorZR_restr d S (fun i => 2 ^ lg i) (fun i => floorAt (S i) (2 ^ lg i) m α p) u
  · intro i l hll hlp
    have hv := lineA_value l (S i) (2 ^ lg i) m α p w W hα hαp hm hm1 hmp hp hw hwW hW (hS i) hll
      (fun e he => (hlp e he).1) (fun e he => (hlp e he).2)
    refine ⟨TensorTape.lineA_length _ _ _ _ _ _ _ l, fun e he => ⟨TensorTape.lineA_width _ _ _ _ _ _ _ l e he, ?_⟩, hv⟩
    have hme : decE w p e ∈ lineOf (floorA (S i) (2 ^ lg i) m α p) (l.map (decE w p)) := by
      rw [← hv]; exact List.mem_map_of_mem he
    simp only [lineOf, List.mem_map, List.mem_range] at hme
    obtain ⟨k, -, hk⟩ := hme
    rw [← hk]
    refine (norm_le_pi_norm _ _).trans (floorA_ball _ _ m α p hα hαp hm hm1 hmp hp _ ?_)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    by_cases hj : j.val < l.length
    · rw [getD_map_lt _ _ _ hj _ [], List.getD_eq_getElem _ _ hj]
      exact (hlp _ (List.getElem_mem _)).2
    · rw [List.getD_eq_default _ _ (by simpa using hj)]; simp

end
end IntegerMultBounds.Resampling.TensorNumeric
