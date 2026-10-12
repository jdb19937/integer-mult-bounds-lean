module

public import IntegerMultBounds.Resampling.ScriptSem
public import IntegerMultBounds.Resampling.AxisDriver

/-! Scripts for the tensor driver. A swap record with headers built from the
values `P, 1, B, h, d` interchanges two adjacent address fields of sizes
`2^h` and `2^d` (`swapRec_spec`); records concatenate (`result_append`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.Script
noncomputable section

open Machine Schoenhage AxisDriver ScriptSem FlatTensor

variable {E : ℕ}

/-- The canonical binary word of `n`. -/
def bin (n : ℕ) : List Bool := GrowingCounterData.advance n []

theorem value_bin (n : ℕ) : Counter.value (bin n) = n := by
  simp [bin, GrowingCounterData.advance_value, Counter.value]

theorem canonical_bin (n : ℕ) : GrowingCounterData.Canonical (bin n) :=
  GrowingCounterData.advance_canonical n [] (Or.inl rfl)

/-- The headers of one interchange: prefix `P`, gap `1`, block `B`, field widths `h` and `d`. -/
def swapHdrs (P h d B : ℕ) : List (List Bool) := [bin P, bin 1, bin B, bin h, bin d]

theorem swapRec_spec (P h d B : ℕ) (A : List Bool) (hP : 0 < P) (hB : 0 < B) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hl : A.length = P * 2 ^ h * 2 ^ d * B) :
    SwapPrim.Pre (swIn (swapHdrs P h d B) A) ∧
      swapF (swapHdrs P h d B) A = SwapPrim.swapList P (2 ^ h) 1 (2 ^ d) B A := by
  have hw : ∀ i : Fin 6, SwapPrim.words (swIn (swapHdrs P h d B) A) i =
      if i.val < 5 then (swapHdrs P h d B).getD i.val [] else A := by
    intro i
    simp only [SwapPrim.words, swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  have hv : ∀ i : Fin 5, SwapPrim.vals (swIn (swapHdrs P h d B) A) i = ![P, 1, B, h, d] i := by
    intro i
    simp only [SwapPrim.vals, SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrs, value_bin]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [swIn]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · intro i
    rw [hw i]; simp only [swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  · intro i
    simp only [SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrs, canonical_bin]
  · rw [hv 0]; simpa using hP
  · rw [hv 1]; simp
  · rw [hv 2]; simpa using hB
  · rw [hv 3, hv 4]; simpa using hhd
  · rw [hv 3, hv 4]; simpa using hdh
  · rw [hw 5, hv 0, hv 1, hv 2, hv 3, hv 4]
    simp [BinaryAdjacentWidthInterchange.volume, hl]
  · simp only [swapF, SwapPrim.swapped, hv, hw]
    simp

/-- The headers of one interchange: prefix `P`, gap `G`, block `B`, field widths `h` and `d`. -/
def swapHdrsG (P G h d B : ℕ) : List (List Bool) := [bin P, bin G, bin B, bin h, bin d]

theorem swapRecG_spec (P G h d B : ℕ) (A : List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hl : A.length = P * 2 ^ h * G * 2 ^ d * B) :
    SwapPrim.Pre (swIn (swapHdrsG P G h d B) A) ∧
      swapF (swapHdrsG P G h d B) A = SwapPrim.swapList P (2 ^ h) G (2 ^ d) B A := by
  have hw : ∀ i : Fin 6, SwapPrim.words (swIn (swapHdrsG P G h d B) A) i =
      if i.val < 5 then (swapHdrsG P G h d B).getD i.val [] else A := by
    intro i
    simp only [SwapPrim.words, swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  have hv : ∀ i : Fin 5, SwapPrim.vals (swIn (swapHdrsG P G h d B) A) i = ![P, G, B, h, d] i := by
    intro i
    simp only [SwapPrim.vals, SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrsG, value_bin]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [swIn]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · intro i
    rw [hw i]; simp only [swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  · intro i
    simp only [SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrsG, canonical_bin]
  · rw [hv 0]; simpa using hP
  · rw [hv 1]; simpa using hG
  · rw [hv 2]; simpa using hB
  · rw [hv 3, hv 4]; simpa using hhd
  · rw [hv 3, hv 4]; simpa using hdh
  · rw [hw 5, hv 0, hv 1, hv 2, hv 3, hv 4]
    simp [BinaryAdjacentWidthInterchange.volume, hl]
  · simp only [swapF, SwapPrim.swapped, hv, hw]
    simp

theorem result_append (S : AxisSpec E) : ∀ (r₁ r₂ : List Rec) (A : List Bool),
    result S (r₁ ++ r₂) A = result S r₂ (result S r₁ A)
  | [], _, _ => rfl
  | .axis _ :: r₁, r₂, _ => result_append S r₁ r₂ _
  | .swap _ :: r₁, r₂, _ => result_append S r₁ r₂ _

theorem valid_append (S : AxisSpec E) : ∀ (r₁ r₂ : List Rec) (A : List Bool),
    Valid S r₁ A → Valid S r₂ (result S r₁ A) → Valid S (r₁ ++ r₂) A
  | [], _, _, _, h => h
  | .axis _ :: r₁, r₂, _, ⟨h1, h2, h3⟩, h => ⟨h1, h2, valid_append S r₁ r₂ _ h3 h⟩
  | .swap _ :: r₁, r₂, _, ⟨h1, h2, h3⟩, h => ⟨h1, h2, valid_append S r₁ r₂ _ h3 h⟩

theorem driveCost_append (S : AxisSpec E) : ∀ (r₁ r₂ : List Rec) (A : List Bool),
    driveCost S (r₁ ++ r₂) A = driveCost S r₁ A + driveCost S r₂ (result S r₁ A)
  | [], _, _ => by simp [driveCost, result]
  | .axis _ :: r₁, r₂, A => by simp only [List.cons_append, driveCost, result, driveCost_append S r₁ r₂]; ring
  | .swap _ :: r₁, r₂, A => by simp only [List.cons_append, driveCost, result, driveCost_append S r₁ r₂]; ring

/-- Move the field of width `2^h` inward past fields of widths `2^lᵢ` (outer to inner). -/
def insRecs (h : ℕ) : ℕ → List ℕ → ℕ → List Rec
  | _, [], _ => []
  | Q, l :: ls, B => .swap (swapHdrs Q h l (B * (ls.map (2 ^ ·)).prod)) :: insRecs h (Q * 2 ^ l) ls B

/-- Move the innermost field of width `2^h` outward past fields of widths `2^lᵢ` (inner to outer). -/
def outRecs (h : ℕ) : ℕ → List ℕ → ℕ → List Rec
  | _, [], _ => []
  | Q, l :: ls, B => .swap (swapHdrs (Q * (ls.map (2 ^ ·)).prod) l h B) :: outRecs h Q ls (2 ^ l * B)

theorem insRecs_spec (S : AxisSpec E) (h : ℕ) : ∀ (Q : ℕ) (ls : List ℕ) (B : ℕ) (A : List Bool),
    0 < Q → 0 < B → (∀ l ∈ ls, l ≤ h + 1 ∧ h ≤ l + 1) →
    A.length = Q * 2 ^ h * (ls.map (2 ^ ·)).prod * B →
    Valid S (insRecs h Q ls B) A ∧ result S (insRecs h Q ls B) A = rotIn (2 ^ h) Q (ls.map (2 ^ ·)) B A
  | Q, [], B, A, _, _, _, _ => ⟨trivial, rfl⟩
  | Q, l :: ls, B, A, hQ, hB, hls, hl => by
    have hR : 0 < (ls.map (2 ^ ·)).prod := List.prod_pos (by simp)
    obtain ⟨hpre, hf⟩ := swapRec_spec Q h l (B * (ls.map (2 ^ ·)).prod) A hQ (by positivity)
      (hls l (by simp)).2 (hls l (by simp)).1 (by rw [hl]; simp only [List.map_cons, List.prod_cons]; ring)
    have hlen : (SwapPrim.swapList Q (2 ^ h) 1 (2 ^ l) (B * (ls.map (2 ^ ·)).prod) A).length =
        Q * 2 ^ l * 2 ^ h * (ls.map (2 ^ ·)).prod * B := by rw [length_swapList']; ring
    obtain ⟨hv, hr⟩ := insRecs_spec S h (Q * 2 ^ l) ls B _ (by positivity) hB
      (fun l' hl' => hls l' (by simp [hl'])) (hlen.trans (by ring))
    refine ⟨⟨by simp [swapHdrs], hpre, by rw [hf]; exact hv⟩, ?_⟩
    simp only [insRecs, result, hf, hr, rotIn, List.map_cons]

theorem outRecs_spec (S : AxisSpec E) (h : ℕ) : ∀ (Q : ℕ) (ls : List ℕ) (B : ℕ) (A : List Bool),
    0 < Q → 0 < B → (∀ l ∈ ls, l ≤ h + 1 ∧ h ≤ l + 1) →
    A.length = Q * (ls.map (2 ^ ·)).prod * 2 ^ h * B →
    Valid S (outRecs h Q ls B) A ∧ result S (outRecs h Q ls B) A = rotOut (2 ^ h) Q (ls.map (2 ^ ·)) B A
  | Q, [], B, A, _, _, _, _ => ⟨trivial, rfl⟩
  | Q, l :: ls, B, A, hQ, hB, hls, hl => by
    have hR : 0 < (ls.map (2 ^ ·)).prod := List.prod_pos (by simp)
    obtain ⟨hpre, hf⟩ := swapRec_spec (Q * (ls.map (2 ^ ·)).prod) l h B A (by positivity) hB
      (hls l (by simp)).1 (hls l (by simp)).2 (by rw [hl]; simp only [List.map_cons, List.prod_cons]; ring)
    have hlen : (SwapPrim.swapList (Q * (ls.map (2 ^ ·)).prod) (2 ^ l) 1 (2 ^ h) B A).length =
        Q * (ls.map (2 ^ ·)).prod * 2 ^ h * (2 ^ l * B) := by rw [length_swapList']; ring
    obtain ⟨hv, hr⟩ := outRecs_spec S h Q ls (2 ^ l * B) _ hQ (by positivity)
      (fun l' hl' => hls l' (by simp [hl'])) hlen
    refine ⟨⟨by simp [swapHdrs], hpre, by rw [hf]; exact hv⟩, ?_⟩
    simp only [outRecs, result, hf, hr, rotOut, List.map_cons]

/-! ### The whole script -/

/-- The tensor script for field widths `2^lgᵢ` inside an outer prefix `Q`, entries of `B` bits: the
tail axes, then axis `0` moved inward, its record, and moved back out. -/
def tScript (B : ℕ) : (d : ℕ) → (Fin d → ℕ) → ℕ → (Fin d → List (List Bool)) → List Rec
  | 0, _, _, _ => []
  | d + 1, lg, Q, aw => tScript B d (fun i => lg i.succ) (Q * 2 ^ lg 0) (fun i => aw i.succ) ++
      insRecs (lg 0) Q (List.ofFn fun i => lg i.succ) B ++ [Rec.axis (aw 0)] ++
      outRecs (lg 0) Q (List.ofFn fun i => lg i.succ).reverse B

theorem prod_map_ofFn {d : ℕ} (lg : Fin d → ℕ) : ((List.ofFn lg).map (2 ^ ·)).prod = ∏ i, 2 ^ lg i := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

theorem tScript_spec (S : AxisSpec E) (B NT : ℕ) (hB : 0 < B) : ∀ (d : ℕ) (lg : Fin d → ℕ) (Q : ℕ)
    (aw : Fin d → List (List Bool)) (G : Fin d → List (List Bool) → List (List Bool)) (es : List (List Bool)),
    (∀ i j, lg i ≤ lg j + 1) →
    (∀ i (l : List (List Bool)), l.length = 2 ^ lg i → (G i l).length = 2 ^ lg i) →
    (∀ i (l : List (List Bool)), l.length = 2 ^ lg i → (∀ e ∈ l, e.length = B) → ∀ e ∈ G i l, e.length = B) →
    (∀ i (xs : List (List Bool)), xs.length = NT → (∀ e ∈ xs, e.length = B) →
      (aw i).length = S.regs.length ∧ S.Good (aw i) xs.flatten ∧
      S.f (aw i) xs.flatten = (mapBlocks (2 ^ lg i) (G i) xs).flatten) →
    0 < Q → Q * ∏ i, 2 ^ lg i = NT → es.length = NT → (∀ e ∈ es, e.length = B) →
    Valid S (tScript B d lg Q aw) es.flatten ∧
      result S (tScript B d lg Q aw) es.flatten =
        (mapBlocks (∏ i, 2 ^ lg i) (flatPass d (fun i => 2 ^ lg i) G []) es).flatten
  | 0, lg, Q, aw, G, es, _, _, _, _, hQ, hNT, hl, hw => by
    refine ⟨trivial, ?_⟩
    simp only [tScript, result, Finset.univ_eq_empty, Finset.prod_empty]
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
    have hG : ∀ i (l : List (List Bool)), l.length = 2 ^ lg i → (∀ e ∈ l, e.length = B) →
        (G i l).length = 2 ^ lg i ∧ ∀ e ∈ G i l, e.length = B := fun i l h1 h2 => ⟨hGl i l h1, hGw i l h1 h2⟩
    set T0 := 2 ^ lg 0
    set R := ∏ i : Fin d, 2 ^ lg i.succ
    have hR : 0 < R := prod_pos_pow _
    have hT0 : 0 < T0 := by positivity
    have hprod : ∏ i : Fin (d + 1), 2 ^ lg i = T0 * R := Fin.prod_univ_succ _
    have hl' : es.length = Q * (T0 * R) := by rw [hl, ← hNT, hprod]
    have hpad : ∀ l ∈ List.ofFn (fun i : Fin d => lg i.succ), l ≤ lg 0 + 1 ∧ lg 0 ≤ l + 1 := by
      intro l hl; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl; exact ⟨hlg _ _, hlg _ _⟩
    have hmapR : ((List.ofFn fun i : Fin d => lg i.succ).map (2 ^ ·)).prod = R := prod_map_ofFn _
    have hmapR' : ((List.ofFn fun i : Fin d => lg i.succ).reverse.map (2 ^ ·)).prod = R := by
      rw [List.map_reverse, List.prod_reverse, hmapR]
    -- 1. the tail axes
    obtain ⟨v1, r1⟩ := tScript_spec S B NT hB d (fun i => lg i.succ) (Q * T0) (fun i => aw i.succ)
      (fun i => G i.succ) es (fun i j => hlg _ _) (fun i l => hGl i.succ l) (fun i l => hGw i.succ l)
      (fun i xs => hax i.succ xs)
      (by positivity) (by rw [← hNT, hprod]; ring) hl hw
    set es1 := mapBlocks R (flatPass d (fun i => 2 ^ lg i.succ) (fun i => G i.succ) []) es
    have hfp := fun b (hb : b < Q * T0) => flatPass_props (fun e : List Bool => e.length = B) d
      (fun i => lg i.succ) (fun i => G i.succ) [] (block R b es) (fun i l => hG i.succ l)
      (length_block _ _ _ (Q * T0) (by rw [hl']; ring) hb)
      (fun e he => hw e (List.mem_of_mem_drop (List.mem_of_mem_take he)))
    have hdivR : es.length / R = Q * T0 := by rw [hl', show Q * (T0 * R) = Q * T0 * R by ring, Nat.mul_div_cancel _ hR]
    have hes1 : es1.length = Q * (T0 * R) := by
      rw [length_mapBlocks R R _ es (fun b hb => (hfp b (hdivR ▸ hb)).1), hdivR]; ring
    have hes1w : ∀ e ∈ es1, e.length = B := by
      intro e he; simp only [es1, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he; exact (hfp b (hdivR ▸ hb)).2 e he
    have hflat1 : es1.flatten.length = Q * T0 * R * B := by
      rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hes1w]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, hes1]; ring
    -- 2. axis 0 moved inward
    obtain ⟨v2, r2⟩ := insRecs_spec S (lg 0) Q (List.ofFn fun i => lg i.succ) B es1.flatten hQ hB hpad
      (by rw [hflat1, hmapR])
    set es2 := mapBlocks (T0 * R) (trL T0 R []) es1
    have r2' : result S (insRecs (lg 0) Q (List.ofFn fun i => lg i.succ) B) es1.flatten = es2.flatten := by
      rw [r2, rotIn_flatten T0 Q _ B es1 hes1w (by rw [hes1, hmapR]) hT0 (by rw [hmapR]; exact hR), hmapR]
    have hdivTR : es1.length / (T0 * R) = Q := by rw [hes1, Nat.mul_div_cancel _ (by positivity)]
    have hes2 : es2.length = Q * (T0 * R) := by
      rw [length_mapBlocks (T0 * R) (R * T0) _ es1 (fun _ _ => length_trL _ _ _ _), hdivTR]; ring
    have hes2w : ∀ e ∈ es2, e.length = B := by
      intro e he; simp only [es2, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he
      rw [hdivTR] at hb
      have := mem_trL T0 R [] _ (length_block _ _ _ Q hes1 hb) he
      exact hes1w e (List.mem_of_mem_drop (List.mem_of_mem_take this))
    -- 3. the record of axis 0
    obtain ⟨ha1, ha2, ha3⟩ := hax 0 es2 (by rw [hes2, ← hl', hl]) hes2w
    set es3 := mapBlocks T0 (G 0) es2
    have hdivT : es2.length / T0 = Q * R := by
      rw [hes2, show Q * (T0 * R) = Q * R * T0 by ring, Nat.mul_div_cancel _ hT0]
    have hes3 : es3.length = Q * (R * T0) := by
      rw [length_mapBlocks T0 T0 _ es2 (fun b hb => hGl 0 _ (length_block _ _ _ (Q * R)
        (by rw [hes2]; ring) (hdivT ▸ hb))), hdivT]; ring
    have hes3w : ∀ e ∈ es3, e.length = B := by
      intro e he; simp only [es3, mapBlocks, List.mem_flatMap, List.mem_range] at he
      obtain ⟨b, hb, he⟩ := he
      rw [hdivT] at hb
      exact hGw 0 _ (length_block _ _ _ (Q * R) (by rw [hes2]; ring) hb)
        (fun e' he' => hes2w e' (List.mem_of_mem_drop (List.mem_of_mem_take he'))) e he
    have hflat3 : es3.flatten.length = Q * R * T0 * B := by
      rw [List.length_flatten, List.map_congr_left (g := fun _ => B) hes3w]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, hes3]; ring
    -- 4. axis 0 moved back out
    obtain ⟨v4, r4⟩ := outRecs_spec S (lg 0) Q (List.ofFn fun i => lg i.succ).reverse B es3.flatten hQ hB
      (fun l hl => hpad l (List.mem_reverse.mp hl)) (by rw [hflat3, hmapR'])
    have r4' : result S (outRecs (lg 0) Q (List.ofFn fun i => lg i.succ).reverse B) es3.flatten =
        (mapBlocks (R * T0) (trL R T0 []) es3).flatten := by
      rw [r4, rotOut_flatten T0 Q _ B es3 hes3w (by rw [hes3, hmapR']) hT0 (by rw [hmapR']; exact hR), hmapR']
    -- assemble
    have hscr : tScript B (d + 1) lg Q aw = tScript B d (fun i => lg i.succ) (Q * T0) (fun i => aw i.succ) ++
        (insRecs (lg 0) Q (List.ofFn fun i => lg i.succ) B ++ ([Rec.axis (aw 0)] ++
          outRecs (lg 0) Q (List.ofFn fun i => lg i.succ).reverse B)) := by
      simp only [tScript, List.append_assoc]; rfl
    rw [hscr]
    refine ⟨valid_append S _ _ _ v1 (by rw [r1]; exact valid_append S _ _ _ v2 (by
      rw [r2']; exact valid_append S _ _ _ ⟨ha1, ha2, trivial⟩ (by
        simp only [result]; rw [ha3]; exact v4))), ?_⟩
    rw [result_append, r1, result_append, r2', result_append]
    simp only [result]
    rw [ha3, r4', hprod]
    congr 1
    set φ := flatPass d (fun i => 2 ^ lg i.succ) (fun i => G i.succ) ([] : List Bool)
    have hφ : ∀ l : List (List Bool), l.length = R → (φ l).length = R := fun l hl =>
      (flatPass_props (fun _ => True) d (fun i => lg i.succ) (fun i => G i.succ) [] l
        (fun i l' hl' _ => ⟨hGl i.succ l' hl', fun _ _ => trivial⟩) hl (fun _ _ => trivial)).1
    have hN : 0 < T0 * R := by positivity
    have f1 : ∀ l : List (List Bool), l.length = T0 * R → (mapBlocks R φ l).length = T0 * R := fun l hl => by
      rw [length_mapBlocks R R φ l (fun b hb => hφ _ (length_block _ _ _ T0 hl (by
        rw [hl, Nat.mul_div_cancel _ hR] at hb; exact hb))), hl, Nat.mul_div_cancel _ hR]
    have f2 : ∀ l : List (List Bool), l.length = T0 * R → (trL T0 R [] l).length = T0 * R := fun l _ => by
      rw [length_trL, mul_comm]
    have f3 : ∀ l : List (List Bool), l.length = T0 * R → (mapBlocks T0 (G 0) l).length = T0 * R := fun l hl => by
      have hl' : l.length = R * T0 := by rw [hl, mul_comm]
      rw [length_mapBlocks T0 T0 (G 0) l (fun b hb => hGl 0 _ (length_block _ _ _ R hl' (by
        rw [hl', Nat.mul_div_cancel _ hT0] at hb; exact hb))), hl', Nat.mul_div_cancel _ hT0, mul_comm]
    have f4 : ∀ l : List (List Bool), l.length = T0 * R → (trL R T0 [] l).length = T0 * R := fun l _ => by
      rw [length_trL]
    have e1 : es1 = mapBlocks (T0 * R) (mapBlocks R φ) es :=
      mapBlocks_nest R T0 Q φ es [] hR hT0 hl' (fun l hl => hφ l hl)
    have e3 : es3 = mapBlocks (T0 * R) (mapBlocks T0 (G 0)) es2 := by
      rw [show T0 * R = R * T0 by ring]
      exact mapBlocks_nest T0 R Q (G 0) es2 [] hT0 hR (by rw [hes2]; ring) (fun l hl => hGl 0 l hl)
    have hes1' : (mapBlocks (T0 * R) (mapBlocks R φ) es).length = Q * (T0 * R) := by rw [← e1, hes1]
    have hes2' : (mapBlocks (T0 * R) (trL T0 R []) (mapBlocks (T0 * R) (mapBlocks R φ) es)).length = Q * (T0 * R) := by
      rw [← e1]; exact hes2
    rw [show R * T0 = T0 * R by ring, e3]
    simp only [es2]
    rw [e1, mapBlocks_comp (T0 * R) Q _ _ _ [] hN hl' f1 f2,
      mapBlocks_comp (T0 * R) Q (mapBlocks T0 (G 0)) (trL T0 R [] ∘ mapBlocks R φ) _ [] hN hl'
        (fun l hl => f2 _ (f1 l hl)) f3,
      mapBlocks_comp (T0 * R) Q (trL R T0 []) (mapBlocks T0 (G 0) ∘ (trL T0 R [] ∘ mapBlocks R φ)) _ [] hN hl'
        (fun l hl => f3 _ (f2 _ (f1 l hl))) f4]
    rfl

end
end IntegerMultBounds.Resampling.Script
