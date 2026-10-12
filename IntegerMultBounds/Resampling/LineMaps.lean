module

public import IntegerMultBounds.Resampling.AxisInst
public import IntegerMultBounds.Resampling.ScriptSem

/-! The axis records as line maps on entries. An entry is a complex
fixed-point number stored as two `w`-bit words, real part first, each most
significant bit first. The expansion record maps every line of `t` entries
by `lineA` (`expandOut_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.LineMaps

open Machine Schoenhage FlatTensor ScriptSem

/-- An entry's two words, least significant bit first. -/
def entryWords (w : ℕ) (e : List Bool) : List (List Bool) := [(e.take w).reverse, (e.drop w).reverse]

/-- Consecutive pairs of words, least significant bit first, as entries. -/
def pairUp : List (List Bool) → List (List Bool)
  | a :: b :: rest => (a.reverse ++ b.reverse) :: pairUp rest
  | _ => []

theorem flatten_pairUp : ∀ (n : ℕ) (fs : List (List Bool)), fs.length = 2 * n →
    (pairUp fs).flatten = (fs.map List.reverse).flatten
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: b :: rest, h => by
    simp only [pairUp, List.flatten_cons, List.map_cons, List.append_assoc]
    rw [flatten_pairUp n rest (by simp at h; omega)]
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem length_pairUp : ∀ (n : ℕ) (fs : List (List Bool)), fs.length = 2 * n → (pairUp fs).length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: b :: rest, h => by
    simp only [pairUp, List.length_cons]; rw [length_pairUp n rest (by simp at h; omega)]
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem length_pairUp_mem : ∀ (k : ℕ) (fs : List (List Bool)), (∀ f ∈ fs, f.length = k) →
    ∀ e ∈ pairUp fs, e.length = 2 * k
  | _, [], _ => by simp [pairUp]
  | _, [_], _ => by simp [pairUp]
  | k, a :: b :: rest, h => by
    intro e he
    simp only [pairUp, List.mem_cons] at he
    rcases he with rfl | he
    · simp [h a (by simp), h b (by simp)]; ring
    · exact length_pairUp_mem k rest (fun f hf => h f (by simp [hf])) e he

variable {α : Type*}

theorem blocks_flatten (n L : ℕ) (es : List α) (x : α) (hl : es.length = L * n) :
    (List.range L).flatMap (fun b => block n b es) = es := by
  have hb : ∀ b, b < L → (block n b es).length = n := fun b hb => length_block n b es L hl hb
  have hlen : ((List.range L).flatMap fun b => block n b es).length = L * n := by
    rw [List.length_flatMap, List.map_congr_left (g := fun _ => n) (fun c hc => hb c (List.mem_range.mp hc))]; simp
  apply ext_getD' x
  · rw [hlen, hl]
  · intro z hz
    rw [hlen] at hz
    obtain ⟨b, j, hb', hj, rfl⟩ := decomp2 hz
    rw [getD_flatMap_const _ L n hb b j hb' hj x, getD_block _ _ _ hj]

theorem block_flatMap (n L : ℕ) (f : ℕ → List α) (hf : ∀ c, c < L → (f c).length = n) (b : ℕ) (hb : b < L) (x : α) :
    block n b ((List.range L).flatMap f) = f b := by
  have hlen : ((List.range L).flatMap f).length = L * n := by
    rw [List.length_flatMap, List.map_congr_left (g := fun _ => n) (fun c hc => hf c (List.mem_range.mp hc))]; simp
  apply ext_getD' x
  · rw [length_block _ _ _ L hlen hb, hf b hb]
  · intro j hj
    rw [length_block _ _ _ L hlen hb] at hj
    rw [getD_block _ _ _ hj, getD_flatMap_const _ L n hf b j hb hj x]

theorem take_flatten_uniform (B : ℕ) : ∀ (es : List (List Bool)), (∀ e ∈ es, e.length = B) → ∀ k : ℕ,
    es.flatten.take (k * B) = (es.take k).flatten
  | [], _, k => by simp
  | e :: es, h, 0 => by simp
  | e :: es, h, k + 1 => by
    have he := h e (by simp)
    have ih := take_flatten_uniform B es (fun x hx => h x (by simp [hx])) k
    rw [List.flatten_cons, List.take_succ_cons, List.flatten_cons, Nat.succ_mul, add_comm, ← he]
    simp [List.take_append, he, ih]

/-! ### The expansion line map -/

open LineApply (outs line)
open GaussianLine (outWords)
open Resampling.NeumannWords (ext)

/-- One line of `t` entries through the expansion record: its first `s` entries as words, the `Ã`
window sums, floored, paired back into `t` entries. -/
def lineA (wt : List (List Bool)) (s t m p w W : ℕ) (line : List (List Bool)) : List (List Bool) :=
  pairUp ((outWords wt (ext s m ((line.take s).flatMap (entryWords w))) s t m p w W t).map (floorWord w))

theorem outs_flatMap (wt arr : List (List Bool)) (s t m p w W : ℕ) : ∀ L : ℕ,
    LineApply.outs wt arr s t m p w W L = (List.range L).flatMap fun ℓ => outWords wt (ext s m (line arr s ℓ)) s t m p w W t
  | 0 => rfl
  | L + 1 => by rw [LineApply.outs, outs_flatMap wt arr s t m p w W L, List.range_succ, List.flatMap_append]; simp

theorem flatMap_entryWords (w : ℕ) : ∀ es : List (List Bool), (∀ e ∈ es, e.length = 2 * w) →
    ((es.flatMap (entryWords w)).map List.reverse).flatten = es.flatten
  | [], _ => rfl
  | e :: es, h => by
    simp only [List.flatMap_cons, List.map_append, List.flatten_append, entryWords, List.map_cons, List.map_nil,
      List.reverse_reverse, List.flatten_cons, List.flatten_nil, List.append_nil, List.take_append_drop]
    rw [flatMap_entryWords w es (fun x hx => h x (by simp [hx]))]

theorem cut_entries (w : ℕ) (hw : 1 ≤ w) (es : List (List Bool)) (h : ∀ e ∈ es, e.length = 2 * w) :
    (cut w es.flatten).map List.reverse = es.flatMap (entryWords w) := by
  have hws : ∀ c ∈ (es.flatMap (entryWords w)).map List.reverse, c.length = w := by
    intro c hc
    simp only [List.mem_map, List.mem_flatMap, entryWords, List.mem_cons, List.mem_nil_iff, or_false] at hc
    obtain ⟨c', ⟨e, he, rfl | rfl⟩, rfl⟩ := hc <;> simp [h e he] <;> omega
  rw [← flatMap_entryWords w es h, cut_flatten_words hw _ hws, List.map_map]
  simp

theorem flatten_flatMap' {β γ : Type*} (f : β → List (List γ)) : ∀ l : List β,
    (l.flatMap f).flatten = (l.map fun x => (f x).flatten).flatten
  | [] => rfl
  | x :: l => by simp [List.flatMap_cons, List.flatten_append, flatten_flatMap' f l]

theorem flatMap_congr' {β γ : Type*} {f g : β → List γ} : ∀ l : List β, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons]; rw [h x (by simp), flatMap_congr' l (fun y hy => h y (by simp [hy]))]

theorem length_flatten_uniform (B : ℕ) (es : List (List Bool)) (h : ∀ e ∈ es, e.length = B) :
    es.flatten.length = es.length * B := by
  rw [List.length_flatten, List.map_congr_left (g := fun _ => B) h]; simp

theorem expandOut_eq (es wt : List (List Bool)) (s t m p w W L : ℕ) (hw : 1 ≤ w) (ht : 0 < t) (hst : s ≤ t)
    (hes : ∀ e ∈ es, e.length = 2 * w) (hl : es.length = L * t) :
    AxisStep.expandOut es.flatten wt s t m p w W L = (mapBlocks t (lineA wt s t m p w W) es).flatten := by
  have hblk : ∀ b, b < L → (block t b es).length = t := fun b hb => length_block t b es L hl hb
  have hblkw : ∀ b e, e ∈ block t b es → e.length = 2 * w := fun b e he =>
    hes e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  -- the lines as bits
  have h1 : cut (2 * t * w) es.flatten = (List.range L).map fun b => (block t b es).flatten := by
    have hA : es.flatten = ((List.range L).map fun b => (block t b es).flatten).flatten := by
      conv_lhs => rw [← blocks_flatten t L es [] hl]
      rw [flatten_flatMap']
    rw [hA, cut_flatten_words (by nlinarith)]
    intro c hc; simp only [List.mem_map, List.mem_range] at hc; obtain ⟨b, hb, rfl⟩ := hc
    rw [length_flatten_uniform (2 * w) _ (hblkw b), hblk b hb]; ring
  have h2 : ∀ b, b < L → Rules.fit (2 * s * w) (block t b es).flatten = ((block t b es).take s).flatten := fun b hb => by
    rw [fit_take _ _ (by rw [length_flatten_uniform (2 * w) _ (hblkw b), hblk b hb]; nlinarith),
      show 2 * s * w = s * (2 * w) by ring, take_flatten_uniform (2 * w) _ (hblkw b)]
  set fB : ℕ → List (List Bool) := fun b => ((block t b es).take s).flatMap (entryWords w)
  have hfB : ∀ b, b < L → (fB b).length = 2 * s := fun b hb => by
    simp only [fB, List.length_flatMap, entryWords, List.length_cons, List.length_nil]
    simp [hblk b hb, hst]; ring
  have harr : (cut w (((cut (2 * t * w) es.flatten).map (Rules.fit (2 * s * w))).flatten)).map List.reverse =
      (List.range L).flatMap fB := by
    rw [h1, List.map_map]
    rw [List.map_congr_left (g := fun b => ((block t b es).take s).flatten) (fun b hb => by
      simp only [Function.comp_apply]; exact h2 b (List.mem_range.mp hb))]
    rw [show ((List.range L).map fun b => ((block t b es).take s).flatten).flatten =
        ((List.range L).flatMap fun b => (block t b es).take s).flatten by
      rw [flatten_flatMap']]
    rw [cut_entries w hw _ (fun e he => by
      simp only [List.mem_flatMap, List.mem_range] at he; obtain ⟨b, -, he⟩ := he
      exact hblkw b e (List.mem_of_mem_take he))]
    simp [fB, List.flatMap_assoc]
  have hline : ∀ ℓ, ℓ < L → line ((List.range L).flatMap fB) s ℓ = fB ℓ := fun ℓ hℓ => by
    rw [show line ((List.range L).flatMap fB) s ℓ = block (2 * s) ℓ ((List.range L).flatMap fB) by
      simp only [line, block]; rw [mul_comm ℓ]]
    exact block_flatMap (2 * s) L fB hfB ℓ hℓ []
  have hOW : ∀ ℓ, (outWords wt (ext s m (fB ℓ)) s t m p w W t).length = 2 * t := fun ℓ =>
    Resampling.NeumannWords.outWords_length _ _ _ _ _ _ _ _ _
  unfold AxisStep.expandOut
  rw [harr, outs_flatMap]
  have e1 : ((List.range L).flatMap fun ℓ => outWords wt (ext s m (line ((List.range L).flatMap fB) s ℓ)) s t m p w W t) =
      (List.range L).flatMap fun ℓ => outWords wt (ext s m (fB ℓ)) s t m p w W t := by
    exact flatMap_congr' _ fun ℓ hℓ => by rw [hline ℓ (List.mem_range.mp hℓ)]
  rw [e1, msbArray, List.map_flatMap, List.map_flatMap, flatten_flatMap']
  rw [mapBlocks, hl, Nat.mul_div_cancel _ ht, flatten_flatMap']
  congr 1
  apply List.map_congr_left
  intro ℓ _
  simp only [lineA]
  rw [flatten_pairUp t _ (by rw [List.length_map]; exact hOW ℓ)]

/-! ### The compression line map -/

open B0Words (vsel oneStep)
open Resampling.NeumannWords (iter nextWords)

/-- `B̃₀` on the words of one line of `t` entries: `s` complex outputs as `2 s` words. -/
noncomputable def b0Word (wtE wtH wtD zeros : List (List Bool)) (s t m p w W : ℕ) (ws : List (List Bool)) : List (List Bool) :=
  oneStep wtD zeros s p w (iter wtE (oneStep wtH zeros s p w (vsel ws s t)) s m p w W p)

/-- One line of `t` entries through the compression record: `B̃₀`, paired into `s` entries, then
`t - s` zero entries. -/
noncomputable def lineB (wtE wtH wtD zeros : List (List Bool)) (s t m p w W : ℕ) (line : List (List Bool)) : List (List Bool) :=
  pairUp (b0Word wtE wtH wtD zeros s t m p w W (line.flatMap (entryWords w))) ++
    List.replicate (t - s) (List.replicate (2 * w) false)

theorem flatten_replicate' (k n : ℕ) (b : Bool) :
    (List.replicate k (List.replicate n b)).flatten = List.replicate (k * n) b := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_append_replicate, Nat.succ_mul, add_comm]

theorem b0Outs_flatMap (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W : ℕ) : ∀ L : ℕ,
    B0Line.b0Outs arr wtE wtH wtD zeros s t m p w W L =
      (List.range L).flatMap fun ℓ => B0Line.b0Out arr wtE wtH wtD zeros s t m p w W ℓ
  | 0 => rfl
  | L + 1 => by
    rw [B0Line.b0Outs, b0Outs_flatMap arr wtE wtH wtD zeros s t m p w W L, List.range_succ, List.flatMap_append]
    simp

theorem compressOut_eq (es wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) (hw : 1 ≤ w) (ht : 0 < t)
    (hs : 0 < s) (hst : s ≤ t) (hz : zeros.length = 2 * s) (hzw : ∀ x ∈ zeros, x.length = w)
    (hes : ∀ e ∈ es, e.length = 2 * w) (hl : es.length = L * t) :
    AxisStep.compressOut es.flatten wtE wtH wtD zeros s t m p w W L =
      (mapBlocks t (lineB wtE wtH wtD zeros s t m p w W) es).flatten := by
  have hblk : ∀ b, b < L → (block t b es).length = t := fun b hb => length_block t b es L hl hb
  have hblkw : ∀ b e, e ∈ block t b es → e.length = 2 * w := fun b e he =>
    hes e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  set fW : ℕ → List (List Bool) := fun b => (block t b es).flatMap (entryWords w)
  have hfW : ∀ b, b < L → (fW b).length = 2 * t := fun b hb => by
    simp only [fW, List.length_flatMap, entryWords, List.length_cons, List.length_nil]
    simp [hblk b hb]; ring
  have harr : AxisStep.compressArr es.flatten w = (List.range L).flatMap fW := by
    rw [AxisStep.compressArr, cut_entries w hw es hes]
    conv_lhs => rw [← blocks_flatten t L es [] hl]
    simp [fW, List.flatMap_assoc]
  have hline : ∀ ℓ, ℓ < L → line ((List.range L).flatMap fW) t ℓ = fW ℓ := fun ℓ hℓ => by
    rw [show line ((List.range L).flatMap fW) t ℓ = block (2 * t) ℓ ((List.range L).flatMap fW) by
      simp only [line, block]; rw [mul_comm ℓ]]
    exact block_flatMap (2 * t) L fW hfW ℓ hℓ []
  set gB : ℕ → List (List Bool) := fun ℓ => b0Word wtE wtH wtD zeros s t m p w W (fW ℓ)
  have hgl : ∀ ℓ, (gB ℓ).length = 2 * s := fun ℓ => by
    simp only [gB, b0Word, B0Words.oneStep, Resampling.NeumannWords.nextWords_length, hz]
  have hgw : ∀ ℓ, ∀ x ∈ gB ℓ, x.length = w := fun ℓ => by
    simp only [gB, b0Word, B0Words.oneStep]; exact NeumannStep.nextWords_shape zeros _ w hzw
  have hb0 : B0Line.b0Outs ((List.range L).flatMap fW) wtE wtH wtD zeros s t m p w W L =
      (List.range L).flatMap gB := by
    rw [b0Outs_flatMap]
    exact flatMap_congr' _ fun ℓ hℓ => by
      simp only [B0Line.b0Out, gB, b0Word]; rw [hline ℓ (List.mem_range.mp hℓ)]
  have hpw : ∀ ℓ, ((pairUp (gB ℓ)).flatten).length = 2 * s * w := fun ℓ => by
    rw [length_flatten_uniform (2 * w) _ (length_pairUp_mem w _ (hgw ℓ)), length_pairUp s _ (hgl ℓ)]; ring
  have hmsb : msbArray ((List.range L).flatMap gB) = ((List.range L).map fun ℓ => (pairUp (gB ℓ)).flatten).flatten := by
    rw [msbArray, List.map_flatMap, flatten_flatMap']
    congr 1
    exact List.map_congr_left fun ℓ _ => (flatten_pairUp s _ (hgl ℓ)).symm
  have hsw : 1 ≤ 2 * s * w := by nlinarith
  unfold AxisStep.compressOut
  rw [harr, hb0, hmsb, cut_flatten_words hsw _ (fun c hc => by
    simp only [List.mem_map, List.mem_range] at hc; obtain ⟨ℓ, -, rfl⟩ := hc; exact hpw ℓ)]
  rw [mapBlocks, hl, Nat.mul_div_cancel _ ht, flatten_flatMap', List.map_map]
  congr 1
  apply List.map_congr_left
  intro ℓ _
  simp only [Function.comp_apply, lineB, List.flatten_append, flatten_replicate']
  rw [fit_pad _ _ (by rw [hpw ℓ]; nlinarith), hpw ℓ]
  congr 2
  rw [show 2 * t * w = 2 * s * w + (t - s) * (2 * w) by
    rw [show t = s + (t - s) by omega]; simp only [Nat.add_sub_cancel_left]; ring]
  omega

end IntegerMultBounds.Resampling.LineMaps
