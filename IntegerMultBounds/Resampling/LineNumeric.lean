module

public import IntegerMultBounds.Resampling.TensorTape
public import IntegerMultBounds.Resampling.FloorStep
public import IntegerMultBounds.Resampling.PaddedTensor

/-! What the line maps compute. An entry decodes to the complex number with
real and imaginary parts its two words' signed values over `2^p` (`decE`).
On lines of entries in the unit disk, the expansion line map with the
machine-built table is the floored tabled `Ã` read on the first `s` entries
(`lineA_value`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.LineNumeric
noncomputable section

open Machine Schoenhage FlatTensor LineMaps PaddedTensor FloorStep
open TwosComplement (signed)
open IntegerMultBounds.NLogN

/-- The complex number of an entry. -/
def decE (w p : ℕ) (e : List Bool) : ℂ :=
  ⟨(signed (e.take w).reverse : ℝ) / 2 ^ p, (signed (e.drop w).reverse : ℝ) / 2 ^ p⟩

theorem decE_nil (w p : ℕ) : decE w p [] = 0 := by
  simp [decE, TwosComplement.signed_nil]; rfl

theorem getD_pairUp : ∀ (n : ℕ) (fs : List (List Bool)), fs.length = 2 * n → ∀ k, k < n →
    (pairUp fs).getD k [] = (fs.getD (2 * k) []).reverse ++ (fs.getD (2 * k + 1) []).reverse
  | 0, _, _, k, hk => by omega
  | n + 1, a :: b :: rest, h, 0, _ => by simp [pairUp]
  | n + 1, a :: b :: rest, h, k + 1, hk => by
    simp only [pairUp, List.getD_cons_succ]
    rw [getD_pairUp n rest (by simp at h; omega) k (by omega)]
    simp [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  | n + 1, [], h, _, _ => by simp at h
  | n + 1, [_], h, _, _ => by simp at h; omega

theorem decE_pair (w p : ℕ) (a b : List Bool) (ha : a.length = w) :
    decE w p (a.reverse ++ b.reverse) = ⟨(signed a : ℝ) / 2 ^ p, (signed b : ℝ) / 2 ^ p⟩ := by
  have : (a.reverse ++ b.reverse).take w = a.reverse := by
    rw [List.take_append_of_le_length (by simp [ha])]; simp [ha]
  have h2 : (a.reverse ++ b.reverse).drop w = b.reverse := by
    rw [List.drop_append_of_le_length (by simp [ha])]; simp [ha]
  simp [decE, this, h2]

theorem getD_flatMap_entryWords (w : ℕ) : ∀ (l : List (List Bool)) (j : ℕ), j < l.length →
    (l.flatMap (entryWords w)).getD (2 * j) [] = ((l.getD j []).take w).reverse ∧
    (l.flatMap (entryWords w)).getD (2 * j + 1) [] = ((l.getD j []).drop w).reverse
  | [], j, h => by simp at h
  | e :: l, 0, _ => by simp [entryWords]
  | e :: l, j + 1, h => by
    have ih := getD_flatMap_entryWords w l j (by simp at h; omega)
    constructor
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring]; simpa [entryWords] using ih.1
    · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring]; simpa [entryWords] using ih.2

theorem floor_half_div (n : ℤ) (p : ℕ) : (⌊(2 : ℝ) ^ p * ((n : ℝ) / 2 ^ (p + 1))⌋ : ℝ) / 2 ^ p = ((n / 2 : ℤ) : ℝ) / 2 ^ p := by
  congr 1
  have : (2 : ℝ) ^ p * ((n : ℝ) / 2 ^ (p + 1)) = (n : ℝ) / ((2 : ℕ) : ℝ) := by
    rw [pow_succ]; field_simp; norm_num
  rw [this]
  congr 1
  rw [Int.floor_eq_iff]
  have h1 : n % 2 + 2 * (n / 2) = n := Int.emod_add_mul_ediv n 2
  have h2 := Int.emod_nonneg n (by norm_num : (2 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 2)
  have e : (n : ℝ) = ((n % 2 : ℤ) : ℝ) + 2 * ((n / 2 : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h1; push_cast at this; linarith
  have h2' : (0 : ℝ) ≤ ((n % 2 : ℤ) : ℝ) := by exact_mod_cast h2
  have h3' : ((n % 2 : ℤ) : ℝ) < 2 := by exact_mod_cast h3
  push_cast
  constructor <;> rw [e] <;> linarith

theorem floorC_half (p : ℕ) (a b : ℤ) :
    floorC p ⟨(a : ℝ) / 2 ^ (p + 1), (b : ℝ) / 2 ^ (p + 1)⟩ = ⟨((a / 2 : ℤ) : ℝ) / 2 ^ p, ((b / 2 : ℤ) : ℝ) / 2 ^ p⟩ := by
  simp only [floorC, floor_half_div]

/-- The floored tabled `Ã` of a line of length `t`, reading its first `s` entries. -/
def floorA (s t m α p : ℕ) (v : ZMod t → ℂ) : ZMod t → ℂ :=
  floorV p (resampANum s t m (WindowSum.termW p fun k j => (WeightTable.tableA s t α p k j : ℝ) / 2 ^ p) (restr s t v))

theorem abs_signed_le_of_decE (w p : ℕ) (e : List Bool) (h : ‖decE w p e‖ ≤ 1) :
    |signed (e.take w).reverse| ≤ 2 ^ p ∧ |signed (e.drop w).reverse| ≤ 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 : |(decE w p e).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h
  have h2 : |(decE w p e).im| ≤ 1 := (Complex.abs_im_le_norm _).trans h
  simp only [decE] at h1 h2
  rw [abs_div, abs_of_pos hp, div_le_one hp] at h1 h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem getD_map_lt {β γ : Type*} (f : β → γ) (l : List β) (i : ℕ) (hi : i < l.length) (d : γ) (d' : β) :
    (l.map f).getD i d = f (l.getD i d') := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_take_lt {β : Type*} (l : List β) (s j : ℕ) (hj : j < s) (d : β) : (l.take s).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, hj]

open Resampling.NeumannWords (ext ext_mem ext_length ext_even ext_odd vec val_intCast_toNat)

set_option maxHeartbeats 1000000 in
/-- The expansion line map with the machine-built table is the floored tabled `Ã` on decoded lines. -/
theorem lineA_value (line : List (List Bool)) (s t m α p w W : ℕ) [NeZero s] [NeZero t]
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hm : p * α ^ 2 ≤ m ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (hw : p + 2 ≤ w) (hwW : w + 1 ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1)) (hst : s ≤ t)
    (hl : line.length = t) (hlw : ∀ e ∈ line, e.length = 2 * w) (hb : ∀ e ∈ line, ‖decE w p e‖ ≤ 1) :
    (lineA (TabATape.tabA s t m α p w (t * (2 * m + 1))) s t m p w W line).map (decE w p) =
      lineOf (floorA s t m α p) (line.map (decE w p)) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  set wt := TabATape.tabA s t m α p w (t * (2 * m + 1))
  set ys := (line.take s).flatMap (entryWords w) with hys
  have hlt : (line.take s).length = s := by simp [hl, hst]
  have hyl : ys.length = 2 * s := by
    simp only [ys, List.length_flatMap, entryWords, List.length_cons, List.length_nil]; simp [hl, hst]; ring
  have hyw : ∀ x ∈ ys, x.length = w := by
    intro x hx; simp only [ys, List.mem_flatMap, entryWords, List.mem_cons, List.mem_nil_iff, or_false] at hx
    obtain ⟨e, he, rfl | rfl⟩ := hx <;> simp [hlw e (List.mem_of_mem_take he)] <;> omega
  have hyb : ∀ x ∈ ys, |signed x| ≤ 2 ^ p := by
    intro x hx; simp only [ys, List.mem_flatMap, entryWords, List.mem_cons, List.mem_nil_iff, or_false] at hx
    obtain ⟨e, he, rfl | rfl⟩ := hx
    · exact (abs_signed_le_of_decE w p e (hb e (List.mem_of_mem_take he))).1
    · exact (abs_signed_le_of_decE w p e (hb e (List.mem_of_mem_take he))).2
  -- the decoded line restricted to its first `s` entries is `vec s p ys`
  have hentry : ∀ j : ℕ, j < s → decE w p (line.getD j []) =
      ⟨(signed (ys.getD (2 * j) []) : ℝ) / 2 ^ p, (signed (ys.getD (2 * j + 1) []) : ℝ) / 2 ^ p⟩ := by
    intro j hj
    obtain ⟨e1, e2⟩ := getD_flatMap_entryWords w (line.take s) j (by rw [hlt]; exact hj)
    rw [e1, e2, getD_take_lt _ _ _ hj]; rfl
  have hu : restr s t (fun j => (line.map (decE w p)).getD j.val 0) = vec s p ys := by
    funext ℓ
    have hℓ := ZMod.val_lt ℓ
    simp only [restr, vec]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), getD_map_lt _ _ _ (by omega) _ [], hentry _ hℓ]
  have hun : ‖vec s p ys‖ ≤ 1 := by
    rw [← hu]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun ℓ => ?_
    have hℓ := ZMod.val_lt ℓ
    simp only [restr]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), getD_map_lt _ _ _ (by omega) _ [],
      List.getD_eq_getElem _ _ (by omega)]
    exact hb _ (List.getElem_mem _)
  -- the floored outputs stay in the unit disk
  have hαr : (2 : ℝ) ≤ α := by exact_mod_cast hα
  have hαpr : (α : ℝ) ^ 2 ≤ p := by exact_mod_cast hαp
  have hmr : (p : ℝ) * (α : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hm
  obtain ⟨-, -, hball⟩ := floorA_tabled (s := s) (t := t) hαr hαpr hmr hm1 hmp hp (WeightTable.tableA s t α p)
    (fun k j => WeightTable.tableA_err s t α p hp hα k j)
  have hfb := hball _ hun
  set Amap := resampANum s t m (WindowSum.termW p fun k j => (WeightTable.tableA s t α p k j : ℝ) / 2 ^ p)
  set OW := GaussianLine.outWords wt (ext s m ys) s t m p w W t
  have hOW : OW.length = 2 * t := Resampling.NeumannWords.outWords_length _ _ _ _ _ _ _ _ _
  have hext : ∀ x ∈ ext s m ys, x ∈ ys := ext_mem s m ys hs hyl
  set ar : ℤ → ℤ := fun j => signed (ys.getD (2 * (j % s).toNat) [])
  set ai : ℤ → ℤ := fun j => signed (ys.getD (2 * (j % s).toNat + 1) [])
  have hvu : ∀ j : ℤ, vec s p ys (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩ := by
    intro j; simp only [vec, val_intCast_toNat s j hs, ar, ai]
  have hre : ∀ q, q < s + 2 * m → signed ((ext s m ys).getD (2 * q) []) = ar ((q : ℤ) - m) := by
    intro q hq; rw [ext_even _ _ _ _ hq]; rfl
  have him : ∀ q, q < s + 2 * m → signed ((ext s m ys).getD (2 * q + 1) []) = ai ((q : ℤ) - m) := by
    intro q hq; rw [ext_odd _ _ _ _ hq]; rfl
  have hval : ∀ k, k < t → Amap (vec s p ys) (k : ZMod t) =
      ⟨(signed (GaussianLine.accR wt (ext s m ys) s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1),
       (signed (GaussianLine.accI wt (ext s m ys) s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1)⟩ := fun k hk =>
    TableValue.a_tables s t m α p w W hα hp (ext s m ys) (vec s p ys) ar ai hvu hre him hw (by omega) hW
      (fun x hx => hyw x (hext x hx)) (fun x hx => hyb x (hext x hx)) (by rw [ext_length]) hst k hk
  have hhalf : ∀ k, k < t → |signed (GaussianLine.accR wt (ext s m ys) s t m p w W k (2 * m + 1)) / 2| ≤ 2 ^ p ∧
      |signed (GaussianLine.accI wt (ext s m ys) s t m p w W k (2 * m + 1)) / 2| ≤ 2 ^ p := fun k hk => by
    have hk1 := (norm_le_pi_norm (floorV p (Amap (vec s p ys))) (k : ZMod t)).trans hfb
    simp only [floorV, hval k hk, floorC_half] at hk1
    have hp' : (0 : ℝ) < 2 ^ p := by positivity
    have h1 := (Complex.abs_re_le_norm _).trans hk1
    have h2 := (Complex.abs_im_le_norm _).trans hk1
    simp only at h1 h2
    rw [abs_div, abs_of_pos hp', div_le_one hp'] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hpw : (2 : ℤ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  apply List.ext_getElem
  · rw [List.length_map, TensorTape.lineA_length, length_lineOf]
  · intro k hk1 hk2
    rw [List.length_map, TensorTape.lineA_length] at hk1
    rw [List.getElem_map, ← List.getD_eq_getElem _ [] , lineA,
      getD_pairUp t _ (by rw [List.length_map, hOW]) k hk1,
      getD_map_lt _ _ _ (by rw [Resampling.NeumannWords.outWords_length]; omega) _ [],
      getD_map_lt _ _ _ (by rw [Resampling.NeumannWords.outWords_length]; omega) _ [],
      Resampling.NeumannWords.outWords_even _ _ _ _ _ _ _ _ _ _ hk1,
      Resampling.NeumannWords.outWords_odd _ _ _ _ _ _ _ _ _ _ hk1,
      decE_pair _ _ _ _ (by simp [floorWord])]
    simp only [lineOf, List.getElem_map, List.getElem_range, floorA, hu]
    simp only [floorV]
    obtain ⟨b1, b2⟩ := hhalf k hk1
    rw [signed_floorWord w _ (by omega) (by rw [GaussianLine.accR_length _ _ _ _ _ _ _ _ _ (by omega)]; omega)
        (by rw [abs_le] at b1; linarith) (by rw [abs_le] at b1; linarith),
      signed_floorWord w _ (by omega) (by rw [GaussianLine.accI_length _ _ _ _ _ _ _ _ _ (by omega)]; omega)
        (by rw [abs_le] at b2; linarith) (by rw [abs_le] at b2; linarith)]
    refine Eq.trans ?_ (congrArg (floorC p) (hval k hk1)).symm
    rw [floorC_half]

end
end IntegerMultBounds.Resampling.LineNumeric
