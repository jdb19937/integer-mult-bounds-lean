module

public import IntegerMultBounds.Schoenhage.PrefixRoundMath
public import IntegerMultBounds.Schoenhage.RingUnpack

/-! Words of the prefix-slot round. A numerator `a` with `|a| < 2^(W-1)` is held
as the offset word `offWord W a`, the `W` low bits of `a + 2^(W-1)` least
significant first. Then a butterfly's sum is plain addition and its difference
is addition of the complement with carry in (`addW_offWord`, `addNotW_offWord`),
both one bit wider. The rule `addNot` computes the latter. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Strm Spec.SignedRingProduct Rules

/-- The offset word of `a`: `bits W (a + 2^(W-1))`. -/
def offWord (W : ℕ) (a : ℤ) : List Bool := bits W (a + 2 ^ (W - 1)).toNat

@[simp] theorem length_offWord (W : ℕ) (a : ℤ) : (offWord W a).length = W := by simp [offWord]

theorem bval_offWord {W : ℕ} {a : ℤ} (hW : 1 ≤ W) (h1 : -2 ^ (W - 1) ≤ a) (h2 : a < 2 ^ (W - 1)) :
    (bval (offWord W a) : ℤ) = a + 2 ^ (W - 1) := by
  unfold offWord
  rw [bval_bits]
  have hW' : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  have h0 : 0 ≤ a + 2 ^ (W - 1) := by linarith
  have hlt : (a + 2 ^ (W - 1)).toNat < 2 ^ W := by
    have : a + 2 ^ (W - 1) < 2 ^ W := by linarith
    zify; rw [Int.toNat_of_nonneg h0]; exact_mod_cast this
  rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0]

theorem offWord_of_bval {W : ℕ} {a : ℤ} {x : List Bool} (hx : x.length = W)
    (hv : (bval x : ℤ) = a + 2 ^ (W - 1)) : x = offWord W a := by
  rw [← bits_bval x, hx, offWord]
  congr 1
  zify
  rw [Int.toNat_of_nonneg (by rw [← hv]; positivity), hv]

/-- The sum of two offset words is the offset word of the sum, one bit wider. -/
theorem addW_offWord {W : ℕ} {a b : ℤ} (hW : 1 ≤ W) (ha1 : -2 ^ (W - 1) ≤ a) (ha2 : a < 2 ^ (W - 1))
    (hb1 : -2 ^ (W - 1) ≤ b) (hb2 : b < 2 ^ (W - 1)) :
    addW false (offWord W a) (offWord W b) = offWord (W + 1) (a + b) := by
  apply offWord_of_bval (by rw [length_addW, length_offWord])
  rw [bval_addW, length_offWord, fit_len (by simp)]
  push_cast
  rw [bval_offWord hW ha1 ha2, bval_offWord hW hb1 hb2]
  simp only [add_zero]
  have : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  linarith

/-- The complement of a word. -/
def cmpl (y : List Bool) : List Bool := y.map not

theorem bval_cmpl (y : List Bool) : bval (cmpl y) + bval y = 2 ^ y.length - 1 := by
  induction y with
  | nil => simp [cmpl]
  | cons b y ih =>
    simp only [cmpl, List.map_cons, bval_cons, List.length_cons, pow_succ] at ih ⊢
    have := Nat.one_le_two_pow (n := y.length)
    cases b <;> simp <;> omega

/-- The difference of two offset words is the complement sum with carry, one bit wider. -/
theorem addNotW_offWord {W : ℕ} {a b : ℤ} (hW : 1 ≤ W) (ha1 : -2 ^ (W - 1) ≤ a) (ha2 : a < 2 ^ (W - 1))
    (hb1 : -2 ^ (W - 1) ≤ b) (hb2 : b < 2 ^ (W - 1)) :
    addW true (offWord W a) (cmpl (offWord W b)) = offWord (W + 1) (a - b) := by
  apply offWord_of_bval (by rw [length_addW, length_offWord])
  rw [bval_addW, length_offWord, fit_len (by simp [cmpl])]
  have hc := bval_cmpl (offWord W b)
  rw [length_offWord] at hc
  have hc' : (bval (cmpl (offWord W b)) : ℤ) = 2 ^ W - 1 - bval (offWord W b) := by
    have := Nat.one_le_two_pow (n := W)
    zify [this] at hc ⊢; linarith
  push_cast
  rw [hc', bval_offWord hW ha1 ha2, bval_offWord hW hb1 hb2]
  simp only [ite_true]
  have : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  linarith

namespace Rules

/-- Ripple-carry addition of the complement of the input with carry in: `x + ~y + 1`. -/
abbrev addNot : Rule 1 where
  Q := Bool
  q0 := true
  step c b o :=
    let d := !((o 0).getD false)
    ((b && d) || (b && c) || (d && c), some (some (b ^^ d ^^ c)), fun _ => true)
  flush c := [some c, none]
  B := 2
  hB _ := le_rfl

theorem go_addNot (c : Bool) (x : List Bool) (ws : Fin 1 → List Bool) (hl : x.length ≤ (ws 0).length) :
    (go addNot c x ws).2.1 ++ addNot.flush (go addNot c x ws).1 = (addW c x (cmpl (ws 0))).map some ++ [none] := by
  induction x generalizing c ws with
  | nil => simp [go, addNot, addW]
  | cons b x ih =>
    rcases h : ws 0 with _ | ⟨y, ys⟩
    · rw [h] at hl; simp at hl
    · simp only [go, addW]
      have := ih ((b && !y) || (b && c) || (!y && c)) (fun j => (ws j).tail) (by rw [h] at hl; simpa [h] using hl)
      simp_all [cmpl]

theorem output_addNot (x : List Bool) (ws : Fin 1 → List Bool) (hl : x.length ≤ (ws 0).length) :
    output addNot x ws = syms [addW true x (cmpl (ws 0))] := by
  unfold output
  have : addNot.q0 = true := rfl
  rw [this, go_addNot true x ws hl]
  simp [syms_cons]

/-- Append one zero bit. -/
abbrev zext : Rule 0 where
  Q := Unit
  q0 := ()
  step _ b _ := ((), some (some b), fun _ => false)
  flush _ := [some false, none]
  B := 2
  hB _ := le_rfl

theorem go_zext (w : List Bool) (ws : Fin 0 → List Bool) :
    (go zext () w ws).2.1 = w.map some ∧ (go zext () w ws).1 = () := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih]

theorem output_zext (w : List Bool) (ws : Fin 0 → List Bool) : output zext w ws = syms [w ++ [false]] := by
  simp [output, syms_cons, (go_zext w ws).1]

end Rules

theorem bits_succ_zext (n v : ℕ) (hv : v < 2 ^ n) : bits n v ++ [false] = bits (n + 1) v := by
  rw [bits_succ_snoc]
  congr 2
  rw [Nat.div_eq_of_lt hv]
  simp

/-! ### Arrays of offset words -/

theorem getD_flatMap_uniform {α β : Type} (g : α → List β) (n : ℕ) (hg : ∀ a, (g a).length = n)
    (d : α) (e : β) : ∀ (L : List α) (k : ℕ), k < n * L.length →
      (L.flatMap g).getD k e = (g (L.getD (k / n) d)).getD (k % n) e
  | [], k, hk => by simp at hk
  | a :: L, k, hk => by
    rw [List.flatMap_cons]
    by_cases hkn : k < n
    · rw [List.getD_append _ _ _ _ (by rw [hg]; exact hkn), Nat.div_eq_of_lt hkn, Nat.mod_eq_of_lt hkn]
      rfl
    · have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h <;> [simp [h] at hk; exact h]
      rw [List.getD_append_right _ _ _ _ (by rw [hg]; omega), hg,
        getD_flatMap_uniform g n hg d e L (k - n) (by simp at hk; rw [Nat.mul_succ] at hk; omega)]
      have e1 : k / n = (k - n) / n + 1 := by
        rw [← Nat.sub_add_cancel (show n ≤ k by omega), Nat.add_div_right _ hn, Nat.sub_add_cancel (by omega)]
      have e2 : k % n = (k - n) % n := by
        conv_lhs => rw [← Nat.sub_add_cancel (show n ≤ k by omega)]
        rw [Nat.add_mod_right]
      rw [e1, e2]; rfl

variable {r : ℕ}

/-- Component `c` of a record: the real part of coefficient `c/2` for even `c`, else its imaginary part. -/
def comp (f : Rec r) (c : ℕ) : ℤ :=
  if h : c / 2 < r then (if c % 2 = 0 then f.1 ⟨c / 2, h⟩ else f.2 ⟨c / 2, h⟩) else 0

/-- A record's offset words, real then imaginary part of each coefficient. -/
def recOff (W : ℕ) (f : Rec r) : List (List Bool) :=
  (List.finRange r).flatMap fun j => [offWord W (f.1 j), offWord W (f.2 j)]

/-- An array's offset words. -/
def arrOff (W : ℕ) (fs : List (Rec r)) : List (List Bool) := fs.flatMap (recOff W)

theorem length_recOff (W : ℕ) (f : Rec r) : (recOff W f).length = 2 * r := by
  simp [recOff, List.length_flatMap, mul_comm]

theorem length_arrOff (W : ℕ) (fs : List (Rec r)) : (arrOff W fs).length = 2 * r * fs.length := by
  simp [arrOff, List.length_flatMap, length_recOff, mul_comm]

theorem getD_recOff (W : ℕ) (f : Rec r) {c : ℕ} (hc : c < 2 * r) :
    (recOff W f).getD c [] = offWord W (comp f c) := by
  unfold recOff
  rw [getD_flatMap_uniform (fun j : Fin r => [offWord W (f.1 j), offWord W (f.2 j)]) 2 (fun _ => rfl)
    ⟨0, by omega⟩ [] (List.finRange r) c (by simp; omega)]
  have hc2 : c / 2 < r := by omega
  have hfr : (List.finRange r).getD (c / 2) ⟨0, by omega⟩ = ⟨c / 2, hc2⟩ := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_finRange]; exact hc2)]
    simp
  rw [hfr]
  simp only [comp, hc2, ↓reduceDIte]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

theorem getD_arrOff (W : ℕ) (fs : List (Rec r)) {k : ℕ} (hk : k < 2 * r * fs.length) :
    (arrOff W fs).getD k [] = offWord W (comp (fs.getD (k / (2 * r)) 0) (k % (2 * r))) := by
  have hr : 0 < r := by rcases Nat.eq_zero_or_pos r with h | h <;> [simp [h] at hk; exact h]
  unfold arrOff
  rw [getD_flatMap_uniform (recOff W) (2 * r) (length_recOff W) 0 [] fs k hk,
    getD_recOff W _ (Nat.mod_lt _ (by omega))]

/-- One pass on a word list: in each pair of consecutive blocks of `B` words, the sums then the
complement sums. -/
def blockPass (B : ℕ) (L : List (List Bool)) : List (List Bool) :=
  List.ofFn fun k : Fin L.length =>
    if k / B % 2 = 0 then addW false (L.getD k []) (L.getD (k + B) [])
    else addW true (L.getD (k - B) []) (cmpl (L.getD k []))

theorem comp_addRec (f g : Rec r) (c : ℕ) : comp (addRec f g) c = comp f c + comp g c := by
  unfold comp addRec; split_ifs <;> simp

theorem comp_subRec (f g : Rec r) (c : ℕ) : comp (subRec f g) c = comp f c - comp g c := by
  unfold comp subRec; split_ifs <;> simp

/-- The components of an array are bounded by `A`. -/
def Bounded (A : ℤ) (fs : List (Rec r)) : Prop := ∀ y c, |comp (fs.getD y 0) c| ≤ A

/-- A pass on the offset words is the exact butterfly, one bit wider. -/
theorem arrOff_bflyRecs {W P : ℕ} (hW : 1 ≤ W) (fs : List (Rec r)) (hlen : 2 ^ (P + 1) ∣ fs.length)
    (hb : Bounded (2 ^ (W - 1) - 1) fs) :
    arrOff (W + 1) (bflyRecs P fs) = blockPass (2 * r * 2 ^ P) (arrOff W fs) := by
  have hr : 0 ≤ r := Nat.zero_le _
  apply List.ext_getElem (by simp [blockPass, length_arrOff])
  intro k h1 h2
  rw [← List.getD_eq_getElem _ [] h1, ← List.getD_eq_getElem _ [] h2]
  rw [length_arrOff, length_bflyRecs] at h1
  have hr0 : 0 < r := by rcases Nat.eq_zero_or_pos r with h | h <;> [simp [h] at h1; exact h]
  set N := fs.length
  set y := k / (2 * r)
  set c := k % (2 * r)
  have hk : k = 2 * r * y + c := (Nat.div_add_mod k (2 * r)).symm
  have hc : c < 2 * r := Nat.mod_lt _ (by omega)
  have hy : y < N := by
    by_contra hh
    have : 2 * r * N ≤ 2 * r * y := Nat.mul_le_mul_left _ (by omega)
    omega
  have hdiv : ∀ z, (2 * r * z + c) / (2 * r) = z := fun z => by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
  have hmod : ∀ z, (2 * r * z + c) % (2 * r) = c := fun z => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hbit : k / (2 * r * 2 ^ P) % 2 = bitAt y P := by
    rw [← Nat.div_div_eq_div_mul]; rfl
  -- the left side
  rw [getD_arrOff (W + 1) _ (by rw [length_bflyRecs]; exact h1)]
  have hgd : (bflyRecs P fs).getD y 0 = if bitAt y P = 0 then addRec (fs.getD y 0) (fs.getD (y + 2 ^ P) 0)
      else subRec (fs.getD (y - 2 ^ P) 0) (fs.getD y 0) := by
    rw [List.getD_eq_getElem _ _ (by rw [length_bflyRecs]; exact hy)]
    simp [bflyRecs, List.getElem?_eq_getElem hy]
  rw [hgd]
  -- the right side
  have hbl : k < (arrOff W fs).length := by rw [length_arrOff]; exact h1
  have hof : ∀ (g : Fin (arrOff W fs).length → List Bool), (List.ofFn g).getD k [] = g ⟨k, hbl⟩ :=
    fun g => by rw [List.getD_eq_getElem _ _ (by simpa using hbl)]; simp
  unfold blockPass
  rw [hof]
  simp only
  rw [hbit]
  obtain ⟨m, hm⟩ := hlen
  have hbd : ∀ z, -2 ^ (W - 1) ≤ comp (fs.getD z 0) c ∧ comp (fs.getD z 0) c < 2 ^ (W - 1) := fun z => by
    have := hb z c
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  split_ifs with h0
  · -- the partner `y + 2^P` lies in the array
    have hyP : y + 2 ^ P < N := by
      have h2P : y / 2 ^ P % 2 = 0 := h0
      have hlt : y / 2 ^ P < 2 * m := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        have : N = 2 ^ P * 2 * m := by rw [hm, pow_succ]
        nlinarith
      have hlt2 : y / 2 ^ P + 1 < 2 * m := by omega
      have := Nat.lt_div_mul_add (a := y) (b := 2 ^ P) (by positivity)
      have : N = 2 ^ P * (2 * m) := by rw [hm, pow_succ]; ring
      nlinarith
    have hkB : k + 2 * r * 2 ^ P = 2 * r * (y + 2 ^ P) + c := by rw [hk]; ring
    rw [getD_arrOff W fs h1, getD_arrOff W fs (by rw [hkB]; nlinarith), hkB, hdiv, hmod,
      addW_offWord (by omega) (hbd y).1 (hbd y).2 (hbd (y + 2 ^ P)).1 (hbd (y + 2 ^ P)).2, comp_addRec]
  · have hyP : 2 ^ P ≤ y := by
      by_contra hh
      apply h0
      unfold bitAt
      rw [Nat.div_eq_of_lt (by omega)]
    have hkB : k - 2 * r * 2 ^ P = 2 * r * (y - 2 ^ P) + c := by
      rw [hk, Nat.mul_sub]
      have : 2 * r * 2 ^ P ≤ 2 * r * y := Nat.mul_le_mul_left _ hyP
      omega
    rw [getD_arrOff W fs h1, getD_arrOff W fs (lt_of_le_of_lt (Nat.sub_le _ _) h1), hkB, hdiv, hmod,
      addNotW_offWord (by omega) (hbd (y - 2 ^ P)).1 (hbd (y - 2 ^ P)).2 (hbd y).1 (hbd y).2, comp_subRec]

theorem Bounded.mono {A A' : ℤ} {fs : List (Rec r)} (h : Bounded A fs) (hA : A ≤ A') : Bounded A' fs :=
  fun y c => (h y c).trans hA

theorem comp_zero (c : ℕ) : comp (0 : Rec r) c = 0 := by unfold comp; split_ifs <;> rfl

theorem bounded_bflyRecs {A : ℤ} {fs : List (Rec r)} (P : ℕ) (h : Bounded A fs) :
    Bounded (2 * A) (bflyRecs P fs) := by
  intro y c
  by_cases hy : y < fs.length
  · rw [List.getD_eq_getElem _ _ (by rw [length_bflyRecs]; exact hy)]
    simp only [bflyRecs, List.getElem_ofFn]
    split_ifs
    · rw [comp_addRec]
      have := abs_add_le (comp (fs.getD y 0) c) (comp (fs.getD (y + 2 ^ P) 0) c)
      linarith [h y c, h (y + 2 ^ P) c]
    · rw [comp_subRec]
      have := abs_sub (comp (fs.getD (y - 2 ^ P) 0) c) (comp (fs.getD y 0) c)
      linarith [h (y - 2 ^ P) c, h y c]
  · rw [List.getD_eq_default _ _ (by rw [length_bflyRecs]; omega), comp_zero, abs_zero]
    have := h y c
    rw [List.getD_eq_default _ _ (by omega), comp_zero, abs_zero] at this
    linarith

/-- `D` passes with block sizes `B, 2B, 4B, …`. -/
def passes : ℕ → ℕ → List (List Bool) → List (List Bool)
  | _, 0, L => L
  | B, D + 1, L => passes (2 * B) D (blockPass B L)

/-- The exact butterflies on bits `s, …, s + D - 1` are `D` passes on the offset words. -/
theorem arrOff_bflysRecs : ∀ (D s W : ℕ) (fs : List (Rec r)), 1 ≤ W → 2 ^ (s + D) ∣ fs.length →
    Bounded (2 ^ (W - 1) - 1) fs →
    arrOff (W + D) (bflysRecs ((List.range D).map (s + ·)) fs) = passes (2 * r * 2 ^ s) D (arrOff W fs)
  | 0, s, W, fs, _, _, _ => by simp [bflysRecs, passes]
  | D + 1, s, W, fs, hW, hd, hb => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, bflysRecs, passes, add_zero]
    have h1 : 2 ^ (s + 1) ∣ fs.length := (Nat.pow_dvd_pow 2 (by omega)).trans hd
    have hstep := arrOff_bflyRecs (W := W) (P := s) hW fs h1 hb
    have hlist : (List.range D).map ((s + ·) ∘ Nat.succ) = (List.range D).map ((s + 1) + ·) := by
      apply List.map_congr_left; intro i _; simp; ring
    rw [hlist, show W + (D + 1) = (W + 1) + D by ring,
      arrOff_bflysRecs D (s + 1) (W + 1) (bflyRecs s fs) (by omega)
        (by rw [length_bflyRecs, show s + 1 + D = s + (D + 1) by ring]; exact hd)
        ((bounded_bflyRecs s hb).mono (by
          have : (2 : ℤ) ^ (W + 1 - 1) = 2 * 2 ^ (W - 1) := by
            rw [Nat.add_sub_cancel, ← pow_succ']; congr 1; omega
          rw [this]; linarith)),
      hstep, pow_succ, show 2 * r * (2 ^ s * 2) = 2 * (2 * r * 2 ^ s) by ring]

end IntegerMultBounds.Schoenhage
