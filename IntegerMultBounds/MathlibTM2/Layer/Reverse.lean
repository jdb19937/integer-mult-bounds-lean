module

public import IntegerMultBounds.MathlibTM2.Layer.Enc

/-!
# Reversing an array stream

Reversing the symbol stream of an array is again the stream of an array: `encZ A w Z` reversed is
`encZ A w (zrev w Z)`, where `zrev` reverses the row and column indices, complements every
address bit and reverses the `w` bits of both parts of every coefficient (`encZ_reverse`). Up to
reduction modulo `2^w`, `zrev` is an involution (`encZ_zrev_zrev`), and it conjugates a change of
basis `L` of the active columns into `t ↦ L (t + 1) + 1` (`zrev_pullM`). So reversing, changing
basis by a linear involution `L` and reversing again translates every column by `L 1 + 1` after
the first change of basis.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks

/-! ### Bit reversal -/

/-- The number whose bits, least significant first, are the list. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

theorem testBit_bitsVal (bs : List Bool) (t : ℕ) : (bitsVal bs).testBit t = bs.getD t false := by
  induction bs generalizing t with
  | nil => simp [bitsVal]
  | cons b bs ih =>
    cases t with
    | zero => cases b <;> simp [bitsVal, Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ t =>
      rw [bitsVal, Nat.testBit_succ, show (b.toNat + 2 * bitsVal bs) / 2 = bitsVal bs by
        cases b <;> simp <;> omega, ih]
      simp

theorem bitsVal_lt (bs : List Bool) : bitsVal bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsVal]
  | cons b bs ih => cases b <;> simp [bitsVal, pow_succ] <;> omega

/-- The `W` low bits of `a` in reverse order. -/
def revNat (W a : ℕ) : ℕ := bitsVal (List.ofFn fun t : Fin W => a.testBit (W - 1 - t))

theorem revNat_lt (W a : ℕ) : revNat W a < 2 ^ W := by
  have h := bitsVal_lt (List.ofFn fun t : Fin W => a.testBit (W - 1 - t))
  rw [List.length_ofFn] at h
  exact h

theorem testBit_revNat (W a : ℕ) (t : ℕ) :
    (revNat W a).testBit t = if t < W then a.testBit (W - 1 - t) else false := by
  rw [revNat, testBit_bitsVal]
  split_ifs with ht
  · simp [List.getD_eq_getElem?_getD, ht]
  · simp [List.getD_eq_getElem?_getD, ht]

theorem revNat_revNat {W a : ℕ} (ha : a < 2 ^ W) : revNat W (revNat W a) = a := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_revNat]
  split_ifs with ht
  · rw [testBit_revNat, show W - 1 - (W - 1 - t) = t by omega]
    simp [show W - 1 - t < W by omega]
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right two_pos (by omega)))).symm

/-- Bit reversal of both parts of a residue modulo `2^W`. -/
def revGR {W : ℕ} (g : GR W) : GR W := ((revNat W g.1.val : ZMod (2 ^ W)), (revNat W g.2.val : ZMod (2 ^ W)))

theorem val_revNat_cast (W a : ℕ) : ((revNat W a : ZMod (2 ^ W))).val = revNat W a :=
  ZMod.val_cast_of_lt (revNat_lt W a)

theorem revGR_revGR {W : ℕ} (g : GR W) : revGR (revGR g) = g := by
  have h1 := revNat_revNat (W := W) (ZMod.val_lt g.1)
  have h2 := revNat_revNat (W := W) (ZMod.val_lt g.2)
  simp only [revGR, val_revNat_cast, h1, h2, ZMod.natCast_val, ZMod.cast_id', id]

theorem reverse_ofFn' {α : Type*} {N : ℕ} (f : Fin N → α) :
    (List.ofFn f).reverse = List.ofFn (f ∘ Fin.rev) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_ofFn, Function.comp_apply, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  simp at h1
  omega

theorem coeffSyms_revGR (A W : ℕ) (g : GR W) : coeffSyms A W (revGR g) = (coeffSyms A W g).reverse := by
  rw [coeffSyms, coeffSyms, reverse_ofFn']
  refine congrArg List.ofFn (funext fun t => ?_)
  simp only [revGR, val_revNat_cast, testBit_revNat, t.isLt, ↓reduceIte, Function.comp_apply,
    Fin.val_rev]
  rw [show W - 1 - (t : ℕ) = W - (t + 1) by omega]

/-- A Gaussian integer whose residue is the bit reversal of the residue of `z`. -/
def bitrevG (W : ℕ) (z : GaussianInt) : GaussianInt :=
  ⟨(revNat W (red W z).1.val : ℤ), (revNat W (red W z).2.val : ℤ)⟩

theorem red_bitrevG (W : ℕ) (z : GaussianInt) : red W (bitrevG W z) = revGR (red W z) := by
  simp [red, bitrevG, revGR]

/-! ### The reversed array -/

variable {R r n : ℕ}

/-- The address with every bit complemented. -/
def compl (b : Fin n → ZMod 2) : Fin n → ZMod 2 := fun t => b t + 1

/-- The array of the reversed stream. -/
def zrev (w : ℕ) (Z : ZArr (Fin R × Fin r) n) : ZArr (Fin R × Fin r) n :=
  fun p => bitrevG w (Z ((Fin.rev p.1.1, Fin.rev p.1.2), compl p.2))

theorem testBit_pow_sub (n a t : ℕ) (ha : a < 2 ^ n) :
    (2 ^ n - 1 - a).testBit t = (decide (t < n) && !a.testBit t) := by
  induction n generalizing a t with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    simp
  | succ n ih =>
    have hP : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    cases t with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero]
      have : (2 ^ (n + 1) - 1 - a) % 2 = 1 - a % 2 := by rw [hP]; omega
      rw [this]
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
    | succ t =>
      rw [Nat.testBit_succ, Nat.testBit_succ, show (2 ^ (n + 1) - 1 - a) / 2 = 2 ^ n - 1 - a / 2 by
        rw [hP]; omega, ih (a / 2) t (by rw [hP] at ha; omega)]
      simp

theorem addrBits_rev {a : ℕ} (ha : a < 2 ^ n) : addrBits n (2 ^ n - 1 - a) = compl (addrBits n a) := by
  funext t
  simp only [addrBits, compl, testBit_pow_sub n a t ha, t.isLt, decide_true, Bool.true_and]
  cases a.testBit t <;> decide

/-- The cell of the reversed stream position. -/
def revCell (p : (Fin R × Fin r) × (Fin n → ZMod 2)) : (Fin R × Fin r) × (Fin n → ZMod 2) :=
  ((Fin.rev p.1.1, Fin.rev p.1.2), compl p.2)

theorem revCell_revCell (p : (Fin R × Fin r) × (Fin n → ZMod 2)) : revCell (revCell p) = p := by
  obtain ⟨⟨u, c⟩, b⟩ := p
  simp only [revCell, Fin.rev_rev, Prod.mk.injEq, true_and, and_self]
  funext t
  simp only [compl]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem cellList_reverse : (cellList R r n).reverse = (cellList R r n).map revCell := by
  unfold cellList
  rw [List.reverse_flatMap, List.finRange_reverse, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun u _ => ?_
  rw [Function.comp_apply, List.reverse_flatMap, List.map_flatMap, List.range_eq_range',
    List.reverse_range', List.flatMap_map, ← List.range_eq_range']
  refine List.flatMap_congr fun a ha => ?_
  have ha' : a < 2 ^ n := by simpa using ha
  rw [Function.comp_apply, reverse_ofFn', List.map_ofFn]
  refine congrArg List.ofFn (funext fun c => ?_)
  simp only [Function.comp_apply, revCell, Fin.rev_rev, zero_add]
  rw [addrBits_rev ha']

theorem coeffList_zrev (w : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    coeffList w (zrev w Z) = (coeffList w Z).reverse.map revGR := by
  rw [coeffList_eq_map, coeffList_eq_map, ← List.map_reverse, cellList_reverse, List.map_map,
    List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [zrev, red_bitrevG, revCell]

/-- **The reversed stream of an array is the stream of the reversed array.** -/
theorem encZ_reverse (A w : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    (encZ A w Z).reverse = encZ A w (zrev w Z) := by
  rw [encZ, encZ, coeffList_zrev, List.reverse_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun z _ => ?_
  simp [coeffSyms_revGR]

theorem encZ_congr {A w : ℕ} {Z Z' : ZArr (Fin R × Fin r) n} (h : ∀ p, red w (Z p) = red w (Z' p)) :
    encZ A w Z = encZ A w Z' := by
  rw [encZ, encZ, coeffList_eq_map, coeffList_eq_map]
  exact congrArg _ (List.map_congr_left fun p _ => h p)

theorem encZ_zrev_zrev (A w : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    encZ A w (zrev w (zrev w Z)) = encZ A w Z := by
  refine encZ_congr fun p => ?_
  change red w (bitrevG w (bitrevG w (Z (revCell (revCell p))))) = _
  rw [red_bitrevG, red_bitrevG, revGR_revGR, revCell_revCell]

/-! ### Reversal and changes of basis -/

variable {k : ℕ} (e : Fin (m * k) → Fin n)

theorem compl_merge {k' : ℕ} (e' : Fin k' → Fin n) (b : Fin n → ZMod 2) (a : Fin k' → ZMod 2) :
    compl (merge e' b a) = merge e' (compl b) (fun i => a i + 1) := by
  funext t
  simp only [compl, merge]
  split_ifs <;> rfl

/-- **Reversal conjugates a change of basis `L` into `t ↦ L (t + 1) + 1`.** -/
theorem zrev_pullM (w : ℕ) (L : BinaryWalsh.Address m → BinaryWalsh.Address m)
    (Z : ZArr (Fin R × Fin r) n) :
    zrev w (pullM e L Z) = pullM e (fun t => L (t + 1) + 1) (zrev w Z) := by
  funext p
  have hcol : ∀ c, colBits e c (compl p.2) = colBits e c p.2 + 1 := fun c => by
    funext j; rfl
  simp only [zrev, pullM]
  refine congrArg (fun b => bitrevG w (Z ((Fin.rev p.1.1, Fin.rev p.1.2), b))) ?_
  rw [compl_merge]
  refine congrArg (merge e (compl p.2)) ?_
  funext i
  simp only [ofCols, hcol, Pi.add_apply, Pi.one_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

variable {e}

theorem pullM_pullM (he : Function.Injective e) (L₁ L₂ : BinaryWalsh.Address m → BinaryWalsh.Address m)
    (Z : ZArr (Fin R × Fin r) n) : pullM e L₁ (pullM e L₂ Z) = pullM e (L₂ ∘ L₁) Z := by
  funext p
  simp only [pullM, colBits_merge he, toCols_ofCols, merge_merge, Function.comp_apply]

theorem encZ_pullM_congr {A w : ℕ} (L : BinaryWalsh.Address m → BinaryWalsh.Address m)
    {Z Z' : ZArr (Fin R × Fin r) n} (h : ∀ p, red w (Z p) = red w (Z' p)) :
    encZ A w (pullM e L Z) = encZ A w (pullM e L Z') :=
  encZ_congr fun p => h _

theorem basisMap_one (w : BinaryWalsh.Address m) (x : Fin m) (hx : w x = 0) :
    basisMap (w + Pi.single x 1) x 1 = 1 + w := by
  funext j
  simp only [basisMap, Pi.add_apply, Pi.one_apply, one_smul, Pi.smul_apply, smul_eq_mul, one_mul]
  by_cases hj : j = x
  · subst hj; simp [hx]; decide
  · simp [hj]

/-- **Translation by reversals.** Changing basis by `basisMap (w + e_x) x`, reversing, changing
basis again and reversing translates every active column by `w`, when `w_x = 0`. -/
theorem encZ_translate (he : Function.Injective e) (A W : ℕ) (w : BinaryWalsh.Address m) (x : Fin m)
    (hx : w x = 0) (Z : ZArr (Fin R × Fin r) n) :
    encZ A W (zrev W (pullM e (basisMap (w + Pi.single x 1) x)
        (zrev W (pullM e (basisMap (w + Pi.single x 1) x) Z)))) =
      encZ A W (pullM e (fun t => t + w) Z) := by
  have hv : (w + Pi.single x 1 : BinaryWalsh.Address m) x = 1 := by simp [hx]
  set B := basisMap (w + Pi.single x 1) x
  have hrr : ∀ (Y : ZArr (Fin R × Fin r) n) p, red W (zrev W (zrev W Y) p) = red W (Y p) := by
    intro Y p
    change red W (bitrevG W (bitrevG W (Y (revCell (revCell p))))) = _
    rw [red_bitrevG, red_bitrevG, revGR_revGR, revCell_revCell]
  have hcomp : (B ∘ fun t => B (t + 1) + 1) = fun t => t + w := by
    funext t
    simp only [Function.comp_apply, B]
    rw [basisMap_add, basisMap_invol _ _ hv, basisMap_one w x hx]
    funext j
    simp only [Pi.add_apply, Pi.one_apply]
    rw [add_assoc, ← add_assoc (1 : ZMod 2), CharTwo.add_self_eq_zero, zero_add]
  calc encZ A W (zrev W (pullM e B (zrev W (pullM e B Z))))
      = encZ A W (pullM e (fun t => B (t + 1) + 1) (zrev W (zrev W (pullM e B Z)))) := by
        rw [zrev_pullM]
    _ = encZ A W (pullM e (fun t => B (t + 1) + 1) (pullM e B Z)) :=
        encZ_pullM_congr _ (hrr _)
    _ = encZ A W (pullM e (fun t => t + w) Z) := by rw [pullM_pullM he, hcomp]

end IntegerMultBounds.MathlibTM2.Layer
