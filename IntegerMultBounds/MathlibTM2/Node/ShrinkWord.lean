module

public import IntegerMultBounds.MathlibTM2.Node.TopWord
public import IntegerMultBounds.MathlibTM2.Layer.TopRS

/-!
# Shrinking the coefficients of a stream by one

`shrinkZ 1` moves both parts of every coefficient one step toward zero, stopping at zero
(`Layer/TopRS.lean`). On a word of `w'` signed bits the part `x` with sign `σ` becomes
`t = x + 1` (`σ` set) or `t = x - 1` (`σ` clear), the sum of `x`, the constant bits `¬σ` and the
carry `σ` (`shrSum`); when the sign of `t` differs from `σ` the result is `0` (`shr_bits`).

**The word program** (`shrWord`, `shrWord_spec`). Copy the word onto `tmp` and back (its sign
pair onto `sg`, which also seeds the carry on `cy`), add it on `tmp` (`shrAddF`), compare the top
of `tmp` with the sign into the mask on `sg` (`shrMaskAct`), move the sum back and emit it with
the mask applied (`shrOutF`). `shrinkP_exec` runs it on every word of a stream.

**The identity** (`tdiv_shrink_mul`): shrinking by `k 2^s'` and truncating by `2^(s' + s₂)` is
truncating by `2^s'`, shrinking by `k` and truncating by `2^s₂`; shrinking by `k` is `k`
shrinks by one (`shrinkZ_succ`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer

/-! ### The integer identities -/

section Ident

lemma shrinkI_zero (x : ℤ) : shrinkI 0 x = x := by
  unfold shrinkI; split_ifs with h <;> omega

lemma shrinkI_succ (k : ℕ) (x : ℤ) : shrinkI (k + 1) x = shrinkI 1 (shrinkI k x) := by
  unfold shrinkI; push_cast; split_ifs <;> omega

lemma shrinkZ_succ (k : ℕ) (z : GaussianInt) : shrinkZ (k + 1) z = shrinkZ 1 (shrinkZ k z) := by
  unfold shrinkZ; congr 1 <;> exact shrinkI_succ k _

lemma shrinkZ_zero (z : GaussianInt) : shrinkZ 0 z = z := by
  simp only [shrinkZ, shrinkI_zero]

/-- `k` shrinks by one. -/
lemma shrinkZ_iterate (k : ℕ) (z : GaussianInt) : shrinkZ k z = (shrinkZ 1)^[k] z := by
  induction k with
  | zero => rw [shrinkZ_zero]; rfl
  | succ k ih => rw [shrinkZ_succ, ih, Function.iterate_succ_apply']

lemma tdiv_tdiv_two_pow (x : ℤ) (a b : ℕ) :
    (x.tdiv (2 ^ a)).tdiv (2 ^ b) = x.tdiv (2 ^ (a + b)) := by
  have ha : (0 : ℤ) ≤ 2 ^ a := by positivity
  rw [pow_add]
  rcases le_or_gt 0 x with hx | hx
  · rw [Int.tdiv_eq_ediv_of_nonneg hx, Int.tdiv_eq_ediv_of_nonneg (Int.ediv_nonneg hx ha),
      Int.tdiv_eq_ediv_of_nonneg hx, Int.ediv_ediv_of_nonneg ha]
  · have hneg : ∀ (z d : ℤ), z ≤ 0 → z.tdiv d = -((-z) / d) := fun z d hz => by
      rw [← Int.tdiv_eq_ediv_of_nonneg (by linarith), Int.neg_tdiv, neg_neg]
    have h1 : (-x) / 2 ^ a ≥ 0 := Int.ediv_nonneg (by linarith) ha
    rw [hneg x _ hx.le, hneg _ _ (by linarith), neg_neg, hneg x _ hx.le,
      Int.ediv_ediv_of_nonneg ha]

/-- Truncation by `2^s'` commutes with shrinking, the shrink scaling by `2^s'`. -/
lemma tdiv_shrinkI (k s' : ℕ) (y : ℤ) :
    (shrinkI (k * 2 ^ s') y).tdiv (2 ^ s') = shrinkI k (y.tdiv (2 ^ s')) := by
  have hd : (0 : ℤ) < 2 ^ s' := by positivity
  unfold shrinkI
  push_cast
  rcases le_or_gt 0 y with hy | hy
  · have hq : 0 ≤ y.tdiv (2 ^ s') := by
      rw [Int.tdiv_eq_ediv_of_nonneg hy]; exact Int.ediv_nonneg hy hd.le
    simp only [hy, hq, ite_true]
    rcases le_total (y - k * 2 ^ s') 0 with h | h
    · rw [max_eq_right h, Int.zero_tdiv]
      rw [Int.tdiv_eq_ediv_of_nonneg hy]
      have : y / 2 ^ s' ≤ k := Int.ediv_le_of_le_mul hd (by linarith)
      rw [max_eq_right (by linarith)]
    · rw [max_eq_left h, Int.tdiv_eq_ediv_of_nonneg h, Int.tdiv_eq_ediv_of_nonneg hy,
        show y - k * 2 ^ s' = y + 2 ^ s' * (-k) by ring, Int.add_mul_ediv_left _ _ hd.ne']
      have : (k : ℤ) ≤ y / 2 ^ s' := Int.le_ediv_of_mul_le hd (by linarith)
      rw [max_eq_left (by linarith)]; ring
  · have hneg : ∀ z : ℤ, z ≤ 0 → z.tdiv (2 ^ s') = -((-z) / 2 ^ s') := fun z hz => by
      rw [← Int.tdiv_eq_ediv_of_nonneg (by linarith), Int.neg_tdiv, neg_neg]
    have hq : y.tdiv (2 ^ s') ≤ 0 := by
      rw [hneg y hy.le]; have := Int.ediv_nonneg (show 0 ≤ -y by linarith) hd.le; linarith
    simp only [show ¬ (0 ≤ y) by omega, ite_false]
    by_cases hq0 : 0 ≤ y.tdiv (2 ^ s')
    · have h0 : y.tdiv (2 ^ s') = 0 := le_antisymm hq hq0
      simp only [h0]
      have h1 : (-y) / 2 ^ s' = 0 := by rw [hneg y hy.le] at h0; linarith
      have h2 : -y < 2 ^ s' := by
        by_contra hc
        have := Int.le_ediv_of_mul_le hd (show 1 * 2 ^ s' ≤ -y by linarith)
        omega
      rcases le_total (y + k * 2 ^ s') 0 with h | h
      · rw [min_eq_left h, hneg _ h]
        have hk : k = 0 ∨ 1 ≤ k := by omega
        rcases hk with rfl | hk
        · simp [h1]
        · nlinarith [show (1 : ℤ) ≤ k by exact_mod_cast hk]
      · rw [min_eq_right h, Int.zero_tdiv]; simp
    · simp only [hq0, ite_false]
      rcases le_total (y + k * 2 ^ s') 0 with h | h
      · rw [min_eq_left h, hneg _ h, hneg y hy.le,
          show -(y + k * 2 ^ s') = -y + 2 ^ s' * (-k) by ring, Int.add_mul_ediv_left _ _ hd.ne']
        have : (k : ℤ) ≤ (-y) / 2 ^ s' := Int.le_ediv_of_mul_le hd (by linarith)
        rw [min_eq_left (by linarith)]; ring
      · rw [min_eq_right h, Int.zero_tdiv, hneg y hy.le]
        have : (-y) / 2 ^ s' ≤ k := Int.ediv_le_of_le_mul hd (by linarith)
        rw [min_eq_right (by linarith)]

/-- **The shrink identity.** Shrinking by `k 2^s'` and truncating by `2^(s' + s₂)` is truncating
by `2^s'`, shrinking by `k` and truncating by `2^s₂`. -/
theorem tdiv_shrink_mul (k s' s₂ : ℕ) (z : GaussianInt) :
    tdivZ (s' + s₂) (shrinkZ (k * 2 ^ s') z) = tdivZ s₂ (shrinkZ k (tdivZ s' z)) := by
  simp only [tdivZ, shrinkZ, ← tdiv_tdiv_two_pow, tdiv_shrinkI]

end Ident

/-! ### Shrinking by one: bits -/

section Bits

/-- The bits of `bs` plus the constant bits `k` and the carry `c`, truncated to the length of
`bs`. -/
def shrSum (k : Bool) : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: bs => xor (xor b k) c :: shrSum k (topMaj b k c) bs

/-- The final carry of `shrSum`. -/
def shrCar (k : Bool) : Bool → List Bool → Bool
  | c, [] => c
  | c, b :: bs => shrCar k (topMaj b k c) bs

lemma shrSum_length (k : Bool) : ∀ (c : Bool) (bs : List Bool), (shrSum k c bs).length = bs.length
  | _, [] => rfl
  | c, b :: bs => by simp [shrSum, shrSum_length k _ bs]

lemma shrSum_val (k : Bool) : ∀ (c : Bool) (bs : List Bool),
    valBits (shrSum k c bs) =
      (valBits bs + k.toNat * (2 ^ bs.length - 1) + c.toNat) % 2 ^ bs.length
  | c, [] => by cases c <;> cases k <;> simp [shrSum, valBits]
  | c, b :: bs => by
      simp only [shrSum, valBits, List.length_cons]
      have hP : 1 ≤ 2 ^ bs.length := Nat.one_le_two_pow
      rw [shrSum_val k (topMaj b k c) bs, pow_succ',
        show b.toNat + 2 * valBits bs + k.toNat * (2 * 2 ^ bs.length - 1) + c.toNat =
          (xor (xor b k) c).toNat +
            2 * (valBits bs + k.toNat * (2 ^ bs.length - 1) + (topMaj b k c).toNat) by
            cases b <;> cases k <;> cases c <;> simp [topMaj] <;> omega,
        topMod_two_mul (Bool.toNat_lt _) (by positivity)]

/-- One step toward zero, without the stop at zero. -/
def shrT (x : ℤ) : ℤ := if x < 0 then x + 1 else x - 1

lemma shrT_fits {w' : ℕ} {x : ℤ} (hx : TopFits w' x) : TopFits w' (shrT x) := by
  have hpos : (1 : ℤ) ≤ 2 ^ (w' - 1) := one_le_pow₀ (by norm_num)
  obtain ⟨h1, h2⟩ := hx
  unfold shrT TopFits
  split_ifs <;> constructor <;> linarith

/-- The sum of the bits of `x`, the constant bits `¬σ` and the carry `σ` is `shrT x`. -/
lemma shrSum_bits {w' : ℕ} {x : ℤ} :
    shrSum (!decide (x < 0)) (decide (x < 0))
        (List.ofFn fun t : Fin w' => (x : ZMod (2 ^ w')).val.testBit t) =
      List.ofFn fun t : Fin w' => ((shrT x : ℤ) : ZMod (2 ^ w')).val.testBit t := by
  set bs := List.ofFn fun t : Fin w' => (x : ZMod (2 ^ w')).val.testBit t with hbs
  have hlen : bs.length = w' := by simp [hbs]
  have hval : valBits bs = (x : ZMod (2 ^ w')).val := valBits_val w' _
  set sr := shrSum (!decide (x < 0)) (decide (x < 0)) bs with hsr
  have hsl : sr.length = w' := by rw [hsr, shrSum_length, hlen]
  have hv : valBits sr = ((shrT x : ℤ) : ZMod (2 ^ w')).val := by
    rw [hsr, shrSum_val, hlen, hval]
    have hP : 1 ≤ 2 ^ w' := Nat.one_le_two_pow
    have hc : (((x : ZMod (2 ^ w')).val + (!decide (x < 0)).toNat * (2 ^ w' - 1) +
        (decide (x < 0)).toNat : ℕ) : ZMod (2 ^ w')) = ((shrT x : ℤ) : ZMod (2 ^ w')) := by
      have h2 : ((2 ^ w' : ℕ) : ZMod (2 ^ w')) = 0 := ZMod.natCast_self _
      unfold shrT
      by_cases hneg : x < 0
      · simp [hneg]
      · simp only [hneg, decide_false, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
          one_mul, add_zero, ite_false]
        push_cast [Nat.cast_sub hP]
        rw [ZMod.natCast_val, ZMod.cast_id', id]
        push_cast at h2
        rw [h2]; ring
    rw [← ZMod.val_natCast, hc]
  apply List.ext_getElem
  · simp [hsl]
  · intro t h1 h2
    rw [topGetElem_valBits sr t h1, hv]
    simp

lemma shrinkI_one_eq (x : ℤ) :
    shrinkI 1 x = if xor (decide (shrT x < 0)) (decide (x < 0)) then 0 else shrT x := by
  unfold shrinkI shrT
  by_cases hx : x < 0
  · by_cases ht : x + 1 < 0
    · simp [hx, ht, show ¬ (0 ≤ x) by omega]
    · simp [hx, ht, show ¬ (0 ≤ x) by omega]; omega
  · by_cases ht : x - 1 < 0
    · simp [hx, ht, show 0 ≤ x by omega]; omega
    · simp [hx, ht, show 0 ≤ x by omega]; omega

end Bits

/-! ### Shrinking by one: words -/

section Words

variable {A : ℕ}

/-- The pair of `b` with the parts selected by the mask pair `m` cleared. -/
def shrOutSym (b m : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (pairRe b && !pairRe m) (pairIm b && !pairIm m)

/-- The mask pair: where the sign pair `b` of the sum differs from the sign pair `σ`. -/
def shrMaskSym (b σ : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (xor (pairRe b) (pairRe σ)) (xor (pairIm b) (pairIm σ))

/-- The sum word: both parts of `x` moved by one toward zero, without the stop at zero. -/
def shrY (A : ℕ) (x : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  List.zipWith (pairSym A)
    (shrSum (!pairRe (x.getLast?.getD blank)) (pairRe (x.getLast?.getD blank)) (x.map pairRe))
    (shrSum (!pairIm (x.getLast?.getD blank)) (pairIm (x.getLast?.getD blank)) (x.map pairIm))

/-- The shrunk word. -/
def shrF (A : ℕ) (x : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  (shrY A x).map fun b =>
    shrOutSym b (shrMaskSym ((shrY A x).getLast?.getD blank) (x.getLast?.getD blank))

/-- **Shrinking a word.** For a coefficient `z` fitting `w'` bits, the shrunk word of its `w'`-bit
word is the `w'`-bit word of `shrinkZ 1 z`. -/
theorem shrF_coeffSyms (hA : 4 ≤ A) {w' : ℕ} (hw' : 1 ≤ w') (z : GaussianInt)
    (hz : TopFitsZ w' z) :
    shrF A (coeffSyms A w' (red w' z)) = coeffSyms A w' (red w' (shrinkZ 1 z)) := by
  have hre : (coeffSyms A w' (red w' z)).map pairRe =
      List.ofFn fun t : Fin w' => (z.re : ZMod (2 ^ w')).val.testBit t := by
    simp [coeffSyms, red, List.map_ofFn, Function.comp_def, pairRe_pairSym hA]
  have him : (coeffSyms A w' (red w' z)).map pairIm =
      List.ofFn fun t : Fin w' => (z.im : ZMod (2 ^ w')).val.testBit t := by
    simp [coeffSyms, red, List.map_ofFn, Function.comp_def, pairIm_pairSym hA]
  have hY : shrY A (coeffSyms A w' (red w' z)) = List.ofFn fun t : Fin w' =>
      pairSym A (((shrT z.re : ℤ) : ZMod (2 ^ w')).val.testBit t)
        (((shrT z.im : ℤ) : ZMod (2 ^ w')).val.testBit t) := by
    simp only [shrY, topLast_coeffSyms hw' z hz, pairRe_pairSym hA, pairIm_pairSym hA, hre, him,
      shrSum_bits (x := z.re), shrSum_bits (x := z.im)]
    apply List.ext_getElem
    · simp
    · intro t h1 h2
      simp
  have hL : (shrY A (coeffSyms A w' (red w' z))).getLast?.getD blank =
      pairSym A (decide (shrT z.re < 0)) (decide (shrT z.im < 0)) := by
    rw [hY, List.getLast?_eq_getElem?, List.getElem?_ofFn]
    simp only [List.length_ofFn, show w' - 1 < w' by omega, dite_true, Option.getD_some]
    rw [topVal_sign hw' (shrT_fits hz.1), topVal_sign hw' (shrT_fits hz.2)]
  rw [shrF, hL, topLast_coeffSyms hw' z hz, hY]
  apply List.ext_getElem
  · simp [coeffSyms]
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, coeffSyms, red, shrinkZ, shrOutSym,
      shrMaskSym, pairRe_pairSym hA, pairIm_pairSym hA]
    rw [shrinkI_one_eq, shrinkI_one_eq]
    cases xor (decide (shrT z.re < 0)) (decide (z.re < 0)) <;>
      cases xor (decide (shrT z.im < 0)) (decide (z.im < 0)) <;> simp

end Words

/-! ### Shrinking by one: the machine -/

section Machine

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Copy the top of `tmp` (the sign pair) onto `sg` and, as a pair, onto `cy`. -/
def shrSignAct (tmp sg cy : Fin T) : Act T Q A U :=
  .peek (.rt tmp) (fun v o => { v with sym := o })
    (.push (.rt sg) (fun v => v.sym.getD blank)
      (.push (.rt cy) (fun v => pairSym A (pairRe (v.sym.getD blank)) (pairIm (v.sym.getD blank)))
        .done))

/-- The sum pair of `b`, the constant pair `¬σ` and the carry pair `c`. -/
def shrSumSym (b σ c : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (xor (xor (pairRe b) (!pairRe σ)) (pairRe c)) (xor (xor (pairIm b) (!pairIm σ)) (pairIm c))

/-- The carry pair of `b`, the constant pair `¬σ` and the carry pair `c`. -/
def shrCarSym (b σ c : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (topMaj (pairRe b) (!pairRe σ) (pairRe c)) (topMaj (pairIm b) (!pairIm σ) (pairIm c))

/-- Add the top of `src` to the constant `¬σ` (`σ` on `sg`) and the carry on `cy`, pushing the
sum onto `tmp`. -/
def shrAddF (src tmp sg cy : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.pop (.rt cy) (fun v o => { v with scan := Function.update v.scan cy (o.getD blank) })
      (.peek (.rt sg) (fun v o => { v with scan := Function.update v.scan sg (o.getD blank) })
        (.push (.rt tmp) (fun v => shrSumSym (v.sym.getD blank) (v.scan sg) (v.scan cy))
          (.push (.rt cy) (fun v => shrCarSym (v.sym.getD blank) (v.scan sg) (v.scan cy)) k))))

/-- The effect of `shrAddF`. -/
def shrAddFx (src tmp sg cy : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update (Function.update R src (R src).tail) cy
      (shrCarSym ((R src).head?.getD blank) ((R sg).head?.getD blank) ((R cy).head?.getD blank) ::
        (R cy).tail)) tmp
    (shrSumSym ((R src).head?.getD blank) ((R sg).head?.getD blank) ((R cy).head?.getD blank) ::
      R tmp)

/-- Replace the sign pair on `sg` by the mask pair against the top of `tmp`; drop `cy`. -/
def shrMaskAct (tmp sg cy : Fin T) : Act T Q A U :=
  .peek (.rt tmp) (fun v o => { v with sym := o })
    (.pop (.rt sg) (fun v o => { v with scan := Function.update v.scan sg (o.getD blank) })
      (.pop (.rt cy) (fun v _ => v)
        (.push (.rt sg) (fun v => shrMaskSym (v.sym.getD blank) (v.scan sg)) .done)))

/-- Emit the top of `src` with the mask on `sg` applied onto `dst`. -/
def shrOutF (src dst sg : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.peek (.rt sg) (fun v o => { v with scan := Function.update v.scan sg (o.getD blank) })
      (.push (.rt dst) (fun v => shrOutSym (v.sym.getD blank) (v.scan sg)) k))

/-- The effect of `shrOutF`. -/
def shrOutFx (src dst sg : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update R src (R src).tail) dst
    (shrOutSym ((R src).head?.getD blank) ((R sg).head?.getD blank) :: R dst)

/-- Drop `sg` and record in `flag` whether `src` is nonempty. -/
def shrEndAct (sg src : Fin T) : Act T Q A U := .pop (.rt sg) (fun v _ => v) (peekR src)

lemma regFx_shrAdd {src tmp sg cy : Fin T} (hst : src ≠ tmp) (hsc : src ≠ cy) (hsg : src ≠ sg)
    (htc : tmp ≠ cy) (hgc : sg ≠ cy) :
    RegFx (shrAddF (T := T) (Q := Q) (A := A) (U := U) src tmp sg cy) (shrAddFx src tmp sg cy) := by
  intro x k v S _
  refine ⟨{ v with
    sym := (S.R src).head?
    scan := Function.update (Function.update v.scan cy ((S.R cy).head?.getD blank)) sg
      ((S.R sg).head?.getD blank) }, rfl, ?_⟩
  simp only [shrAddF, shrAddFx, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk,
    Function.update_of_ne hsc.symm, Function.update_of_ne hsg.symm, Function.update_of_ne hgc,
    Function.update_of_ne hgc.symm, Function.update_of_ne hst.symm, Function.update_of_ne htc,
    Function.update_of_ne htc.symm, Function.update_self]
  rw [Function.update_comm htc, Function.update_idem]

lemma frame_shrAdd {a src tmp sg cy : Fin T} (has : a ≠ src) (hat : a ≠ tmp) (hag : a ≠ sg)
    (hac : a ≠ cy) : Frame a (shrAddFx (A := A) src tmp sg cy) := by
  intro x R l
  funext k
  simp only [shrAddFx, Function.update_apply]
  split_ifs <;> simp_all

lemma regFx_shrOut {src dst sg : Fin T} (hsd : src ≠ dst) (hsg : src ≠ sg) :
    RegFx (shrOutF (T := T) (Q := Q) (A := A) (U := U) src dst sg) (shrOutFx src dst sg) := by
  intro x k v S _
  refine ⟨{ v with
    sym := (S.R src).head?
    scan := Function.update v.scan sg ((S.R sg).head?.getD blank) }, rfl, ?_⟩
  simp only [shrOutF, shrOutFx, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk,
    Function.update_of_ne hsg.symm, Function.update_of_ne hsd.symm, Function.update_self]

lemma frame_shrOut {a src dst sg : Fin T} (has : a ≠ src) (had : a ≠ dst) (hag : a ≠ sg) :
    Frame a (shrOutFx (A := A) src dst sg) := by
  intro x R l
  funext k
  simp only [shrOutFx, Function.update_apply]
  split_ifs <;> simp_all

lemma foldl_shrAdd (hA : 4 ≤ A) {src tmp sg cy : Fin T} (hst : src ≠ tmp) (hsc : src ≠ cy)
    (hsg : src ≠ sg) (htc : tmp ≠ cy) (htg : tmp ≠ sg) (hgc : sg ≠ cy) (σ : Fin (A + 4)) :
    ∀ (l x rest : List (Fin (A + 4))) (R : Regs T A) (cr ci : Bool), l.length = x.length →
      R src = x ++ rest → R cy = [pairSym A cr ci] → R sg = [σ] →
      l.foldl (fun R a => shrAddFx src tmp sg cy a R) R =
        Function.update (Function.update (Function.update R src rest) cy
          [pairSym A (shrCar (!pairRe σ) cr (x.map pairRe)) (shrCar (!pairIm σ) ci (x.map pairIm))])
          tmp ((List.zipWith (pairSym A) (shrSum (!pairRe σ) cr (x.map pairRe))
            (shrSum (!pairIm σ) ci (x.map pairIm))).reverse ++ R tmp)
  | [], x, rest, R, cr, ci, hl, hs, hc, _ => by
      obtain rfl : x = [] := List.eq_nil_of_length_eq_zero hl.symm
      funext k
      simp only [List.nil_append] at hs
      simp only [List.foldl_nil, Function.update_apply]
      split_ifs with h1 h2 h3 <;> simp_all [shrSum, shrCar]
  | a :: l, e :: x, rest, R, cr, ci, hl, hs, hc, hg => by
      simp only [List.foldl_cons]
      rw [foldl_shrAdd hA hst hsc hsg htc htg hgc σ l x rest _
        (topMaj (pairRe e) (!pairRe σ) cr) (topMaj (pairIm e) (!pairIm σ) ci) (by simpa using hl)
        (by simp [shrAddFx, Function.update_of_ne hsc, Function.update_of_ne hst, hs])
        (by simp [shrAddFx, Function.update_of_ne htc.symm, hs, hc, hg, shrCarSym,
          pairRe_pairSym hA, pairIm_pairSym hA])
        (by simp [shrAddFx, Function.update_of_ne hsg.symm, Function.update_of_ne hgc,
          Function.update_of_ne htg.symm, hg])]
      funext k
      simp only [shrAddFx, Function.update_apply]
      split_ifs <;> simp_all [shrSum, shrCar, shrSumSym, pairRe_pairSym hA, pairIm_pairSym hA]
  | _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl

lemma foldl_shrOut {src dst sg : Fin T} (hsd : src ≠ dst) (hsg : src ≠ sg) (hdg : dst ≠ sg)
    (m : Fin (A + 4)) :
    ∀ (l x rest : List (Fin (A + 4))) (R : Regs T A), l.length = x.length →
      R src = x ++ rest → R sg = [m] →
      l.foldl (fun R a => shrOutFx src dst sg a R) R =
        Function.update (Function.update R src rest) dst
          ((x.map fun b => shrOutSym b m).reverse ++ R dst)
  | [], x, rest, R, hl, hs, _ => by
      obtain rfl : x = [] := List.eq_nil_of_length_eq_zero hl.symm
      funext k
      simp only [List.nil_append] at hs
      simp only [List.foldl_nil, Function.update_apply]
      split_ifs with h1 h2 <;> simp_all
  | a :: l, e :: x, rest, R, hl, hs, hg => by
      simp only [List.foldl_cons]
      rw [foldl_shrOut hsd hsg hdg m l x rest _ (by simpa using hl)
        (by simp [shrOutFx, Function.update_of_ne hsd, hs])
        (by simp [shrOutFx, Function.update_of_ne hsg.symm, Function.update_of_ne hdg.symm, hg])]
      funext k
      simp only [shrOutFx, Function.update_apply]
      split_ifs <;> simp_all
  | _ :: _, [], _, _, hl, _, _ => by simp at hl

end Machine

/-! ### Shrinking by one: the word program -/

section WordProg

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Shrink one word of `|cW|` symbols: copy it onto `tmp` and back (the sign pair onto `sg` and
`cy`), add it onto `tmp`, form the mask on `sg`, move the sum back, emit it masked onto `dst`, drop
`sg` and record in `flag` whether `src` is nonempty (spare `sp`). -/
def shrWord (src dst tmp cW sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (Shift.counted cW sp (Shift.copyStep cW sp src tmp))
  (.seq (.act (shrSignAct tmp sg cy))
  (.seq (Shift.counted cW sp (Shift.copyStep cW sp tmp src))
  (.seq (scanR cW sp (shrAddF src tmp sg cy))
  (.seq (.act (shrMaskAct tmp sg cy))
  (.seq (Shift.counted cW sp (Shift.copyStep cW sp tmp src))
  (.seq (scanR cW sp (shrOutF src dst sg))
    (.act (shrEndAct sg src))))))))

/-- The registers of the shrink pass: `cW` holds `w'` symbols, `sp`, `sg`, `cy`, `tmp` empty. -/
def shrG (tmp cW sp sg cy : Fin T) (w' : ℕ) (R : Regs T A) : Prop :=
  (R cW).length = w' ∧ R sp = [] ∧ R sg = [] ∧ R cy = [] ∧ R tmp = []

/-- The step count of one shrunk word. -/
def shrWordCost (w' : ℕ) : ℕ :=
  (4 * w' + 4) + (1 + ((4 * w' + 4) + ((4 * w' + 4) + (1 + ((4 * w' + 4) + ((4 * w' + 4) + 1))))))

theorem shrWord_spec (hA : 4 ≤ A) {src dst tmp cW sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, sp, sg, cy].Nodup) {w' : ℕ} (hw' : 1 ≤ w') :
    TopWordSpec body (shrWord src dst tmp cW sp sg cy) src dst (shrG tmp cW sp sg cy w') w'
      (shrF A) (shrWordCost w') := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg'
  obtain ⟨⟨hsd, hst, hsW, hsp, hsg, hsc⟩, ⟨hdt, hdW, hdp, hdg, hdc⟩, ⟨htW, htp, htg, htc⟩,
    ⟨hWp, hWg, hWc⟩, ⟨hpg, hpc⟩, hgc⟩ := hreg'
  intro x rest v S hx hs ⟨hcW, hsp0, hsg0, hcy0, htmp0⟩
  have hne : x ≠ [] := by rintro rfl; simp at hx; omega
  -- onto `tmp`
  obtain ⟨v₁, hv₁, e₁⟩ := topCopyC_exec body (c := cW) (t := sp) (src := src) (dst := tmp)
    (by simp [hWp, Ne.symm hsW, Ne.symm htW, Ne.symm hsp, Ne.symm htp, hst]) x rest v S
    (by rw [hcW, hx]) hs hsp0
  set R₁ := Function.update (Function.update S.R src rest) tmp (x.reverse ++ S.R tmp) with hR₁
  -- the sign
  set σ := x.getLast hne with hσ
  have e₂ := Exec.act (body := body) (shrSignAct tmp sg cy : Act T Q A U) (mk v₁ { S with R := R₁ })
  have hR₁t : R₁ tmp = x.reverse := by simp [hR₁, htmp0]
  have hR₁g : R₁ sg = [] := by
    simp [hR₁, Function.update_of_ne (Ne.symm hsg), Function.update_of_ne (Ne.symm htg), hsg0]
  have hR₁c : R₁ cy = [] := by
    simp [hR₁, Function.update_of_ne (Ne.symm hsc), Function.update_of_ne (Ne.symm htc), hcy0]
  simp only [shrSignAct, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, hR₁t,
    List.head?_reverse, List.getLast?_eq_some_getLast hne, Option.getD_some, hR₁g, hR₁c,
    Function.update_of_ne (Ne.symm hgc)] at e₂
  set R₂ := Function.update (Function.update R₁ sg [σ]) cy [pairSym A (pairRe σ) (pairIm σ)]
    with hR₂
  -- back onto `src`
  obtain ⟨v₃, hv₃, e₃⟩ := topCopyC_exec body (c := cW) (t := sp) (src := tmp) (dst := src)
    (by simp [hWp, Ne.symm htW, Ne.symm hsW, Ne.symm htp, Ne.symm hsp, Ne.symm hst]) x.reverse []
    _ { S with R := R₂ }
    (by simp [hR₂, hR₁, Function.update_of_ne hWg, Function.update_of_ne hWc,
      Function.update_of_ne (Ne.symm hsW), Function.update_of_ne (Ne.symm htW), hcW, hx])
    (by simp [hR₂, Function.update_of_ne htg, Function.update_of_ne htc, hR₁t])
    (by simp [hR₂, hR₁, Function.update_of_ne hpg, Function.update_of_ne hpc,
      Function.update_of_ne (Ne.symm hsp), Function.update_of_ne (Ne.symm htp), hsp0])
  rw [List.length_reverse, List.reverse_reverse] at e₃
  set R₃ := Function.update (Function.update R₂ tmp []) src (x ++ R₂ src) with hR₃
  have hR₃s : R₃ src = x ++ rest := by
    simp [hR₃, hR₂, hR₁, Function.update_of_ne hsc, Function.update_of_ne hsg,
      Function.update_of_ne hst]
  have hR₃c : R₃ cy = [pairSym A (pairRe σ) (pairIm σ)] := by
    simp [hR₃, hR₂, Function.update_of_ne (Ne.symm hsc), Function.update_of_ne (Ne.symm htc)]
  have hR₃g : R₃ sg = [σ] := by
    simp [hR₃, hR₂, Function.update_of_ne (Ne.symm hsg), Function.update_of_ne (Ne.symm htg),
      Function.update_of_ne hgc]
  have hR₃t : R₃ tmp = [] := by
    rw [hR₃, Function.update_of_ne (Ne.symm hst), Function.update_self]
  have hR₃o : ∀ k, k ≠ src → k ≠ tmp → k ≠ sg → k ≠ cy → R₃ k = S.R k := by
    intro k h1 h2 h3 h4
    simp [hR₃, hR₂, hR₁, h1, h2, h3, h4]
  have hR₃W : R₃ cW = S.R cW := hR₃o _ (Ne.symm hsW) (Ne.symm htW) hWg hWc
  -- add
  obtain ⟨v₄, hu₄, e₄⟩ := scanR_exec' body hWp (regFx_shrAdd hst hsc hsg htc hgc)
    (frame_shrAdd (Ne.symm hsW) (Ne.symm htW) hWg hWc)
    (frame_shrAdd (Ne.symm hsp) (Ne.symm htp) hpg hpc) v₃ { S with R := R₃ }
    (by show R₃ sp = []; rw [hR₃o _ (Ne.symm hsp) (Ne.symm htp) hpg hpc]; exact hsp0)
  dsimp only at e₄
  rw [foldl_shrAdd hA hst hsc hsg htc htg hgc σ (R₃ cW) x rest R₃ _ _
    (by rw [hR₃W, hcW, hx]) hR₃s hR₃c hR₃g, hR₃W, hcW] at e₄
  set y := List.zipWith (pairSym A) (shrSum (!pairRe σ) (pairRe σ) (x.map pairRe))
    (shrSum (!pairIm σ) (pairIm σ) (x.map pairIm)) with hy
  have hyl : y.length = w' := by simp [hy, shrSum_length, hx]
  have hyne : y ≠ [] := by rintro h; rw [h] at hyl; simp at hyl; omega
  set R₄ := Function.update (Function.update (Function.update R₃ src rest) cy
    [pairSym A (shrCar (!pairRe σ) (pairRe σ) (x.map pairRe))
      (shrCar (!pairIm σ) (pairIm σ) (x.map pairIm))]) tmp (y.reverse ++ R₃ tmp) with hR₄
  -- the mask
  have e₅ := Exec.act (body := body) (shrMaskAct tmp sg cy : Act T Q A U) (mk v₄ { S with R := R₄ })
  have hR₄t : R₄ tmp = y.reverse := by rw [hR₄, Function.update_self, hR₃t, List.append_nil]
  have hR₄g : R₄ sg = [σ] := by
    rw [hR₄, Function.update_of_ne (Ne.symm htg), Function.update_of_ne hgc,
      Function.update_of_ne (Ne.symm hsg), hR₃g]
  have hR₄c : R₄ cy = [pairSym A (shrCar (!pairRe σ) (pairRe σ) (x.map pairRe))
      (shrCar (!pairIm σ) (pairIm σ) (x.map pairIm))] := by
    rw [hR₄, Function.update_of_ne (Ne.symm htc), Function.update_self]
  simp only [shrMaskAct, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, hR₄t,
    List.head?_reverse, List.getLast?_eq_some_getLast hyne, Option.getD_some, hR₄g, hR₄c,
    Function.update_of_ne hgc, Function.update_of_ne (Ne.symm hgc), Function.update_self,
    List.tail_cons] at e₅
  have hlast : y.getLast?.getD blank = y.getLast hyne := by
    rw [List.getLast?_eq_some_getLast hyne]; rfl
  set mk' := shrMaskSym (y.getLast?.getD blank) σ with hmk
  set R₅ := Function.update (Function.update R₄ sg []) cy [] with hR₅
  have e₅' : Exec body (.act (shrMaskAct tmp sg cy)) (mk v₄ { S with R := R₄ }) 1
      (mk { v₄ with sym := some (y.getLast hyne), scan := Function.update v₄.scan sg σ }
        { S with R := Function.update R₅ sg [mk'] }) := by
    refine Exec.cast e₅ rfl ?_
    rw [hmk, hlast]
    rfl
  -- back onto `src`
  obtain ⟨v₆, hv₆, e₆⟩ := topCopyC_exec body (c := cW) (t := sp) (src := tmp) (dst := src)
    (by simp [hWp, Ne.symm htW, Ne.symm hsW, Ne.symm htp, Ne.symm hsp, Ne.symm hst]) y.reverse []
    _ { S with R := Function.update R₅ sg [mk'] }
    (by simp [hR₅, hR₄, Function.update_of_ne hWg, Function.update_of_ne hWc,
      Function.update_of_ne (Ne.symm hsW), Function.update_of_ne (Ne.symm htW), hR₃W, hcW, hyl])
    (by simp [hR₅, Function.update_of_ne htg, Function.update_of_ne htc, hR₄t])
    (by simp [hR₅, hR₄, Function.update_of_ne hpg, Function.update_of_ne hpc,
      Function.update_of_ne (Ne.symm hsp), Function.update_of_ne (Ne.symm htp),
      hR₃o _ (Ne.symm hsp) (Ne.symm htp) hpg hpc, hsp0])
  rw [List.length_reverse, List.reverse_reverse] at e₆
  set R₆ := Function.update (Function.update (Function.update R₅ sg [mk']) tmp []) src
    (y ++ Function.update R₅ sg [mk'] src) with hR₆
  have hR₆s : R₆ src = y ++ rest := by
    simp [hR₆, hR₅, hR₄, Function.update_of_ne hsc, Function.update_of_ne hsg,
      Function.update_of_ne hst]
  have hR₆g : R₆ sg = [mk'] := by
    simp [hR₆, Function.update_of_ne (Ne.symm hsg), Function.update_of_ne (Ne.symm htg)]
  have hR₆o : ∀ k, k ≠ src → k ≠ tmp → k ≠ sg → k ≠ cy → R₆ k = S.R k := by
    intro k h1 h2 h3 h4
    simp [hR₆, hR₅, hR₄, h1, h2, h3, h4, hR₃o k h1 h2 h3 h4]
  have hR₆W : R₆ cW = S.R cW := hR₆o _ (Ne.symm hsW) (Ne.symm htW) hWg hWc
  -- emit
  obtain ⟨v₇, hu₇, e₇⟩ := scanR_exec' body hWp (regFx_shrOut hsd hsg)
    (frame_shrOut (Ne.symm hsW) (Ne.symm hdW) hWg) (frame_shrOut (Ne.symm hsp) (Ne.symm hdp) hpg)
    v₆ { S with R := R₆ }
    (by show R₆ sp = []; rw [hR₆o _ (Ne.symm hsp) (Ne.symm htp) hpg hpc]; exact hsp0)
  dsimp only at e₇
  rw [foldl_shrOut hsd hsg hdg mk' (R₆ cW) y rest R₆ (by rw [hR₆W, hcW, hyl]) hR₆s hR₆g, hR₆W,
    hcW] at e₇
  set R₇ := Function.update (Function.update R₆ src rest) dst
    ((y.map fun b => shrOutSym b mk').reverse ++ R₆ dst) with hR₇
  -- drop the mask
  have e₈ := Exec.act (body := body) (shrEndAct sg src : Act T Q A U) (mk v₇ { S with R := R₇ })
  have hrun : (shrEndAct sg src : Act T Q A U).run (mk v₇ { S with R := R₇ }) =
      mk { v₇ with flag := rest.head?.isSome }
        { S with R := Function.update R₇ sg [] } := by
    have hR₇s : R₇ src = rest := by rw [hR₇, Function.update_of_ne hsd, Function.update_self]
    have hR₇g : R₇ sg = [mk'] := by
      rw [hR₇, Function.update_of_ne (Ne.symm hdg), Function.update_of_ne (Ne.symm hsg), hR₆g]
    simp [shrEndAct, peekR, Action.run, update_rt, hR₇g, Function.update_of_ne hsg, hR₇s]
  rw [hrun] at e₈
  have houtF : y.map (fun b => shrOutSym b mk') = shrF A x := by
    simp only [hmk, hy, hσ, shrF, shrY, List.getLast?_eq_some_getLast hne, Option.getD_some]
  refine ⟨{ v₇ with flag := rest.head?.isSome }, by rw [hu₇, hv₆.user, hu₄, hv₃.user, hv₁.user],
    rfl, Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅'
      (Exec.seq e₆ (Exec.seq e₇ e₈))))))) (by rw [hx, hyl]; simp [shrWordCost]) ?_⟩
  congr 2
  funext k
  by_cases hk3 : k = sg
  · subst hk3
    rw [Function.update_self, Function.update_of_ne (Ne.symm hdg),
      Function.update_of_ne (Ne.symm hsg), hsg0]
  rw [Function.update_of_ne hk3]
  by_cases hk1 : k = src
  · subst hk1; rw [hR₇, Function.update_of_ne hsd, Function.update_self, Function.update_of_ne hsd,
      Function.update_self]
  by_cases hk2 : k = dst
  · subst hk2
    rw [hR₇, Function.update_self, Function.update_self, houtF,
      hR₆o _ (Ne.symm hsd) hdt hdg hdc]
  rw [hR₇, Function.update_of_ne hk2, Function.update_of_ne hk1, Function.update_of_ne hk2,
    Function.update_of_ne hk1]
  by_cases hk5 : k = tmp
  · subst hk5
    rw [hR₆, Function.update_of_ne hk1, Function.update_self, htmp0]
  by_cases hk4 : k = cy
  · subst hk4
    rw [hR₆, Function.update_of_ne hk1, Function.update_of_ne hk5, Function.update_of_ne hk3,
      hR₅, Function.update_self, hcy0]
  exact hR₆o k hk1 hk5 hk3 hk4

end WordProg

/-! ### Shrinking a stream -/

section Pass

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- The step bound of the shrink pass. -/
def shrinkCost (R n r w' : ℕ) : ℕ :=
  1 + (R * 2 ^ n * r * (shrWordCost w' + 1) + 1) + (2 * (R * 2 ^ n * r * w') + 2)

lemma topFitsZ_shrinkZ_one {w' : ℕ} {z : GaussianInt} (hz : TopFitsZ w' z) :
    TopFitsZ w' (shrinkZ 1 z) := by
  have hpos : (0 : ℤ) < 2 ^ (w' - 1) := by positivity
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  unfold TopFitsZ TopFits shrinkZ shrinkI
  simp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> split_ifs <;> omega

/-- **Shrinking by one** (`shrinkP_exec`). `src` holding the `w'`-bit stream of an array whose
coefficients fit `w'` signed bits ends holding the stream of `shrinkZ 1` of every coefficient,
`cW` holding `w'` symbols and `dst`, `tmp`, `sp`, `sg`, `cy` empty; every other register ends as it
started. -/
theorem shrinkP_exec (hA : 4 ≤ A) {src dst tmp cW sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, sp, sg, cy].Nodup) {R r n w' : ℕ} (hw' : 1 ≤ w')
    (Z : ZArr (Fin R × Fin r) n) (hZ : ∀ p, TopFitsZ w' (Z p)) (v : HS T Q A U)
    (S : Stacks T A) (hs : S.R src = encZ A w' Z) (hd : S.R dst = [])
    (hg : shrG tmp cW sp sg cy w' S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (topPass src dst (shrWord src dst tmp cW sp sg cy)) (mk v S)
        (shrinkCost R n r w')
        (mk v' { S with R := Function.update S.R src (encZ A w' (fun p => shrinkZ 1 (Z p))) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg'
  obtain ⟨⟨hsd, hst, hsW, hsp, hsg, hsc⟩, ⟨hdt, hdW, hdp, hdg, hdc⟩, -, -, -, -⟩ := hreg'
  have hG : TopWordFrame src dst (shrG tmp cW sp sg cy (A := A) w') := by
    intro R l l' ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Ne.symm hst, Ne.symm hsW, Ne.symm hsp, Ne.symm hsg, Ne.symm hsc, Ne.symm hdt,
        Ne.symm hdW, Ne.symm hdp, Ne.symm hdg, Ne.symm hdc]
  have hmap : ((cellList R r n).map fun p => coeffSyms A w' (red w' (Z p))).map (shrF A) =
      (cellList R r n).map fun p => coeffSyms A w' (red w' (shrinkZ 1 (Z p))) := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => shrF_coeffSyms hA hw' (Z p) (hZ p)
  obtain ⟨v', hu, he⟩ := topPass_exec body hsd hG hw' (shrWord_spec body hA hreg hw')
    ((cellList R r n).map fun p => coeffSyms A w' (red w' (Z p))) v S
    (fun x hx => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
      simp) (by rw [hs, topEnc_words]) hd hg
  rw [hmap, ← topEnc_words (Z := fun p => shrinkZ 1 (Z p)), topEnc_length] at he
  refine ⟨v', hu, Exec.cast he ?_ rfl⟩
  simp [shrinkCost, length_cellList]

end Pass

end IntegerMultBounds.MathlibTM2.Node
