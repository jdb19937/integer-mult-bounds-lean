module

public import IntegerMultBounds.MathlibTM2.Node.SlotXor
public import IntegerMultBounds.MathlibTM2.Node.CompactFix

/-!
# The full slot XOR of the field model on the record stream

`fullXorC len X Y K ρ n` (`IntegerMultBounds.MathlibTM2.Layer.CompactXor`) XORs the bits
`ρ, ρ + K, …, ρ + nK` of field `X` into the same bits of field `Y`, keeping every other field.
It is the ideal map `idealC` at `n + 1` positions (`fullXorC_eq_idealC`), hence an involution of
the indices below `R · 2^S` whenever field `Y` lies below bit `S` (`fullXorPermC`).

**Addresses.** With the records of an array `Z` over `R` rows and `n` address bits listed in
address order (row `u`, address `a` at position `2^n u + a`), and the fields `X`, `Y` holding the
`L = K k` bits of the slots `x`, `y` at `a₀ + x L`, `a₀ + y L`, with the column bits of the slots
at `e (bitIdx j c) = a₀ + ρ + K (c + k j)`, the full XOR at `k` positions moves the index
`2^n u + a` to `2^n u + addrNum (sxMap e x y) a` (`fullXorC_addr`): the slot map `sxMap` adds
column `c` of slot `x` to column `c` of slot `y`, which on bits is the XOR of the bit
`a₀ + x L + ρ + c K` into the bit `a₀ + y L + ρ + c K`.

**Streams.** Moving the records by `fullXorPermC` therefore turns the stream of `Z` into the
stream of `pullM e (sxXorCol x y) Z` (`moveRecs_fullXorPermC`), the field-model form of
`sx_moveRecs_xorSel`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer.CompactXor
open IntegerMultBounds.MathlibTM2.Layer (m ZArr encZ recList addrBits addrNum pullAddr pullM bitIdx)
open IntegerMultBounds.MathlibTM2.Layer.PackedXor (selMask IsSel testBit_selMask selMask_false)

set_option linter.unusedSimpArgs false

/-! ### The full XOR as a permutation of indices -/

section FullXorPerm

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- The full XOR at `n + 1` positions is the ideal map at `n + 1` positions. -/
lemma fullXorC_eq_idealC (X Y : Fin nf) (K ρ n i : ℕ) :
    fullXorC len X Y K ρ n i = idealC len X Y K ρ (n + 1) i := rfl

lemma dig_fullXorC_Y {X Y : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (i : ℕ) :
    dig len Y (fullXorC len X Y K ρ n i) =
      dig len Y i ^^^ (dig len X i &&& selMask K ρ (n + 1)) := by
  rw [fullXorC_eq_idealC]; exact dig_idealC_Y len hLXY i

lemma dig_fullXorC_ne {X Y f : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (hf : f ≠ Y) (i : ℕ) :
    dig len f (fullXorC len X Y K ρ n i) = dig len f i := by
  rw [fullXorC_eq_idealC]; exact dig_idealC_ne len hLXY hf i

lemma fullXorC_fullXorC {X Y : Fin nf} {K ρ n : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y) (i : ℕ) :
    fullXorC len X Y K ρ n (fullXorC len X Y K ρ n i) = i := by
  rw [fullXorC_eq_idealC, fullXorC_eq_idealC]; exact idealC_idealC len hXY hLXY i

lemma fullXorC_lt {X Y : Fin nf} {K ρ n R S : ℕ} (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) {i : ℕ} (hi : i < R * 2 ^ S) :
    fullXorC len X Y K ρ n i < R * 2 ^ S := by
  rw [fullXorC_eq_idealC]; exact idealC_lt len hLXY hSY hi

/-- The full XOR as a permutation of the indices below `R · 2^S`. -/
def fullXorPermC (X Y : Fin nf) (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) : Equiv.Perm (Fin (R * 2 ^ S)) where
  toFun i := ⟨fullXorC len X Y K ρ n i, fullXorC_lt len hLXY hSY i.isLt⟩
  invFun i := ⟨fullXorC len X Y K ρ n i, fullXorC_lt len hLXY hSY i.isLt⟩
  left_inv i := Fin.ext (fullXorC_fullXorC len hXY hLXY i)
  right_inv i := Fin.ext (fullXorC_fullXorC len hXY hLXY i)

lemma fullXorPermC_apply (X Y : Fin nf) (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y)
    (hLXY : len X = len Y) (hSY : foff len Y + len Y ≤ S) (i : Fin (R * 2 ^ S)) :
    (fullXorPermC len X Y K ρ n hXY hLXY hSY i : ℕ) = fullXorC len X Y K ρ n i := rfl

lemma fullXorPermC_symm (X Y : Fin nf) (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y)
    (hLXY : len X = len Y) (hSY : foff len Y + len Y ≤ S) :
    (fullXorPermC len X Y K ρ n hXY hLXY hSY (R := R)).symm =
      fullXorPermC len X Y K ρ n hXY hLXY hSY := rfl

end FullXorPerm

/-! ### The full XOR on record indices -/

section Identity

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- **The full XOR on indices.** With field `X` holding slot `x` and field `Y` holding slot `y`
(each of `L = K k` bits at `a₀ + (slot) L`) and the column bits at `e`, the full XOR at the `k`
positions `ρ + c K` moves the index `2^n u + a` to `2^n u + addrNum (sxMap e x y) a`. -/
theorem fullXorC_addr {n k a₀ K ρ L : ℕ} {x y : Fin m} {e : Fin (m * k) → Fin n} {X Y : Fin nf}
    (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k)
    (hfX : foff len X = a₀ + x * L) (hLX : len X = L)
    (hfY : foff len Y = a₀ + y * L) (hLY : len Y = L) (hSY : foff len Y + len Y ≤ n)
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (j : ℕ) :
    fullXorC len X Y K ρ (k - 1) j = 2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) := by
  have hK : 0 < K := by omega
  have hLXY : len X = len Y := by rw [hLX, hLY]
  have heinj : Function.Injective e := fun i i' h => by
    have := congrArg Fin.val h; rw [he, he] at this
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hK (by omega))
  set P := a₀ + (y : ℕ) * L with hP
  set Px := a₀ + (x : ℕ) * L with hPx
  have hPfit : P + L ≤ n := by rw [hfY, hLY] at hSY; exact hSY
  have hk1 : k - 1 + 1 = k := by omega
  have hmask : dig len Y j ^^^ (dig len X j &&& selMask K ρ k) < 2 ^ len Y :=
    idealC_mask_lt len (K := K) (ρ := ρ) (n := k) hLXY j
  have hey : ∀ c : Fin k, ((e (bitIdx y c) : Fin n) : ℕ) = P + (ρ + c * K) := fun c => by
    rw [he, bitIdx, finProdFinEquiv_apply_val, hP, hLK]; ring
  have hex : ∀ c : Fin k, ((e (bitIdx x c) : Fin n) : ℕ) = Px + (ρ + c * K) := fun c => by
    rw [he, bitIdx, finProdFinEquiv_apply_val, hPx, hLK]; ring
  have hbit : ∀ t' (h : t' < n), addrBits n (j % 2 ^ n) ⟨t', h⟩ =
      if j.testBit t' then 1 else 0 := fun t' h => by
    simp [addrBits, Nat.testBit_mod_two_pow, h]
  unfold fullXorC
  rw [hk1]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_setDig len Y j hmask, hfY, hLY,
    Nat.testBit_two_pow_mul_add _ (IntegerMultBounds.MathlibTM2.Layer.addrNum_lt _ _)]
  by_cases htn : t < n
  · rw [if_pos htn, sx_testBit_addrNum _ _ _ htn]
    by_cases hin : P ≤ t ∧ t < P + L
    · rw [if_pos hin]
      set i := t - P with hi
      have hiL : i < L := by omega
      have htP : t = P + i := by omega
      rw [Nat.testBit_xor, Nat.testBit_and, testBit_dig len Y j (by rw [hLY]; exact hiL),
        testBit_dig len X j (by rw [hLX]; exact hiL), hfY, hfX]
      by_cases hsel : IsSel K ρ k i
      · obtain ⟨c, hc, hci⟩ := hsel
        have hsel' : (selMask K ρ k).testBit i = true := (testBit_selMask K ρ k i).2 ⟨c, hc, hci⟩
        rw [hsel', Bool.and_true]
        have hyc : e (bitIdx y ⟨c, hc⟩) = ⟨t, htn⟩ := Fin.ext (by rw [hey]; simp [htP, hci])
        rw [← hyc, sxMap_apply_y heinj x y]
        have hx1 : (e (bitIdx x ⟨c, hc⟩) : ℕ) < n := (e _).isLt
        rw [show e (bitIdx y ⟨c, hc⟩) = ⟨_, (e (bitIdx y ⟨c, hc⟩)).isLt⟩ from rfl,
          show e (bitIdx x ⟨c, hc⟩) = ⟨_, hx1⟩ from rfl, hbit, hbit, sx_zmod2_ite_add, hey, hex]
        simp [hci]
      · have hsel' : (selMask K ρ k).testBit i = false := selMask_false K ρ k hsel
        rw [hsel', Bool.and_false, Bool.xor_false]
        rw [sxMap_apply_ne heinj x y _ _ (fun c hc => by
          apply hsel
          refine ⟨c, c.isLt, ?_⟩
          have := congrArg Fin.val hc
          rw [hey] at this
          simp at this
          omega), hbit, sx_decide_ite_one, htP]
    · rw [if_neg hin]
      rw [sxMap_apply_ne heinj x y _ _ (fun c hc => by
        apply hin
        have := congrArg Fin.val hc
        rw [hey] at this
        simp at this
        have hcK : (c : ℕ) * K + K ≤ L := by
          rw [hLK, ← Nat.succ_mul, Nat.mul_comm]
          exact Nat.mul_le_mul_left _ c.isLt
        omega), hbit, sx_decide_ite_one]
  · rw [if_neg htn, if_neg (by omega), Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

/-- **The full XOR on the stream.** Moving the records by `fullXorPermC` at the `k` positions
turns the records of `Z` into the records of `pullM e (sxXorCol x y) Z`. -/
theorem moveRecs_fullXorPermC {A w r R n k a₀ K ρ L : ℕ} {x y : Fin m} {e : Fin (m * k) → Fin n}
    {X Y : Fin nf} (hXY : X ≠ Y) (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k)
    (hfX : foff len X = a₀ + x * L) (hLX : len X = L)
    (hfY : foff len Y = a₀ + y * L) (hLY : len Y = L)
    (hLXY : len X = len Y) (hSY : foff len Y + len Y ≤ n)
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (Z : ZArr (Fin R × Fin r) n) :
    (moveRecs (fullXorPermC len X Y K ρ (k - 1) (R := R) hXY hLXY hSY)
        ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w))).flatten =
      encZ A w (pullM e (sxXorCol x y) Z) := by
  rw [sx_encZ_eq_flatten, sx_pullM_xorCol]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp [length_moveRecs, IntegerMultBounds.MathlibTM2.Layer.length_recList]
  intro j h1 h2
  have hj : j < R * 2 ^ n := by simpa [length_moveRecs] using h1
  have hu : j / 2 ^ n < R := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; linarith [hj]
  have ha : j % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hdec : 2 ^ n * (j / 2 ^ n) + j % 2 ^ n = j := Nat.div_add_mod j (2 ^ n)
  have hperm := fullXorC_addr len hρ hLK hk hfX hLX hfY hLY hSY he j
  have hlt : 2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) < (recList w Z).length := by
    rw [IntegerMultBounds.MathlibTM2.Layer.length_recList]
    have := IntegerMultBounds.MathlibTM2.Layer.addrNum_lt (sxMap e x y) (j % 2 ^ n)
    have h3 : 2 ^ n * (j / 2 ^ n + 1) ≤ 2 ^ n * R := Nat.mul_le_mul_left _ hu
    rw [Nat.mul_succ] at h3
    rw [Nat.mul_comm R]; omega
  simp only [moveRecs, List.getElem_ofFn, List.getElem_map]
  have hpermS : ((fullXorPermC len X Y K ρ (k - 1) (R := R) hXY hLXY hSY).symm ⟨j, hj⟩ : ℕ) =
      2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) := by
    rw [fullXorPermC_symm, fullXorPermC_apply]; exact hperm
  have hlt' : 2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) <
      ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w)).length := by
    rw [List.length_map]; exact hlt
  rw [hpermS, List.getD_eq_getElem _ _ hlt', List.getElem_map]
  congr 1
  have := IntegerMultBounds.MathlibTM2.Layer.recList_pull (w := w) (sxMap e x y) Z (j / 2 ^ n) hu
    (j % 2 ^ n) ha
  simp only [hdec] at this
  rw [this]

end Identity

end IntegerMultBounds.MathlibTM2.Node
