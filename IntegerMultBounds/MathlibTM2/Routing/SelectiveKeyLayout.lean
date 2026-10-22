module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIdeal
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveLayout
public import IntegerMultBounds.MathlibTM2.Node.KeyPass

/-!
# Complete destination keys, including row bits

A sixth, most-significant counter holds the row. The five physical fields keep
exactly their original widths and offsets; appending this counter does not
change R1's record layout. The emitted key is the entire ideal destination rank.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X rb : ℕ)

def selectiveKeyLen : Fin 6 → ℕ := ![p.wc, p.wy, p.wc, p.wc, X, rb]

theorem selectiveKeyWidth : fieldsLen (selectiveKeyLen p X rb) =
    fieldsLen (selectiveLen p X) + rb := by
  simp [fieldsLen, Fin.sum_univ_succ, selectiveKeyLen, selectiveLen]
  omega

theorem selectiveKeyOff (f : Fin 6) : fieldOff (selectiveKeyLen p X rb) f =
    ![0, p.wc, p.wc + p.wy, p.wc + p.wy + p.wc, p.wc + p.wy + 2 * p.wc,
      fieldsLen (selectiveLen p X)] f := by
  have h0 := fieldOff_zero (selectiveKeyLen p X rb) 0 rfl
  have h1 := fieldOff_succ (selectiveKeyLen p X rb) 0 (by decide)
  have h2 := fieldOff_succ (selectiveKeyLen p X rb) 1 (by decide)
  have h3 := fieldOff_succ (selectiveKeyLen p X rb) 2 (by decide)
  have h4 := fieldOff_succ (selectiveKeyLen p X rb) 3 (by decide)
  have h5 := fieldOff_succ (selectiveKeyLen p X rb) 4 (by decide)
  fin_cases f <;> simp_all [selectiveKeyLen, selectiveLen, fieldsLen,
    Fin.sum_univ_succ, Nat.two_mul, Nat.add_assoc]

theorem selectiveKey_digit (f : Fin 5) (i : ℕ) :
    digit (selectiveKeyLen p X rb) f.castSucc i = digit (selectiveLen p X) f i := by
  simp only [digit, selectiveKeyOff, selectiveFieldOff]
  fin_cases f <;> simp [selectiveKeyLen, selectiveLen]

theorem selectiveKey_row (i : ℕ) : digit (selectiveKeyLen p X rb) 5 i =
    (i / 2 ^ fieldsLen (selectiveLen p X)) % 2 ^ rb := by
  simp only [digit, selectiveKeyOff]
  simp [selectiveKeyLen]

/-- The target key digit uses the actual arbitrary-source XOR; every other digit
is copied unchanged, including the row. -/
def selectiveKeyDig (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (i : ℕ)
    (f : Fin 6) : ℕ :=
  if f = 1 then (selectiveView p X i).y ^^^
    targetWord p active s (selectiveView p X i).y (selectiveView p X i).x
  else digit (selectiveKeyLen p X rb) f i

variable (hK : 0 < p.K) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

include hK in
theorem selectiveKeyDig_ideal (f : Fin 6) (i : ℕ) :
    selectiveKeyDig p X rb active s i f =
      digit (selectiveKeyLen p X rb) f (selectiveIdealIdx p X active s i) := by
  have hsmall (g : Fin 5) :
      digit (selectiveKeyLen p X rb) g.castSucc (selectiveIdealIdx p X active s i) =
        digit (selectiveLen p X) g (selectiveIdealIdx p X active s i) :=
    selectiveKey_digit p X rb g _
  have hy := Nat.xor_lt_two_pow (selectiveView_fits p X i).y
    (targetWord_lt p X hK active s (selectiveView p X i).y (selectiveView p X i).x)
  have hd (g : Fin 5) :
      digit (selectiveKeyLen p X rb) g.castSucc (selectiveIdealIdx p X active s i) =
        if g = 1 then (selectiveView p X i).y ^^^
          targetWord p active s (selectiveView p X i).y (selectiveView p X i).x
        else digit (selectiveLen p X) g i := by
    rw [hsmall]
    by_cases hg : g = 1
    · subst g
      simp only [ite_true, selectiveIdealIdx, digit_setDigit_self]
      exact Nat.mod_eq_of_lt hy
    · simp only [hg, ite_false, selectiveIdealIdx, digit_setDigit_ne _ _ _ hg]
  fin_cases f
  · change digit (selectiveKeyLen p X rb) 0 i = _
    exact (selectiveKey_digit p X rb 0 i).trans (by simpa using (hd 0).symm)
  · simpa [selectiveKeyDig] using (hd 1).symm
  · change digit (selectiveKeyLen p X rb) 2 i = _
    exact (selectiveKey_digit p X rb 2 i).trans (by simpa using (hd 2).symm)
  · change digit (selectiveKeyLen p X rb) 3 i = _
    exact (selectiveKey_digit p X rb 3 i).trans (by simpa using (hd 3).symm)
  · change digit (selectiveKeyLen p X rb) 4 i = _
    exact (selectiveKey_digit p X rb 4 i).trans (by simpa using (hd 4).symm)
  · change digit (selectiveKeyLen p X rb) 5 i =
      digit (selectiveKeyLen p X rb) 5 (selectiveIdealIdx p X active s i)
    rw [selectiveKey_row, selectiveKey_row, selectiveIdealIdx, setDigit_div_total]

/-- The entire key, in least-significant-field order, including the row field. -/
def selectiveKeyBits {A : ℕ} (i : ℕ) : List (Fin (A + 4)) :=
  (List.finRange 6).flatMap fun f =>
    binSyms (selectiveKeyLen p X rb f) (selectiveKeyDig p X rb active s i f)

include hK in
/-- The emitted bits are the complete ideal destination, not merely an in-row key. -/
theorem selectiveKeyBits_ideal {A : ℕ} (i : ℕ) :
    selectiveKeyBits (A := A) p X rb active s i =
      binSyms (fieldsLen (selectiveKeyLen p X rb)) (selectiveIdealIdx p X active s i) := by
  unfold selectiveKeyBits
  simp_rw [selectiveKeyDig_ideal p X rb hK active s]
  simp only [binSyms_eq]
  rw [← List.map_flatMap, flatMap_binBits_digit]

/-- Keying in input order matches the exact key representation used by repair. -/
theorem selectiveKeyedFrom {A R : ℕ} (hs : ∀ c, (s c).Allowed active)
    (l : List (List (Fin (A + 4))))
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X)) :
    keyedFrom (selectiveKeyBits p X rb active s) 0 l =
      keyRecs (fieldsLen (selectiveKeyLen p X rb)) (selectiveIdealPerm hK active s R hs) l := by
  rw [keyedFrom_eq, keyRecs, hl]
  symm
  apply ofFn_eq_range_map
  intro j
  rw [Nat.zero_add, selectiveKeyBits_ideal p X rb hK active s]
  rfl

/-- Every record fits in the full key range when the row counter fits. -/
theorem selectiveKey_rank_bound (R : ℕ) (hR : R ≤ 2 ^ rb) :
    R * 2 ^ fieldsLen (selectiveLen p X) ≤ 2 ^ fieldsLen (selectiveKeyLen p X rb) := by
  rw [selectiveKeyWidth, Nat.pow_add, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ hR

end IntegerMultBounds.MathlibTM2.Routing
