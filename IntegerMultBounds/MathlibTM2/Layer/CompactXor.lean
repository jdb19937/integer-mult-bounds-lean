module

public import IntegerMultBounds.MathlibTM2.Layer.PackedXor

/-!
# Compact-control slot XOR: fields of an index and the instruction model

The compact-control replacement of the packed slot XOR (CrocSwap, *Compact dirty controls for
selected-bit additions*) never moves the two wide slots `x` and `y`. It moves three narrow
control fields `u`, `t` (above both slots) and `b` (below both slots), each of `n G` bits for
`n = f - 1` radix-`2^G` digits, and rotates `y` and `b` in place by offsets computed from fields
above the rotated one.

This file sets up the index model used by every pass of the compact machine: a record address is
a natural number `i` whose mixed-radix digits are its fields, field `0` least significant
(`dig`, the `digit` of `Host/Index.lean` written without the host), with `setDig` replacing one
field. An instruction is a rotation of one field by an offset function of the index (`rot`), or
the exchange of two fields of equal length (`swap`); a program is a list of instructions run head
first (`runC`). An instruction whose offset ignores its own field is a bijection of the indices
below `R · 2^S` whenever its fields lie below bit `S` (`instrPerm`, `progPerm`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### Fields of an index -/

section Fields

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- Bit offset of field `f`: the total length of the fields below it. -/
def foff (f : Fin nf) : ℕ := ∑ g ∈ Finset.univ.filter (· < f), len g

/-- Field `f` of the index `i`. -/
def dig (f : Fin nf) (i : ℕ) : ℕ := (i / 2 ^ foff len f) % 2 ^ len f

/-- The index `i` with field `f` replaced by `v`. -/
def setDig (f : Fin nf) (i v : ℕ) : ℕ :=
  i % 2 ^ foff len f + 2 ^ foff len f * (v + 2 ^ len f * (i / 2 ^ (foff len f + len f)))

lemma foff_add_len_le {f g : Fin nf} (hfg : f < g) : foff len f + len f ≤ foff len g := by
  unfold foff
  rw [Nat.add_comm, ← Finset.sum_insert (s := Finset.univ.filter (· < f)) (by simp)]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with rfl | hx
  · exact hfg
  · exact hx.trans hfg

lemma foff_zero (f : Fin nf) (hf : f.val = 0) : foff len f = 0 := by
  apply Finset.sum_eq_zero
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hg
  omega

lemma dig_lt (f : Fin nf) (i : ℕ) : dig len f i < 2 ^ len f := Nat.mod_lt _ (by positivity)

lemma testBit_dig (f : Fin nf) (i : ℕ) {t : ℕ} (ht : t < len f) :
    (dig len f i).testBit t = i.testBit (foff len f + t) := by
  unfold dig
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht, Nat.add_comm]

/-- Bits of a replaced field. -/
lemma testBit_setDig (f : Fin nf) (i : ℕ) {v : ℕ} (hv : v < 2 ^ len f) (t : ℕ) :
    (setDig len f i v).testBit t =
      if foff len f ≤ t ∧ t < foff len f + len f then v.testBit (t - foff len f)
      else i.testBit t := by
  unfold setDig
  have hlo : i % 2 ^ foff len f < 2 ^ foff len f := Nat.mod_lt _ (by positivity)
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo, Nat.add_comm v,
    Nat.testBit_two_pow_mul_add _ hv]
  by_cases h1 : t < foff len f
  · simp [h1, Nat.testBit_mod_two_pow]
  · by_cases h2 : t - foff len f < len f
    · simp [h1, h2, show foff len f ≤ t ∧ t < foff len f + len f by omega]
    · simp only [h1, h2, ↓reduceIte, Nat.testBit_div_two_pow]
      rw [if_neg (by omega)]
      congr 1; omega

lemma setDig_dig (f : Fin nf) (i : ℕ) : setDig len f i (dig len f i) = i := by
  unfold setDig dig
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div, Nat.mod_add_div]

lemma dig_setDig_self (f : Fin nf) (i : ℕ) {v : ℕ} (hv : v < 2 ^ len f) :
    dig len f (setDig len f i v) = v := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < len f
  · rw [testBit_dig len f _ ht, testBit_setDig len f i hv]
    simp [ht]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (dig_lt len f _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]

lemma dig_setDig_ne {f g : Fin nf} (hfg : g ≠ f) (i : ℕ) {v : ℕ} (hv : v < 2 ^ len f) :
    dig len g (setDig len f i v) = dig len g i := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < len g
  · rw [testBit_dig len g _ ht, testBit_dig len g _ ht, testBit_setDig len f i hv]
    rcases lt_or_gt_of_ne hfg with h | h
    · have := foff_add_len_le len h
      rw [if_neg (by omega)]
    · have := foff_add_len_le len h
      rw [if_neg (by omega)]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (dig_lt len g _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (dig_lt len g _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- Two indices with the same bits are equal: extensionality through `testBit`. -/
lemma setDig_ext {i j : ℕ} (h : ∀ t, i.testBit t = j.testBit t) : i = j :=
  Nat.eq_of_testBit_eq h

lemma setDig_setDig_self (f : Fin nf) (i : ℕ) {v v' : ℕ} (hv : v < 2 ^ len f)
    (hv' : v' < 2 ^ len f) : setDig len f (setDig len f i v) v' = setDig len f i v' := by
  apply setDig_ext
  intro t
  rw [testBit_setDig len f _ hv', testBit_setDig len f _ hv', testBit_setDig len f _ hv]
  split_ifs <;> rfl

lemma setDig_comm {f g : Fin nf} (hfg : f ≠ g) (i : ℕ) {v w : ℕ} (hv : v < 2 ^ len f)
    (hw : w < 2 ^ len g) :
    setDig len f (setDig len g i w) v = setDig len g (setDig len f i v) w := by
  apply setDig_ext
  intro t
  rw [testBit_setDig len f _ hv, testBit_setDig len g _ hw, testBit_setDig len g _ hw,
    testBit_setDig len f _ hv]
  rcases lt_or_gt_of_ne hfg with h | h
  · have := foff_add_len_le len h
    split_ifs <;> first | rfl | omega
  · have := foff_add_len_le len h
    split_ifs <;> first | rfl | omega

/-- The high part above bit `S` is unchanged by replacing a field below `S`. -/
lemma setDig_div (f : Fin nf) (i : ℕ) {v : ℕ} (hv : v < 2 ^ len f) {S : ℕ}
    (hS : foff len f + len f ≤ S) : setDig len f i v / 2 ^ S = i / 2 ^ S := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, testBit_setDig len f i hv,
    if_neg (by omega)]

lemma setDig_lt {R S : ℕ} (f : Fin nf) {i : ℕ} (hi : i < R * 2 ^ S) {v : ℕ}
    (hv : v < 2 ^ len f) (hS : foff len f + len f ≤ S) : setDig len f i v < R * 2 ^ S := by
  have h1 : i / 2 ^ S < R := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hi
  rw [← setDig_div len f i hv hS] at h1
  rw [Nat.div_lt_iff_lt_mul (by positivity)] at h1
  exact h1

lemma setDig_mod_pow (f : Fin nf) (i : ℕ) {v : ℕ} (hv : v < 2 ^ len f) {S : ℕ}
    (hS : foff len f + len f ≤ S) : setDig len f i v % 2 ^ S = setDig len f (i % 2 ^ S) v := by
  apply setDig_ext
  intro t
  rw [Nat.testBit_mod_two_pow, testBit_setDig len f _ hv, testBit_setDig len f _ hv,
    Nat.testBit_mod_two_pow]
  by_cases ht : t < S
  · simp [ht]
  · have hc : ¬ (foff len f ≤ t ∧ t < foff len f + len f) := by omega
    simp [ht, hc]

lemma dig_mod_pow (f : Fin nf) (i : ℕ) {S : ℕ} (hS : foff len f + len f ≤ S) :
    dig len f (i % 2 ^ S) = dig len f i := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < len f
  · rw [testBit_dig len f _ ht, testBit_dig len f _ ht, Nat.testBit_mod_two_pow]
    simp [show foff len f + t < S by omega]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (dig_lt len f _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (dig_lt len f _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end Fields

/-! ### Rotations and swaps of fields -/

section Ops

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- `v + off` or `v - off` modulo `2^W`. -/
def rotVal (W : ℕ) (neg : Bool) (off v : ℕ) : ℕ :=
  if neg then (v + (2 ^ W - off % 2 ^ W)) % 2 ^ W else (v + off) % 2 ^ W

lemma rotVal_lt (W : ℕ) (neg : Bool) (off v : ℕ) : rotVal W neg off v < 2 ^ W := by
  unfold rotVal; split_ifs <;> exact Nat.mod_lt _ (by positivity)

lemma rotVal_neg_rotVal (W : ℕ) (neg : Bool) (off : ℕ) {v : ℕ} (hv : v < 2 ^ W) :
    rotVal W (!neg) off (rotVal W neg off v) = v := by
  have hW : 0 < 2 ^ W := by positivity
  have hr : off % 2 ^ W < 2 ^ W := Nat.mod_lt _ hW
  have hqr : off % 2 ^ W + 2 ^ W * (off / 2 ^ W) = off := Nat.mod_add_div off (2 ^ W)
  set P := 2 ^ W with hP
  set q := off / P
  set r := off % P
  cases neg
  · simp only [rotVal, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : v + off + (P - r) = v + P * (q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · simp only [rotVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : v + (P - r) + off = v + P * (q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- The rotation of field `f` by the offset `off i`, which may depend on the index. -/
def rotF (f : Fin nf) (neg : Bool) (off : ℕ → ℕ) (i : ℕ) : ℕ :=
  setDig len f i (rotVal (len f) neg (off i) (dig len f i))

/-- The exchange of the fields `f` and `g` (of equal length). -/
def swapF (f g : Fin nf) (i : ℕ) : ℕ :=
  setDig len f (setDig len g i (dig len f i)) (dig len g i)

/-- An offset function that ignores field `f`. -/
def IgnoresF (f : Fin nf) (off : ℕ → ℕ) : Prop :=
  ∀ i v, v < 2 ^ len f → off (setDig len f i v) = off i

lemma dig_rotF (f : Fin nf) (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    dig len f (rotF len f neg off i) = rotVal (len f) neg (off i) (dig len f i) :=
  dig_setDig_self len f i (rotVal_lt _ _ _ _)

lemma dig_rotF_ne {f g : Fin nf} (hfg : g ≠ f) (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    dig len g (rotF len f neg off i) = dig len g i :=
  dig_setDig_ne len hfg i (rotVal_lt _ _ _ _)

lemma rotF_rotF (f : Fin nf) (neg : Bool) {off : ℕ → ℕ} (hoff : IgnoresF len f off) (i : ℕ) :
    rotF len f (!neg) off (rotF len f neg off i) = i := by
  unfold rotF
  rw [dig_setDig_self len f i (rotVal_lt _ _ _ _), hoff i _ (rotVal_lt _ _ _ _),
    setDig_setDig_self len f i (rotVal_lt _ _ _ _) (rotVal_lt _ _ _ _),
    rotVal_neg_rotVal _ _ _ (dig_lt len f i), setDig_dig]

lemma dig_swapF_left {f g : Fin nf} (_hfg : f ≠ g) (hlen : len f = len g) (i : ℕ) :
    dig len f (swapF len f g i) = dig len g i :=
  dig_setDig_self len f _ (by rw [hlen]; exact dig_lt len g i)

lemma dig_swapF_right {f g : Fin nf} (hfg : f ≠ g) (hlen : len f = len g) (i : ℕ) :
    dig len g (swapF len f g i) = dig len f i := by
  unfold swapF
  rw [dig_setDig_ne len hfg.symm _ (by rw [hlen]; exact dig_lt len g i),
    dig_setDig_self len g i (by rw [← hlen]; exact dig_lt len f i)]

lemma dig_swapF_ne {f g h : Fin nf} (hhf : h ≠ f) (hhg : h ≠ g) (hlen : len f = len g) (i : ℕ) :
    dig len h (swapF len f g i) = dig len h i := by
  unfold swapF
  rw [dig_setDig_ne len hhf _ (by rw [hlen]; exact dig_lt len g i),
    dig_setDig_ne len hhg _ (by rw [← hlen]; exact dig_lt len f i)]

lemma swapF_swapF {f g : Fin nf} (hfg : f ≠ g) (hlen : len f = len g) (i : ℕ) :
    swapF len f g (swapF len f g i) = i := by
  have h1 := dig_swapF_left len hfg hlen i
  have h2 := dig_swapF_right len hfg hlen i
  have hgf : dig len g i < 2 ^ len f := by rw [hlen]; exact dig_lt len g i
  have hfg' : dig len f i < 2 ^ len g := by rw [← hlen]; exact dig_lt len f i
  rw [swapF, h1, h2, swapF]
  rw [← setDig_comm len hfg _ hgf (dig_lt len g i),
    setDig_setDig_self len g i hfg' (dig_lt len g i), setDig_dig,
    setDig_setDig_self len f i hgf (dig_lt len f i), setDig_dig]

lemma rotF_lt {R S : ℕ} (f : Fin nf) (neg : Bool) (off : ℕ → ℕ) {i : ℕ} (hi : i < R * 2 ^ S)
    (hS : foff len f + len f ≤ S) : rotF len f neg off i < R * 2 ^ S :=
  setDig_lt len f hi (rotVal_lt _ _ _ _) hS

lemma swapF_lt {R S : ℕ} (f g : Fin nf) {i : ℕ} (hi : i < R * 2 ^ S)
    (hSf : foff len f + len f ≤ S) (hSg : foff len g + len g ≤ S) (hlen : len f = len g) :
    swapF len f g i < R * 2 ^ S :=
  setDig_lt len f (setDig_lt len g hi (hlen ▸ dig_lt len f i) hSg) (hlen ▸ dig_lt len g i) hSf

end Ops

/-! ### Instructions and programs -/

section Instr

variable {nf : ℕ}

/-- An instruction: a rotation of one field by an offset function, or a field exchange. -/
inductive CInstr (nf : ℕ)
  | rot (f : Fin nf) (neg : Bool) (off : ℕ → ℕ)
  | swap (f g : Fin nf)

variable (len : Fin nf → ℕ)

/-- The index map of an instruction. -/
def CInstr.run : CInstr nf → ℕ → ℕ
  | .rot f neg off => rotF len f neg off
  | .swap f g => swapF len f g

/-- The inverse instruction. -/
def CInstr.inv : CInstr nf → CInstr nf
  | .rot f neg off => .rot f (!neg) off
  | .swap f g => .swap f g

def CInstr.isRot : CInstr nf → Bool
  | .rot _ _ _ => true
  | .swap _ _ => false

/-- Well-formedness below bit `S`: a rotation ignores its own field and acts below `S`; a swap
exchanges distinct fields of equal length below `S`. -/
def CInstr.WF (S : ℕ) : CInstr nf → Prop
  | .rot f _ off => IgnoresF len f off ∧ foff len f + len f ≤ S
  | .swap f g => f ≠ g ∧ len f = len g ∧ foff len f + len f ≤ S ∧ foff len g + len g ≤ S

lemma CInstr.WF_inv {S : ℕ} {ins : CInstr nf} (h : ins.WF len S) : ins.inv.WF len S := by
  cases ins <;> exact h

lemma CInstr.inv_run {S : ℕ} {ins : CInstr nf} (h : ins.WF len S) (i : ℕ) :
    ins.inv.run len (ins.run len i) = i := by
  cases ins with
  | rot f neg off => exact rotF_rotF len f neg h.1 i
  | swap f g => exact swapF_swapF len h.1 h.2.1 i

lemma CInstr.run_inv {S : ℕ} {ins : CInstr nf} (h : ins.WF len S) (i : ℕ) :
    ins.run len (ins.inv.run len i) = i := by
  cases ins with
  | rot f neg off =>
    show rotF len f neg off (rotF len f (!neg) off i) = i
    simpa using rotF_rotF len f (!neg) h.1 i
  | swap f g => exact swapF_swapF len h.1 h.2.1 i

lemma CInstr.run_lt {R S : ℕ} {ins : CInstr nf} (h : ins.WF len S) {i : ℕ} (hi : i < R * 2 ^ S) :
    ins.run len i < R * 2 ^ S := by
  cases ins with
  | rot f neg off => exact rotF_lt len f neg off hi h.2
  | swap f g => exact swapF_lt len f g hi h.2.2.1 h.2.2.2 h.2.1

/-- A program runs its instructions head first. -/
def runC (P : List (CInstr nf)) (i : ℕ) : ℕ := P.foldl (fun i ins => ins.run len i) i

lemma runC_nil (i : ℕ) : runC len [] i = i := rfl

lemma runC_cons (ins : CInstr nf) (P : List (CInstr nf)) (i : ℕ) :
    runC len (ins :: P) i = runC len P (ins.run len i) := rfl

lemma runC_append (P P' : List (CInstr nf)) (i : ℕ) :
    runC len (P ++ P') i = runC len P' (runC len P i) := by
  simp [runC, List.foldl_append]

/-- The instruction `ins` as a permutation of the indices below `R · 2^S`. -/
def instrPerm {R S : ℕ} {ins : CInstr nf} (h : ins.WF len S) : Equiv.Perm (Fin (R * 2 ^ S)) where
  toFun i := ⟨ins.run len i, ins.run_lt len h i.isLt⟩
  invFun i := ⟨ins.inv.run len i, ins.inv.run_lt len (ins.WF_inv len h) i.isLt⟩
  left_inv i := Fin.ext (ins.inv_run len h i)
  right_inv i := Fin.ext (ins.run_inv len h i)

lemma instrPerm_apply {R S : ℕ} {ins : CInstr nf} (h : ins.WF len S) (i : Fin (R * 2 ^ S)) :
    (instrPerm len h i : ℕ) = ins.run len i := rfl

/-- A program as a permutation, head first. -/
def progPerm {R S : ℕ} : (P : List (CInstr nf)) → (∀ ins ∈ P, ins.WF len S) →
    Equiv.Perm (Fin (R * 2 ^ S))
  | [], _ => Equiv.refl _
  | ins :: P, h => (instrPerm len (h ins List.mem_cons_self)).trans
      (progPerm P fun i hi => h i (List.mem_cons_of_mem _ hi))

lemma progPerm_apply {R S : ℕ} : (P : List (CInstr nf)) → (h : ∀ ins ∈ P, ins.WF len S) →
    ∀ i : Fin (R * 2 ^ S), (progPerm len P h i : ℕ) = runC len P i
  | [], _, i => rfl
  | ins :: P, h, i => by
    simp only [progPerm, Equiv.trans_apply, runC_cons]
    rw [progPerm_apply P _ (instrPerm len _ i), instrPerm_apply]

end Instr


/-! ### Digit extensionality -/

section Ext

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma foff_succ (j : ℕ) (h : j + 1 < nf) :
    foff len ⟨j + 1, h⟩ = foff len ⟨j, by omega⟩ + len ⟨j, by omega⟩ := by
  have hs : Finset.univ.filter (· < (⟨j + 1, h⟩ : Fin nf)) =
      insert ⟨j, by omega⟩ (Finset.univ.filter (· < (⟨j, by omega⟩ : Fin nf))) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.ext_iff]
    omega
  rw [foff, hs, Finset.sum_insert (by simp), Nat.add_comm]
  rfl

lemma foff_last (j : ℕ) (h : j < nf) (hl : j + 1 = nf) :
    foff len ⟨j, h⟩ + len ⟨j, h⟩ = ∑ g, len g := by
  rw [foff, Nat.add_comm, ← Finset.sum_insert (s := Finset.univ.filter (· < (⟨j, h⟩ : Fin nf)))
    (by simp)]
  congr 1
  ext g
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
    Fin.ext_iff, iff_true]
  have := g.isLt
  omega

/-- Every bit below the total length lies in some field. -/
lemma exists_field {t : ℕ} (ht : t < ∑ g, len g) :
    ∃ f : Fin nf, foff len f ≤ t ∧ t < foff len f + len f := by
  have hnf : 0 < nf := by
    rcases Nat.eq_zero_or_pos nf with h | h
    · subst h; simp at ht
    · exact h
  suffices key : ∀ m, m < nf → foff len ⟨nf - 1 - m, by omega⟩ ≤ t →
      ∃ f : Fin nf, foff len f ≤ t ∧ t < foff len f + len f by
    refine key (nf - 1) (by omega) ?_
    have e : nf - 1 - (nf - 1) = 0 := by omega
    simp only [e]
    rw [foff_zero len ⟨0, hnf⟩ rfl]
    exact Nat.zero_le t
  intro m
  induction m with
  | zero =>
    intro hm hle
    refine ⟨⟨nf - 1 - 0, by omega⟩, hle, ?_⟩
    rw [foff_last len (nf - 1 - 0) (by omega) (by omega)]
    exact ht
  | succ m ih =>
    intro hm hle
    by_cases hend : t < foff len ⟨nf - 1 - (m + 1), by omega⟩ + len ⟨nf - 1 - (m + 1), by omega⟩
    · exact ⟨_, hle, hend⟩
    · rw [not_lt] at hend
      apply ih (by omega)
      have e : nf - 1 - m = nf - 1 - (m + 1) + 1 := by omega
      rw [show (⟨nf - 1 - m, by omega⟩ : Fin nf) = ⟨nf - 1 - (m + 1) + 1, by omega⟩ from
        Fin.ext e, foff_succ len (nf - 1 - (m + 1)) (by omega)]
      exact hend

/-- Two indices below `2^(∑ len)` with the same fields are equal. -/
lemma ext_dig {i j : ℕ} (hi : i < 2 ^ ∑ g, len g) (hj : j < 2 ^ ∑ g, len g)
    (h : ∀ f, dig len f i = dig len f j) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < ∑ g, len g
  · obtain ⟨f, hf1, hf2⟩ := exists_field len ht
    have e1 := testBit_dig len f i (t := t - foff len f) (by omega)
    have e2 := testBit_dig len f j (t := t - foff len f) (by omega)
    rw [show foff len f + (t - foff len f) = t by omega] at e1 e2
    rw [← e1, ← e2, h f]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end Ext


/-! ### The compact layout, its offsets and programs -/

section Layout

open IntegerMultBounds.MathlibTM2.Layer.PackedXor (selMask GuardOK)

variable {nf : ℕ} (len : Fin nf → ℕ) (U T X Y B : Fin nf) (K ρ G n : ℕ)

/-- `1` or `0`. -/
def b2n (b : Bool) : ℕ := if b then 1 else 0

lemma b2n_le_one (b : Bool) : b2n b ≤ 1 := by cases b <;> simp [b2n]

/-- Bit `o + c s` of field `A` of the index `i`. -/
def bitAt (A : Fin nf) (o s c i : ℕ) : Bool := (dig len A i).testBit (o + c * s)

/-- Digit `c` in radix `2^G` of field `D` of the index `i`. -/
def digAt (D : Fin nf) (c i : ℕ) : ℕ := dig len D i / 2 ^ (c * G) % 2 ^ G

lemma digAt_lt (D : Fin nf) (c i : ℕ) : digAt len G D c i < 2 ^ G := Nat.mod_lt _ (by positivity)

/-- `∑_{c<n} [z_c] · 2 w_c · 2^{ρ + cK}`: the control bits `z_c` of field `A` at `oA + c sA`
times twice the digits `w_c` of `T`. -/
def offYW (A : Fin nf) (oA sA : ℕ) (i : ℕ) : ℕ :=
  ∑ c ∈ Finset.range n, b2n (bitAt len A oA sA c i) * (2 * digAt len G T c i) * 2 ^ (ρ + c * K)

/-- `∑_{c<n} [z_c] 2^{ρ + cK}`. -/
def offYb (A : Fin nf) (oA sA : ℕ) (i : ℕ) : ℕ :=
  ∑ c ∈ Finset.range n, b2n (bitAt len A oA sA c i) * 2 ^ (ρ + c * K)

/-- `∑_{c<n} [a_c] 2^{cG}` for the bits `a_c` of field `A` at `oA + c sA`. -/
def offBb (A : Fin nf) (oA sA : ℕ) (i : ℕ) : ℕ :=
  ∑ c ∈ Finset.range n, b2n (bitAt len A oA sA c i) * 2 ^ (c * G)

/-- `∑_{c<n} [y_{j_c} ⊕ z_c] 2^{cG}`. -/
def offBx (A : Fin nf) (oA sA : ℕ) (i : ℕ) : ℕ :=
  ∑ c ∈ Finset.range n, b2n (xor (bitAt len Y ρ K c i) (bitAt len A oA sA c i)) * 2 ^ (c * G)

/-- **The core sequence** with control field `A` (bits at `oA + c sA`): the four-step identity
`v ← v + 2zw; w ← w + (v mod 2); v ← v + z(1 - 2w); w ← w - ((v mod 2) ⊕ z)` on every
column `c < n`, the temporary `w_c` being digit `c` of `t`, moved through `b` for its two
updates. Four swaps and five rotations. -/
def core (A : Fin nf) (oA sA : ℕ) : List (CInstr nf) :=
  [.rot Y false (offYW len T K ρ G n A oA sA), .swap T B,
   .rot B false (offBb len G n Y ρ K), .swap T B,
   .rot Y false (offYb len K ρ n A oA sA), .rot Y true (offYW len T K ρ G n A oA sA),
   .swap T B, .rot B true (offBx len Y K ρ G n A oA sA), .swap T B]

/-- **Earlier source** (`x` above `y`): the core with the control bits of `x`. -/
def progE : List (CInstr nf) := core len T Y B K ρ G n X ρ K

/-- The load of the selected bits of `x` into the digits of `u`, and its inverse. -/
def loadU (neg : Bool) : List (CInstr nf) :=
  [.swap U B, .rot B neg (offBb len G n X ρ K), .swap U B]

/-- **Later source** (`x` below `y`): the core with the parities of `u` as controls, the load
of `x` into `u`, the core again, and the unload. Twelve swaps and twelve rotations. -/
def progL : List (CInstr nf) :=
  core len T Y B K ρ G n U 0 G ++ loadU len U X B K ρ G n false ++
    core len T Y B K ρ G n U 0 G ++ loadU len U X B K ρ G n true

/-- **The ideal map**: `y ← y ⊕ (x ∧ selMask K ρ n)`, the XOR at the first `n` selected
positions. -/
def idealC (i : ℕ) : ℕ := setDig len Y i (dig len Y i ^^^ (dig len X i &&& selMask K ρ n))

/-- Every used digit of `D` is at most `2^G - 2`. -/
def DigOK (D : Fin nf) (i : ℕ) : Prop := ∀ c < n, digAt len G D c i + 2 ≤ 2 ^ G

/-- Good indices of the earlier source: the used digits of `t` are at most `2^G - 2` and the
guards of the used segments of `y` lie in `[2^{G+1}, 2^{K-1} - 1 - 2^{G+1}]`. -/
def GoodE (i : ℕ) : Prop :=
  DigOK len G n T i ∧ ∀ c < n, GuardOK K ρ (2 ^ (G + 1)) (dig len Y i) c

/-- Good indices of the later source: also the used digits of `u`. -/
def GoodL (i : ℕ) : Prop := GoodE len T Y K ρ G n i ∧ DigOK len G n U i

instance (D : Fin nf) (i : ℕ) : Decidable (DigOK len G n D i) := by unfold DigOK; infer_instance

instance (i : ℕ) : Decidable (GoodE len T Y K ρ G n i) := by unfold GoodE; infer_instance

instance (i : ℕ) : Decidable (GoodL len U T Y K ρ G n i) := by unfold GoodL; infer_instance

lemma countP_core (A : Fin nf) (oA sA : ℕ) :
    (core len T Y B K ρ G n A oA sA).countP CInstr.isRot = 5 ∧
      (core len T Y B K ρ G n A oA sA).countP (fun ins => !ins.isRot) = 4 := by
  simp [core, List.countP_cons, CInstr.isRot]

lemma countP_progE :
    (progE len T X Y B K ρ G n).countP CInstr.isRot = 5 ∧
      (progE len T X Y B K ρ G n).countP (fun ins => !ins.isRot) = 4 :=
  countP_core len T Y B K ρ G n X ρ K

lemma countP_progL :
    (progL len U T X Y B K ρ G n).countP CInstr.isRot = 12 ∧
      (progL len U T X Y B K ρ G n).countP (fun ins => !ins.isRot) = 12 := by
  simp [progL, core, loadU, List.countP_cons, CInstr.isRot]

end Layout


/-! ### Arithmetic of the compact fields -/

section Arith

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix
open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma foff_add_len_le_sum (f : Fin nf) : foff len f + len f ≤ ∑ g, len g := by
  rw [foff, Nat.add_comm, ← Finset.sum_insert (s := Finset.univ.filter (· < f)) (by simp)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma rotF_lt_sum (f : Fin nf) (neg : Bool) (off : ℕ → ℕ) {i : ℕ} (hi : i < 2 ^ ∑ g, len g) :
    rotF len f neg off i < 2 ^ ∑ g, len g := by
  have := rotF_lt (R := 1) len f neg off (by rw [one_mul]; exact hi) (foff_add_len_le_sum len f)
  rwa [one_mul] at this

lemma swapF_lt_sum (f g : Fin nf) (hlen : len f = len g) {i : ℕ} (hi : i < 2 ^ ∑ g, len g) :
    swapF len f g i < 2 ^ ∑ g, len g := by
  have := swapF_lt (R := 1) len f g (by rw [one_mul]; exact hi) (foff_add_len_le_sum len f)
    (foff_add_len_le_sum len g) hlen
  rwa [one_mul] at this

/-- A rotation of `B` conjugated by the swap `T ↔ B` is a rotation of `T` by the offset read
through the swap. -/
lemma swap_rot_swap {T B : Fin nf} (hTB : T ≠ B) (hlen : len T = len B) (neg : Bool)
    (off : ℕ → ℕ) {i : ℕ} (hi : i < 2 ^ ∑ g, len g) :
    swapF len T B (rotF len B neg off (swapF len T B i)) =
      rotF len T neg (fun j => off (swapF len T B j)) i := by
  have h1 := swapF_lt_sum len T B hlen hi
  have h2 := rotF_lt_sum len B neg off h1
  have h3 := swapF_lt_sum len T B hlen h2
  have h4 := rotF_lt_sum len T neg (fun j => off (swapF len T B j)) hi
  apply ext_dig len h3 h4
  intro f
  by_cases hfT : f = T
  · subst hfT
    rw [dig_swapF_left len hTB hlen, dig_rotF, dig_swapF_right len hTB hlen, dig_rotF, hlen]
  by_cases hfB : f = B
  · subst hfB
    rw [dig_swapF_right len hTB hlen, dig_rotF_ne len hTB, dig_swapF_left len hTB hlen,
      dig_rotF_ne len hTB.symm]
  · rw [dig_swapF_ne len hfT hfB hlen, dig_rotF_ne len hfB, dig_swapF_ne len hfT hfB hlen,
      dig_rotF_ne len hfT]

/-- A guard in `[m, 2^(K-1) - 1 - m]` gives `2m ≤ seg ≤ 2^K - 1 - 2m`. -/
lemma seg_bounds_of_guard' {K ρ : ℕ} (hK : 1 ≤ K) (m y c : ℕ) (h : GuardOK K ρ m y c) :
    2 * m ≤ seg K ρ (y : ℤ) c ∧ seg K ρ (y : ℤ) c + 2 * m + 1 ≤ 2 ^ K := by
  have h1 := seg_half K ρ hK y c
  have h2 : 0 ≤ seg K ρ (y : ℤ) c := Int.emod_nonneg _ (by positivity)
  have h3 : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨g1, g2⟩ := h
  have g1' : (m : ℤ) ≤ ((guard K ρ y c : ℕ) : ℤ) := by exact_mod_cast g1
  have g2' : ((guard K ρ y c : ℕ) : ℤ) + m < (2 : ℤ) ^ (K - 1) := by exact_mod_cast g2
  omega

/-- A digit field of `n` radix-`2^G` digits is the pack of its digits. -/
lemma dig_eq_pack (D : Fin nf) {G n : ℕ} (hlen : len D = n * G) (i : ℕ) :
    ((dig len D i : ℕ) : ℤ) =
      pack (2 ^ G) ((List.range n).map fun c => ((digAt len G D c i : ℕ) : ℤ)) := by
  have hlt : dig len D i < 2 ^ len D := dig_lt len D i
  rw [hlen, Nat.mul_comm, pow_mul] at hlt
  have hB : (0 : ℤ) < 2 ^ G := by positivity
  have h := pack_digits_mod (2 ^ G) hB n ((dig len D i : ℕ) : ℤ)
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)] at h
  rw [← h, digits_eq_range _ hB.le]
  congr 1
  apply List.map_congr_left
  intro c _
  unfold digAt
  rw [Nat.mul_comm c G, pow_mul]
  push_cast
  rfl

/-- `∑_{c<n} e_c 2^{ρ + cK} = 2^ρ · pack (2^K) e`. -/
lemma sum_pow_eq_pack (K ρ n : ℕ) (e : ℕ → ℤ) :
    ∑ c ∈ Finset.range n, e c * 2 ^ (ρ + c * K) =
      2 ^ ρ * pack (2 ^ K) ((List.range n).map e) := by
  rw [pack_range_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [pow_add, Nat.mul_comm c K, pow_mul]
  ring

lemma offYW_cast {T : Fin nf} {K ρ G n : ℕ} (A : Fin nf) (oA sA i : ℕ) :
    ((offYW len T K ρ G n A oA sA i : ℕ) : ℤ) = 2 ^ ρ * pack (2 ^ K) ((List.range n).map fun c =>
      (b2n (bitAt len A oA sA c i) : ℤ) * (2 * (digAt len G T c i : ℤ))) := by
  rw [← sum_pow_eq_pack]
  unfold offYW
  push_cast
  rfl

lemma offYb_cast {K ρ n : ℕ} (A : Fin nf) (oA sA i : ℕ) :
    ((offYb len K ρ n A oA sA i : ℕ) : ℤ) =
      2 ^ ρ * pack (2 ^ K) ((List.range n).map fun c => (b2n (bitAt len A oA sA c i) : ℤ)) := by
  rw [← sum_pow_eq_pack]
  unfold offYb
  push_cast
  rfl

lemma offBb_cast {G n : ℕ} (A : Fin nf) (oA sA i : ℕ) :
    ((offBb len G n A oA sA i : ℕ) : ℤ) =
      pack (2 ^ G) ((List.range n).map fun c => (b2n (bitAt len A oA sA c i) : ℤ)) := by
  have := sum_pow_eq_pack G 0 n (fun c => (b2n (bitAt len A oA sA c i) : ℤ))
  simp only [Nat.zero_add, pow_zero, one_mul] at this
  rw [← this]
  unfold offBb
  push_cast
  rfl

lemma offBx_cast {Y : Fin nf} {K ρ G n : ℕ} (A : Fin nf) (oA sA i : ℕ) :
    ((offBx len Y K ρ G n A oA sA i : ℕ) : ℤ) =
      pack (2 ^ G) ((List.range n).map fun c =>
        (b2n (xor (bitAt len Y ρ K c i) (bitAt len A oA sA c i)) : ℤ)) := by
  have := sum_pow_eq_pack G 0 n
    (fun c => (b2n (xor (bitAt len Y ρ K c i) (bitAt len A oA sA c i)) : ℤ))
  simp only [Nat.zero_add, pow_zero, one_mul] at this
  rw [← this]
  unfold offBx
  push_cast
  rfl

lemma assemble_add (K ρ n : ℕ) (lo hi : ℤ) (d e : ℕ → ℤ) :
    assemble K ρ n lo hi d + 2 ^ ρ * pack (2 ^ K) ((List.range n).map e) =
      assemble K ρ n lo hi (fun c => d c + e c) := by
  unfold assemble
  rw [← pack_range_add]
  ring

lemma rotVal_false_cast (W off v : ℕ) :
    ((rotVal W false off v : ℕ) : ℤ) = ((v : ℤ) + off) % 2 ^ W := by
  simp [rotVal]

lemma rotVal_true_cast (W : ℕ) {off : ℕ} (hoff : off < 2 ^ W) (v : ℕ) :
    ((rotVal W true off v : ℕ) : ℤ) = ((v : ℤ) - off) % 2 ^ W := by
  simp only [rotVal, ↓reduceIte, Nat.mod_eq_of_lt hoff]
  push_cast [Nat.cast_sub hoff.le]
  have : (v : ℤ) + ((2 : ℤ) ^ W - off) = ((v : ℤ) - off) + 2 ^ W * 1 := by ring
  rw [this, Int.add_mul_emod_self_left]

/-- Adding a packed segment offset to an `(n+1)K`-bit value whose segments stay in range acts
segmentwise without wrap. -/
lemma rotVal_false_assemble {K ρ n : ℕ} (hρ : ρ ≤ K) (lo hi : ℤ) (d e : ℕ → ℤ)
    (h : Fits K ρ n lo hi d) (he : ∀ c < n, 0 ≤ d c + e c ∧ d c + e c < 2 ^ K) {v off : ℕ}
    (hv : (v : ℤ) = assemble K ρ n lo hi d)
    (hoff : (off : ℤ) = 2 ^ ρ * pack (2 ^ K) ((List.range n).map e)) :
    ((rotVal ((n + 1) * K) false off v : ℕ) : ℤ) = assemble K ρ n lo hi (fun c => d c + e c) := by
  have hf : Fits K ρ n lo hi (fun c => d c + e c) := ⟨h.1, h.2.1, he⟩
  have hb := assemble_bounds K ρ n hρ lo hi _ hf
  rw [rotVal_false_cast, hv, hoff, assemble_add]
  exact Int.emod_eq_of_lt hb.1 hb.2

/-- Subtracting a packed segment offset, segmentwise without wrap. -/
lemma rotVal_true_assemble {K ρ n : ℕ} (hρ : ρ ≤ K) (lo hi : ℤ) (d e : ℕ → ℤ)
    (h : Fits K ρ n lo hi d) (he : ∀ c < n, 0 ≤ e c ∧ 0 ≤ d c - e c ∧ d c - e c < 2 ^ K)
    {v off : ℕ} (hv : (v : ℤ) = assemble K ρ n lo hi d)
    (hoff : (off : ℤ) = 2 ^ ρ * pack (2 ^ K) ((List.range n).map e)) :
    ((rotVal ((n + 1) * K) true off v : ℕ) : ℤ) = assemble K ρ n lo hi (fun c => d c - e c) := by
  have hf : Fits K ρ n lo hi (fun c => d c - e c) := ⟨h.1, h.2.1, fun c hc => (he c hc).2⟩
  have hb := assemble_bounds K ρ n hρ lo hi _ hf
  have hbv := assemble_bounds K ρ n hρ lo hi d h
  have hoff_le : (off : ℤ) ≤ v := by
    rw [hv, hoff]
    have : assemble K ρ n lo hi d = assemble K ρ n lo hi (fun c => d c - e c) +
        2 ^ ρ * pack (2 ^ K) ((List.range n).map e) := by
      rw [assemble_add]
      congr 1
      funext c
      ring
    rw [this]
    linarith [hb.1]
  have hoff_lt : off < 2 ^ ((n + 1) * K) := by
    have : (off : ℤ) < 2 ^ ((n + 1) * K) := by linarith [hbv.2]
    exact_mod_cast this
  rw [rotVal_true_cast _ hoff_lt, hv, hoff]
  have : assemble K ρ n lo hi d - 2 ^ ρ * pack (2 ^ K) ((List.range n).map e) =
      assemble K ρ n lo hi (fun c => d c - e c) := by
    rw [sub_eq_iff_eq_add, assemble_add]
    congr 1
    funext c
    ring
  rw [this]
  exact Int.emod_eq_of_lt hb.1 hb.2

/-- Adding packed digits to a digit field, digitwise without wrap. -/
lemma rotVal_false_pack {G n : ℕ} (w e : ℕ → ℤ)
    (he : ∀ c < n, 0 ≤ w c + e c ∧ w c + e c < 2 ^ G) {v off : ℕ}
    (hv : (v : ℤ) = pack (2 ^ G) ((List.range n).map w))
    (hoff : (off : ℤ) = pack (2 ^ G) ((List.range n).map e)) :
    ((rotVal (n * G) false off v : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => w c + e c) := by
  have hb := pack_bounds (2 ^ G) (by positivity) _ (bounded_range _ n _ he)
  rw [List.length_map, List.length_range] at hb
  rw [rotVal_false_cast, hv, hoff, pack_range_add]
  rw [Nat.mul_comm n G, pow_mul]
  exact Int.emod_eq_of_lt hb.1 hb.2

/-- Subtracting packed digits from a digit field, digitwise without wrap. -/
lemma rotVal_true_pack {G n : ℕ} (w e : ℕ → ℤ) (hw : ∀ c < n, 0 ≤ w c ∧ w c < 2 ^ G)
    (he : ∀ c < n, 0 ≤ e c ∧ 0 ≤ w c - e c ∧ w c - e c < 2 ^ G) {v off : ℕ}
    (hv : (v : ℤ) = pack (2 ^ G) ((List.range n).map w))
    (hoff : (off : ℤ) = pack (2 ^ G) ((List.range n).map e)) :
    ((rotVal (n * G) true off v : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => w c - e c) := by
  have hb := pack_bounds (2 ^ G) (by positivity) _
    (bounded_range _ n (fun c => w c - e c) (fun c hc => (he c hc).2))
  rw [List.length_map, List.length_range] at hb
  have hbw := pack_bounds (2 ^ G) (by positivity) _ (bounded_range _ n w hw)
  rw [List.length_map, List.length_range] at hbw
  have hsplit : pack (2 ^ G) ((List.range n).map w) =
      pack (2 ^ G) ((List.range n).map fun c => w c - e c) +
        pack (2 ^ G) ((List.range n).map e) := by
    rw [pack_range_add]
    congr 1
    exact List.map_congr_left (fun c _ => by ring)
  have hoff_le : (off : ℤ) ≤ v := by rw [hv, hoff, hsplit]; linarith [hb.1]
  have hoff_lt : off < 2 ^ (n * G) := by
    have : (off : ℤ) < (2 ^ G) ^ n := by linarith [hbw.2]
    rw [← pow_mul, Nat.mul_comm G n] at this
    exact_mod_cast this
  rw [rotVal_true_cast _ hoff_lt, hv, hoff, hsplit, add_sub_cancel_right]
  rw [Nat.mul_comm n G, pow_mul]
  exact Int.emod_eq_of_lt hb.1 hb.2

end Arith

/-! ### Bits of a sum of distinct powers of two -/

section SumPow

lemma b2n_testBit (b : Bool) (k : ℕ) : (b2n b).testBit k = (b && decide (k = 0)) := by
  cases b
  · simp [b2n]
  · simp only [b2n, ↓reduceIte, Bool.true_and]
    cases k with
    | zero => simp
    | succ k => simp [Nat.testBit_succ]

lemma sum_pow_lt (p : ℕ → ℕ) (b : ℕ → Bool) (hp : ∀ c, p c + 1 ≤ p (c + 1)) :
    ∀ n, ∑ c ∈ Finset.range n, b2n (b c) * 2 ^ p c < 2 ^ p n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_pow_lt p b hp n
    have h1 := b2n_le_one (b n)
    have h2 := hp n
    have h3 : 2 ^ p n * 2 ≤ 2 ^ p (n + 1) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) h2
    have h4 := Nat.mul_le_mul_right (2 ^ p n) h1
    omega

lemma p_mono (p : ℕ → ℕ) (hp : ∀ c, p c + 1 ≤ p (c + 1)) {c n : ℕ} (h : c < n) : p c < p n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact lt_of_lt_of_le (ih h) (by have := hp n; omega)
    · have := hp c; omega

/-- Bit `t` of `∑_{c<n} [b_c] 2^{p_c}` for strictly increasing positions. -/
lemma testBit_sum_pow (p : ℕ → ℕ) (b : ℕ → Bool) (hp : ∀ c, p c + 1 ≤ p (c + 1)) :
    ∀ n t, (∑ c ∈ Finset.range n, b2n (b c) * 2 ^ p c).testBit t =
      decide (∃ c < n, p c = t ∧ b c = true)
  | 0, t => by simp
  | n + 1, t => by
    rw [Finset.sum_range_succ, Nat.add_comm, Nat.mul_comm,
      Nat.testBit_two_pow_mul_add _ (sum_pow_lt p b hp n), testBit_sum_pow p b hp n t]
    by_cases ht : t < p n
    · simp only [ht, ↓reduceIte]
      congr 1
      apply propext
      constructor
      · rintro ⟨c, hc, rfl, hb⟩; exact ⟨c, by omega, rfl, hb⟩
      · rintro ⟨c, hc, rfl, hb⟩
        refine ⟨c, ?_, rfl, hb⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
        · exact hc
        · omega
    · have ht' : ¬ t < p n := ht
      simp only [ht', ↓reduceIte, b2n_testBit]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.lt_succ_iff]
      rw [not_lt] at ht
      constructor
      · rintro ⟨hb, ht0⟩
        exact ⟨n, le_rfl, by omega, hb⟩
      · rintro ⟨c, hc, hpc, hbc⟩
        rcases Nat.lt_or_eq_of_le hc with hc | rfl
        · have := p_mono p hp hc; omega
        · exact ⟨hbc, by omega⟩

end SumPow


/-! ### The control mask and the ideal map -/

section Mask

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix
open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma sel_pos_step {K ρ : ℕ} (hK : 1 ≤ K) (c : ℕ) : ρ + c * K + 1 ≤ ρ + (c + 1) * K := by
  rw [Nat.succ_mul]; omega

lemma testBit_offYb {K ρ n : ℕ} (hK : 1 ≤ K) (A : Fin nf) (oA sA i t : ℕ) :
    (offYb len K ρ n A oA sA i).testBit t =
      decide (∃ c < n, ρ + c * K = t ∧ bitAt len A oA sA c i = true) :=
  testBit_sum_pow (fun c => ρ + c * K) (fun c => bitAt len A oA sA c i) (sel_pos_step hK) n t

lemma cbit_offYb {K ρ n : ℕ} (hK : 1 ≤ K) (A : Fin nf) (oA sA i : ℕ) {c : ℕ} (hc : c < n) :
    cbit K ρ (offYb len K ρ n A oA sA i) c = (b2n (bitAt len A oA sA c i) : ℤ) := by
  unfold cbit
  rw [testBit_offYb len hK]
  have key : (∃ c' < n, ρ + c' * K = ρ + c * K ∧ bitAt len A oA sA c' i = true) ↔
      bitAt len A oA sA c i = true := by
    constructor
    · rintro ⟨c', _, h, hb⟩
      have : c' = c := by
        have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < K) (by omega : c' * K = c * K)
        exact this
      rwa [this] at hb
    · intro hb; exact ⟨c, hc, rfl, hb⟩
  simp only [decide_eq_true_eq, key]
  cases bitAt len A oA sA c i <;> simp [b2n]

lemma offYb_and_selMask {K ρ n : ℕ} (hK : 1 ≤ K) (A : Fin nf) (oA sA i : ℕ) :
    offYb len K ρ n A oA sA i &&& selMask K ρ n = offYb len K ρ n A oA sA i := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, testBit_offYb len hK]
  by_cases h : ∃ c < n, ρ + c * K = t ∧ bitAt len A oA sA c i = true
  · obtain ⟨c, hc, rfl, hb⟩ := h
    have : (selMask K ρ n).testBit (ρ + c * K) = true :=
      (testBit_selMask K ρ n _).mpr ⟨c, hc, rfl⟩
    simp [this]
  · simp [h]

/-- The ideal XOR of a mask into `y`, as assembled toggled segments (`PackedXor.idealT_rep`
without the triple). -/
lemma xor_rep {K ρ n : ℕ} (hρ : ρ < K) (x y : ℕ) :
    (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) =
      assemble K ρ n ((y : ℤ) % 2 ^ ρ) ((y : ℤ) / 2 ^ ρ / (2 ^ K) ^ n)
        (fun c => toggle (seg K ρ (y : ℤ) c) (cbit K ρ x c)) := by
  have hK : 1 ≤ K := by omega
  rw [decompose K ρ n (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ)]
  have h1 : (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) % 2 ^ ρ = (y : ℤ) % 2 ^ ρ := by
    exact_mod_cast xor_lo K ρ n x y
  have h2 : (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) / 2 ^ ρ / (2 ^ K) ^ n =
      (y : ℤ) / 2 ^ ρ / (2 ^ K) ^ n := by
    rw [Int.ediv_ediv_of_nonneg (by positivity), Int.ediv_ediv_of_nonneg (by positivity),
      ← pow_mul, ← pow_add, Nat.mul_comm K n]
    exact_mod_cast xor_hi K ρ n hK x y
  rw [h1, h2]
  apply assemble_congr
  intro c hc
  unfold seg cbit
  have h3 := xor_seg K ρ n hK x y hc
  have h4 : (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) / 2 ^ (ρ + c * K) % 2 ^ K =
      (((y ^^^ (x &&& selMask K ρ n)) / 2 ^ (ρ + c * K) % 2 ^ K : ℕ) : ℤ) := by
    push_cast; rfl
  have h5 : (y : ℤ) / 2 ^ (ρ + c * K) % 2 ^ K = ((y / 2 ^ (ρ + c * K) % 2 ^ K : ℕ) : ℤ) := by
    push_cast; rfl
  rw [h4, h3, natCast_xor_bit, h5]

/-- The digits of a field whose value is a pack of bounded digits. -/
lemma digAt_of_pack (D : Fin nf) {G n : ℕ} (f : ℕ → ℤ) (hf : ∀ c < n, 0 ≤ f c ∧ f c < 2 ^ G)
    {j : ℕ} (hj : ((dig len D j : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map f)) {c : ℕ}
    (hc : c < n) : ((digAt len G D c j : ℕ) : ℤ) = f c := by
  have hd := digits_pack (2 ^ G) (by positivity) ((List.range n).map f) (bounded_range _ n f hf)
  rw [List.length_map, List.length_range] at hd
  have h1 := congrArg (fun l => l[c]?) hd
  simp only [digits_eq_range _ (by positivity : (0 : ℤ) ≤ 2 ^ G), List.getElem?_map,
    List.getElem?_range hc, Option.map_some, Option.some.injEq] at h1
  rw [← hj] at h1
  unfold digAt
  rw [Nat.mul_comm c G, pow_mul]
  push_cast
  exact h1

lemma b2n_decide_mod (d : ℤ) (hd : 0 ≤ d) : (b2n (decide (d % 2 = 1)) : ℤ) = d % 2 := by
  have : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases this with h | h <;> simp [b2n, h]

lemma b2n_xor (a b : Bool) : (b2n (xor a b) : ℤ) = ((b2n a : ℤ) + b2n b) % 2 := by
  cases a <;> cases b <;> simp [b2n]

lemma b2n_zero_or_one (b : Bool) : (b2n b : ℤ) = 0 ∨ (b2n b : ℤ) = 1 := by
  cases b <;> simp [b2n]

end Mask

/-! ### Offsets depend only on the fields they read -/

section Congr

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma offYW_congr {T : Fin nf} {K ρ G n : ℕ} (A : Fin nf) (oA sA : ℕ) {i j : ℕ}
    (hA : dig len A i = dig len A j) (hT : dig len T i = dig len T j) :
    offYW len T K ρ G n A oA sA i = offYW len T K ρ G n A oA sA j := by
  simp only [offYW, bitAt, digAt, hA, hT]

lemma offYb_congr {K ρ n : ℕ} (A : Fin nf) (oA sA : ℕ) {i j : ℕ}
    (hA : dig len A i = dig len A j) :
    offYb len K ρ n A oA sA i = offYb len K ρ n A oA sA j := by
  simp only [offYb, bitAt, hA]

lemma offBb_congr {G n : ℕ} (A : Fin nf) (oA sA : ℕ) {i j : ℕ}
    (hA : dig len A i = dig len A j) :
    offBb len G n A oA sA i = offBb len G n A oA sA j := by
  simp only [offBb, bitAt, hA]

lemma offBx_congr {Y : Fin nf} {K ρ G n : ℕ} (A : Fin nf) (oA sA : ℕ) {i j : ℕ}
    (hA : dig len A i = dig len A j) (hY : dig len Y i = dig len Y j) :
    offBx len Y K ρ G n A oA sA i = offBx len Y K ρ G n A oA sA j := by
  simp only [offBx, bitAt, hA, hY]

end Congr

/-! ### The core sequence on a good index -/

section Core

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix
open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

set_option maxHeartbeats 1000000 in
/-- **The core sequence computes the XOR of the control bits into `y`.** On a good index the
four-step identity runs without carries in every column: `y` gains `offYb` (the control bits at
the selected positions), `t` and `b` return to their original values, and every other field is
unchanged. -/
theorem core_spec {T Y B A : Fin nf} {K ρ G n oA sA : ℕ} (hK : 1 ≤ K) (hρ : ρ < K)
    (hLY : len Y = (n + 1) * K) (hLT : len T = n * G) (hLB : len B = n * G)
    (hTY : T ≠ Y) (hBY : B ≠ Y) (hTB : T ≠ B) (hAY : A ≠ Y) (hAT : A ≠ T) (hAB : A ≠ B)
    {i : ℕ} (hi : i < 2 ^ ∑ g, len g) (hgood : GoodE len T Y K ρ G n i) :
    runC len (core len T Y B K ρ G n A oA sA) i =
      setDig len Y i (dig len Y i ^^^ offYb len K ρ n A oA sA i) := by
  obtain ⟨hdig, hgrd⟩ := hgood
  have hlenTB : len T = len B := by rw [hLT, hLB]
  have hρK : ρ ≤ K := hρ.le
  -- the program as nested maps, with the two `B` rotations conjugated to `T`
  simp only [runC, core, List.foldl_cons, List.foldl_nil, CInstr.run]
  set i₁ := rotF len Y false (offYW len T K ρ G n A oA sA) i with hi₁
  have hi₁lt := rotF_lt_sum len Y false (offYW len T K ρ G n A oA sA) hi
  rw [swap_rot_swap len hTB hlenTB false _ hi₁lt]
  set i₂ := rotF len T false (fun j => offBb len G n Y ρ K (swapF len T B j)) i₁ with hi₂
  have hi₂lt := rotF_lt_sum len T false (fun j => offBb len G n Y ρ K (swapF len T B j)) hi₁lt
  set i₃ := rotF len Y false (offYb len K ρ n A oA sA) i₂ with hi₃
  have hi₃lt := rotF_lt_sum len Y false (offYb len K ρ n A oA sA) hi₂lt
  set i₄ := rotF len Y true (offYW len T K ρ G n A oA sA) i₃ with hi₄
  have hi₄lt := rotF_lt_sum len Y true (offYW len T K ρ G n A oA sA) hi₃lt
  rw [swap_rot_swap len hTB hlenTB true _ hi₄lt]
  set i₅ := rotF len T true (fun j => offBx len Y K ρ G n A oA sA (swapF len T B j)) i₄ with hi₅
  have hi₅lt := rotF_lt_sum len T true
    (fun j => offBx len Y K ρ G n A oA sA (swapF len T B j)) hi₄lt
  -- the fields along the way
  have hA₁ : dig len A i₁ = dig len A i := dig_rotF_ne len hAY _ _ _
  have hT₁ : dig len T i₁ = dig len T i := dig_rotF_ne len hTY _ _ _
  have hB₁ : dig len B i₁ = dig len B i := dig_rotF_ne len hBY _ _ _
  have hY₁ : dig len Y i₁ = rotVal (len Y) false (offYW len T K ρ G n A oA sA i) (dig len Y i) :=
    dig_rotF len Y _ _ _
  have hA₂ : dig len A i₂ = dig len A i := by rw [hi₂, dig_rotF_ne len hAT, hA₁]
  have hY₂ : dig len Y i₂ = dig len Y i₁ := dig_rotF_ne len hTY.symm _ _ _
  have hB₂ : dig len B i₂ = dig len B i := by rw [hi₂, dig_rotF_ne len hTB.symm, hB₁]
  have hT₂ : dig len T i₂ = rotVal (len T) false (offBb len G n Y ρ K i₁) (dig len T i) := by
    rw [hi₂, dig_rotF, hT₁]
    congr 1
    exact offBb_congr len Y ρ K (dig_swapF_ne len hTY.symm hBY.symm hlenTB i₁)
  have hA₃ : dig len A i₃ = dig len A i := by rw [hi₃, dig_rotF_ne len hAY, hA₂]
  have hT₃ : dig len T i₃ = dig len T i₂ := dig_rotF_ne len hTY _ _ _
  have hB₃ : dig len B i₃ = dig len B i := by rw [hi₃, dig_rotF_ne len hBY, hB₂]
  have hY₃ : dig len Y i₃ = rotVal (len Y) false (offYb len K ρ n A oA sA i) (dig len Y i₁) := by
    rw [hi₃, dig_rotF, hY₂, offYb_congr len A oA sA hA₂]
  have hA₄ : dig len A i₄ = dig len A i := by rw [hi₄, dig_rotF_ne len hAY, hA₃]
  have hT₄ : dig len T i₄ = dig len T i₂ := by rw [hi₄, dig_rotF_ne len hTY, hT₃]
  have hB₄ : dig len B i₄ = dig len B i := by rw [hi₄, dig_rotF_ne len hBY, hB₃]
  have hY₄ : dig len Y i₄ = rotVal (len Y) true (offYW len T K ρ G n A oA sA i₃) (dig len Y i₃) :=
    dig_rotF len Y _ _ _
  have hA₅ : dig len A i₅ = dig len A i := by rw [hi₅, dig_rotF_ne len hAT, hA₄]
  have hY₅ : dig len Y i₅ = dig len Y i₄ := dig_rotF_ne len hTY.symm _ _ _
  have hB₅ : dig len B i₅ = dig len B i := by rw [hi₅, dig_rotF_ne len hTB.symm, hB₄]
  have hT₅ : dig len T i₅ = rotVal (len T) true (offBx len Y K ρ G n A oA sA i₄) (dig len T i₂) := by
    rw [hi₅, dig_rotF, hT₄]
    congr 1
    exact offBx_congr len A oA sA (dig_swapF_ne len hAT hAB hlenTB i₄)
      (dig_swapF_ne len hTY.symm hBY.symm hlenTB i₄)
  -- the integer picture of the columns
  set y₀ := dig len Y i with hy₀
  set t₀ := dig len T i with ht₀
  have hB2pos : (0 : ℤ) < 2 ^ G := by positivity
  set d : ℕ → ℤ := seg K ρ (y₀ : ℤ) with hd
  set lo : ℤ := (y₀ : ℤ) % 2 ^ ρ with hlo
  set hiv : ℤ := (y₀ : ℤ) / 2 ^ ρ / (2 ^ K) ^ n with hhiv
  set z : ℕ → ℤ := fun c => (b2n (bitAt len A oA sA c i) : ℤ) with hz
  set w : ℕ → ℤ := fun c => ((digAt len G T c i : ℕ) : ℤ) with hw
  set a : ℕ → ℤ := fun c => d c % 2 with ha
  have hy₀lt : y₀ < 2 ^ ((n + 1) * K) := hLY ▸ dig_lt len Y i
  have hy₀rep : (y₀ : ℤ) = assemble K ρ n lo hiv d := decompose K ρ n (y₀ : ℤ)
  have hfits : Fits K ρ n lo hiv d :=
    decompose_fits K ρ n hρK (y₀ : ℤ) ⟨by positivity, by exact_mod_cast hy₀lt⟩
  have hz01 : ∀ c, z c = 0 ∨ z c = 1 := fun c => b2n_zero_or_one _
  have hw01 : ∀ c < n, 0 ≤ w c ∧ w c + 2 ≤ 2 ^ G := fun c hc => by
    have := hdig c hc
    constructor
    · positivity
    · simp only [hw]; exact_mod_cast this
  have hdb : ∀ c < n, 4 * 2 ^ G ≤ d c ∧ d c + 4 * 2 ^ G + 1 ≤ 2 ^ K := fun c hc => by
    have := seg_bounds_of_guard' hK (2 ^ (G + 1)) y₀ c (hgrd c hc)
    rw [pow_succ] at this
    push_cast at this
    simp only [hd]
    constructor <;> linarith [this.1, this.2]
  have ha01 : ∀ c, 0 ≤ a c ∧ a c ≤ 1 := fun c => by
    rcases Int.emod_two_eq_zero_or_one (d c) with h | h <;> simp only [ha, h] <;> norm_num
  have hd0 : ∀ c, 0 ≤ d c := fun c => Int.emod_nonneg _ (by positivity)
  -- `t₀` as a pack of its digits
  have ht₀rep : (t₀ : ℤ) = pack (2 ^ G) ((List.range n).map w) := dig_eq_pack len T hLT i
  clear_value d lo hiv z w a
  -- step 1: `y₁ = y₀ + ∑ 2 z w`
  set e₁ : ℕ → ℤ := fun c => z c * (2 * w c) with he₁
  have hy₁ : ((dig len Y i₁ : ℕ) : ℤ) = assemble K ρ n lo hiv (fun c => d c + e₁ c) := by
    rw [hY₁, hLY]
    refine rotVal_false_assemble hρK lo hiv d e₁ hfits ?_ hy₀rep ?_
    swap
    · rw [offYW_cast]
      congr 2
      apply List.map_congr_left
      intro c _
      simp only [he₁, hz, hw]
    intro c hc
    have h1 := hdb c hc; have h2 := hw01 c hc; have h3 := hz01 c
    simp only [he₁]
    rcases h3 with h3 | h3 <;> rw [h3] <;> simp only [zero_mul, one_mul, add_zero, mul_zero, sub_zero] <;>
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hB2pos]
  have hfits₁ : Fits K ρ n lo hiv (fun c => d c + e₁ c) := ⟨hfits.1, hfits.2.1, fun c hc => by
    have h1 := hdb c hc; have h2 := hw01 c hc; have h3 := hz01 c
    simp only [he₁]
    rcases h3 with h3 | h3 <;> rw [h3] <;> simp only [zero_mul, one_mul, add_zero, mul_zero, sub_zero] <;>
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hB2pos]⟩
  -- the selected bits of `y₁` are the parities `a`
  have hbit₁ : ∀ c < n, bitAt len Y ρ K c i₁ = decide (d c % 2 = 1) := fun c hc => by
    unfold bitAt
    rw [testBit_assemble K ρ n hK _ lo hiv _ hy₁ hfits₁ c hc]
    congr 1
    apply propext
    simp only [he₁]
    rcases hz01 c with h | h <;> rw [h] <;> simp only [zero_mul, one_mul, add_zero] <;> omega
  -- step 2: `t₁ = t₀ + ∑ a`
  have ht₂ : ((dig len T i₂ : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => w c + a c) := by
    rw [hT₂, hLT]
    refine rotVal_false_pack w a ?_ ht₀rep ?_
    · intro c hc
      have h1 := hw01 c hc; have h2 := ha01 c
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [offBb_cast]
      congr 1
      apply List.map_congr_left
      intro c hc
      rw [List.mem_range] at hc
      rw [hbit₁ c hc, b2n_decide_mod _ (hd0 c)]
      simp only [ha]
  have hwa : ∀ c < n, 0 ≤ w c + a c ∧ w c + a c < 2 ^ G := fun c hc => by
    have h1 := hw01 c hc; have h2 := ha01 c
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hdigT₂ : ∀ c < n, ((digAt len G T c i₂ : ℕ) : ℤ) = w c + a c := fun c hc =>
    digAt_of_pack len T (fun c => w c + a c) hwa ht₂ hc
  have ht₃ : ((dig len T i₃ : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => w c + a c) := by
    rw [hT₃]; exact ht₂
  have hdigT₃ : ∀ c < n, ((digAt len G T c i₃ : ℕ) : ℤ) = w c + a c := fun c hc =>
    digAt_of_pack len T (fun c => w c + a c) hwa ht₃ hc
  -- step 3: `y₂ = y₁ + ∑ z`
  have hy₃ : ((dig len Y i₃ : ℕ) : ℤ) = assemble K ρ n lo hiv (fun c => d c + e₁ c + z c) := by
    rw [hY₃, hLY]
    refine rotVal_false_assemble hρK lo hiv _ z hfits₁ ?_ hy₁ ?_
    swap
    · rw [offYb_cast]
      congr 2
      apply List.map_congr_left
      intro c _
      simp only [hz]
    intro c hc
    have h1 := hdb c hc; have h2 := hw01 c hc; have h3 := hz01 c
    simp only [he₁]
    rcases h3 with h3 | h3 <;> rw [h3] <;> simp only [zero_mul, one_mul, add_zero, mul_zero, sub_zero] <;>
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hB2pos]
  have hfits₃ : Fits K ρ n lo hiv (fun c => d c + e₁ c + z c) :=
    ⟨hfits.1, hfits.2.1, fun c hc => by
      have h1 := hdb c hc; have h2 := hw01 c hc; have h3 := hz01 c
      simp only [he₁]
      rcases h3 with h3 | h3 <;> rw [h3] <;> simp only [zero_mul, one_mul, add_zero, mul_zero, sub_zero] <;>
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hB2pos]⟩
  -- step 4: `y₃ = y₂ - ∑ 2 z (w + a)`
  set e₄ : ℕ → ℤ := fun c => z c * (2 * (w c + a c)) with he₄
  have hoff₄ : ((offYW len T K ρ G n A oA sA i₃ : ℕ) : ℤ) =
      2 ^ ρ * pack (2 ^ K) ((List.range n).map e₄) := by
    rw [offYW_cast]
    congr 1
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [List.mem_range] at hc
    simp only [he₄, hz, bitAt, hA₃]
    rw [hdigT₃ c hc]
  have hy₄ : ((dig len Y i₄ : ℕ) : ℤ) =
      assemble K ρ n lo hiv (fun c => d c + e₁ c + z c - e₄ c) := by
    rw [hY₄, hLY]
    refine rotVal_true_assemble hρK lo hiv _ e₄ hfits₃ ?_ hy₃ hoff₄
    intro c hc
    have h1 := hdb c hc; have h2 := hw01 c hc; have h3 := hz01 c; have h4 := ha01 c
    simp only [he₁, he₄]
    rcases h3 with h3 | h3 <;> rw [h3] <;> simp only [zero_mul, one_mul, add_zero, mul_zero, sub_zero] <;>
      refine ⟨?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2, hB2pos]
  have hseg₄ : ∀ c, d c + e₁ c + z c - e₄ c = toggle (d c) (z c) := fun c => by
    simp only [he₁, he₄, toggle, ha]; ring
  have hy₄' : ((dig len Y i₄ : ℕ) : ℤ) =
      assemble K ρ n lo hiv (fun c => toggle (d c) (z c)) := by
    rw [hy₄]; exact assemble_congr K ρ n lo hiv _ _ (fun c _ => hseg₄ c)
  have hfits₄ : Fits K ρ n lo hiv (fun c => toggle (d c) (z c)) :=
    ⟨hfits.1, hfits.2.1, fun c hc => by
      have h1 := hdb c hc; have h3 := hz01 c
      have h4 : 0 ≤ d c % 2 ∧ d c % 2 ≤ 1 := by have := ha01 c; simpa only [ha] using this
      simp only [toggle]
      rcases h3 with h3 | h3 <;> rw [h3] <;> simp only [zero_mul, one_mul, add_zero, mul_zero, sub_zero] <;>
      constructor <;> linarith [h1.1, h1.2, h4.1, h4.2, hB2pos]⟩
  -- the selected bits of `y₃` are `a ⊕ z`
  have hbit₄ : ∀ c < n, bitAt len Y ρ K c i₄ = decide ((a c + z c) % 2 = 1) := fun c hc => by
    unfold bitAt
    rw [testBit_assemble K ρ n hK _ lo hiv _ hy₄' hfits₄ c hc, toggle_parity _ _ (hz01 c)]
    simp only [ha]
  -- step 5: `t₂ = t₁ - ∑ a = t₀`
  have hoff₅ : ((offBx len Y K ρ G n A oA sA i₄ : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map a) := by
    rw [offBx_cast]
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [List.mem_range] at hc
    rw [b2n_xor, hbit₄ c hc, b2n_decide_mod _ (by have := ha01 c; have := hz01 c; omega)]
    have hzc : ((b2n (bitAt len A oA sA c i₄) : ℕ) : ℤ) = z c := by simp only [hz, bitAt, hA₄]
    rw [hzc]
    have hz' := hz01 c
    have ha' := ha01 c
    rcases hz' with h | h <;> rw [h] <;> omega
  have ht₅ : ((dig len T i₅ : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => w c + a c - a c) := by
    rw [hT₅, hLT]
    exact rotVal_true_pack (fun c => w c + a c) a hwa (fun c hc => by
      have h1 := hw01 c hc; have h2 := ha01 c
      refine ⟨h2.1, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]) ht₂ hoff₅
  have ht₅' : dig len T i₅ = t₀ := by
    have : ((dig len T i₅ : ℕ) : ℤ) = (t₀ : ℤ) := by
      rw [ht₅, ht₀rep]
      congr 1
      apply List.map_congr_left
      intro c _
      ring
    exact_mod_cast this
  -- the final `y` is the ideal XOR
  have hyfin : dig len Y i₅ = y₀ ^^^ offYb len K ρ n A oA sA i := by
    have : ((dig len Y i₅ : ℕ) : ℤ) = (((y₀ ^^^ offYb len K ρ n A oA sA i : ℕ)) : ℤ) := by
      rw [hY₅, hy₄', ← offYb_and_selMask len hK A oA sA i, xor_rep hρ, hlo, hhiv]
      apply assemble_congr
      intro c hc
      rw [cbit_offYb len hK A oA sA i hc, hd, hz]
    exact_mod_cast this
  -- extensionality
  have hxor_lt : y₀ ^^^ offYb len K ρ n A oA sA i < 2 ^ len Y := by
    apply Nat.xor_lt_two_pow (dig_lt len Y i)
    have := testBit_offYb len (K := K) (ρ := ρ) (n := n) hK A oA sA i
    apply Nat.lt_pow_two_of_testBit
    intro t ht
    rw [this, decide_eq_false_iff_not]
    rintro ⟨c, hc, rfl, _⟩
    rw [hLY] at ht
    have : (c + 1) * K ≤ n * K := Nat.mul_le_mul_right K hc
    rw [Nat.succ_mul] at ht this
    omega
  apply ext_dig len hi₅lt (setDig_lt (R := 1) len Y (by rw [one_mul]; exact hi) hxor_lt
    (foff_add_len_le_sum len Y) |>.trans_eq (one_mul _))
  intro f
  by_cases hfY : f = Y
  · subst hfY; rw [hyfin, dig_setDig_self len _ i hxor_lt]
  rw [dig_setDig_ne len hfY i hxor_lt]
  by_cases hfT : f = T
  · subst hfT; exact ht₅'
  by_cases hfB : f = B
  · subst hfB; exact hB₅
  by_cases hfA : f = A
  · subst hfA; exact hA₅
  · -- any other field is untouched by every instruction
    have h1 : dig len f i₁ = dig len f i := dig_rotF_ne len hfY _ _ _
    have h2 : dig len f i₂ = dig len f i₁ := dig_rotF_ne len hfT _ _ _
    have h3 : dig len f i₃ = dig len f i₂ := dig_rotF_ne len hfY _ _ _
    have h4 : dig len f i₄ = dig len f i₃ := dig_rotF_ne len hfY _ _ _
    have h5 : dig len f i₅ = dig len f i₄ := dig_rotF_ne len hfT _ _ _
    rw [h5, h4, h3, h2, h1]

end Core


/-! ### The earlier source, well-formedness and the top fixup -/

section Programs

open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- With the control bits of `x` at the selected positions, the control mask is `x ∧ selMask`. -/
lemma offYb_X {K ρ n : ℕ} (hK : 1 ≤ K) (X : Fin nf) (i : ℕ) :
    offYb len K ρ n X ρ K i = dig len X i &&& selMask K ρ n := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_offYb len hK, Nat.testBit_and]
  by_cases h : ∃ c < n, ρ + c * K = t ∧ bitAt len X ρ K c i = true
  · obtain ⟨c, hc, rfl, hb⟩ := h
    have hs : (selMask K ρ n).testBit (ρ + c * K) = true :=
      (testBit_selMask K ρ n _).mpr ⟨c, hc, rfl⟩
    have hb' : (dig len X i).testBit (ρ + c * K) = true := hb
    rw [hs, hb', Bool.and_true]
    exact decide_eq_true ⟨c, hc, rfl, hb⟩
  · simp only [decide_eq_false_iff_not.mpr h]
    by_cases hsel : IsSel K ρ n t
    · obtain ⟨c, hc, rfl⟩ := hsel
      have : bitAt len X ρ K c i = false := by
        cases hb : bitAt len X ρ K c i
        · rfl
        · exact absurd ⟨c, hc, rfl, hb⟩ h
      unfold bitAt at this
      simp [this]
    · simp [selMask_false K ρ n hsel]

/-- **The earlier source computes the ideal map** on every good index. -/
theorem progE_spec {T X Y B : Fin nf} {K ρ G n : ℕ} (hK : 1 ≤ K) (hρ : ρ < K)
    (hLY : len Y = (n + 1) * K) (hLT : len T = n * G) (hLB : len B = n * G)
    (hTY : T ≠ Y) (hBY : B ≠ Y) (hTB : T ≠ B) (hXY : X ≠ Y) (hXT : X ≠ T) (hXB : X ≠ B)
    {i : ℕ} (hi : i < 2 ^ ∑ g, len g) (hgood : GoodE len T Y K ρ G n i) :
    runC len (progE len T X Y B K ρ G n) i = idealC len X Y K ρ n i := by
  unfold progE idealC
  rw [core_spec len hK hρ hLY hLT hLB hTY hBY hTB hXY hXT hXB hi hgood, offYb_X len hK]

lemma offYW_ignores {T Y : Fin nf} {K ρ G n : ℕ} (A : Fin nf) (oA sA : ℕ) (hAY : A ≠ Y)
    (hTY : T ≠ Y) : IgnoresF len Y (offYW len T K ρ G n A oA sA) := by
  intro i v hv
  exact offYW_congr len A oA sA (dig_setDig_ne len hAY i hv) (dig_setDig_ne len hTY i hv)

lemma offYb_ignores {Y : Fin nf} {K ρ n : ℕ} (A : Fin nf) (oA sA : ℕ) (hAY : A ≠ Y) :
    IgnoresF len Y (offYb len K ρ n A oA sA) := by
  intro i v hv
  exact offYb_congr len A oA sA (dig_setDig_ne len hAY i hv)

lemma offBb_ignores {B : Fin nf} {G n : ℕ} (A : Fin nf) (oA sA : ℕ) (hAB : A ≠ B) :
    IgnoresF len B (offBb len G n A oA sA) := by
  intro i v hv
  exact offBb_congr len A oA sA (dig_setDig_ne len hAB i hv)

lemma offBx_ignores {Y B : Fin nf} {K ρ G n : ℕ} (A : Fin nf) (oA sA : ℕ) (hAB : A ≠ B)
    (hYB : Y ≠ B) : IgnoresF len B (offBx len Y K ρ G n A oA sA) := by
  intro i v hv
  exact offBx_congr len A oA sA (dig_setDig_ne len hAB i hv) (dig_setDig_ne len hYB i hv)

/-- The core sequence is well formed below every bit `S` above its fields. -/
lemma core_WF {T Y B A : Fin nf} {K ρ G n oA sA S : ℕ} (hLT : len T = n * G) (hLB : len B = n * G)
    (hTY : T ≠ Y) (hBY : B ≠ Y) (hTB : T ≠ B) (hAY : A ≠ Y) (hAB : A ≠ B)
    (hST : foff len T + len T ≤ S) (hSY : foff len Y + len Y ≤ S) (hSB : foff len B + len B ≤ S) :
    ∀ ins ∈ core len T Y B K ρ G n A oA sA, ins.WF len S := by
  have hlen : len T = len B := by rw [hLT, hLB]
  intro ins hins
  simp only [core, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hins
  rcases hins with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨offYW_ignores len A oA sA hAY hTY, hSY⟩
  · exact ⟨hTB, hlen, hST, hSB⟩
  · exact ⟨offBb_ignores len Y ρ K hBY.symm, hSB⟩
  · exact ⟨hTB, hlen, hST, hSB⟩
  · exact ⟨offYb_ignores len A oA sA hAY, hSY⟩
  · exact ⟨offYW_ignores len A oA sA hAY hTY, hSY⟩
  · exact ⟨hTB, hlen, hST, hSB⟩
  · exact ⟨offBx_ignores len A oA sA hAB hBY.symm, hSB⟩
  · exact ⟨hTB, hlen, hST, hSB⟩

lemma progE_WF {T X Y B : Fin nf} {K ρ G n S : ℕ} (hLT : len T = n * G) (hLB : len B = n * G)
    (hTY : T ≠ Y) (hBY : B ≠ Y) (hTB : T ≠ B) (hXY : X ≠ Y) (hXB : X ≠ B)
    (hST : foff len T + len T ≤ S) (hSY : foff len Y + len Y ≤ S) (hSB : foff len B + len B ≤ S) :
    ∀ ins ∈ progE len T X Y B K ρ G n, ins.WF len S :=
  core_WF len hLT hLB hTY hBY hTB hXY hXB hST hSY hSB

lemma loadU_WF {U X B : Fin nf} {K ρ G n S : ℕ} (hLU : len U = n * G) (hLB : len B = n * G)
    (hUB : U ≠ B) (hXB : X ≠ B) (hSU : foff len U + len U ≤ S) (hSB : foff len B + len B ≤ S)
    (neg : Bool) : ∀ ins ∈ loadU len U X B K ρ G n neg, ins.WF len S := by
  have hlen : len U = len B := by rw [hLU, hLB]
  intro ins hins
  simp only [loadU, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hins
  rcases hins with rfl | rfl | rfl
  · exact ⟨hUB, hlen, hSU, hSB⟩
  · exact ⟨offBb_ignores len X ρ K hXB, hSB⟩
  · exact ⟨hUB, hlen, hSU, hSB⟩

lemma progL_WF {U T X Y B : Fin nf} {K ρ G n S : ℕ} (hLU : len U = n * G) (hLT : len T = n * G)
    (hLB : len B = n * G) (hTY : T ≠ Y) (hBY : B ≠ Y) (hTB : T ≠ B) (hUY : U ≠ Y) (hUB : U ≠ B)
    (hXB : X ≠ B) (hSU : foff len U + len U ≤ S) (hST : foff len T + len T ≤ S)
    (hSY : foff len Y + len Y ≤ S) (hSB : foff len B + len B ≤ S) :
    ∀ ins ∈ progL len U T X Y B K ρ G n, ins.WF len S := by
  intro ins hins
  simp only [progL, List.mem_append] at hins
  rcases hins with ((h | h) | h) | h
  · exact core_WF len hLT hLB hTY hBY hTB hUY hUB hST hSY hSB ins h
  · exact loadU_WF len hLU hLB hUB hXB hSU hSB false ins h
  · exact core_WF len hLT hLB hTY hBY hTB hUY hUB hST hSY hSB ins h
  · exact loadU_WF len hLU hLB hUB hXB hSU hSB true ins h

/-- The top-position fixup `y_{ρ + nK} ← y_{ρ + nK} ⊕ x_{ρ + nK}`. -/
def topFixC (X Y : Fin nf) (K ρ n : ℕ) (i : ℕ) : ℕ :=
  setDig len Y i (dig len Y i ^^^ (dig len X i &&& 2 ^ (ρ + n * K)))

/-- The full XOR at all `n + 1` selected positions. -/
def fullXorC (X Y : Fin nf) (K ρ n : ℕ) (i : ℕ) : ℕ :=
  setDig len Y i (dig len Y i ^^^ (dig len X i &&& selMask K ρ (n + 1)))

/-- `fullXorC = topFixC ∘ idealC` (`PackedXor.xorSel_eq` on digits). -/
theorem fullXorC_eq {X Y : Fin nf} {K ρ n : ℕ} (hK : 1 ≤ K) (hXY : X ≠ Y) (hLXY : len X = len Y)
    (i : ℕ) : fullXorC len X Y K ρ n i = topFixC len X Y K ρ n (idealC len X Y K ρ n i) := by
  unfold fullXorC topFixC idealC
  have hX : dig len X i < 2 ^ len Y := by rw [← hLXY]; exact dig_lt len X i
  have h1 : dig len Y i ^^^ (dig len X i &&& selMask K ρ n) < 2 ^ len Y :=
    Nat.xor_lt_two_pow (dig_lt len Y i) (lt_of_le_of_lt Nat.and_le_left hX)
  rw [dig_setDig_self len Y i h1, dig_setDig_ne len hXY i h1,
    setDig_setDig_self len Y i h1 (Nat.xor_lt_two_pow h1 (lt_of_le_of_lt Nat.and_le_left hX))]
  congr 1
  rw [Nat.xor_assoc, ← Nat.and_xor_distrib_left]
  congr 2
  show selMask K ρ n ||| 2 ^ (ρ + n * K) = selMask K ρ n ^^^ 2 ^ (ρ + n * K)
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases ht : t = ρ + n * K
  · subst ht
    have : (selMask K ρ n).testBit (ρ + n * K) = false :=
      selMask_false K ρ n (by simpa using not_isSel_hi K ρ n hK 0)
    simp [this]
  · have ht' : ¬ (ρ + n * K = t) := fun h => ht h.symm
    simp [ht, ht']

end Programs


/-! ### The later source -/

section Later

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix
open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- `∑_{c<n} [b_c] 2^{ρ + cK}`. -/
def selSum (K ρ n : ℕ) (b : ℕ → Bool) : ℕ := ∑ c ∈ Finset.range n, b2n (b c) * 2 ^ (ρ + c * K)

lemma offYb_eq_selSum {K ρ n : ℕ} (A : Fin nf) (oA sA i : ℕ) :
    offYb len K ρ n A oA sA i = selSum K ρ n (fun c => bitAt len A oA sA c i) := rfl

lemma testBit_selSum {K ρ n : ℕ} (hK : 1 ≤ K) (b : ℕ → Bool) (t : ℕ) :
    (selSum K ρ n b).testBit t = decide (∃ c < n, ρ + c * K = t ∧ b c = true) :=
  testBit_sum_pow (fun c => ρ + c * K) b (sel_pos_step hK) n t

lemma selSum_xor {K ρ n : ℕ} (hK : 1 ≤ K) (b₁ b₂ : ℕ → Bool) :
    selSum K ρ n b₁ ^^^ selSum K ρ n b₂ = selSum K ρ n (fun c => xor (b₁ c) (b₂ c)) := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor, testBit_selSum hK, testBit_selSum hK, testBit_selSum hK]
  by_cases hsel : ∃ c < n, ρ + c * K = t
  · obtain ⟨c, hc, rfl⟩ := hsel
    have key : ∀ b : ℕ → Bool, (∃ c' < n, ρ + c' * K = ρ + c * K ∧ b c' = true) ↔ b c = true := by
      intro b
      constructor
      · rintro ⟨c', _, h, hb⟩
        have : c' = c := Nat.eq_of_mul_eq_mul_right (by omega : 0 < K) (by omega : c' * K = c * K)
        rwa [this] at hb
      · intro hb; exact ⟨c, hc, rfl, hb⟩
    simp only [key]
    cases b₁ c <;> cases b₂ c <;> simp
  · have h : ∀ b : ℕ → Bool, ¬ ∃ c < n, ρ + c * K = t ∧ b c = true := fun b ⟨c, hc, h, _⟩ =>
      hsel ⟨c, hc, h⟩
    simp only [h, decide_false, Bool.false_xor]

lemma selSum_congr {K ρ n : ℕ} {b₁ b₂ : ℕ → Bool} (h : ∀ c < n, b₁ c = b₂ c) :
    selSum K ρ n b₁ = selSum K ρ n b₂ := by
  unfold selSum
  apply Finset.sum_congr rfl
  intro c hc
  rw [h c (Finset.mem_range.mp hc)]

/-- The parity bit of digit `c` of a digit field. -/
lemma bitAt_zero_digit {G : ℕ} (hG : 1 ≤ G) (D : Fin nf) (c j : ℕ) :
    bitAt len D 0 G c j = decide (digAt len G D c j % 2 = 1) := by
  unfold bitAt digAt
  rw [Nat.zero_add, Nat.testBit_eq_decide_div_mod_eq]
  congr 2
  rw [Nat.mod_mod_of_dvd _ (by
    rw [show 2 ^ G = 2 * 2 ^ (G - 1) by rw [← pow_succ']; congr 1; omega]
    exact Dvd.intro _ rfl)]

/-- XOR with a mask supported on the selected positions keeps every guard. -/
lemma guardOK_xor {K ρ n : ℕ} (hK : 1 ≤ K) (m y mm c : ℕ) (hm : m &&& selMask K ρ n = m) :
    GuardOK K ρ mm (y ^^^ m) c ↔ GuardOK K ρ mm y c := by
  have := xor_guard K ρ n hK m y c
  rw [hm] at this
  unfold GuardOK PackedXor.guard
  rw [this]

/-- The good set of the earlier source is kept by XORing a selected-position mask into `y`. -/
lemma goodE_setDig_xor {T Y : Fin nf} {K ρ G n : ℕ} (hK : 1 ≤ K) (hTY : T ≠ Y) (i m : ℕ)
    (hm : m &&& selMask K ρ n = m) (hgood : GoodE len T Y K ρ G n i)
    (hlt : dig len Y i ^^^ m < 2 ^ len Y) :
    GoodE len T Y K ρ G n (setDig len Y i (dig len Y i ^^^ m)) := by
  obtain ⟨hdig, hgrd⟩ := hgood
  refine ⟨?_, ?_⟩
  · intro c hc
    unfold digAt
    rw [dig_setDig_ne len hTY i hlt]
    exact hdig c hc
  · intro c hc
    rw [dig_setDig_self len Y i hlt, guardOK_xor hK m _ _ c hm]
    exact hgrd c hc

lemma runC_lt_sum {S : ℕ} (P : List (CInstr nf)) (h : ∀ ins ∈ P, ins.WF len S)
    (hS : S = ∑ g, len g) : ∀ {i : ℕ}, i < 2 ^ ∑ g, len g → runC len P i < 2 ^ ∑ g, len g := by
  subst hS
  induction P with
  | nil => intro i hi; simpa [runC] using hi
  | cons ins P ih =>
    intro i hi
    rw [runC_cons]
    apply ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have := ins.run_lt (R := 1) len (h ins List.mem_cons_self) (by rw [one_mul]; exact hi)
    rwa [one_mul] at this

lemma runC_loadU {U X B : Fin nf} {K ρ G n : ℕ} (neg : Bool) (j : ℕ) :
    runC len (loadU len U X B K ρ G n neg) j =
      swapF len U B (rotF len B neg (offBb len G n X ρ K) (swapF len U B j)) := rfl

/-- **The later source computes the ideal map** on every good index. -/
theorem progL_spec {U T X Y B : Fin nf} {K ρ G n : ℕ} (hK : 1 ≤ K) (hG : 1 ≤ G) (hρ : ρ < K)
    (hLY : len Y = (n + 1) * K) (hLU : len U = n * G) (hLT : len T = n * G) (hLB : len B = n * G)
    (hTY : T ≠ Y) (hBY : B ≠ Y) (hTB : T ≠ B) (hUY : U ≠ Y) (hUT : U ≠ T) (hUB : U ≠ B)
    (hXY : X ≠ Y) (hXU : X ≠ U) (hXB : X ≠ B)
    {i : ℕ} (hi : i < 2 ^ ∑ g, len g) (hgood : GoodL len U T Y K ρ G n i) :
    runC len (progL len U T X Y B K ρ G n) i = idealC len X Y K ρ n i := by
  obtain ⟨hgoodE, hdigU⟩ := hgood
  have hlenUB : len U = len B := by rw [hLU, hLB]
  have hS := fun f => foff_add_len_le_sum len f
  -- the first core
  unfold progL
  rw [runC_append, runC_append, runC_append]
  set m₁ := offYb len K ρ n U 0 G i with hm₁
  have hm₁sel : m₁ &&& selMask K ρ n = m₁ := offYb_and_selMask len hK U 0 G i
  have hm₁lt : dig len Y i ^^^ m₁ < 2 ^ len Y := by
    apply Nat.xor_lt_two_pow (dig_lt len Y i)
    apply Nat.lt_pow_two_of_testBit
    intro t ht
    rw [hm₁, testBit_offYb len (K := K) (ρ := ρ) (n := n) hK, decide_eq_false_iff_not]
    rintro ⟨c, hc, rfl, _⟩
    rw [hLY] at ht
    have : (c + 1) * K ≤ n * K := Nat.mul_le_mul_right K hc
    rw [Nat.succ_mul] at ht this
    omega
  have h1 : runC len (core len T Y B K ρ G n U 0 G) i = setDig len Y i (dig len Y i ^^^ m₁) :=
    core_spec len hK hρ hLY hLT hLB hTY hBY hTB hUY hUT hUB hi hgoodE
  rw [h1]
  set i₁ := setDig len Y i (dig len Y i ^^^ m₁) with hi₁
  have hi₁lt : i₁ < 2 ^ ∑ g, len g := by
    have := setDig_lt (R := 1) len Y (by rw [one_mul]; exact hi) hm₁lt (hS Y)
    rwa [one_mul] at this
  have hY₁ : dig len Y i₁ = dig len Y i ^^^ m₁ := dig_setDig_self len Y i hm₁lt
  have hne₁ : ∀ f, f ≠ Y → dig len f i₁ = dig len f i := fun f hf => dig_setDig_ne len hf i hm₁lt
  -- the load of `x` into `u`
  rw [runC_loadU len false i₁, swap_rot_swap len hUB hlenUB false _ hi₁lt]
  set i₂ := rotF len U false (fun j => offBb len G n X ρ K (swapF len U B j)) i₁ with hi₂
  have hi₂lt := rotF_lt_sum len U false (fun j => offBb len G n X ρ K (swapF len U B j)) hi₁lt
  set u : ℕ → ℤ := fun c => ((digAt len G U c i : ℕ) : ℤ) with hu
  set x : ℕ → ℤ := fun c => (b2n (bitAt len X ρ K c i) : ℤ) with hx
  have hu0 : ∀ c < n, 0 ≤ u c ∧ u c + 2 ≤ 2 ^ G := fun c hc => by
    have := hdigU c hc
    exact ⟨by positivity, by simp only [hu]; exact_mod_cast this⟩
  have hx01 : ∀ c, x c = 0 ∨ x c = 1 := fun c => b2n_zero_or_one _
  have hux : ∀ c < n, 0 ≤ u c + x c ∧ u c + x c < 2 ^ G := fun c hc => by
    have h1 := hu0 c hc; have h2 := hx01 c
    rcases h2 with h2 | h2 <;> rw [h2] <;> constructor <;> linarith [h1.1, h1.2]
  have hurep : ((dig len U i : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map u) :=
    dig_eq_pack len U hLU i
  have hU₂ : ((dig len U i₂ : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => u c + x c) := by
    rw [hi₂, dig_rotF, hne₁ U hUY, hLU]
    refine rotVal_false_pack u x hux hurep ?_
    rw [offBb_congr len X ρ K (dig_swapF_ne len hXU hXB hlenUB i₁), offBb_cast]
    congr 1
    apply List.map_congr_left
    intro c _
    simp only [hx, bitAt, hne₁ X hXY]
  have hne₂ : ∀ f, f ≠ U → dig len f i₂ = dig len f i₁ := fun f hf => dig_rotF_ne len hf _ _ _
  -- the second core
  have hgood₂ : GoodE len T Y K ρ G n i₂ := by
    have := goodE_setDig_xor len hK hTY i m₁ hm₁sel hgoodE hm₁lt
    obtain ⟨hd, hg⟩ := this
    refine ⟨?_, ?_⟩
    · intro c hc
      unfold digAt
      rw [hne₂ T hUT.symm]
      exact hd c hc
    · intro c hc
      rw [hne₂ Y hUY.symm]
      exact hg c hc
  set m₂ := offYb len K ρ n U 0 G i₂ with hm₂
  have h2 : runC len (core len T Y B K ρ G n U 0 G) i₂ = setDig len Y i₂ (dig len Y i₂ ^^^ m₂) :=
    core_spec len hK hρ hLY hLT hLB hTY hBY hTB hUY hUT hUB hi₂lt hgood₂
  rw [h2]
  have hm₂lt : dig len Y i₂ ^^^ m₂ < 2 ^ len Y := by
    apply Nat.xor_lt_two_pow (dig_lt len Y i₂)
    apply Nat.lt_pow_two_of_testBit
    intro t ht
    rw [hm₂, testBit_offYb len (K := K) (ρ := ρ) (n := n) hK, decide_eq_false_iff_not]
    rintro ⟨c, hc, rfl, _⟩
    rw [hLY] at ht
    have : (c + 1) * K ≤ n * K := Nat.mul_le_mul_right K hc
    rw [Nat.succ_mul] at ht this
    omega
  set i₃ := setDig len Y i₂ (dig len Y i₂ ^^^ m₂) with hi₃
  have hi₃lt : i₃ < 2 ^ ∑ g, len g := by
    have := setDig_lt (R := 1) len Y (by rw [one_mul]; exact hi₂lt) hm₂lt (hS Y)
    rwa [one_mul] at this
  have hY₃ : dig len Y i₃ = dig len Y i₂ ^^^ m₂ := dig_setDig_self len Y i₂ hm₂lt
  have hne₃ : ∀ f, f ≠ Y → dig len f i₃ = dig len f i₂ := fun f hf => dig_setDig_ne len hf i₂ hm₂lt
  -- the unload
  rw [runC_loadU len true i₃, swap_rot_swap len hUB hlenUB true _ hi₃lt]
  set i₄ := rotF len U true (fun j => offBb len G n X ρ K (swapF len U B j)) i₃ with hi₄
  have hi₄lt := rotF_lt_sum len U true (fun j => offBb len G n X ρ K (swapF len U B j)) hi₃lt
  have hU₃ : ((dig len U i₃ : ℕ) : ℤ) = pack (2 ^ G) ((List.range n).map fun c => u c + x c) := by
    rw [hne₃ U hUY, hU₂]
  have hU₄ : dig len U i₄ = dig len U i := by
    have : ((dig len U i₄ : ℕ) : ℤ) = ((dig len U i : ℕ) : ℤ) := by
      rw [hi₄, dig_rotF, hLU, hurep]
      have := rotVal_true_pack (fun c => u c + x c) x hux (fun c hc => by
        have h1 := hu0 c hc; have h2 := hx01 c
        rcases h2 with h2 | h2 <;> rw [h2] <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2])
        hU₃ (off := offBb len G n X ρ K (swapF len U B i₃)) ?_
      · rw [this]
        congr 1
        apply List.map_congr_left
        intro c _
        ring
      · rw [offBb_congr len X ρ K (dig_swapF_ne len hXU hXB hlenUB i₃), offBb_cast]
        congr 1
        apply List.map_congr_left
        intro c _
        simp only [hx, bitAt, hne₃ X hXY, hne₂ X hXU, hne₁ X hXY]
    exact_mod_cast this
  have hne₄ : ∀ f, f ≠ U → dig len f i₄ = dig len f i₃ := fun f hf => dig_rotF_ne len hf _ _ _
  -- the two control masks combine to the bits of `x`
  have hbitU₂ : ∀ c < n, bitAt len U 0 G c i₂ = xor (bitAt len U 0 G c i) (bitAt len X ρ K c i) := by
    intro c hc
    have hd₂ := digAt_of_pack len U (fun c => u c + x c) hux hU₂ hc
    have hd₀ : ((digAt len G U c i : ℕ) : ℤ) = u c := rfl
    rw [bitAt_zero_digit len hG, bitAt_zero_digit len hG]
    have e₂ : ((digAt len G U c i₂ : ℕ) : ℤ) % 2 = (u c + x c) % 2 := by rw [hd₂]
    have e₀ : ((digAt len G U c i : ℕ) : ℤ) % 2 = u c % 2 := by rw [hd₀]
    have hx' := hx01 c
    cases hb : bitAt len X ρ K c i
    · have : x c = 0 := by simp [hx, hb, b2n]
      rw [this, add_zero] at e₂
      have : digAt len G U c i₂ % 2 = digAt len G U c i % 2 := by exact_mod_cast e₂.trans e₀.symm
      simp [this]
    · have : x c = 1 := by simp [hx, hb, b2n]
      rw [this] at e₂
      have h2 : (digAt len G U c i₂ % 2 : ℕ) = (digAt len G U c i + 1) % 2 := by
        have : ((digAt len G U c i₂ : ℕ) : ℤ) % 2 = (((digAt len G U c i : ℕ) : ℤ) + 1) % 2 := by
          rw [e₂, hd₀]
        exact_mod_cast this
      rw [h2]
      rcases Nat.mod_two_eq_zero_or_one (digAt len G U c i) with h | h <;> simp [Nat.add_mod, h]
  have hmask : m₁ ^^^ m₂ = dig len X i &&& selMask K ρ n := by
    rw [hm₁, hm₂, offYb_eq_selSum, offYb_eq_selSum, selSum_xor hK, ← offYb_X len hK X i,
      offYb_eq_selSum]
    apply selSum_congr
    intro c hc
    rw [hbitU₂ c hc]
    cases bitAt len U 0 G c i <;> cases bitAt len X ρ K c i <;> rfl
  -- extensionality
  have hxlt : dig len Y i ^^^ (dig len X i &&& selMask K ρ n) < 2 ^ len Y := by
    rw [← hmask, ← Nat.xor_assoc]
    rw [← hY₁, ← hne₂ Y hUY.symm]
    exact hm₂lt
  unfold idealC
  apply ext_dig len hi₄lt (by
    have := setDig_lt (R := 1) len Y (by rw [one_mul]; exact hi) hxlt (hS Y)
    rwa [one_mul] at this)
  intro f
  by_cases hfY : f = Y
  · subst hfY
    rw [dig_setDig_self len _ i hxlt, hne₄ _ hUY.symm, hY₃, hne₂ _ hUY.symm, hY₁, Nat.xor_assoc,
      hmask]
  rw [dig_setDig_ne len hfY i hxlt]
  by_cases hfU : f = U
  · subst hfU; exact hU₄
  · rw [hne₄ f hfU, hne₃ f hfY, hne₂ f hfU, hne₁ f hfY]

end Later


/-! ### The ideal map and the good set -/

section Ideal

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix
open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma idealC_mask_lt {X Y : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (i : ℕ) :
    dig len Y i ^^^ (dig len X i &&& selMask K ρ n) < 2 ^ len Y :=
  Nat.xor_lt_two_pow (dig_lt len Y i)
    (lt_of_le_of_lt Nat.and_le_left (by rw [← hLXY]; exact dig_lt len X i))

lemma dig_idealC_Y {X Y : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (i : ℕ) :
    dig len Y (idealC len X Y K ρ n i) = dig len Y i ^^^ (dig len X i &&& selMask K ρ n) :=
  dig_setDig_self len Y i (idealC_mask_lt len hLXY i)

lemma dig_idealC_ne {X Y f : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (hf : f ≠ Y) (i : ℕ) :
    dig len f (idealC len X Y K ρ n i) = dig len f i :=
  dig_setDig_ne len hf i (idealC_mask_lt len hLXY i)

lemma idealC_idealC {X Y : Fin nf} {K ρ n : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y) (i : ℕ) :
    idealC len X Y K ρ n (idealC len X Y K ρ n i) = i := by
  unfold idealC
  rw [dig_setDig_self len Y i (idealC_mask_lt len hLXY i),
    dig_setDig_ne len hXY i (idealC_mask_lt len hLXY i),
    setDig_setDig_self len Y i (idealC_mask_lt len hLXY i) (Nat.xor_lt_two_pow
      (idealC_mask_lt len hLXY i) (lt_of_le_of_lt Nat.and_le_left
        (by rw [← hLXY]; exact dig_lt len X i))),
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, setDig_dig]

lemma idealC_lt {X Y : Fin nf} {K ρ n R S : ℕ} (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) {i : ℕ} (hi : i < R * 2 ^ S) :
    idealC len X Y K ρ n i < R * 2 ^ S :=
  setDig_lt len Y hi (idealC_mask_lt len hLXY i) hSY

/-- The ideal map keeps the good set of the earlier source. -/
lemma goodE_idealC {T X Y : Fin nf} {K ρ G n : ℕ} (hK : 1 ≤ K) (hTY : T ≠ Y)
    (hLXY : len X = len Y) (i : ℕ) :
    GoodE len T Y K ρ G n (idealC len X Y K ρ n i) ↔ GoodE len T Y K ρ G n i := by
  unfold GoodE DigOK
  have hT : ∀ c, digAt len G T c (idealC len X Y K ρ n i) = digAt len G T c i := fun c => by
    unfold digAt; rw [dig_idealC_ne len hLXY hTY]
  have hm : (dig len X i &&& selMask K ρ n) &&& selMask K ρ n = dig len X i &&& selMask K ρ n := by
    rw [Nat.and_assoc, Nat.and_self]
  simp only [hT, dig_idealC_Y len hLXY, guardOK_xor hK _ _ _ _ hm]

/-- The ideal map keeps the good set of the later source. -/
lemma goodL_idealC {U T X Y : Fin nf} {K ρ G n : ℕ} (hK : 1 ≤ K) (hTY : T ≠ Y) (hUY : U ≠ Y)
    (hLXY : len X = len Y) (i : ℕ) :
    GoodL len U T Y K ρ G n (idealC len X Y K ρ n i) ↔ GoodL len U T Y K ρ G n i := by
  unfold GoodL
  have hU : ∀ c, digAt len G U c (idealC len X Y K ρ n i) = digAt len G U c i := fun c => by
    unfold digAt; rw [dig_idealC_ne len hLXY hUY]
  simp only [goodE_idealC len hK hTY hLXY, DigOK, hU]

end Ideal

/-! ### Permutations of the record index space and the repair pipeline -/

section Perms

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix
open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- The ideal map as a permutation of the indices below `R · 2^S`. -/
def idealPerm {X Y : Fin nf} (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) : Equiv.Perm (Fin (R * 2 ^ S)) where
  toFun i := ⟨idealC len X Y K ρ n i, idealC_lt len hLXY hSY i.isLt⟩
  invFun i := ⟨idealC len X Y K ρ n i, idealC_lt len hLXY hSY i.isLt⟩
  left_inv i := Fin.ext (idealC_idealC len hXY hLXY i)
  right_inv i := Fin.ext (idealC_idealC len hXY hLXY i)

lemma idealPerm_apply {X Y : Fin nf} (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) (i : Fin (R * 2 ^ S)) :
    (idealPerm len K ρ n hXY hLXY hSY i : ℕ) = idealC len X Y K ρ n i := rfl

lemma idealPerm_symm {X Y : Fin nf} (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) :
    (idealPerm len K ρ n hXY hLXY hSY (R := R)).symm = idealPerm len K ρ n hXY hLXY hSY := rfl

/-- The exceptional set of the earlier source. -/
def BadE (T Y : Fin nf) (K ρ G n : ℕ) {R S : ℕ} (a : Fin (R * 2 ^ S)) : Prop :=
  ¬ GoodE len T Y K ρ G n a

/-- The exceptional set of the later source. -/
def BadL (U T Y : Fin nf) (K ρ G n : ℕ) {R S : ℕ} (a : Fin (R * 2 ^ S)) : Prop :=
  ¬ GoodL len U T Y K ρ G n a

instance (T Y : Fin nf) (K ρ G n : ℕ) {R S : ℕ} : DecidablePred (BadE len T Y K ρ G n (R := R) (S := S)) :=
  fun a => by unfold BadE; infer_instance

instance (U T Y : Fin nf) (K ρ G n : ℕ) {R S : ℕ} :
    DecidablePred (BadL len U T Y K ρ G n (R := R) (S := S)) :=
  fun a => by unfold BadL; infer_instance

/-- The hypotheses of the earlier source: field lengths, distinctness and placement below `S`,
and `R · 2^S ≤ 2^(∑ len)`. -/
structure LayE (T X Y B : Fin nf) (K ρ G n R S : ℕ) : Prop where
  hK : 1 ≤ K
  hρ : ρ < K
  hLY : len Y = (n + 1) * K
  hLX : len X = (n + 1) * K
  hLT : len T = n * G
  hLB : len B = n * G
  hTY : T ≠ Y
  hBY : B ≠ Y
  hTB : T ≠ B
  hXY : X ≠ Y
  hXT : X ≠ T
  hXB : X ≠ B
  hST : foff len T + len T ≤ S
  hSY : foff len Y + len Y ≤ S
  hSB : foff len B + len B ≤ S
  hRS : R * 2 ^ S ≤ 2 ^ ∑ g, len g

/-- The hypotheses of the later source. -/
structure LayL (U T X Y B : Fin nf) (K ρ G n R S : ℕ) : Prop where
  hK : 1 ≤ K
  hG : 1 ≤ G
  hρ : ρ < K
  hLY : len Y = (n + 1) * K
  hLX : len X = (n + 1) * K
  hLU : len U = n * G
  hLT : len T = n * G
  hLB : len B = n * G
  hTY : T ≠ Y
  hBY : B ≠ Y
  hTB : T ≠ B
  hUY : U ≠ Y
  hUT : U ≠ T
  hUB : U ≠ B
  hXY : X ≠ Y
  hXU : X ≠ U
  hXT : X ≠ T
  hXB : X ≠ B
  hSU : foff len U + len U ≤ S
  hST : foff len T + len T ≤ S
  hSY : foff len Y + len Y ≤ S
  hSB : foff len B + len B ≤ S
  hRS : R * 2 ^ S ≤ 2 ^ ∑ g, len g

lemma LayE.hLXY {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S) :
    len X = len Y := by rw [h.hLX, h.hLY]

lemma LayL.hLXY {U T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayL len U T X Y B K ρ G n R S) :
    len X = len Y := by rw [h.hLX, h.hLY]

/-- The program of the earlier source as a permutation. -/
def progEPerm {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S) :
    Equiv.Perm (Fin (R * 2 ^ S)) :=
  progPerm len (progE len T X Y B K ρ G n)
    (progE_WF len h.hLT h.hLB h.hTY h.hBY h.hTB h.hXY h.hXB h.hST h.hSY h.hSB)

lemma progEPerm_apply {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S)
    (a : Fin (R * 2 ^ S)) : (progEPerm len h a : ℕ) = runC len (progE len T X Y B K ρ G n) a :=
  progPerm_apply len _ _ a

/-- The program of the later source as a permutation. -/
def progLPerm {U T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayL len U T X Y B K ρ G n R S) :
    Equiv.Perm (Fin (R * 2 ^ S)) :=
  progPerm len (progL len U T X Y B K ρ G n)
    (progL_WF len h.hLU h.hLT h.hLB h.hTY h.hBY h.hTB h.hUY h.hUB h.hXB h.hSU h.hST h.hSY h.hSB)

lemma progLPerm_apply {U T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayL len U T X Y B K ρ G n R S)
    (a : Fin (R * 2 ^ S)) : (progLPerm len h a : ℕ) = runC len (progL len U T X Y B K ρ G n) a :=
  progPerm_apply len _ _ a

/-- **Agreement off the exceptional set** (earlier source). -/
theorem progEPerm_agrees {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S)
    (a : Fin (R * 2 ^ S)) (ha : ¬ BadE len T Y K ρ G n a) :
    progEPerm len h a = idealPerm len K ρ n h.hXY h.hLXY h.hSY a := by
  apply Fin.ext
  rw [progEPerm_apply, idealPerm_apply]
  exact progE_spec len h.hK h.hρ h.hLY h.hLT h.hLB h.hTY h.hBY h.hTB h.hXY h.hXT h.hXB
    (lt_of_lt_of_le a.isLt h.hRS) (not_not.mp ha)

/-- **Agreement off the exceptional set** (later source). -/
theorem progLPerm_agrees {U T X Y B : Fin nf} {K ρ G n R S : ℕ}
    (h : LayL len U T X Y B K ρ G n R S) (a : Fin (R * 2 ^ S))
    (ha : ¬ BadL len U T Y K ρ G n a) :
    progLPerm len h a = idealPerm len K ρ n h.hXY h.hLXY h.hSY a := by
  apply Fin.ext
  rw [progLPerm_apply, idealPerm_apply]
  exact progL_spec len h.hK h.hG h.hρ h.hLY h.hLU h.hLT h.hLB h.hTY h.hBY h.hTB h.hUY h.hUT h.hUB
    h.hXY h.hXU h.hXB (lt_of_lt_of_le a.isLt h.hRS) (not_not.mp ha)

theorem idealPerm_badE {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S)
    (a : Fin (R * 2 ^ S)) :
    BadE len T Y K ρ G n (idealPerm len K ρ n h.hXY h.hLXY h.hSY a) ↔ BadE len T Y K ρ G n a := by
  unfold BadE
  rw [idealPerm_apply, goodE_idealC len h.hK h.hTY h.hLXY]

theorem idealPerm_badL {U T X Y B : Fin nf} {K ρ G n R S : ℕ}
    (h : LayL len U T X Y B K ρ G n R S) (a : Fin (R * 2 ^ S)) :
    BadL len U T Y K ρ G n (idealPerm len K ρ n h.hXY h.hLXY h.hSY a) ↔
      BadL len U T Y K ρ G n a := by
  unfold BadL
  rw [idealPerm_apply, goodL_idealC len h.hK h.hTY h.hUY h.hLXY]

theorem progEPerm_badE {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S)
    (a : Fin (R * 2 ^ S)) :
    BadE len T Y K ρ G n (progEPerm len h a) ↔ BadE len T Y K ρ G n a :=
  actual_preserves_bad _ _ _ (idealPerm_badE len h) (progEPerm_agrees len h) a

theorem progLPerm_badL {U T X Y B : Fin nf} {K ρ G n R S : ℕ}
    (h : LayL len U T X Y B K ρ G n R S) (a : Fin (R * 2 ^ S)) :
    BadL len U T Y K ρ G n (progLPerm len h a) ↔ BadL len U T Y K ρ G n a :=
  actual_preserves_bad _ _ _ (idealPerm_badL len h) (progLPerm_agrees len h) a

/-- **Exceptional repair** (earlier source): the vendored extract–sort–fill pipeline after the
program yields the stream of the ideal map. -/
theorem repairE_exact {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S)
    (k : ℕ) (hk : R * 2 ^ S ≤ 2 ^ k) (data : Fin (R * 2 ^ S) → List Bool) :
    pipeline (Equiv.refl _) (progEPerm len h) (idealPerm len K ρ n h.hXY h.hLXY h.hSY)
        (BadE len T Y K ρ G n) k data =
      stream (Equiv.refl _) (BadE len T Y K ρ G n)
        (data ∘ (idealPerm len K ρ n h.hXY h.hLXY h.hSY).symm) :=
  pipeline_exact _ _ _ _ (idealPerm_badE len h) (progEPerm_agrees len h) k hk data

/-- **Exceptional repair** (later source). -/
theorem repairL_exact {U T X Y B : Fin nf} {K ρ G n R S : ℕ}
    (h : LayL len U T X Y B K ρ G n R S) (k : ℕ) (hk : R * 2 ^ S ≤ 2 ^ k)
    (data : Fin (R * 2 ^ S) → List Bool) :
    pipeline (Equiv.refl _) (progLPerm len h) (idealPerm len K ρ n h.hXY h.hLXY h.hSY)
        (BadL len U T Y K ρ G n) k data =
      stream (Equiv.refl _) (BadL len U T Y K ρ G n)
        (data ∘ (idealPerm len K ρ n h.hXY h.hLXY h.hSY).symm) :=
  pipeline_exact _ _ _ _ (idealPerm_badL len h) (progLPerm_agrees len h) k hk data

end Perms


/-! ### Counting the exceptional set -/

section Count

open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- Indices below `R · 2^S` satisfying a condition on field `f`: at most `R · 2^(S - |f|)` times
the number of field values satisfying it. -/
lemma card_dig_le {R S : ℕ} (f : Fin nf) (hS : foff len f + len f ≤ S) (Q : ℕ → Prop)
    [DecidablePred Q] :
    Fintype.card {a : Fin (R * 2 ^ S) // Q (dig len f a)} ≤
      R * 2 ^ (S - len f) * Fintype.card {v : Fin (2 ^ len f) // Q v} := by
  set P := foff len f with hP
  set L := len f with hL
  let F : {a : Fin (R * 2 ^ S) // Q (dig len f a)} →
      Fin (R * 2 ^ (S - (P + L))) × {v : Fin (2 ^ L) // Q v} × Fin (2 ^ P) := fun a =>
    (⟨(a.1 : ℕ) / 2 ^ (P + L), by
        rw [Nat.div_lt_iff_lt_mul (by positivity), mul_assoc, ← pow_add,
          show S - (P + L) + (P + L) = S by omega]
        exact a.1.isLt⟩,
     ⟨⟨dig len f a.1, dig_lt len f _⟩, a.2⟩,
     ⟨(a.1 : ℕ) % 2 ^ P, Nat.mod_lt _ (by positivity)⟩)
  have hF : Function.Injective F := by
    intro a b h
    simp only [F, Prod.mk.injEq, Fin.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    apply Subtype.ext; apply Fin.ext
    rw [← setDig_dig len f (a.1 : ℕ), ← setDig_dig len f (b.1 : ℕ)]
    unfold setDig
    rw [h1, h2, h3]
  have := Fintype.card_le_of_injective F hF
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  calc Fintype.card {a : Fin (R * 2 ^ S) // Q (dig len f a)}
      ≤ R * 2 ^ (S - (P + L)) * (Fintype.card {v : Fin (2 ^ L) // Q v} * 2 ^ P) := this
    _ = R * 2 ^ (S - L) * Fintype.card {v : Fin (2 ^ L) // Q v} := by
        rw [show S - L = S - (P + L) + P by omega, pow_add]
        ring

/-- At most `2^(nG - G)` values of an `nG`-bit field have digit `c < n` equal to `2^G - 1`. -/
lemma card_digit_top {G n c : ℕ} (hc : c < n) :
    Fintype.card {v : Fin (2 ^ (n * G)) // 2 ^ G < (v : ℕ) / 2 ^ (c * G) % 2 ^ G + 2} ≤
      2 ^ (n * G - G) := by
  have hcG : (c + 1) * G ≤ n * G := Nat.mul_le_mul_right G hc
  let F : {v : Fin (2 ^ (n * G)) // 2 ^ G < (v : ℕ) / 2 ^ (c * G) % 2 ^ G + 2} →
      Fin (2 ^ (n * G - (c + 1) * G)) × Fin (2 ^ (c * G)) := fun v =>
    (⟨(v.1 : ℕ) / 2 ^ ((c + 1) * G), by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
          show n * G - (c + 1) * G + (c + 1) * G = n * G by omega]
        exact v.1.isLt⟩,
     ⟨(v.1 : ℕ) % 2 ^ (c * G), Nat.mod_lt _ (by positivity)⟩)
  have hdig : ∀ v : {v : Fin (2 ^ (n * G)) // 2 ^ G < (v : ℕ) / 2 ^ (c * G) % 2 ^ G + 2},
      (v.1 : ℕ) / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1 := fun v => by
    have h1 := v.2
    have h2 : (v.1 : ℕ) / 2 ^ (c * G) % 2 ^ G < 2 ^ G := Nat.mod_lt _ (by positivity)
    omega
  have hF : Function.Injective F := by
    intro a b h
    simp only [F, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext; apply Fin.ext
    have key : ∀ x : ℕ, x = x % 2 ^ (c * G) + 2 ^ (c * G) *
        (x / 2 ^ (c * G) % 2 ^ G + 2 ^ G * (x / 2 ^ ((c + 1) * G))) := fun x => by
      rw [show (c + 1) * G = c * G + G by ring, pow_add, ← Nat.div_div_eq_div_mul,
        Nat.mod_add_div, Nat.mod_add_div]
    rw [key (a.1 : ℕ), key (b.1 : ℕ), h1, h2, hdig a, hdig b]
  have := Fintype.card_le_of_injective F hF
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  calc _ ≤ 2 ^ (n * G - (c + 1) * G) * 2 ^ (c * G) := this
    _ = 2 ^ (n * G - G) := by
        rw [← pow_add]; congr 1
        rw [Nat.add_mul, one_mul] at hcG ⊢; omega

/-- The exceptional set of a digit field, column `c`: at most `M / 2^G`. -/
lemma card_digOK_fail_le {R S G n : ℕ} (D : Fin nf) (hLD : len D = n * G)
    (hSD : foff len D + len D ≤ S) {c : ℕ} (hc : c < n) :
    Fintype.card {a : Fin (R * 2 ^ S) // 2 ^ G < digAt len G D c a + 2} * 2 ^ G ≤ R * 2 ^ S := by
  have h1 := card_dig_le len (R := R) D hSD (fun v => 2 ^ G < v / 2 ^ (c * G) % 2 ^ G + 2)
  have h2 : Fintype.card {v : Fin (2 ^ len D) // 2 ^ G < (v : ℕ) / 2 ^ (c * G) % 2 ^ G + 2} ≤
      2 ^ (n * G - G) := by
    have := card_digit_top (G := G) (n := n) (c := c) hc
    rw [hLD]
    exact this
  have hnG : G ≤ n * G := Nat.le_mul_of_pos_left G (by omega)
  have hS : n * G ≤ S := by rw [hLD] at hSD; omega
  have e : S - n * G + (n * G - G) + G = S := by omega
  calc Fintype.card {a : Fin (R * 2 ^ S) // 2 ^ G < digAt len G D c a + 2} * 2 ^ G
      ≤ R * 2 ^ (S - len D) * 2 ^ (n * G - G) * 2 ^ G := by
        apply Nat.mul_le_mul_right
        exact h1.trans (Nat.mul_le_mul_left _ h2)
    _ = R * 2 ^ (S - n * G + (n * G - G) + G) := by rw [hLD, pow_add, pow_add]; ring
    _ = R * 2 ^ S := by rw [e]

/-- The exceptional set of guard `c` of `y`: at most `2^(G+2) · M / 2^(K-1)`. -/
lemma card_guard_fail_le {R S K ρ G n : ℕ} (Y : Fin nf) (hK : 1 ≤ K) (hρ : ρ < K)
    (hLY : len Y = (n + 1) * K) (hSY : foff len Y + len Y ≤ S) {c : ℕ} (hc : c < n) :
    Fintype.card {a : Fin (R * 2 ^ S) // ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} *
        2 ^ (K - 1) ≤ 2 ^ (G + 2) * (R * 2 ^ S) := by
  have h1 := card_dig_le len (R := R) Y hSY (fun v => ¬ GuardOK K ρ (2 ^ (G + 1)) v c)
  have h2 : Fintype.card {v : Fin (2 ^ len Y) // ¬ GuardOK K ρ (2 ^ (G + 1)) v c} ≤
      2 * 2 ^ (G + 1) * 2 ^ (len Y - (K - 1)) := by
    apply card_guard_fail K ρ (len Y) hK (2 ^ (G + 1)) c
    have e1 : (c + 1) * K = c * K + K := by ring
    have e2 : (n + 1) * K = n * K + K := by ring
    rw [hLY, e1, e2]
    have : (c + 1) * K ≤ n * K := Nat.mul_le_mul_right K hc
    rw [e1] at this
    omega
  have hKS : K - 1 ≤ len Y := by rw [hLY, Nat.add_mul, one_mul]; omega
  have e : S - len Y + (len Y - (K - 1)) + (K - 1) = S := by
    have h1 : len Y ≤ S := le_trans (Nat.le_add_left _ _) hSY
    rw [Nat.add_assoc, Nat.sub_add_cancel hKS, Nat.sub_add_cancel h1]
  calc Fintype.card {a : Fin (R * 2 ^ S) // ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} *
        2 ^ (K - 1)
      ≤ R * 2 ^ (S - len Y) * (2 * 2 ^ (G + 1) * 2 ^ (len Y - (K - 1))) * 2 ^ (K - 1) := by
        apply Nat.mul_le_mul_right
        exact h1.trans (Nat.mul_le_mul_left _ h2)
    _ = 2 ^ (G + 2) * (R * 2 ^ (S - len Y + (len Y - (K - 1)) + (K - 1))) := by
        have e3 : (2 : ℕ) ^ (G + 2) = 2 * 2 ^ (G + 1) := by ring
        rw [pow_add (2 : ℕ) (S - len Y + (len Y - (K - 1))) (K - 1),
          pow_add (2 : ℕ) (S - len Y) (len Y - (K - 1)), e3]
        ring
    _ = 2 ^ (G + 2) * (R * 2 ^ S) := by rw [e]

/-- A union bound over `c < n`. -/
lemma card_exists_le {α : Type*} [Fintype α] [DecidableEq α] (P : ℕ → α → Prop)
    [∀ c, DecidablePred (P c)] (n : ℕ) :
    Fintype.card {a : α // ∃ c < n, P c a} ≤ ∑ c ∈ Finset.range n, Fintype.card {a : α // P c a} := by
  simp only [Fintype.card_subtype]
  have : Finset.univ.filter (fun a : α => ∃ c < n, P c a) =
      (Finset.range n).biUnion fun c => Finset.univ.filter (fun a => P c a) := by
    ext a
    simp
  rw [this]
  exact Finset.card_biUnion_le

lemma card_or_le {α : Type*} [Fintype α] [DecidableEq α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] :
    Fintype.card {a : α // p a ∨ q a} ≤ Fintype.card {a : α // p a} + Fintype.card {a : α // q a} := by
  simp only [Fintype.card_subtype]
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

/-- The digit failures of a field, summed over the columns, in real form. -/
lemma card_digFail_sum_le {R S G n : ℕ} (D : Fin nf) (hLD : len D = n * G)
    (hSD : foff len D + len D ≤ S) :
    (Fintype.card {a : Fin (R * 2 ^ S) // ∃ c < n, 2 ^ G < digAt len G D c a + 2} : ℝ) ≤
      n * (1 / 2 ^ G) * (R * 2 ^ S) := by
  classical
  have h1 := card_exists_le (fun c (a : Fin (R * 2 ^ S)) => 2 ^ G < digAt len G D c a + 2) n
  have hd : ∀ c ∈ Finset.range n,
      (Fintype.card {a : Fin (R * 2 ^ S) // 2 ^ G < digAt len G D c a + 2} : ℝ) ≤
        1 / 2 ^ G * (R * 2 ^ S) := fun c hc => by
    have := card_digOK_fail_le len (R := R) (S := S) D hLD hSD (Finset.mem_range.mp hc)
    have hcast : (Fintype.card {a : Fin (R * 2 ^ S) // 2 ^ G < digAt len G D c a + 2} : ℝ) *
        2 ^ G ≤ R * 2 ^ S := by exact_mod_cast this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    exact hcast
  calc (Fintype.card {a : Fin (R * 2 ^ S) // ∃ c < n, 2 ^ G < digAt len G D c a + 2} : ℝ)
      ≤ ((∑ c ∈ Finset.range n,
          Fintype.card {a : Fin (R * 2 ^ S) // 2 ^ G < digAt len G D c a + 2} : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∑ c ∈ Finset.range n,
          (Fintype.card {a : Fin (R * 2 ^ S) // 2 ^ G < digAt len G D c a + 2} : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ c ∈ Finset.range n, (1 / 2 ^ G * (R * 2 ^ S) : ℝ) := Finset.sum_le_sum hd
    _ = n * (1 / 2 ^ G) * (R * 2 ^ S) := by simp; ring

/-- The guard failures of `y`, summed over the columns, in real form. -/
lemma card_guardFail_sum_le {R S K ρ G n : ℕ} (Y : Fin nf) (hK : 1 ≤ K) (hρ : ρ < K)
    (hLY : len Y = (n + 1) * K) (hSY : foff len Y + len Y ≤ S) :
    (Fintype.card {a : Fin (R * 2 ^ S) //
        ∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ) ≤
      n * (8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := by
  classical
  have h2 := card_exists_le
    (fun c (a : Fin (R * 2 ^ S)) => ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c) n
  have hg : ∀ c ∈ Finset.range n,
      (Fintype.card {a : Fin (R * 2 ^ S) // ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ) ≤
        8 * 2 ^ G / 2 ^ K * (R * 2 ^ S) := fun c hc => by
    have := card_guard_fail_le len (R := R) (S := S) (G := G) Y hK hρ hLY hSY
      (Finset.mem_range.mp hc)
    have hcast : (Fintype.card {a : Fin (R * 2 ^ S) //
        ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ) * 2 ^ (K - 1) ≤
        2 ^ (G + 2) * (R * 2 ^ S) := by exact_mod_cast this
    have hK2 : (2 : ℝ) ^ K = 2 * 2 ^ (K - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hG2 : (2 : ℝ) ^ (G + 2) = 4 * 2 ^ G := by rw [pow_add]; norm_num; ring
    rw [hG2] at hcast
    rw [hK2, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e : (Fintype.card {a : Fin (R * 2 ^ S) //
        ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ) * (2 * 2 ^ (K - 1)) =
        2 * ((Fintype.card {a : Fin (R * 2 ^ S) //
          ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ) * 2 ^ (K - 1)) := by ring
    rw [e]
    linarith [hcast]
  calc (Fintype.card {a : Fin (R * 2 ^ S) //
        ∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ)
      ≤ ((∑ c ∈ Finset.range n, Fintype.card {a : Fin (R * 2 ^ S) //
          ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℕ) : ℝ) := by exact_mod_cast h2
    _ = ∑ c ∈ Finset.range n, (Fintype.card {a : Fin (R * 2 ^ S) //
          ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} : ℝ) := by push_cast; rfl
    _ ≤ ∑ c ∈ Finset.range n, (8 * 2 ^ G / 2 ^ K * (R * 2 ^ S) : ℝ) := Finset.sum_le_sum hg
    _ = n * (8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := by simp; ring

lemma badE_iff {T Y : Fin nf} {K ρ G n R S : ℕ} (a : Fin (R * 2 ^ S)) :
    BadE len T Y K ρ G n a ↔
      (∃ c < n, 2 ^ G < digAt len G T c a + 2) ∨
        (∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c) := by
  unfold BadE GoodE DigOK
  constructor
  · intro hb
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    push_neg at h1 h2
    exact hb ⟨h1, h2⟩
  · rintro (⟨c, hc, h1⟩ | ⟨c, hc, h1⟩) ⟨hd, hg⟩
    · have := hd c hc; omega
    · exact h1 (hg c hc)

/-- **The exceptional fraction of the earlier source**: `|Bad| ≤ n (2^{-G} + 8 · 2^{G-K}) M`. -/
theorem card_badE_le {T X Y B : Fin nf} {K ρ G n R S : ℕ} (h : LayE len T X Y B K ρ G n R S) :
    (Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a} : ℝ) ≤
      n * (1 / 2 ^ G + 8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := by
  classical
  have hcard : Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a} ≤
      Fintype.card {a : Fin (R * 2 ^ S) // ∃ c < n, 2 ^ G < digAt len G T c a + 2} +
        Fintype.card {a : Fin (R * 2 ^ S) //
          ∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} := by
    calc Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a}
        = Fintype.card {a : Fin (R * 2 ^ S) // (∃ c < n, 2 ^ G < digAt len G T c a + 2) ∨
            (∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (badE_iff len))
      _ ≤ _ := card_or_le _ _
  have h1 := card_digFail_sum_le len (R := R) (S := S) T h.hLT h.hST
  have h2 := card_guardFail_sum_le len (R := R) (S := S) (G := G) Y h.hK h.hρ h.hLY h.hSY
  calc (Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a} : ℝ)
      ≤ (Fintype.card {a : Fin (R * 2 ^ S) // ∃ c < n, 2 ^ G < digAt len G T c a + 2} : ℝ) +
        Fintype.card {a : Fin (R * 2 ^ S) //
          ∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y a) c} := by exact_mod_cast hcard
    _ ≤ n * (1 / 2 ^ G) * (R * 2 ^ S) + n * (8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := add_le_add h1 h2
    _ = n * (1 / 2 ^ G + 8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := by ring

lemma badL_iff {U T Y : Fin nf} {K ρ G n R S : ℕ} (a : Fin (R * 2 ^ S)) :
    BadL len U T Y K ρ G n a ↔
      BadE len T Y K ρ G n a ∨ (∃ c < n, 2 ^ G < digAt len G U c a + 2) := by
  unfold BadL GoodL
  rw [not_and_or]
  apply or_congr Iff.rfl
  unfold DigOK
  constructor
  · intro hb
    by_contra hcon
    push_neg at hcon
    exact hb hcon
  · rintro ⟨c, hc, h1⟩ hd
    have := hd c hc; omega

/-- **The exceptional fraction of the later source**: `|Bad| ≤ n (2 · 2^{-G} + 8 · 2^{G-K}) M`. -/
theorem card_badL_le {U T X Y B : Fin nf} {K ρ G n R S : ℕ}
    (h : LayL len U T X Y B K ρ G n R S) :
    (Fintype.card {a : Fin (R * 2 ^ S) // BadL len U T Y K ρ G n a} : ℝ) ≤
      n * (2 / 2 ^ G + 8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := by
  classical
  have hE : LayE len T X Y B K ρ G n R S :=
    ⟨h.hK, h.hρ, h.hLY, h.hLX, h.hLT, h.hLB, h.hTY, h.hBY, h.hTB, h.hXY, h.hXT, h.hXB, h.hST,
      h.hSY, h.hSB, h.hRS⟩
  have hcard : Fintype.card {a : Fin (R * 2 ^ S) // BadL len U T Y K ρ G n a} ≤
      Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a} +
        Fintype.card {a : Fin (R * 2 ^ S) // ∃ c < n, 2 ^ G < digAt len G U c a + 2} := by
    calc Fintype.card {a : Fin (R * 2 ^ S) // BadL len U T Y K ρ G n a}
        = Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a ∨
            (∃ c < n, 2 ^ G < digAt len G U c a + 2)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (badL_iff len))
      _ ≤ _ := card_or_le _ _
  have h1 := card_badE_le len hE
  have h2 := card_digFail_sum_le len (R := R) (S := S) U h.hLU h.hSU
  calc (Fintype.card {a : Fin (R * 2 ^ S) // BadL len U T Y K ρ G n a} : ℝ)
      ≤ (Fintype.card {a : Fin (R * 2 ^ S) // BadE len T Y K ρ G n a} : ℝ) +
        Fintype.card {a : Fin (R * 2 ^ S) // ∃ c < n, 2 ^ G < digAt len G U c a + 2} := by
          exact_mod_cast hcard
    _ ≤ n * (1 / 2 ^ G + 8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) + n * (1 / 2 ^ G) * (R * 2 ^ S) :=
        add_le_add h1 h2
    _ = n * (2 / 2 ^ G + 8 * 2 ^ G / 2 ^ K) * (R * 2 ^ S) := by ring

end Count

end IntegerMultBounds.MathlibTM2.Layer.CompactXor
