module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Views
public import IntegerMultBounds.MathlibTM2.M8.Rev.Node
public import IntegerMultBounds.MathlibTM2.M8.AtomOps
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-!
# Stream addresses and the atom reversal

A field of `m` coordinates of `f` atoms over `ZMod Q` sits in the array at the index of its
refined vector (`AtomOps.refine`, coordinate-major) in the most-significant-first layout
(`FlatCoordinateLayout.rank`). The node's reversed interchange reads the other field with its
coordinates reversed by `Rev.revS` and its atoms by `atomRev f` (`twist`). On indices this is the
atom reversal `revAtoms` of the `m f` atoms (`rank_twist`), so the node theorem
`RevNetwork.run_identity` is the reversed interchange `RevMachine.RevT` of the views.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine

open IntegerMultBounds.Machine.FlatCoordinateLayout (rank)

/-! ### Digits -/

theorem digit_append {Q : ℕ} (hQ : 0 < Q) {k j : ℕ} (hj : j < k) (a b : ℕ) :
    (a * Q ^ k + b) / Q ^ j % Q = b / Q ^ j % Q := by
  have hk : Q ^ k = Q ^ (k - j - 1) * Q * Q ^ j := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  rw [hk, show a * (Q ^ (k - j - 1) * Q * Q ^ j) + b = (a * Q ^ (k - j - 1) * Q) * Q ^ j + b by ring,
    Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos hQ j), Nat.add_mul_mod_self_right]

theorem digit_top {Q : ℕ} (hQ : 0 < Q) {k : ℕ} (a b : ℕ) (ha : a < Q) (hb : b < Q ^ k) :
    (a * Q ^ k + b) / Q ^ k % Q = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos hQ k), Nat.div_eq_of_lt hb, zero_add,
    Nat.mod_eq_of_lt ha]

/-- Digit `j` of the reversal is digit `k - 1 - j` of the original. -/
theorem revAtoms_digit {Q : ℕ} (hQ : 0 < Q) : ∀ (k h j : ℕ), j < k →
    revAtoms Q k h / Q ^ j % Q = h / Q ^ (k - 1 - j) % Q
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, h, j, hj => by
    have hlt := revAtoms_lt hQ k (h / Q)
    have hdef : revAtoms Q (k + 1) h = h % Q * Q ^ k + revAtoms Q k (h / Q) := rfl
    rw [hdef]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [digit_append hQ hj, revAtoms_digit hQ k (h / Q) j hj, Nat.div_div_eq_div_mul,
        ← pow_succ', show k - 1 - j + 1 = k + 1 - 1 - j by omega]
    · rw [digit_top hQ _ _ (Nat.mod_lt h hQ) hlt]
      simp

/-- Two numbers below `Q^k` with the same `k` digits are equal. -/
theorem eq_of_digits {Q : ℕ} (hQ : 0 < Q) : ∀ (k a b : ℕ), a < Q ^ k → b < Q ^ k →
    (∀ j < k, a / Q ^ j % Q = b / Q ^ j % Q) → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | k + 1, a, b, ha, hb, h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have hrest : a / Q = b / Q := eq_of_digits hQ k (a / Q) (b / Q)
      (by rw [Nat.div_lt_iff_lt_mul hQ, ← pow_succ]; exact ha)
      (by rw [Nat.div_lt_iff_lt_mul hQ, ← pow_succ]; exact hb)
      (fun j hj => by
        have := h (j + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this)
    rw [← Nat.div_add_mod a Q, ← Nat.div_add_mod b Q, hrest, h0]

/-! ### Layout -/

variable {Q : ℕ} [NeZero Q]

/-- **Reversing the coordinates reverses the digits.** -/
theorem rank_comp_rev {k : ℕ} (y : Fin k → ZMod Q) :
    (rank (y ∘ Fin.rev)).val = revAtoms Q k (rank y).val := by
  have hQ : 0 < Q := NeZero.pos Q
  apply eq_of_digits hQ k _ _ (rank _).isLt (revAtoms_lt hQ k _)
  intro j hj
  rw [revAtoms_digit hQ k _ j hj]
  have h1 := Machine.FlatCoordinateLayout.coordinate_value (y ∘ Fin.rev) (Fin.rev ⟨j, hj⟩)
  have h2 := Machine.FlatCoordinateLayout.coordinate_value y ⟨j, hj⟩
  simp only [Machine.FlatCoordinateLayout.suffixFields, Fin.val_rev, Function.comp_apply,
    Fin.rev_rev] at h1 h2
  rw [show k - 1 - (k - (j + 1)) = j by omega] at h1
  rw [h1, h2]

omit [NeZero Q] in
/-- Reversing the coordinates and the atoms of every coordinate reverses the refined vector. -/
theorem refine_rev {m f : ℕ} (v : Fin m → Fin f → ZMod Q) :
    AtomOps.refine (fun i x => v i.rev x.rev) = AtomOps.refine v ∘ Fin.rev := by
  funext k
  obtain ⟨⟨i, x⟩, rfl⟩ := finProdFinEquiv.surjective k
  change AtomOps.refine _ (AtomOps.«at» i x) = AtomOps.refine v (AtomOps.«at» i x).rev
  have hrev : (AtomOps.«at» (n := m) (f := f) i x).rev = AtomOps.«at» i.rev x.rev := by
    apply Fin.ext
    simp only [AtomOps.«at», Fin.val_rev, finProdFinEquiv_apply_val]
    have hi := i.isLt
    have hx := x.isLt
    obtain ⟨A, hA⟩ : ∃ A, m = i + 1 + A := ⟨m - (i + 1), by omega⟩
    rw [show m - (i + 1) = A by omega, show m * f = f * i + f + f * A by
      calc m * f = (i + 1 + A) * f := by rw [← hA]
        _ = f * i + f + f * A := by ring]
    omega
  rw [hrev, AtomOps.refine_at, AtomOps.refine_at]

end IntegerMultBounds.MathlibTM2.M8.RevMachine
