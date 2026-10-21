module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Address
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemPieces

/-!
# Field numbers of reversed atom states

A field of `N` coordinates over `ZMod Q` is the number `rank y` with coordinate `t` its digit
`N - 1 - t` (`digit_rank`). Swapping the first `c` coordinates of the head with the last `c` of
the tail, each reversed, acts on the numbers as the reversed interchange of a view `sub 0 c`
(`rank_head`, `rank_tail`).

On atom states, coordinates of `f` atoms refined coordinate-major (`AtomOps.refine`), the twisted
interchanges of the reversed pivots `revPivots m r` are this swap with `c = r f`
(`refine_swap_fst`, `refine_swap_snd`), and the node theorem's reading `(σ(C d), σ(C h))` is the
swap of all `m f` atoms (`refine_twist`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Networks
open Machine.FlatCoordinateLayout (rank)
open ReversedExchange (revPivots)
open TwistedExchange (revSwaps atomRev twist)
open Matrix

/-! ### Digits -/

section Digits

variable {Q : ℕ}

theorem digit_mod (_hQ : 0 < Q) {x K j : ℕ} (hj : j < K) : x % Q ^ K / Q ^ j % Q = x / Q ^ j % Q := by
  have hK : Q ^ K = Q ^ j * Q ^ (K - j) := by rw [← pow_add]; congr 1; omega
  rw [hK, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self Q (by omega))]

theorem digit_high (hQ : 0 < Q) {X Y K j : ℕ} (hY : Y < Q ^ K) (hj : K ≤ j) :
    (X * Q ^ K + Y) / Q ^ j % Q = X / Q ^ (j - K) % Q := by
  have : Q ^ j = Q ^ K * Q ^ (j - K) := by rw [← pow_add]; congr 1; omega
  rw [this, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos hQ K),
    Nat.div_eq_of_lt hY, zero_add]

theorem digit_div {x K j : ℕ} : x / Q ^ K / Q ^ j % Q = x / Q ^ (K + j) % Q := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem pack_lt_pow (_hQ : 0 < Q) {X Y c N : ℕ} (hc : c ≤ N) (hX : X < Q ^ c) (hY : Y < Q ^ (N - c)) :
    X * Q ^ (N - c) + Y < Q ^ N := by
  have h1 : X * Q ^ (N - c) + Y < (X + 1) * Q ^ (N - c) := by nlinarith
  have h2 : (X + 1) * Q ^ (N - c) ≤ Q ^ c * Q ^ (N - c) := Nat.mul_le_mul_right _ hX
  rw [← pow_add, Nat.add_sub_cancel' hc] at h2
  omega

variable [NeZero Q]

theorem digit_rank {N : ℕ} (y : Fin N → ZMod Q) {j : ℕ} (hj : j < N) :
    (rank y).val / Q ^ j % Q = (y ⟨N - 1 - j, by omega⟩).val := by
  have := Machine.FlatCoordinateLayout.coordinate_value y ⟨N - 1 - j, by omega⟩
  simp only [Machine.FlatCoordinateLayout.suffixFields] at this
  rwa [show N - 1 - (N - 1 - j) = j by omega] at this

/-- **The head after the swap.** -/
theorem rank_head {N c : ℕ} (hc : c ≤ N) (h d h' : Fin N → ZMod Q)
    (hh : ∀ k : Fin N, h' k = if k.val < c then d k.rev else h k) :
    (rank h').val = revAtoms Q c ((rank d).val % Q ^ c) * Q ^ (N - c) + (rank h).val % Q ^ (N - c) := by
  have hQ : 0 < Q := NeZero.pos Q
  refine eq_of_digits hQ N _ _ (rank h').isLt
    (pack_lt_pow hQ hc (revAtoms_lt hQ c _) (Nat.mod_lt _ (pow_pos hQ _))) fun j hj => ?_
  rw [digit_rank h' hj, hh]
  by_cases hjc : j < N - c
  · have hn : ¬ N - 1 - j < c := by omega
    simp only [hn, ↓reduceIte]
    rw [digit_append hQ hjc, digit_mod hQ hjc, digit_rank h hj]
  · have hn : N - 1 - j < c := by omega
    simp only [hn, ↓reduceIte]
    rw [digit_high hQ (Nat.mod_lt _ (pow_pos hQ _)) (by omega), revAtoms_digit hQ c _ _ (by omega),
      digit_mod hQ (by omega), digit_rank d (by omega)]
    congr 2
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- **The tail after the swap.** -/
theorem rank_tail {N c : ℕ} (hc : c ≤ N) (h d d' : Fin N → ZMod Q)
    (hd : ∀ k : Fin N, d' k = if N - c ≤ k.val then h k.rev else d k) :
    (rank d').val = (rank d).val / Q ^ c * Q ^ c + revAtoms Q c ((rank h).val / Q ^ (N - c)) := by
  have hQ : 0 < Q := NeZero.pos Q
  have hlt : (rank d).val / Q ^ c < Q ^ (N - c) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hQ _), ← pow_add, Nat.sub_add_cancel hc]; exact (rank d).isLt
  have hb : (rank d).val / Q ^ c * Q ^ c + revAtoms Q c ((rank h).val / Q ^ (N - c)) < Q ^ N := by
    have := pack_lt_pow hQ (Nat.sub_le N c) hlt
      (show revAtoms Q c ((rank h).val / Q ^ (N - c)) < Q ^ (N - (N - c)) by
        rw [Nat.sub_sub_self hc]; exact revAtoms_lt hQ c _)
    rwa [Nat.sub_sub_self hc] at this
  refine eq_of_digits hQ N _ _ (rank d').isLt hb fun j hj => ?_
  rw [digit_rank d' hj, hd]
  by_cases hjc : j < c
  · have hn : N - c ≤ N - 1 - j := by omega
    simp only [hn, ↓reduceIte]
    rw [digit_append hQ hjc, revAtoms_digit hQ c _ _ hjc, digit_div, digit_rank h (by omega)]
    congr 2
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  · have hn : ¬ N - c ≤ N - 1 - j := by omega
    simp only [hn, ↓reduceIte]
    rw [digit_high hQ (revAtoms_lt hQ c _) (by omega), digit_div, Nat.add_sub_cancel' (by omega),
      digit_rank d hj]

end Digits

/-! ### Atom states -/

section Atoms

variable {m f : ℕ} {R : Type}

theorem at_val (i : Fin m) (l : Fin f) : (AtomOps.«at» i l).val = l.val + f * i.val := by
  simp [AtomOps.«at»]

theorem exists_at (k : Fin (m * f)) : ∃ i l, k = AtomOps.«at» i l :=
  ⟨(finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2, (finProdFinEquiv.apply_symm_apply k).symm⟩

theorem at_rev (i : Fin m) (l : Fin f) : (AtomOps.«at» i l).rev = AtomOps.«at» i.rev l.rev := by
  apply Fin.ext
  simp only [Fin.val_rev, at_val]
  have hi := i.isLt
  have hl := l.isLt
  obtain ⟨A, hA⟩ : ∃ A, m = i.val + 1 + A := ⟨m - (i.val + 1), by omega⟩
  have e : m * f = f * i.val + f + f * A := by
    have h2 : m * f = (i.val + 1 + A) * f := by rw [← hA]
    rw [h2]; ring
  rw [show m - (i.val + 1) = A by omega, e]
  omega

theorem at_lt_iff (i : Fin m) (l : Fin f) {r : ℕ} : (AtomOps.«at» i l).val < r * f ↔ i.val < r := by
  rw [at_val]
  have hl := l.isLt
  constructor
  · intro h
    by_contra hc
    have : f * r ≤ f * i.val := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm r f] at h
    omega
  · intro h
    have : f * (i.val + 1) ≤ f * r := Nat.mul_le_mul_left _ h
    rw [Nat.mul_comm r f, Nat.mul_add, Nat.mul_one] at *
    omega

theorem at_ge_iff (i : Fin m) (l : Fin f) {r : ℕ} :
    m * f - r * f ≤ (AtomOps.«at» i l).val ↔ i.rev.val < r := by
  have h := at_lt_iff i.rev l.rev (r := r)
  rw [← at_rev, Fin.val_rev] at h
  rw [← h]
  have hk := (AtomOps.«at» i l).isLt
  constructor <;> intro h' <;> omega

theorem refine_ext {x y : Fin (m * f) → R} (h : ∀ i l, x (AtomOps.«at» i l) = y (AtomOps.«at» i l)) : x = y := by
  funext k
  obtain ⟨i, l, rfl⟩ := exists_at k
  exact h i l

variable [CommRing R]

/-- The head of the twisted reversed pivots, refined. -/
theorem refine_swap_fst {r : ℕ} (s : Swap.Shear.State (Fin m) (Fin f → R)) (k : Fin (m * f)) :
    AtomOps.refine (revSwaps (atomRev f) (revPivots m r) s).1 k =
      if k.val < r * f then AtomOps.refine s.2 k.rev else AtomOps.refine s.1 k := by
  obtain ⟨i, l, rfl⟩ := exists_at k
  simp only [AtomOps.refine_at, revPivots_fst, at_lt_iff, at_rev]
  split_ifs <;> rfl

/-- The tail of the twisted reversed pivots, refined. -/
theorem refine_swap_snd {r : ℕ} (s : Swap.Shear.State (Fin m) (Fin f → R)) (k : Fin (m * f)) :
    AtomOps.refine (revSwaps (atomRev f) (revPivots m r) s).2 k =
      if m * f - r * f ≤ k.val then AtomOps.refine s.1 k.rev else AtomOps.refine s.2 k := by
  obtain ⟨i, l, rfl⟩ := exists_at k
  simp only [AtomOps.refine_at, revPivots_snd, at_ge_iff, at_rev]
  split_ifs <;> rfl

/-- The reversal of the coordinates. -/
theorem revS_mulVec {q b : ℕ} (φ : ZMod (q ^ b) →+* R) (d : Fin m → R) :
    Rev.revS (d := m) φ *ᵥ d = fun i : Fin m => d i.rev := by
  funext i
  simp only [Rev.revS, mulVec, dotProduct, Matrix.map_apply, Swap.Modular.reduce, ReversedExchange.rev,
    Matrix.of_apply]
  rw [Finset.sum_eq_single i.rev]
  · simp [Swap.Modular.ratMod_one]
  · intro j _ hj; simp [hj, Swap.Modular.ratMod_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The node theorem's reading**, refined: all atoms reversed. -/
theorem refine_twist {q b : ℕ} (φ : ZMod (q ^ b) →+* (Fin f → R)) (d : Fin m → Fin f → R) (k : Fin (m * f)) :
    AtomOps.refine (twist (atomRev f) (Rev.revS (d := m) φ *ᵥ d)) k = AtomOps.refine d k.rev := by
  obtain ⟨i, l, rfl⟩ := exists_at k
  rw [at_rev, AtomOps.refine_at, AtomOps.refine_at, revS_mulVec]
  rfl

end Atoms

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
