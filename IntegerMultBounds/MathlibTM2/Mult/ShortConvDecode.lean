module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixed

/-! # Reading the actual shared-convolution output tape

Pair symbols store low bits first. Reverse each component before signed decoding;
the disk bound proves that this recovers the integer numerator without aliasing.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

/-- Read one pair-symbol word from a tape. -/
def decodeWord {A : ℕ} (s : List (Fin (A + 4))) : GaussianInt :=
  ⟨compValue (s.map pairRe).reverse, compValue (s.map pairIm).reverse⟩

theorem decodeWord_csyms {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    decodeWord (csyms A w z) =
      ⟨compValue (compWord w z.re), compValue (compWord w z.im)⟩ := by
  simp [decodeWord, csyms, coeffSyms, List.map_ofFn, Function.comp_def,
    pairRe_pairSym hA, pairIm_pairSym hA, rp_compWord_eq_rev, rpLsb, red]

/-- Fixed-width stream indexing remains valid in front of any pre-existing output tail. -/
theorem cstream_word {A : ℕ} (w : ℕ) (x : List GaussianInt)
    (tail : List (Fin (A + 4))) (j : ℕ) (hj : j < x.length) :
    ((cstream A w x ++ tail).drop (j * w)).take w = csyms A w x[j] := by
  induction x generalizing j with
  | nil => simp at hj
  | cons z x ih =>
    cases j with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, cstream_cons, List.append_assoc,
        List.getElem_cons_zero]
      rw [List.take_append_of_le_length (by simp [csyms])]
      exact List.take_of_length_le (by simp [csyms])
    | succ j =>
      rw [cstream_cons, List.append_assoc, Nat.succ_mul, Nat.add_comm (j * w) w,
        ← List.drop_drop]
      have hd : (csyms A w z ++ (cstream A w x ++ tail)).drop w =
          cstream A w x ++ tail := by
        rw [List.drop_append_of_le_length (by simp [csyms])]
        simp [csyms]
      rw [hd]
      exact ih j (by simpa using hj)

namespace Fixed

/-- Read coefficient `c` of record `n` directly from the final output stack in `closed_exec`. -/
theorem output_coeff {A p l w M a b : ℕ} (hA : 4 ≤ A) (hw : p + 2 ≤ w)
    (hab : a + b ≤ 2 ^ l + 1) (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (c : Fin (2 ^ l)) :
    decodeWord (((cstream A w (result p l M X Y) ++ tail).drop
      ((n * 2 ^ l + c.val) * w)).take w) = coeff p l (X n) (Y n) c := by
  have hj : n * 2 ^ l + c.val < (result p l M X Y).length := by
    rw [result_length]
    have hmul := Nat.mul_le_mul_right (2 ^ l) (Nat.succ_le_of_lt hn)
    rw [Nat.succ_mul] at hmul
    omega
  rw [cstream_word w _ tail _ hj, decodeWord_csyms hA]
  have he := result_coeff p l M X Y n hn c
  rw [List.getElem?_eq_getElem hj] at he
  have he' := Option.some.inj he
  rw [he']
  have hxy : (X n).length + (Y n).length ≤ 2 ^ l + 1 := by
    rw [hlenX n hn, hlenY n hn]
    exact hab
  obtain ⟨hre, him⟩ := coeff_fits p l w (X n) (Y n) hxy hw (hX n hn) (hY n hn) c
  rw [hre, him]

/-- The rescaled error guarantee applies to the symbols on the returned tape. -/
theorem output_err {A p l w M a b : ℕ} (hA : 4 ≤ A) (hw : p + 2 ≤ w)
    (hab : a + b ≤ 2 ^ l + 1) (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (c : Fin (2 ^ l)) :
    ‖((2 ^ l : ℕ) : ℂ) * value p (decodeWord
      (((cstream A w (result p l M X Y) ++ tail).drop
        ((n * 2 ^ l + c.val) * w)).take w)) -
      ∑ i ∈ Finset.range (c.val + 1), value p (block (X n) i) * value p (block (Y n) (c.val - i))‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ p := by
  rw [output_coeff hA hw hab X Y hlenX hlenY hX hY tail n hn c]
  apply coeff_err
  rw [hlenX n hn, hlenY n hn]
  exact hab

end Fixed
end IntegerMultBounds.MathlibTM2.Mult.ShortConv
