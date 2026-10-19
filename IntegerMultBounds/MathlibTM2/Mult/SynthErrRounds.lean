module

public import IntegerMultBounds.MathlibTM2.Mult.Rounds

/-!
# Computed transform rounds: truncation error, disk, layouts

Paper §6, numerical part of the proof of `lem:synthetic-transform-cost`: the transform rounds
`fwdRound`, `oppRound` of `IntegerMultBounds.MathlibTM2.Mult.Rounds`, each followed by one truncation `Q_p`
(`NLogN.rhoC`, toward zero on every real and imaginary part).

## Record arrays

Arrays are the vendored `Recs r = ℕ → Fin r → ℂ`. Bounds concern the first `2^N` records,
`N = Σ aᵢ`: `SupLe N u a` says every coefficient of every record below `2^N` has modulus at most
`a`; `GridR p u` says every coefficient lies on the `p`-bit grid; `rdR p` is `Q_p` on every
coefficient.

* `rho0_neg`, `shiftNegZ_rhoC`, `shiftInv_rhoC`: truncation toward zero is odd, so `Q_p` commutes
  with multiplication by `y^{±e}`, a signed coefficient permutation.
* `mulYInv_rdR_bflyL`: the machine's forward round, the layer output `Q_p(ℋ z)` followed by the
  twiddle `J_E`, is `Q_p(fwdRound z)` (`J_E Q_p(ℋ z) = Q_p(J_E ℋ z)`). `oppRound_layer_input`:
  `J_E⁻¹` keeps a disk grid array a disk grid array, and the layer of the opposite round returns
  `Q_p(oppRound z)`.
* `fwdRound_sub`, `fwdRound_supLe`, `oppRound_sub`, `oppRound_supLe`: every exact round is linear
  and does not increase the coefficient sup norm on the first `2^N` records (normalized
  butterflies `bfly_supLe`, signed coefficient permutations `mulY_supLe`, `mulYInv_supLe`).

## Computed rounds

* `fwdRoundsC p es k`, `oppRoundsC p es k`: `Q_p` after each of `k` exact rounds, in the round
  orders of `fwdRounds` and `oppRounds`.
* `fwdRoundsC_err`, `oppRoundsC_err`: input error `e` gives error at most `e + k √2 2^{-p}`;
  `fwdRoundsC_err_lt`, `oppRoundsC_err_lt`: less than `e + (k + 1) √2 2^{-p}` after `k + 1`
  rounds.
* `fwdRoundsC_supLe`, `fwdRoundsC_grid` and their opposite forms: disk and grid are preserved.
* `fwdRoundsC_close`, `oppRoundsC_close`: with `A = maxᵢ aᵢ ≤ ℓ` and `1 ≤ ℓ`, the computed
  transforms are within less than `√2 ℓ 2^{-p}` of `fwdExact ts 1 = B F⁻` and
  `oppExact ts 1 = F⁺ B⁻¹` on the first `M = ∏ tᵢ` records, in the form
  `Spec.SignedRingProduct.Close` of `MeetsForward` and `MeetsOpposite` (identity layout).

## Flat arrays and layouts

* `fwdRoundsFlatC`, `oppRoundsFlatC`: the computed rounds on the flattened arrays
  `IntegerMultBounds.MathlibTM2.Layer.Arr (Fin r) N` with their sup norm (`flat_fwdRoundsC`); `twFwdFlat_rdA_Hl`: the
  layer output `Q_p(Hl z)` followed by the twiddle; `fwdRoundsFlatC_err`,
  `oppRoundsFlatC_err`: error at most `‖f - g‖ + k √2 2^{-p}`.
* `relabel L` for `L : Equiv.Perm (Fin N)`: the array stored with its address bits permuted by
  `L`, an isometry commuting with `Q_p`. `fwdRoundsFlatL`, `oppRoundsFlatL` and the computed
  `fwdRoundsFlatLC`, `oppRoundsFlatLC` are the rounds conjugated by `L`; `fwdRoundsFlatLC_err`,
  `oppRoundsFlatLC_err`, `norm_fwdRoundsFlatLC_le`, `norm_oppRoundsFlatLC_le`: the same error and
  disk bounds in every layout. `fwd_rounds_flatL`: in the layout `L` the exact forward rounds
  compute `L B F⁻`; `fwdRoundsFlatLC_err_LBF`: the computed ones are within `√2 A 2^{-p}` of it.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.SynthErr

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Mult.Rounds

/-! ### Truncation and signed coefficient permutations -/

section Truncation

theorem rho0_neg (x : ℝ) : rho0 (-x) = -rho0 x := by
  unfold rho0
  rcases lt_trichotomy x 0 with h | h | h
  · have h1 : 0 ≤ -x := by linarith
    have h2 : ¬ 0 ≤ x := by linarith
    simp only [h1, h2, ↓reduceIte, Int.floor_neg]
  · subst h; simp
  · have h1 : ¬ 0 ≤ -x := by linarith
    simp only [h1, h.le, ↓reduceIte, Int.ceil_neg]

theorem rhoC_neg (p : ℕ) (u : ℂ) : rhoC p (-u) = -rhoC p u := by
  apply Complex.ext <;>
    simp only [rhoC_re, rhoC_im, Complex.neg_re, Complex.neg_im, mul_neg, rho0_neg, Int.cast_neg,
      neg_div]

theorem rhoC_neg_one_pow_mul (p m : ℕ) (u : ℂ) :
    rhoC p ((-1 : ℂ) ^ m * u) = (-1 : ℂ) ^ m * rhoC p u := by
  rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h]
  · simp
  · simp [rhoC_neg]

variable {r : ℕ} [NeZero r]

/-- `Q_p` commutes with multiplication by `y^e`, a signed coefficient permutation. -/
theorem shiftNegZ_rhoC (p e : ℕ) (a : Fin r → ℂ) :
    shiftNegZ e (fun c => rhoC p (a c)) = fun c => rhoC p (shiftNegZ e a c) := by
  funext i
  rw [shiftNegZ_apply, shiftNegZ_apply, rhoC_neg_one_pow_mul]

theorem shiftInv_rhoC (p e : ℕ) (a : Fin r → ℂ) :
    shiftInv e (fun c => rhoC p (a c)) = fun c => rhoC p (shiftInv e a c) := by
  unfold shiftInv; exact shiftNegZ_rhoC p _ a

theorem norm_shiftNegZ_apply_le {e : ℕ} {a : Fin r → ℂ} {b : ℝ} (h : ∀ c, ‖a c‖ ≤ b) (i : Fin r) :
    ‖shiftNegZ e a i‖ ≤ b := by
  rw [shiftNegZ_apply, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact h _

theorem norm_shiftInv_apply_le {e : ℕ} {a : Fin r → ℂ} {b : ℝ} (h : ∀ c, ‖a c‖ ≤ b) (i : Fin r) :
    ‖shiftInv e a i‖ ≤ b := by
  unfold shiftInv; exact norm_shiftNegZ_apply_le h i

theorem isFixed_shiftNegZ {p e : ℕ} {a : Fin r → ℂ} (h : ∀ c, IsFixed p (a c)) (i : Fin r) :
    IsFixed p (shiftNegZ e a i) := by
  rw [shiftNegZ_apply]
  rcases neg_one_pow_eq_or ℂ (((shiftSrc r e i).val + e) / r) with hs | hs <;> rw [hs]
  · rw [one_mul]; exact h _
  · rw [neg_one_mul]; exact (h _).neg

theorem isFixed_shiftInv {p e : ℕ} {a : Fin r → ℂ} (h : ∀ c, IsFixed p (a c)) (i : Fin r) :
    IsFixed p (shiftInv e a i) := by
  unfold shiftInv; exact isFixed_shiftNegZ h i

theorem shiftNegZ_sub (e : ℕ) (a b : Fin r → ℂ) :
    shiftNegZ e (a - b) = shiftNegZ e a - shiftNegZ e b := by
  funext i
  simp only [shiftNegZ_apply, Pi.sub_apply, mul_sub]

theorem shiftInv_sub (e : ℕ) (a b : Fin r → ℂ) :
    shiftInv e (a - b) = shiftInv e a - shiftInv e b := by
  unfold shiftInv; exact shiftNegZ_sub _ a b

end Truncation

/-! ### Record arrays: truncation, bounds, linearity -/

section Arrays

variable {r : ℕ}

/-- `Q_p` on every real and imaginary part of every coefficient of every record. -/
noncomputable def rdR (p : ℕ) (u : Recs r) : Recs r := fun n c => rhoC p (u n c)

/-- Every coefficient of the first `2^N` records has modulus at most `a`. -/
def SupLe (N : ℕ) (u : Recs r) (a : ℝ) : Prop := ∀ n < 2 ^ N, ∀ c, ‖u n c‖ ≤ a

/-- Every coefficient of every record lies on the `p`-bit grid. -/
def GridR (p : ℕ) (u : Recs r) : Prop := ∀ n c, IsFixed p (u n c)

theorem SupLe.mono {N : ℕ} {u : Recs r} {a b : ℝ} (h : SupLe N u a) (hab : a ≤ b) : SupLe N u b :=
  fun n hn c => (h n hn c).trans hab

theorem gridR_rdR (p : ℕ) (u : Recs r) : GridR p (rdR p u) := fun _ _ => isFixed_rhoC _ _

theorem rdR_supLe {N : ℕ} {u : Recs r} {a : ℝ} (p : ℕ) (h : SupLe N u a) : SupLe N (rdR p u) a :=
  fun n hn c => (norm_rhoC_le p _).trans (h n hn c)

/-- One truncation moves a coefficient by less than `√2·2^{-p}`. -/
theorem rdR_sub_lt (p : ℕ) (u : Recs r) (n : ℕ) (c : Fin r) :
    ‖rdR p u n c - u n c‖ < Real.sqrt 2 / 2 ^ p :=
  norm_rhoC_sub_lt p _

theorem bfly_sub (q : ℕ) (u v : Recs r) : bfly q (u - v) = bfly q u - bfly q v := by
  funext n c
  simp only [bfly, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem bflyL_sub (l : List ℕ) (u v : Recs r) : bflyL l (u - v) = bflyL l u - bflyL l v := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    show bfly q (bflyL l (u - v)) = bfly q (bflyL l u) - bfly q (bflyL l v)
    rw [ih, bfly_sub]

/-- A normalized butterfly does not increase the coefficient sup norm. -/
theorem bfly_supLe {N q : ℕ} (hq : q < N) {u : Recs r} {a : ℝ} (h : SupLe N u a) :
    SupLe N (bfly q u) a := by
  intro n hn c
  have hq' : 2 ^ q < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) hq
  have h1 := h n hn c
  have h2 := h _ (Nat.xor_lt_two_pow hn hq') c
  have hs : ‖(if n.testBit q then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp
  simp only [bfly, Pi.smul_apply, Pi.add_apply, smul_eq_mul, norm_mul]
  calc ‖(1 / 2 : ℂ)‖ * ‖(if n.testBit q then (-1 : ℂ) else 1) * u n c + u (n ^^^ 2 ^ q) c‖
      ≤ ‖(1 / 2 : ℂ)‖ * (‖(if n.testBit q then (-1 : ℂ) else 1)‖ * ‖u n c‖ +
          ‖u (n ^^^ 2 ^ q) c‖) := by
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ 1 / 2 * (1 * a + a) := by
        rw [hs]
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [this]
        gcongr
    _ = a := by ring

theorem bflyL_supLe {N : ℕ} {l : List ℕ} (hl : ∀ q ∈ l, q < N) {u : Recs r} {a : ℝ}
    (h : SupLe N u a) : SupLe N (bflyL l u) a := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact bfly_supLe (hl q (by simp)) (ih fun q' hq' => hl q' (by simp [hq']))

variable [NeZero r]

theorem mulY_sub (e : ℕ → ℕ) (u v : Recs r) : mulY e (u - v) = mulY e u - mulY e v := by
  funext n
  simp only [mulY, Pi.sub_apply, shiftNegZ_sub]

theorem mulYInv_sub (e : ℕ → ℕ) (u v : Recs r) :
    mulYInv e (u - v) = mulYInv e u - mulYInv e v := by
  funext n
  simp only [mulYInv, Pi.sub_apply, shiftInv_sub]

theorem mulY_supLe {N : ℕ} (e : ℕ → ℕ) {u : Recs r} {a : ℝ} (h : SupLe N u a) :
    SupLe N (mulY e u) a :=
  fun n hn c => norm_shiftNegZ_apply_le (h n hn) c

theorem mulYInv_supLe {N : ℕ} (e : ℕ → ℕ) {u : Recs r} {a : ℝ} (h : SupLe N u a) :
    SupLe N (mulYInv e u) a :=
  fun n hn c => norm_shiftInv_apply_le (h n hn) c

theorem gridR_mulY {p : ℕ} (e : ℕ → ℕ) {u : Recs r} (h : GridR p u) : GridR p (mulY e u) :=
  fun n c => isFixed_shiftNegZ (h n) c

theorem gridR_mulYInv {p : ℕ} (e : ℕ → ℕ) {u : Recs r} (h : GridR p u) :
    GridR p (mulYInv e u) :=
  fun n c => isFixed_shiftInv (h n) c

theorem mulYInv_rdR (p : ℕ) (e : ℕ → ℕ) (u : Recs r) :
    mulYInv e (rdR p u) = rdR p (mulYInv e u) := by
  funext n
  exact shiftInv_rhoC p (e n) (u n)

end Arrays

/-! ### The exact rounds are linear sup-norm contractions -/

section Rounds

variable {r : ℕ} [NeZero r] (es : List ℕ)

theorem fwdRound_sub (h : ℕ) (u v : Recs r) :
    fwdRound es h (u - v) = fwdRound es h u - fwdRound es h v := by
  unfold fwdRound; rw [bflyL_sub, mulYInv_sub]

theorem oppRound_sub (h : ℕ) (u v : Recs r) :
    oppRound es h (u - v) = oppRound es h u - oppRound es h v := by
  unfold oppRound; rw [mulY_sub, bflyL_sub]

theorem fwdRound_supLe (h : ℕ) {u : Recs r} {a : ℝ} (hu : SupLe es.sum u a) :
    SupLe es.sum (fwdRound es h u) a :=
  mulYInv_supLe _ (bflyL_supLe (fun _ hq => selBits_lt es hq) hu)

theorem oppRound_supLe (h : ℕ) {u : Recs r} {a : ℝ} (hu : SupLe es.sum u a) :
    SupLe es.sum (oppRound es h u) a :=
  bflyL_supLe (fun _ hq => selBits_lt es hq) (mulY_supLe _ hu)

theorem fwdRounds_supLe : ∀ (k : ℕ) {u : Recs r} {a : ℝ}, SupLe es.sum u a →
    SupLe es.sum (fwdRounds es k u) a
  | 0, _, _, hu => hu
  | k + 1, _, _, hu => fwdRounds_supLe k (fwdRound_supLe es k hu)

/-- The machine's forward round: the layer returns `Q_p(ℋ z)` and the twiddle `J_E` follows.
Since `J_E` is a signed coefficient permutation, `J_E Q_p(ℋ z) = Q_p(J_E ℋ z)`: the forward
round truncates once after the exact round. -/
theorem mulYInv_rdR_bflyL (p h : ℕ) (u : Recs r) :
    mulYInv (twE es r h (parts es h)) (rdR p (bflyL (selBits es h) u)) =
      rdR p (fwdRound es h u) :=
  mulYInv_rdR p _ _

/-- The machine's opposite round: `J_E⁻¹` preserves the disk grid, and the layer returns
`Q_p(ℋ J_E⁻¹ z)`. -/
theorem oppRound_layer_input {p : ℕ} (h : ℕ) {u : Recs r} (hg : GridR p u)
    (hd : SupLe es.sum u 1) :
    GridR p (mulY (twE es r h (parts es h)) u) ∧
      SupLe es.sum (mulY (twE es r h (parts es h)) u) 1 :=
  ⟨gridR_mulY _ hg, mulY_supLe _ hd⟩

end Rounds

/-! ### Computed rounds -/

section Computed

variable {r : ℕ} [NeZero r] (p : ℕ) (es : List ℕ)

/-- The computed forward rounds at `h = k - 1, …, 0`: each exact round followed by `Q_p`. -/
noncomputable def fwdRoundsC : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => fwdRoundsC k (rdR p (fwdRound es k u))

/-- The computed opposite rounds at `h = 0, …, k - 1`: each exact round followed by `Q_p`. -/
noncomputable def oppRoundsC : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => rdR p (oppRound es k (oppRoundsC k u))

omit [NeZero r] in
/-- The truncation after an exact round, against the exact round of another array. -/
theorem rdR_round_err {R : Recs r → Recs r} (hR : ∀ u v, R (u - v) = R u - R v)
    (hc : ∀ {w : Recs r} {a : ℝ}, SupLe es.sum w a → SupLe es.sum (R w) a) {u v : Recs r}
    {e : ℝ} (h : SupLe es.sum (u - v) e) (n : ℕ) (hn : n < 2 ^ es.sum) (c : Fin r) :
    ‖(rdR p (R u) - R v) n c‖ < e + Real.sqrt 2 / 2 ^ p := by
  have h1 := rdR_sub_lt p (R u) n c
  have h2 : ‖R u n c - R v n c‖ ≤ e := by
    have := hc h n hn c
    rwa [hR] at this
  calc ‖(rdR p (R u) - R v) n c‖ = ‖(rdR p (R u) n c - R u n c) + (R u n c - R v n c)‖ := by
        simp only [Pi.sub_apply]; congr 1; abel
    _ ≤ ‖rdR p (R u) n c - R u n c‖ + ‖R u n c - R v n c‖ := norm_add_le _ _
    _ < Real.sqrt 2 / 2 ^ p + e := add_lt_add_of_lt_of_le h1 h2
    _ = e + Real.sqrt 2 / 2 ^ p := add_comm _ _

/-- `k` computed forward rounds stay within `k √2 2^{-p}` of the exact rounds (plus the input
error). -/
theorem fwdRoundsC_err : ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum (u - v) e →
    SupLe es.sum (fwdRoundsC p es k u - fwdRounds es k v) (e + k * (Real.sqrt 2 / 2 ^ p))
  | 0, u, v, e, h => by simpa [fwdRoundsC, fwdRounds] using h
  | k + 1, u, v, e, h => by
    have h' : SupLe es.sum (rdR p (fwdRound es k u) - fwdRound es k v)
        (e + Real.sqrt 2 / 2 ^ p) := fun n hn c =>
      (rdR_round_err p es (fwdRound_sub es k) (fwdRound_supLe es k) h n hn c).le
    have := fwdRoundsC_err k h'
    refine this.mono (le_of_eq ?_)
    push_cast; ring

/-- The strict form: after `k + 1` computed forward rounds the error is less than
`e + (k + 1) √2 2^{-p}`. -/
theorem fwdRoundsC_err_lt : ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum (u - v) e →
    ∀ n < 2 ^ es.sum, ∀ c,
      ‖(fwdRoundsC p es (k + 1) u - fwdRounds es (k + 1) v) n c‖ <
        e + (k + 1) * (Real.sqrt 2 / 2 ^ p)
  | 0, u, v, e, h, n, hn, c => by
    have := rdR_round_err p es (fwdRound_sub es 0) (fwdRound_supLe es 0) h n hn c
    simpa [fwdRoundsC, fwdRounds] using this
  | k + 1, u, v, e, h, n, hn, c => by
    have h' : SupLe es.sum (rdR p (fwdRound es (k + 1) u) - fwdRound es (k + 1) v)
        (e + Real.sqrt 2 / 2 ^ p) := fun n hn c =>
      (rdR_round_err p es (fwdRound_sub es (k + 1)) (fwdRound_supLe es (k + 1)) h n hn c).le
    have := fwdRoundsC_err_lt k h' n hn c
    calc _ = _ := rfl
      _ < _ := this
      _ = _ := by push_cast; ring

/-- `k` computed opposite rounds stay within `k √2 2^{-p}` of the exact rounds (plus the input
error). -/
theorem oppRoundsC_err : ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum (u - v) e →
    SupLe es.sum (oppRoundsC p es k u - oppRounds es k v) (e + k * (Real.sqrt 2 / 2 ^ p))
  | 0, u, v, e, h => by simpa [oppRoundsC, oppRounds] using h
  | k + 1, u, v, e, h => by
    have ih := oppRoundsC_err k h
    intro n hn c
    have := rdR_round_err p es (oppRound_sub es k) (oppRound_supLe es k) ih n hn c
    refine this.le.trans (le_of_eq ?_)
    push_cast; ring

theorem oppRoundsC_err_lt (k : ℕ) {u v : Recs r} {e : ℝ} (h : SupLe es.sum (u - v) e) :
    ∀ n < 2 ^ es.sum, ∀ c,
      ‖(oppRoundsC p es (k + 1) u - oppRounds es (k + 1) v) n c‖ <
        e + (k + 1) * (Real.sqrt 2 / 2 ^ p) := by
  intro n hn c
  have := rdR_round_err p es (oppRound_sub es k) (oppRound_supLe es k)
    (oppRoundsC_err p es k h) n hn c
  calc _ = _ := rfl
    _ < _ := this
    _ = _ := by ring

/-- The computed forward rounds preserve the disk (any radius). -/
theorem fwdRoundsC_supLe : ∀ (k : ℕ) {u : Recs r} {a : ℝ}, SupLe es.sum u a →
    SupLe es.sum (fwdRoundsC p es k u) a
  | 0, _, _, h => h
  | k + 1, _, _, h => fwdRoundsC_supLe k (rdR_supLe p (fwdRound_supLe es k h))

theorem oppRoundsC_supLe : ∀ (k : ℕ) {u : Recs r} {a : ℝ}, SupLe es.sum u a →
    SupLe es.sum (oppRoundsC p es k u) a
  | 0, _, _, h => h
  | k + 1, _, _, h => rdR_supLe p (oppRound_supLe es k (oppRoundsC_supLe k h))

/-- The computed forward rounds return grid arrays (on grid inputs when `k = 0`). -/
theorem fwdRoundsC_grid : ∀ (k : ℕ) {u : Recs r}, GridR p u → GridR p (fwdRoundsC p es k u)
  | 0, _, h => h
  | k + 1, _, _ => fwdRoundsC_grid k (gridR_rdR p _)

theorem oppRoundsC_grid : ∀ (k : ℕ) {u : Recs r}, GridR p u → GridR p (oppRoundsC p es k u)
  | 0, _, h => h
  | _ + 1, _, _ => gridR_rdR p _

end Computed

theorem supLe_sub_self {r : ℕ} (N : ℕ) (u : Recs r) : SupLe N (u - u) 0 := by
  intro n _ c; simp

/-! ### Flat arrays -/

section Flat

open IntegerMultBounds.MathlibTM2.Layer

variable {r : ℕ}

/-- `Q_p` on every entry of a flat array. -/
noncomputable def rdA {X : Type} {N : ℕ} (p : ℕ) (f : Arr X N) : Arr X N := fun q => rhoC p (f q)

/-- The bits of an address. -/
def toBits (N n : ℕ) : Fin N → ZMod 2 := fun q => if n.testBit q then 1 else 0

/-- A flat array read as a record array. -/
noncomputable def unflat {N : ℕ} (f : Arr (Fin r) N) : Recs r := fun n c => f (c, toBits N n)

theorem toBits_ofBits {N : ℕ} (b : Fin N → ZMod 2) : toBits N (ofBits b) = b := by
  funext q
  simp only [toBits, testBit_ofBits_fin]
  rcases zmod2_cases (b q) with h | h <;> simp [h]

theorem flat_unflat {N : ℕ} (f : Arr (Fin r) N) : flat N (unflat f) = f := by
  funext q
  simp only [flat, unflat, toBits_ofBits]

theorem flat_sub {N : ℕ} (u v : Recs r) : flat N (u - v) = flat N u - flat N v := rfl

theorem flat_rdR {N : ℕ} (p : ℕ) (u : Recs r) : flat N (rdR p u) = rdA p (flat N u) := rfl

theorem norm_flat_le {N : ℕ} {u : Recs r} {a : ℝ} (ha : 0 ≤ a) (h : SupLe N u a) :
    ‖flat N u‖ ≤ a :=
  (pi_norm_le_iff_of_nonneg ha).2 fun q => h _ (ofBits_lt q.2) q.1

theorem supLe_unflat {N : ℕ} (f : Arr (Fin r) N) : SupLe N (unflat f) ‖f‖ :=
  fun n _ c => norm_le_pi_norm f (c, toBits N n)

variable [NeZero r] (p : ℕ) (es : List ℕ)

/-- The computed forward rounds on the flattened array. -/
noncomputable def fwdRoundsFlatC : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => fwdRoundsFlatC k (rdA p (fwdRoundFlat es k f))

/-- The computed opposite rounds on the flattened array. -/
noncomputable def oppRoundsFlatC : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => rdA p (oppRoundFlat es k (oppRoundsFlatC k f))

theorem flat_fwdRoundsC : ∀ (k : ℕ) (u : Recs r),
    flat es.sum (fwdRoundsC p es k u) = fwdRoundsFlatC p es k (flat es.sum u)
  | 0, _ => rfl
  | k + 1, u => by
    rw [fwdRoundsC, fwdRoundsFlatC, flat_fwdRoundsC k, flat_rdR, flat_fwdRound]

theorem flat_oppRoundsC : ∀ (k : ℕ) (u : Recs r),
    flat es.sum (oppRoundsC p es k u) = oppRoundsFlatC p es k (flat es.sum u)
  | 0, _ => rfl
  | k + 1, u => by
    rw [oppRoundsC, oppRoundsFlatC, flat_rdR, flat_oppRound, flat_oppRoundsC k]

/-- The machine's forward round on the flattened array: the layer returns `Q_p(Hl z)` on the
selected bits, and the twiddle that follows commutes with `Q_p`. -/
theorem twFwdFlat_rdA_Hl (h : ℕ) (f : Arr (Fin r) es.sum) :
    twFwdFlat es h (rdA p (Hl (Fin r) (selFin es h) f)) = rdA p (fwdRoundFlat es h f) := by
  funext q
  exact congrFun (shiftInv_rhoC p _ fun c => Hl (Fin r) (selFin es h) f (c, q.2)) q.1

/-- `k` computed forward rounds on flat arrays: error at most `‖f - g‖ + k √2 2^{-p}`. -/
theorem fwdRoundsFlatC_err (k : ℕ) (f g : Arr (Fin r) es.sum) :
    ‖fwdRoundsFlatC p es k f - fwdRoundsFlat es k g‖ ≤ ‖f - g‖ + k * (Real.sqrt 2 / 2 ^ p) := by
  have h : SupLe es.sum (unflat f - unflat g) ‖f - g‖ := supLe_unflat (f - g)
  have := norm_flat_le (by positivity) (fwdRoundsC_err p es k h)
  rwa [flat_sub, flat_fwdRoundsC, flat_fwdRounds, flat_unflat, flat_unflat] at this

theorem oppRoundsFlatC_err (k : ℕ) (f g : Arr (Fin r) es.sum) :
    ‖oppRoundsFlatC p es k f - oppRoundsFlat es k g‖ ≤ ‖f - g‖ + k * (Real.sqrt 2 / 2 ^ p) := by
  have h : SupLe es.sum (unflat f - unflat g) ‖f - g‖ := supLe_unflat (f - g)
  have := norm_flat_le (by positivity) (oppRoundsC_err p es k h)
  rwa [flat_sub, flat_oppRoundsC, flat_oppRounds, flat_unflat, flat_unflat] at this

theorem norm_fwdRoundsFlatC_le (k : ℕ) {f : Arr (Fin r) es.sum} {a : ℝ} (hf : ‖f‖ ≤ a) :
    ‖fwdRoundsFlatC p es k f‖ ≤ a := by
  have := norm_flat_le ((norm_nonneg f).trans hf)
    (fwdRoundsC_supLe p es k ((supLe_unflat f).mono hf))
  rwa [flat_fwdRoundsC, flat_unflat] at this

theorem norm_oppRoundsFlatC_le (k : ℕ) {f : Arr (Fin r) es.sum} {a : ℝ} (hf : ‖f‖ ≤ a) :
    ‖oppRoundsFlatC p es k f‖ ≤ a := by
  have := norm_flat_le ((norm_nonneg f).trans hf)
    (oppRoundsC_supLe p es k ((supLe_unflat f).mono hf))
  rwa [flat_oppRoundsC, flat_unflat] at this

end Flat

/-! ### Layouts -/

section Layout

open IntegerMultBounds.MathlibTM2.Layer

/-- The flat array stored in the layout `L`, a permutation of the address bits: entry `(c, b)` is
the logical entry `(c, b ∘ L)`. -/
def relabel {X : Type} {N : ℕ} (L : Equiv.Perm (Fin N)) (f : Arr X N) : Arr X N :=
  fun q => f (q.1, q.2 ∘ L)

variable {X : Type} {N : ℕ}

theorem relabel_symm_relabel (L : Equiv.Perm (Fin N)) (f : Arr X N) :
    relabel L.symm (relabel L f) = f := by
  funext q
  simp only [relabel]
  congr 2
  funext x
  simp

theorem relabel_relabel_symm (L : Equiv.Perm (Fin N)) (f : Arr X N) :
    relabel L (relabel L.symm f) = f := by
  simpa using relabel_symm_relabel L.symm f

theorem relabel_sub (L : Equiv.Perm (Fin N)) (f g : Arr X N) :
    relabel L (f - g) = relabel L f - relabel L g := rfl

theorem rdA_relabel (p : ℕ) (L : Equiv.Perm (Fin N)) (f : Arr X N) :
    rdA p (relabel L f) = relabel L (rdA p f) := rfl

variable [Fintype X]

theorem norm_relabel_le (L : Equiv.Perm (Fin N)) (f : Arr X N) : ‖relabel L f‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 fun _ => norm_le_pi_norm f _

/-- A layout is an isometry. -/
theorem norm_relabel (L : Equiv.Perm (Fin N)) (f : Arr X N) : ‖relabel L f‖ = ‖f‖ :=
  le_antisymm (norm_relabel_le L f) (by
    conv_lhs => rw [← relabel_symm_relabel L f]
    exact norm_relabel_le L.symm _)

variable {r : ℕ} [NeZero r] (p : ℕ) (es : List ℕ) (L : Equiv.Perm (Fin es.sum))

/-- The forward round on an array stored in the layout `L`. -/
noncomputable def fwdRoundFlatL (h : ℕ) (f : Arr (Fin r) es.sum) : Arr (Fin r) es.sum :=
  relabel L (fwdRoundFlat es h (relabel L.symm f))

/-- The opposite round on an array stored in the layout `L`. -/
noncomputable def oppRoundFlatL (h : ℕ) (f : Arr (Fin r) es.sum) : Arr (Fin r) es.sum :=
  relabel L (oppRoundFlat es h (relabel L.symm f))

/-- The exact forward rounds in the layout `L`. -/
noncomputable def fwdRoundsFlatL : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => fwdRoundsFlatL k (fwdRoundFlatL es L k f)

/-- The computed forward rounds in the layout `L`. -/
noncomputable def fwdRoundsFlatLC : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => fwdRoundsFlatLC k (rdA p (fwdRoundFlatL es L k f))

/-- The exact opposite rounds in the layout `L`. -/
noncomputable def oppRoundsFlatL : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => oppRoundFlatL es L k (oppRoundsFlatL k f)

/-- The computed opposite rounds in the layout `L`. -/
noncomputable def oppRoundsFlatLC : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => rdA p (oppRoundFlatL es L k (oppRoundsFlatLC k f))

theorem fwdRoundsFlatL_relabel : ∀ (k : ℕ) (f : Arr (Fin r) es.sum),
    fwdRoundsFlatL es L k (relabel L f) = relabel L (fwdRoundsFlat es k f)
  | 0, _ => rfl
  | k + 1, f => by
    rw [fwdRoundsFlatL, fwdRoundsFlat, fwdRoundFlatL, relabel_symm_relabel,
      fwdRoundsFlatL_relabel k]

theorem fwdRoundsFlatLC_relabel : ∀ (k : ℕ) (f : Arr (Fin r) es.sum),
    fwdRoundsFlatLC p es L k (relabel L f) = relabel L (fwdRoundsFlatC p es k f)
  | 0, _ => rfl
  | k + 1, f => by
    rw [fwdRoundsFlatLC, fwdRoundsFlatC, fwdRoundFlatL, relabel_symm_relabel, rdA_relabel,
      fwdRoundsFlatLC_relabel k]

omit [NeZero r] in
theorem oppRoundsFlatL_relabel : ∀ (k : ℕ) (f : Arr (Fin r) es.sum),
    oppRoundsFlatL es L k (relabel L f) = relabel L (oppRoundsFlat es k f)
  | 0, _ => rfl
  | k + 1, f => by
    rw [oppRoundsFlatL, oppRoundsFlat, oppRoundsFlatL_relabel k, oppRoundFlatL,
      relabel_symm_relabel]

omit [NeZero r] in
theorem oppRoundsFlatLC_relabel : ∀ (k : ℕ) (f : Arr (Fin r) es.sum),
    oppRoundsFlatLC p es L k (relabel L f) = relabel L (oppRoundsFlatC p es k f)
  | 0, _ => rfl
  | k + 1, f => by
    rw [oppRoundsFlatLC, oppRoundsFlatC, oppRoundsFlatLC_relabel k, oppRoundFlatL,
      relabel_symm_relabel, rdA_relabel]

/-- In any layout `L` of the address bits, `k` computed forward rounds stay within
`‖f - g‖ + k √2 2^{-p}` of the exact rounds. -/
theorem fwdRoundsFlatLC_err (k : ℕ) (f g : Arr (Fin r) es.sum) :
    ‖fwdRoundsFlatLC p es L k f - fwdRoundsFlatL es L k g‖ ≤
      ‖f - g‖ + k * (Real.sqrt 2 / 2 ^ p) := by
  rw [← relabel_relabel_symm L f, ← relabel_relabel_symm L g, fwdRoundsFlatLC_relabel,
    fwdRoundsFlatL_relabel, ← relabel_sub, norm_relabel, ← relabel_sub, norm_relabel]
  exact fwdRoundsFlatC_err p es k _ _

theorem oppRoundsFlatLC_err (k : ℕ) (f g : Arr (Fin r) es.sum) :
    ‖oppRoundsFlatLC p es L k f - oppRoundsFlatL es L k g‖ ≤
      ‖f - g‖ + k * (Real.sqrt 2 / 2 ^ p) := by
  rw [← relabel_relabel_symm L f, ← relabel_relabel_symm L g, oppRoundsFlatLC_relabel,
    oppRoundsFlatL_relabel, ← relabel_sub, norm_relabel, ← relabel_sub, norm_relabel]
  exact oppRoundsFlatC_err p es k _ _

/-- In any layout the computed rounds preserve the disk. -/
theorem norm_fwdRoundsFlatLC_le (k : ℕ) {f : Arr (Fin r) es.sum} {a : ℝ} (hf : ‖f‖ ≤ a) :
    ‖fwdRoundsFlatLC p es L k f‖ ≤ a := by
  rw [← relabel_relabel_symm L f, fwdRoundsFlatLC_relabel, norm_relabel]
  exact norm_fwdRoundsFlatC_le p es k ((norm_relabel L.symm f).le.trans hf)

theorem norm_oppRoundsFlatLC_le (k : ℕ) {f : Arr (Fin r) es.sum} {a : ℝ} (hf : ‖f‖ ≤ a) :
    ‖oppRoundsFlatLC p es L k f‖ ≤ a := by
  rw [← relabel_relabel_symm L f, oppRoundsFlatLC_relabel, norm_relabel]
  exact norm_oppRoundsFlatC_le p es k ((norm_relabel L.symm f).le.trans hf)

end Layout

/-! ### The transforms of `lem:synthetic-transform-cost` in the vendored form -/

section Transforms

variable {r : ℕ} [NeZero r]

/-- `k ≤ ℓ` computed forward rounds, `ℓ ≥ 1`: error less than `√2 ℓ 2^{-p}`. -/
theorem fwdRoundsC_lt_ell (p : ℕ) (es : List ℕ) {k ℓ : ℕ} (hk : k ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (z : Recs r) : ∀ n < 2 ^ es.sum, ∀ c,
      ‖fwdRoundsC p es k z n c - fwdRounds es k z n c‖ < Real.sqrt 2 * ℓ / 2 ^ p := by
  intro n hn c
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hpos : 0 < Real.sqrt 2 * ℓ / 2 ^ p :=
    div_pos (mul_pos (Real.sqrt_pos.2 two_pos) hℓ') (by positivity)
  rcases k with _ | k
  · simpa [fwdRoundsC, fwdRounds] using hpos
  · have := fwdRoundsC_err_lt p es k (supLe_sub_self es.sum z) n hn c
    have hk' : (k : ℝ) + 1 ≤ ℓ := by exact_mod_cast hk
    calc ‖fwdRoundsC p es (k + 1) z n c - fwdRounds es (k + 1) z n c‖
        = ‖(fwdRoundsC p es (k + 1) z - fwdRounds es (k + 1) z) n c‖ := rfl
      _ < 0 + (k + 1) * (Real.sqrt 2 / 2 ^ p) := this
      _ ≤ ℓ * (Real.sqrt 2 / 2 ^ p) := by rw [zero_add]; gcongr
      _ = Real.sqrt 2 * ℓ / 2 ^ p := by ring

/-- `k ≤ ℓ` computed opposite rounds, `ℓ ≥ 1`: error less than `√2 ℓ 2^{-p}`. -/
theorem oppRoundsC_lt_ell (p : ℕ) (es : List ℕ) {k ℓ : ℕ} (hk : k ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (w : Recs r) : ∀ n < 2 ^ es.sum, ∀ c,
      ‖oppRoundsC p es k w n c - oppRounds es k w n c‖ < Real.sqrt 2 * ℓ / 2 ^ p := by
  intro n hn c
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hpos : 0 < Real.sqrt 2 * ℓ / 2 ^ p :=
    div_pos (mul_pos (Real.sqrt_pos.2 two_pos) hℓ') (by positivity)
  rcases k with _ | k
  · simpa [oppRoundsC, oppRounds] using hpos
  · have := oppRoundsC_err_lt p es k (supLe_sub_self es.sum w) n hn c
    have hk' : (k : ℝ) + 1 ≤ ℓ := by exact_mod_cast hk
    calc ‖oppRoundsC p es (k + 1) w n c - oppRounds es (k + 1) w n c‖
        = ‖(oppRoundsC p es (k + 1) w - oppRounds es (k + 1) w) n c‖ := rfl
      _ < 0 + (k + 1) * (Real.sqrt 2 / 2 ^ p) := this
      _ ≤ ℓ * (Real.sqrt 2 / 2 ^ p) := by rw [zero_add]; gcongr
      _ = Real.sqrt 2 * ℓ / 2 ^ p := by ring

variable {d : ℕ} (a : Fin d → ℕ)

/-- The axis lengths `tᵢ = 2^(aᵢ)`. -/
abbrev tsA : List ℕ := List.ofFn fun i => 2 ^ a i

/-- The number of rounds `A = maxᵢ aᵢ`. -/
abbrev nRounds : ℕ := Finset.univ.sup a

omit [NeZero r] in
theorem tsA_prod : (tsA a).prod = 2 ^ (List.ofFn a).sum := by
  unfold tsA; rw [← tsOf_ofFn, tsOf_prod]

omit [NeZero r] in
theorem powAxes_tsA (hr : ∀ i, 2 ^ a i ∣ 2 * r) : PowAxes r (tsA a) := by
  have hP := powAxes_tsOf (List.ofFn a) (hr_ofFn a hr)
  rwa [tsOf_ofFn] at hP


omit [NeZero r] in
theorem lt_two_pow_of_lt_prod {n : ℕ} (hn : n < (tsA a).prod) : n < 2 ^ (List.ofFn a).sum := by
  rwa [← tsA_prod]

/-- The numerical guarantee of `lem:synthetic-transform-cost` for the forward procedure (identity
layout) in the form `Spec.SignedRingProduct.Close`: error less than `√2 ℓ 2^{-p}` against
`fwdExact = L B F⁻` on the first `M` records. -/
theorem fwdRoundsC_close (hr : ∀ i, 2 ^ a i ∣ 2 * r) (p : ℕ) {ℓ : ℕ} (hA : nRounds a ≤ ℓ)
    (hℓ : 1 ≤ ℓ) (z : Recs r) :
    Close (tsA a).prod (fwdRoundsC p (List.ofFn a) (nRounds a) z) (fwdExact (tsA a) 1 z)
      (Real.sqrt 2 * ℓ / 2 ^ p) := by
  intro n hn c
  rw [← fwd_rounds_exact a hr z hn]
  exact fwdRoundsC_lt_ell p _ hA hℓ z n (lt_two_pow_of_lt_prod a hn) c

/-- The opposite counterpart of `fwdRoundsC_close`, against `oppExact = F⁺ B⁻¹ L⁻¹`. -/
theorem oppRoundsC_close (hr : ∀ i, 2 ^ a i ∣ 2 * r) (p : ℕ) {ℓ : ℕ} (hA : nRounds a ≤ ℓ)
    (hℓ : 1 ≤ ℓ) (w : Recs r) :
    Close (tsA a).prod (oppRoundsC p (List.ofFn a) (nRounds a) w) (oppExact (tsA a) 1 w)
      (Real.sqrt 2 * ℓ / 2 ^ p) := by
  intro n hn c
  rw [← opp_rounds_exact a hr w hn]
  exact oppRoundsC_lt_ell p _ hA hℓ w n (lt_two_pow_of_lt_prod a hn) c

end Transforms

/-! ### Layouts of the multi-axis transforms -/

section LayoutAxes

open IntegerMultBounds.MathlibTM2.Layer

variable {r : ℕ} [NeZero r] {d : ℕ} (a : Fin d → ℕ) (L : Equiv.Perm (Fin (List.ofFn a).sum))

/-- In the layout `L` the exact forward rounds compute `L B F⁻`. -/
theorem fwd_rounds_flatL (hr : ∀ i, 2 ^ a i ∣ 2 * r) (z : Recs r) :
    fwdRoundsFlatL (List.ofFn a) L (nRounds a) (relabel L (flat _ z)) =
      relabel L (flat _ fun n => fwdT (tsA a) z (bitrevAddr (tsA a) n)) := by
  rw [fwdRoundsFlatL_relabel, fwd_rounds_flat a hr z]

/-- In every layout `L` the computed forward rounds are within `√2 A 2^{-p}` of `L B F⁻`. -/
theorem fwdRoundsFlatLC_err_LBF (hr : ∀ i, 2 ^ a i ∣ 2 * r) (p : ℕ) (z : Recs r) :
    ‖fwdRoundsFlatLC p (List.ofFn a) L (nRounds a) (relabel L (flat _ z)) -
        relabel L (flat _ fun n => fwdT (tsA a) z (bitrevAddr (tsA a) n))‖ ≤
      nRounds a * (Real.sqrt 2 / 2 ^ p) := by
  rw [← fwd_rounds_flatL a L hr z]
  simpa using fwdRoundsFlatLC_err p (List.ofFn a) L (nRounds a) (relabel L (flat _ z))
    (relabel L (flat _ z))

end LayoutAxes

end IntegerMultBounds.MathlibTM2.Mult.SynthErr
