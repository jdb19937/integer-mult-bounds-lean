module

public import IntegerMultBounds.MathlibTM2.Layer.H0
import IntegerMultBounds.MathlibTM2.Mult.RoundsForward
import IntegerMultBounds.MathlibTM2.Mult.RoundsOpposite
public import IntegerMultBounds.MathlibTM2.Mult.RoundsBasic

/-!
# Iterative rounds of the multi-axis synthetic transforms

The decimation-in-frequency form of `F⁻ = fwdT ts` and the matching form of `F⁺ = oppT ts`
(paper §6: "Roots, butterflies, and stored frequency order" and the proof of
`lem:synthetic-transform-cost`), for axis lengths `tᵢ = 2^(aᵢ)` dividing `2r`,
`ts = List.ofFn fun i => 2 ^ a i`.

## Arrays and addresses

Arrays are the vendored record arrays `Recs r = ℕ → Fin r → ℂ` of `fwdT` and `oppT`, on the
mixed-radix addresses `n < M = ∏ tᵢ`, first axis most significant. Bit `h` of coordinate `i`,
`xᵢ = digit ts i n`, is bit `off i + h` of `n`, where `off i = Σ_{j > i} aⱼ` (`dg_eq`,
`testBit_dg`).
`flat` reads such an array as an `IntegerMultBounds.MathlibTM2.Layer.Arr (Fin r) N`, `N = Σ aᵢ`: the coefficient index
is the spectator and bit `q` of the address is active bit `q`.

## Rounds

The round at named position `h` involves the axes with `h < aᵢ` (`parts`), with one selected
bit per such axis: bit `h` of its coordinate, at position `off i + h` of the address (`selBits`,
and `selFin` as a `List (Fin N)`).
* `fwdRound h`: the normalized butterflies `H₀(u, v) = ((u + v)/2, (u - v)/2)` on the selected
  bits, then the record at address `x` is multiplied by `y^(-E_h(x))` modulo `y^r + 1`, with
  `E_h(x) = Σ_{i : h < aᵢ} (2r/2^(h+1)) · bitₕ(xᵢ) · (xᵢ mod 2^h)` (`twE`). This is the paper's
  `J_E` of `(combined-twiddle)` with `uᵢ = 2^(h+1)`, `bᵢ = bitₕ(xᵢ)`, `kᵢ = xᵢ mod 2^h`, and the
  vendored root `ω_t = y^(2r/t)`.
* `oppRound h`: the record at `x` is multiplied by `y^(E_h(x))`, then the same normalized
  butterflies on the selected bits.
On the flattened array the butterfly part is `IntegerMultBounds.MathlibTM2.Layer.Hl (Fin r) (selFin h)` and the
twiddle part multiplies each record by a monomial read from its address (`fwdRoundFlat`,
`oppRoundFlat`, `flat_fwdRound`, `flat_oppRound`). `fwdRounds A` runs the forward rounds at
`h = A - 1, …, 0` and `oppRounds A` the opposite rounds at `h = 0, …, A - 1`. With
`A = maxᵢ aᵢ` the first forward round and the last opposite round involve only the longest axes.

## Results

* `fwd_rounds`: `fwdRounds A z n = fwdT ts z (bitrevAddr ts n)` for `n < M`. The forward rounds
  compute `B F⁻`: entry `j` of `F⁻ z` is stored at address `B j`.
* `opp_rounds`: `oppRounds A w n = oppT ts (fun j => w (bitrevAddr ts j)) n` for `n < M`. The
  opposite rounds compute `F⁺ B⁻¹`. Both directions use the same normalized `H₀`; the `N`
  factors `1/2` of the butterflies make up exactly the `1/M` of `oppT` (and of `fwdT`).
* `fwd_rounds_flat`, `opp_rounds_flat`: the same identities for the rounds on the flattened
  arrays.
* `fwd_rounds_exact`, `opp_rounds_exact`: the vendored counterparts `fwdExact ts 1` and
  `oppExact ts 1` with the identity layout.

The proofs (`RoundsForward.lean`, `RoundsOpposite.lean`) run through closed forms of the
intermediate states, one axis step at a time; the axis steps of a round commute because the
twiddle of one axis reads only that axis's coordinate.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Rounds

open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct

/-! ### The flattened address and `Hl` -/

section Flat

open IntegerMultBounds.MathlibTM2.Layer

/-- The address whose bit `q` is `b q`. -/
def ofBits {N : ℕ} (b : Fin N → ZMod 2) : ℕ := ∑ q : Fin N, (b q).val * 2 ^ (q : ℕ)

theorem zmod2_val_le (x : ZMod 2) : x.val ≤ 1 := by have := ZMod.val_lt x; omega

theorem ofBits_succ {N : ℕ} (b : Fin (N + 1) → ZMod 2) :
    ofBits b = 2 ^ N * (b (Fin.last N)).val + ofBits (fun q : Fin N => b q.castSucc) := by
  unfold ofBits
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  ring

theorem ofBits_lt : ∀ {N : ℕ} (b : Fin N → ZMod 2), ofBits b < 2 ^ N
  | 0, b => by simp [ofBits]
  | N + 1, b => by
    rw [ofBits_succ, pow_succ]
    have h1 := ofBits_lt (fun q : Fin N => b q.castSucc)
    have h2 := zmod2_val_le (b (Fin.last N))
    have h3 : 2 ^ N * (b (Fin.last N)).val ≤ 2 ^ N := by nlinarith
    omega

theorem testBit_ofBits : ∀ {N : ℕ} (b : Fin N → ZMod 2) (j : ℕ),
    (ofBits b).testBit j = if h : j < N then decide (b ⟨j, h⟩ = 1) else false
  | 0, b, j => by simp [ofBits]
  | N + 1, b, j => by
    rw [ofBits_succ, Nat.testBit_two_pow_mul_add _ (ofBits_lt _), testBit_ofBits]
    have hv := zmod2_val_le (b (Fin.last N))
    by_cases hj : j < N
    · simp only [hj, ↓reduceIte, dite_true, show j < N + 1 by omega]
      rfl
    · simp only [hj, ↓reduceIte]
      by_cases hjN : j = N
      · subst hjN
        simp only [Nat.sub_self, show j < j + 1 by omega, dite_true]
        have hl : (⟨j, by omega⟩ : Fin (j + 1)) = Fin.last j := rfl
        rw [hl]
        rcases zmod2_cases (b (Fin.last j)) with e | e <;> rw [e] <;> decide
      · simp only [show ¬ j < N + 1 by omega, ↓reduceDIte]
        apply Nat.testBit_lt_two_pow
        calc (b (Fin.last N)).val < 2 ^ 1 := by omega
          _ ≤ 2 ^ (j - N) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem testBit_ofBits_fin {N : ℕ} (b : Fin N → ZMod 2) (q : Fin N) :
    (ofBits b).testBit q = decide (b q = 1) := by
  simp only [testBit_ofBits, q.isLt, ↓reduceDIte]

theorem ofBits_flip {N : ℕ} (q : Fin N) (b : Fin N → ZMod 2) :
    ofBits (Layer.flip q b) = ofBits b ^^^ 2 ^ (q : ℕ) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_ofBits, testBit_ofBits, Nat.testBit_two_pow]
  by_cases hj : j < N
  · simp only [hj, dite_true]
    by_cases hqj : (q : ℕ) = j
    · have e : (⟨j, hj⟩ : Fin N) = q := Fin.ext hqj.symm
      rw [e, flip_self]
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      rcases zmod2_cases (b q) with h | h <;> simp [h, hqj, h2]
    · rw [flip_other (fun e => hqj (by rw [← e]))]
      simp [hqj]
  · simp only [hj, dite_false]
    have : (q : ℕ) ≠ j := by have := q.isLt; omega
    simp [this]

/-- The flattened array of `IntegerMultBounds.MathlibTM2.Layer`: entry `(c, b)` is coefficient `c` of the record at the
address with bits `b`. -/
noncomputable def flat {r : ℕ} (N : ℕ) (u : Recs r) : Arr (Fin r) N := fun p => u (ofBits p.2) p.1

theorem flat_bfly {r N : ℕ} (q : Fin N) (u : Recs r) :
    flat N (bfly q u) = hBit q (flat N u) := by
  funext p
  obtain ⟨c, b⟩ := p
  simp only [flat, bfly, hBit, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, testBit_ofBits_fin]
  rw [ofBits_flip]
  rcases zmod2_cases (b q) with h | h <;> simp [h] <;> ring

theorem Hl_cons {X : Type} {N : ℕ} (q : Fin N) (l : List (Fin N)) (f : Arr X N) :
    Hl X (q :: l) f = hBit q (Hl X l f) := by
  simp [Hl, List.map_cons, List.prod_cons, Module.End.mul_apply]

/-- Butterflies on a list of flattened bits are `IntegerMultBounds.MathlibTM2.Layer.Hl` on that list. -/
theorem flat_bflyL {r N : ℕ} (l : List (Fin N)) (u : Recs r) :
    flat N (bflyL (l.map Fin.val) u) = Hl (Fin r) l (flat N u) := by
  induction l with
  | nil => simp [bflyL, Hl]
  | cons q l ih =>
    show flat N (bfly q (bflyL (l.map Fin.val) u)) = _
    rw [flat_bfly, ih, Hl_cons]

theorem flat_eq_of_eqBelow {r N : ℕ} {u v : Recs r} (h : EqBelow N u v) : flat N u = flat N v := by
  funext p
  simp only [flat, h _ (ofBits_lt p.2)]

/-- The selected bits of the round at named position `h` as bits of the flattened address:
bit `h` of every participating axis. -/
def selFin (es : List ℕ) (h : ℕ) : List (Fin es.sum) :=
  (selBits es h).filterMap fun q => if hq : q < es.sum then some ⟨q, hq⟩ else none

theorem map_val_filterMap {N : ℕ} : ∀ l : List ℕ, (∀ q ∈ l, q < N) →
    (l.filterMap fun q => if hq : q < N then some (⟨q, hq⟩ : Fin N) else none).map Fin.val = l
  | [], _ => rfl
  | q :: l, hl => by
    simp only [List.filterMap_cons, hl q (by simp), ↓reduceDIte]
    simp only [List.map_cons]
    rw [map_val_filterMap l fun q' hq' => hl q' (by simp [hq'])]

theorem selFin_map_val (es : List ℕ) (h : ℕ) : (selFin es h).map Fin.val = selBits es h :=
  map_val_filterMap _ fun _ hq => selBits_lt es hq

variable {r : ℕ} [NeZero r]

/-- The forward twiddle on the flattened array: the record at the address with bits `b` is
multiplied by `y^(-E_h)`, `E_h` read from the address. -/
noncomputable def twFwdFlat (es : List ℕ) (h : ℕ) (f : Arr (Fin r) es.sum) : Arr (Fin r) es.sum :=
  fun p => shiftInv (twE es r h (parts es h) (ofBits p.2)) (fun c => f (c, p.2)) p.1

/-- The opposite twiddle on the flattened array: multiplication by `y^(E_h)`. -/
noncomputable def twOppFlat (es : List ℕ) (h : ℕ) (f : Arr (Fin r) es.sum) : Arr (Fin r) es.sum :=
  fun p => shiftNegZ (twE es r h (parts es h) (ofBits p.2)) (fun c => f (c, p.2)) p.1

/-- The forward round on the flattened array: `Hl` on the selected bits, then the twiddle. -/
noncomputable def fwdRoundFlat (es : List ℕ) (h : ℕ) (f : Arr (Fin r) es.sum) :
    Arr (Fin r) es.sum :=
  twFwdFlat es h (Hl (Fin r) (selFin es h) f)

/-- The opposite round on the flattened array: the inverse twiddle, then `Hl` on the selected
bits. -/
noncomputable def oppRoundFlat (es : List ℕ) (h : ℕ) (f : Arr (Fin r) es.sum) :
    Arr (Fin r) es.sum :=
  Hl (Fin r) (selFin es h) (twOppFlat es h f)

/-- The forward rounds on the flattened array at `h = k - 1, …, 0`. -/
noncomputable def fwdRoundsFlat (es : List ℕ) : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => fwdRoundsFlat es k (fwdRoundFlat es k f)

/-- The opposite rounds on the flattened array at `h = 0, …, k - 1`. -/
noncomputable def oppRoundsFlat (es : List ℕ) : ℕ → Arr (Fin r) es.sum → Arr (Fin r) es.sum
  | 0, f => f
  | k + 1, f => oppRoundFlat es k (oppRoundsFlat es k f)

theorem flat_fwdRound (es : List ℕ) (h : ℕ) (u : Recs r) :
    flat es.sum (fwdRound es h u) = fwdRoundFlat es h (flat es.sum u) := by
  have e := flat_bflyL (selFin es h) u
  rw [selFin_map_val] at e
  unfold fwdRoundFlat
  rw [← e]
  rfl

theorem flat_oppRound (es : List ℕ) (h : ℕ) (u : Recs r) :
    flat es.sum (oppRound es h u) = oppRoundFlat es h (flat es.sum u) := by
  have e := flat_bflyL (selFin es h) (mulY (twE es r h (parts es h)) u)
  rw [selFin_map_val] at e
  unfold oppRound oppRoundFlat
  rw [e]
  rfl

theorem flat_fwdRounds (es : List ℕ) : ∀ (k : ℕ) (u : Recs r),
    flat es.sum (fwdRounds es k u) = fwdRoundsFlat es k (flat es.sum u)
  | 0, _ => rfl
  | k + 1, u => by
    rw [fwdRounds, fwdRoundsFlat, flat_fwdRounds es k, flat_fwdRound]

theorem flat_oppRounds (es : List ℕ) : ∀ (k : ℕ) (u : Recs r),
    flat es.sum (oppRounds es k u) = oppRoundsFlat es k (flat es.sum u)
  | 0, _ => rfl
  | k + 1, u => by
    rw [oppRounds, oppRoundsFlat, flat_oppRound, flat_oppRounds es k]

/-- `fwdRounds_eq` on the flattened array of `IntegerMultBounds.MathlibTM2.Layer`. -/
theorem fwdRoundsFlat_eq (es : List ℕ) (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) {A : ℕ}
    (hA : ∀ e ∈ es, e ≤ A) (z : Recs r) :
    fwdRoundsFlat es A (flat es.sum z) =
      flat es.sum (fun n => fwdT (tsOf es) z (bitrevAddr (tsOf es) n)) := by
  rw [← flat_fwdRounds]
  apply flat_eq_of_eqBelow
  intro n hn
  exact fwdRounds_eq es hr hA z (by rw [tsOf_prod]; exact hn)

/-- `oppRounds_eq` on the flattened array of `IntegerMultBounds.MathlibTM2.Layer`. -/
theorem oppRoundsFlat_eq (es : List ℕ) (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) {A : ℕ}
    (hA : ∀ e ∈ es, e ≤ A) (w : Recs r) :
    oppRoundsFlat es A (flat es.sum w) =
      flat es.sum (fun n => oppT (tsOf es) (fun j => w (bitrevAddr (tsOf es) j)) n) := by
  rw [← flat_oppRounds]
  apply flat_eq_of_eqBelow
  intro n hn
  exact oppRounds_eq es hr hA w (by rw [tsOf_prod]; exact hn)

end Flat

/-! ### Axes indexed by `Fin D` -/

section Axes

variable {r : ℕ} [NeZero r] {D : ℕ} (a : Fin D → ℕ)

theorem tsOf_ofFn : tsOf (List.ofFn a) = List.ofFn fun i => 2 ^ a i := by
  simp only [tsOf, List.map_ofFn]; rfl

theorem ax_ofFn (i : Fin D) : ax (List.ofFn a) i = a i := by
  simp [ax]

theorem mem_parts_ofFn {h i : ℕ} :
    i ∈ parts (List.ofFn a) h ↔ ∃ hi : i < D, h < a ⟨i, hi⟩ := by
  rw [mem_parts, List.length_ofFn]
  constructor
  · rintro ⟨hi, hh⟩; exact ⟨hi, by rwa [← ax_ofFn a ⟨i, hi⟩]⟩
  · rintro ⟨hi, hh⟩; exact ⟨hi, by rwa [show i = ((⟨i, hi⟩ : Fin D) : ℕ) from rfl, ax_ofFn]⟩

omit [NeZero r] in
theorem hr_ofFn (hr : ∀ i, 2 ^ a i ∣ 2 * r) : ∀ e ∈ List.ofFn a, 2 ^ e ∣ 2 * r := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact hr i

theorem le_sup_ofFn : ∀ e ∈ List.ofFn a, e ≤ Finset.univ.sup a := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact Finset.le_sup (Finset.mem_univ i)

/-- The forward rounds at `h = A - 1, …, 0`, `A = maxᵢ aᵢ`, compute `B F⁻` for the axis lengths
`tᵢ = 2^(aᵢ)`: the record at address `n` is entry `B n` of `F⁻ z`. -/
theorem fwd_rounds (hr : ∀ i, 2 ^ a i ∣ 2 * r) (z : Recs r) {n : ℕ}
    (hn : n < (List.ofFn fun i => 2 ^ a i).prod) :
    fwdRounds (List.ofFn a) (Finset.univ.sup a) z n =
      fwdT (List.ofFn fun i => 2 ^ a i) z (bitrevAddr (List.ofFn fun i => 2 ^ a i) n) := by
  rw [← tsOf_ofFn] at hn ⊢
  exact fwdRounds_eq _ (hr_ofFn a hr) (le_sup_ofFn a) z hn

/-- The opposite rounds at `h = 0, …, A - 1`, `A = maxᵢ aᵢ`, compute `F⁺ B⁻¹` with the `1/M`
normalization of `oppT`: `F⁺` of the array whose entry `j` is the record stored at `B j`. -/
theorem opp_rounds (hr : ∀ i, 2 ^ a i ∣ 2 * r) (w : Recs r) {n : ℕ}
    (hn : n < (List.ofFn fun i => 2 ^ a i).prod) :
    oppRounds (List.ofFn a) (Finset.univ.sup a) w n =
      oppT (List.ofFn fun i => 2 ^ a i)
        (fun j => w (bitrevAddr (List.ofFn fun i => 2 ^ a i) j)) n := by
  rw [← tsOf_ofFn] at hn ⊢
  exact oppRounds_eq _ (hr_ofFn a hr) (le_sup_ofFn a) w hn

/-- `fwd_rounds` on the flattened array of `IntegerMultBounds.MathlibTM2.Layer`: every forward round is `Hl` on the
selected bits followed by a recordwise twiddle. -/
theorem fwd_rounds_flat (hr : ∀ i, 2 ^ a i ∣ 2 * r) (z : Recs r) :
    fwdRoundsFlat (List.ofFn a) (Finset.univ.sup a) (flat _ z) =
      flat _ (fun n => fwdT (List.ofFn fun i => 2 ^ a i) z
        (bitrevAddr (List.ofFn fun i => 2 ^ a i) n)) := by
  rw [← tsOf_ofFn]
  exact fwdRoundsFlat_eq _ (hr_ofFn a hr) (le_sup_ofFn a) z

/-- `opp_rounds` on the flattened array of `IntegerMultBounds.MathlibTM2.Layer`: every opposite round is a recordwise
twiddle followed by `Hl` on the selected bits. -/
theorem opp_rounds_flat (hr : ∀ i, 2 ^ a i ∣ 2 * r) (w : Recs r) :
    oppRoundsFlat (List.ofFn a) (Finset.univ.sup a) (flat _ w) =
      flat _ (fun n => oppT (List.ofFn fun i => 2 ^ a i)
        (fun j => w (bitrevAddr (List.ofFn fun i => 2 ^ a i) j)) n) := by
  rw [← tsOf_ofFn]
  exact oppRoundsFlat_eq _ (hr_ofFn a hr) (le_sup_ofFn a) w

/-- `fwd_rounds` as the vendored exact counterpart `fwdExact` with the identity layout. -/
theorem fwd_rounds_exact (hr : ∀ i, 2 ^ a i ∣ 2 * r) (z : Recs r) {n : ℕ}
    (hn : n < (List.ofFn fun i => 2 ^ a i).prod) :
    fwdRounds (List.ofFn a) (Finset.univ.sup a) z n =
      fwdExact (List.ofFn fun i => 2 ^ a i) 1 z n := by
  rw [fwd_rounds a hr z hn]
  simp only [fwdExact, hn, ↓reduceDIte]
  rfl

/-- `opp_rounds` as the vendored exact counterpart `oppExact` with the identity layout. -/
theorem opp_rounds_exact (hr : ∀ i, 2 ^ a i ∣ 2 * r) (w : Recs r) {n : ℕ}
    (hn : n < (List.ofFn fun i => 2 ^ a i).prod) :
    oppRounds (List.ofFn a) (Finset.univ.sup a) w n =
      oppExact (List.ofFn fun i => 2 ^ a i) 1 w n := by
  rw [opp_rounds a hr w hn, oppExact]
  congr 1
  funext j
  have hP := powAxes_tsOf (List.ofFn a) (hr_ofFn a hr)
  rw [tsOf_ofFn] at hP
  have hb := bitrevAddr_lt hP j
  simp only [Nat.mod_eq_of_lt hb, hb, ↓reduceDIte]
  rfl

end Axes

end IntegerMultBounds.MathlibTM2.Mult.Rounds
