module

public import IntegerMultBounds.MathlibTM2.Mult.RoundsBasic
import Mathlib.Data.List.GetD

/-!
# The forward rounds compute `B F⁻`

For a depth vector `m` (`mᵢ ≤ aᵢ`: the bits of axis `i` from `mᵢ` up are processed) the state
`SF es z m` at address `n` is

  `2^(-Σᵢ (aᵢ - mᵢ)) Σ_{k : kᵢ ≡ nᵢ (mod 2^(mᵢ))} y^(-Eₘ(n, k)) z_k`,
  `Eₘ(n, k) = Σᵢ (2r/2^(aᵢ)) rev_{aᵢ-mᵢ}(⌊nᵢ/2^(mᵢ)⌋) kᵢ`.

`SF_step`: the butterfly on bit `h` of axis `i` followed by `y^(-twA es r h i)` takes depth
`mᵢ = h + 1` to `mᵢ = h`. Bit `h` of `nᵢ`, `bₕ`, becomes frequency bit `aᵢ - 1 - h`, which adds
`(2r/2^(h+1)) bₕ kᵢ` to the exponent; modulo `2r` this is `bₕ bitₕ(kᵢ) r`, the butterfly sign,
plus `(2r/2^(h+1)) bₕ (nᵢ mod 2^h)`, the twiddle. `SF_list` groups the axis steps of one round,
`fwdRound_SF` identifies the round, and `SF_top`, `SF_bot` are the input and `F⁻` in stored order.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Rounds

open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct

/-! ### The forward closed form -/

section Forward

variable (es : List ℕ)

/-- Agreement of the unprocessed bits: `kᵢ ≡ nᵢ (mod 2^(mᵢ))` on every axis. -/
def AgrF (m : ℕ → ℕ) (n k : ℕ) : Prop :=
  ∀ i < es.length, dg es i k % 2 ^ m i = dg es i n % 2 ^ m i

instance (m : ℕ → ℕ) (n : ℕ) : DecidablePred (AgrF es m n) := fun k => by
  unfold AgrF; infer_instance

/-- The number of processed bits. -/
def depF (m : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range es.length, (ax es i - m i)

/-- The exponent `Σᵢ (2r/2^(aᵢ)) · rev_{aᵢ-mᵢ}(nᵢ / 2^(mᵢ)) · kᵢ`. -/
def ExF (r : ℕ) (m : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range es.length,
    2 * r / 2 ^ ax es i * bitrev (ax es i - m i) (dg es i n / 2 ^ m i) * dg es i k

variable {r : ℕ} [NeZero r]

/-- The forward state when the bits of axis `i` from `mᵢ` up are processed: the partial
transform over the processed bits, written in stored order. -/
noncomputable def SF (z : Recs r) (m : ℕ → ℕ) : Recs r := fun n =>
  (1 / 2 ^ depF es m : ℂ) •
    ∑ k ∈ (Finset.range (2 ^ es.sum)).filter (AgrF es m n), shiftInv (ExF es r m n k) (z k)

/-- One axis step of the forward recursion: butterfly on bit `h` of axis `i`, then the twiddle. -/
theorem SF_step (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (z : Recs r) {m m' : ℕ → ℕ} {i h : ℕ}
    (hh : h < ax es i) (hm : m i = h + 1) (hm' : m' i = h) (hmm : ∀ j, j ≠ i → m' j = m j) :
    SF es z m' = mulYInv (twA es r h i) (bfly (off es i + h) (SF es z m)) := by
  funext n
  have hi : i < es.length := lt_length_of_lt_ax es hh
  have hdvd : 2 ^ ax es i ∣ 2 * r := hr _ (ax_mem es hi)
  have hdvd' : 2 ^ (h + 1) ∣ 2 * r := (pow_dvd_pow 2 (by omega)).trans hdvd
  have hw1 : 2 * r / 2 ^ (h + 1) * 2 ^ (h + 1) = 2 * r := Nat.div_mul_cancel hdvd'
  have hw2 : 2 * r / 2 ^ (h + 1) * 2 ^ h = r := by
    have e : ∀ w : ℕ, w * 2 ^ (h + 1) = w * 2 ^ h * 2 := fun w => by ring
    rw [e] at hw1; linarith
  have hcw : 2 * r / 2 ^ ax es i * 2 ^ (ax es i - (h + 1)) = 2 * r / 2 ^ (h + 1) := by
    have e : 2 * r = 2 * r / 2 ^ ax es i * 2 ^ (ax es i - (h + 1)) * 2 ^ (h + 1) := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), Nat.div_mul_cancel hdvd]
    conv_rhs => rw [e]
    rw [Nat.mul_div_cancel _ (by positivity)]
  have hdn' : dg es i (n ^^^ 2 ^ (off es i + h)) = dg es i n ^^^ 2 ^ h := dg_xor_self es hh n
  have hdj : ∀ j, j ≠ i → dg es j (n ^^^ 2 ^ (off es i + h)) = dg es j n :=
    fun j hj => dg_xor_ne es hh hj n
  have hb1 := bit_le_one (dg es i n) h
  -- splitting the class of `n` at depth `m'` into the classes of `n` and `n'` at depth `m`
  have h1 : ∀ k,
      AgrF es m' n k ∧ dg es i k / 2 ^ h % 2 = dg es i n / 2 ^ h % 2 ↔ AgrF es m n k := by
    intro k
    unfold AgrF
    constructor
    · rintro ⟨hA, hbk⟩ j hj
      rcases eq_or_ne j i with rfl | hji
      · rw [hm]
        exact (mod_succ_eq_iff _ _ _).mpr ⟨by simpa [hm'] using hA j hj, hbk⟩
      · rw [← hmm j hji]; exact hA j hj
    · intro hA
      have hAi := (mod_succ_eq_iff _ _ _).mp (by simpa [hm] using hA i hi)
      refine ⟨fun j hj => ?_, hAi.2⟩
      rcases eq_or_ne j i with rfl | hji
      · rw [hm']; exact hAi.1
      · rw [hmm j hji]; exact hA j hj
  have h2 : ∀ k, AgrF es m' n k ∧ ¬ dg es i k / 2 ^ h % 2 = dg es i n / 2 ^ h % 2 ↔
      AgrF es m (n ^^^ 2 ^ (off es i + h)) k := by
    intro k
    have hbk := bit_le_one (dg es i k) h
    unfold AgrF
    constructor
    · rintro ⟨hA, hbk'⟩ j hj
      rcases eq_or_ne j i with rfl | hji
      · rw [hm, hdn']
        refine (mod_succ_eq_iff _ _ _).mpr ⟨?_, ?_⟩
        · rw [xor_two_pow_mod]; simpa [hm'] using hA j hj
        · rw [xor_two_pow_bit]; omega
      · rw [← hmm j hji, hdj j hji]; exact hA j hj
    · intro hA
      have hAi := (mod_succ_eq_iff _ _ _).mp (by simpa [hm, hdn'] using hA i hi)
      rw [xor_two_pow_mod, xor_two_pow_bit] at hAi
      refine ⟨fun j hj => ?_, by omega⟩
      rcases eq_or_ne j i with rfl | hji
      · rw [hm']; exact hAi.1
      · rw [hmm j hji, ← hdj j hji]; exact hA j hj
  -- the exponents
  have hE' : ∀ k, ExF es r m (n ^^^ 2 ^ (off es i + h)) k = ExF es r m n k := by
    intro k
    unfold ExF
    apply Finset.sum_congr rfl
    intro j _
    rcases eq_or_ne j i with rfl | hji
    · rw [hm, hdn', xor_two_pow_div_succ]
    · rw [hdj j hji]
  have hE : ∀ k, ExF es r m' n k =
      ExF es r m n k + dg es i n / 2 ^ h % 2 * (2 * r / 2 ^ (h + 1)) * dg es i k := by
    intro k
    unfold ExF
    apply sum_eq_add_of_ne (Finset.mem_range.mpr hi)
    · intro j _ hji; rw [hmm j hji]
    · rw [hm', hm, show ax es i - h = (ax es i - (h + 1)) + 1 by omega, bitrev_succ',
        Nat.div_div_eq_div_mul, ← pow_succ, ← hcw]
      ring
  have hdec : ∀ k, dg es i k % 2 ^ h = dg es i n % 2 ^ h →
      dg es i n / 2 ^ h % 2 * (2 * r / 2 ^ (h + 1)) * dg es i k =
        twA es r h i n + dg es i n / 2 ^ h % 2 * (dg es i k / 2 ^ h % 2) * r +
          2 * r * (dg es i n / 2 ^ h % 2 * (dg es i k / 2 ^ (h + 1))) := by
    intro k hk
    have e1 := Nat.mod_add_div (dg es i k) (2 ^ (h + 1))
    rw [Nat.mod_pow_succ, hk] at e1
    unfold twA
    exact twiddle_decomp_fwd e1 hw1 hw2
  have hdep : depF es m' = depF es m + 1 := by
    unfold depF
    apply sum_eq_add_of_ne (Finset.mem_range.mpr hi)
    · intro j _ hji; rw [hmm j hji]
    · rw [hm', hm]; omega
  set sg : ℂ := if n.testBit (off es i + h) then -1 else 1 with hsg
  have hsg' : sg = if dg es i n / 2 ^ h % 2 = 1 then -1 else 1 := by
    rw [hsg, testBit_off es n hh]; simp
  have hs1 : ∀ k ∈ (Finset.range (2 ^ es.sum)).filter (AgrF es m n),
      shiftInv (ExF es r m' n k) (z k) =
        shiftInv (twA es r h i n) (sg • shiftInv (ExF es r m n k) (z k)) := by
    intro k hk
    have hA := (h1 k).mpr (Finset.mem_filter.mp hk).2
    rw [hE, hdec k (by simpa [hm'] using hA.1 i hi), hA.2,
      show ∀ a b c d : ℕ, a + (b + c + d) = (b + (c + a)) + d by intros; ring,
      shiftInv_add_two_r_mul, shiftInv_add, shiftInv_add,
      show dg es i n / 2 ^ h % 2 * (dg es i n / 2 ^ h % 2) = dg es i n / 2 ^ h % 2 by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with e | e <;> rw [e],
      shiftInv_bit_r hb1, hsg']
  have hs2 : ∀ k ∈ (Finset.range (2 ^ es.sum)).filter (AgrF es m (n ^^^ 2 ^ (off es i + h))),
      shiftInv (ExF es r m' n k) (z k) =
        shiftInv (twA es r h i n) (shiftInv (ExF es r m (n ^^^ 2 ^ (off es i + h)) k) (z k)) := by
    intro k hk
    have hA := (h2 k).mpr (Finset.mem_filter.mp hk).2
    have hbk := bit_le_one (dg es i k) h
    have hz : dg es i n / 2 ^ h % 2 * (dg es i k / 2 ^ h % 2) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with e | e <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbk with e' | e' <;> simp_all
    rw [hE, hdec k (by simpa [hm'] using hA.1 i hi), hz, hE',
      show ∀ a b d : ℕ, a + (b + 0 * r + d) = (b + a) + d by intros; ring,
      shiftInv_add_two_r_mul, shiftInv_add]
  simp only [SF, mulYInv, bfly]
  rw [hdep, sum_filter_split _ _ _ _ _ h1 h2, Finset.sum_congr rfl hs1, Finset.sum_congr rfl hs2,
    ← shiftInv_sum, ← shiftInv_sum, ← Finset.smul_sum, ← hsg]
  simp only [shiftInv_smul, shiftInv_add_vec, smul_add, smul_smul]
  congr 2 <;> ring

/-- The axis steps of one forward round, grouped: the butterflies on the axes `l`, then the
combined twiddle. -/
theorem SF_list (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (z : Recs r) (h : ℕ) :
    ∀ (l : List ℕ) (m : ℕ → ℕ), l.Nodup → (∀ i ∈ l, h < ax es i ∧ m i = h + 1) →
      SF es z (fun j => if j ∈ l then h else m j) =
        mulYInv (twE es r h l) (bflyL (l.map fun i => off es i + h) (SF es z m))
  | [], m, _, _ => by
    funext n
    simp [twE, bflyL, mulYInv, shiftInv_zero]
  | i :: l, m, hnd, hl => by
    rw [List.nodup_cons] at hnd
    have ih := SF_list hr z h l m hnd.2 (fun j hj => hl j (by simp [hj]))
    have hi := hl i (by simp)
    have step := SF_step es hr z (m := fun j => if j ∈ l then h else m j)
      (m' := fun j => if j ∈ i :: l then h else m j) hi.1 (by simp [hnd.1, hi.2]) (by simp)
      (by intro j hj; simp [hj])
    rw [step, ih, ← mulYInv_bfly (fun n => twE_xor_ne es hi.1 hnd.1 n)]
    funext n
    simp only [mulYInv, twE, List.map_cons, List.sum_cons, shiftInv_add]
    rfl

/-- The forward round at `h` takes the depths `min aᵢ (h + 1)` to `min aᵢ h`. -/
theorem fwdRound_SF (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (z : Recs r) (h : ℕ) :
    fwdRound es h (SF es z fun j => min (ax es j) (h + 1)) = SF es z fun j => min (ax es j) h := by
  have hl := SF_list es hr z h (parts es h) (fun j => min (ax es j) (h + 1)) (parts_nodup es h)
    (by intro i hi; rw [mem_parts] at hi; omega)
  have e : (fun j => if j ∈ parts es h then h else min (ax es j) (h + 1)) =
      fun j => min (ax es j) h := by
    funext j
    by_cases hj : j ∈ parts es h
    · simp only [hj, ↓reduceIte]; rw [mem_parts] at hj; omega
    · simp only [hj, ↓reduceIte]
      have : ax es j ≤ h := by
        by_contra hc
        exact hj ((mem_parts es).mpr ⟨lt_length_of_lt_ax es (h := h) (by omega), by omega⟩)
      omega
  rw [e] at hl
  rw [hl]
  rfl

/-- The forward rounds at `h = k - 1, …, 0` take the depths `min aᵢ k` to `0`. -/
theorem fwdRounds_SF (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (z : Recs r) :
    ∀ k, fwdRounds es k (SF es z fun j => min (ax es j) k) = SF es z fun _ => 0
  | 0 => by simp [fwdRounds]
  | k + 1 => by
    rw [fwdRounds, fwdRound_SF es hr z k, fwdRounds_SF hr z k]

/-- No bit processed: the input. -/
theorem SF_top (z : Recs r) {n : ℕ} (hn : n < 2 ^ es.sum) : SF es z (ax es) n = z n := by
  have hpos : ∀ t ∈ tsOf es, 0 < t := by
    intro t ht; obtain ⟨e, -, rfl⟩ := List.mem_map.mp ht; positivity
  have hfil : (Finset.range (2 ^ es.sum)).filter (AgrF es (ax es) n) = {n} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hA⟩
      rw [← tsOf_prod] at hk hn
      apply digits_eq hpos hk hn
      intro i hi
      rw [tsOf_length] at hi
      have := hA i hi
      rwa [Nat.mod_eq_of_lt (dg_lt es i k), Nat.mod_eq_of_lt (dg_lt es i n)] at this
    · rintro rfl; exact ⟨hn, fun _ _ => rfl⟩
  have hdep : depF es (ax es) = 0 := by simp [depF]
  have hE : ExF es r (ax es) n n = 0 := by simp [ExF, bitrev_zero]
  simp only [SF, hfil, hdep, hE, Finset.sum_singleton, shiftInv_zero, pow_zero, div_one, one_smul]

/-- All bits processed: `F⁻` in stored order. -/
theorem SF_bot (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (z : Recs r) (n : ℕ) :
    SF es z (fun _ => 0) n = fwdT (tsOf es) z (bitrevAddr (tsOf es) n) := by
  have hP := powAxes_tsOf es hr
  have hfil : (Finset.range (2 ^ es.sum)).filter (AgrF es (fun _ => 0) n) =
      Finset.range (2 ^ es.sum) :=
    Finset.filter_true_of_mem fun k _ i _ => by simp only [pow_zero, Nat.mod_one]
  have hdep : depF es (fun _ => 0) = es.sum := by simp [depF, sum_range_getD]
  have hE : ∀ k, ExF es r (fun _ => 0) n k = synthExpL r (tsOf es) (bitrevAddr (tsOf es) n) k := by
    intro k
    unfold ExF synthExpL
    rw [list_sum_range, tsOf_length]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [tsOf_getD, digit_bitrevAddr hP n (by rw [tsOf_length]; exact hi), tsOf_getD,
      Nat.log_pow (by norm_num)]
    simp [dg]
  simp only [SF, fwdT, hfil, hdep, hE, tsOf_prod]
  push_cast
  rfl

end Forward

/-- The forward rounds at `h = A - 1, …, 0` compute `B F⁻`: the record at address `n` is entry
`B n` of `F⁻ z`. -/
theorem fwdRounds_eq {r : ℕ} [NeZero r] (es : List ℕ) (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) {A : ℕ}
    (hA : ∀ e ∈ es, e ≤ A) (z : Recs r) {n : ℕ} (hn : n < (tsOf es).prod) :
    fwdRounds es A z n = fwdT (tsOf es) z (bitrevAddr (tsOf es) n) := by
  rw [tsOf_prod] at hn
  have hm : (fun j => min (ax es j) A) = ax es := by
    funext j
    by_cases hj : j < es.length
    · have := hA _ (ax_mem es hj); omega
    · have : ax es j = 0 := List.getD_eq_default _ _ (by omega)
      rw [this]; simp
  have hloc : EqBelow es.sum z (SF es z (ax es)) := fun n hn => (SF_top es z hn).symm
  rw [fwdRounds_eqBelow es hloc A n hn, ← hm, fwdRounds_SF es hr z A, SF_bot es hr]

end IntegerMultBounds.MathlibTM2.Mult.Rounds
