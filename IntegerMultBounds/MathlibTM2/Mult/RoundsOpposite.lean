module

public import IntegerMultBounds.MathlibTM2.Mult.RoundsBasic

/-!
# The opposite rounds compute `F⁺ B⁻¹`

For a depth vector `m` (`mᵢ ≤ aᵢ`: the bits of axis `i` below `mᵢ` are processed) the state
`SO es w m` at address `n` is

  `2^(-Σᵢ mᵢ) Σ_{x : ⌊xᵢ/2^(mᵢ)⌋ = ⌊nᵢ/2^(mᵢ)⌋} y^(Eₘ(n, x)) w_x`,
  `Eₘ(n, x) = Σᵢ (2r/2^(mᵢ)) (nᵢ mod 2^(mᵢ)) rev_{mᵢ}(xᵢ)`.

`SO_step`: `y^(twA es r h i)` followed by the butterfly on bit `h` of axis `i` takes depth
`mᵢ = h` to `mᵢ = h + 1`. The twiddle reads bit `h` and the low bits `nᵢ mod 2^h` of the address
before the butterfly; at that stage the low bits index the inputs of the level, as in the forward
direction. `SO_list` groups the axis steps of one round, and `SO_bot`, `SO_top` are the input and
`F⁺ B⁻¹` with the `1/M` of `oppT`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Rounds

open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct

/-! ### The opposite closed form -/

section Opposite

variable (es : List ℕ)

/-- Agreement of the unprocessed bits: `xᵢ / 2^(mᵢ) = nᵢ / 2^(mᵢ)` on every axis. -/
def AgrO (m : ℕ → ℕ) (n x : ℕ) : Prop :=
  ∀ i < es.length, dg es i x / 2 ^ m i = dg es i n / 2 ^ m i

instance (m : ℕ → ℕ) (n : ℕ) : DecidablePred (AgrO es m n) := fun x => by
  unfold AgrO; infer_instance

/-- The number of processed bits. -/
def depO (m : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range es.length, m i

/-- The exponent `Σᵢ (2r/2^(mᵢ)) · (nᵢ mod 2^(mᵢ)) · rev_{mᵢ}(xᵢ)`. -/
def ExO (r : ℕ) (m : ℕ → ℕ) (n x : ℕ) : ℕ :=
  ∑ i ∈ Finset.range es.length, 2 * r / 2 ^ m i * (dg es i n % 2 ^ m i) * bitrev (m i) (dg es i x)

variable {r : ℕ} [NeZero r]

/-- The opposite state when the bits of axis `i` below `mᵢ` are processed: the inverse partial
transforms over the low bits, read in stored order. -/
noncomputable def SO (w : Recs r) (m : ℕ → ℕ) : Recs r := fun n =>
  (1 / 2 ^ depO es m : ℂ) •
    ∑ x ∈ (Finset.range (2 ^ es.sum)).filter (AgrO es m n), shiftNegZ (ExO es r m n x) (w x)

/-- One axis step of the opposite recursion: the inverse twiddle, then the butterfly on bit `h`
of axis `i`. -/
theorem SO_step (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (w : Recs r) {m m' : ℕ → ℕ} {i h : ℕ}
    (hh : h < ax es i) (hm : m i = h) (hm' : m' i = h + 1) (hmm : ∀ j, j ≠ i → m' j = m j) :
    SO es w m' = bfly (off es i + h) (mulY (twA es r h i) (SO es w m)) := by
  funext n
  have hi : i < es.length := lt_length_of_lt_ax es hh
  have hdvd : 2 ^ ax es i ∣ 2 * r := hr _ (ax_mem es hi)
  have hdvd' : 2 ^ (h + 1) ∣ 2 * r := (pow_dvd_pow 2 (by omega)).trans hdvd
  have hw1 : 2 * r / 2 ^ (h + 1) * 2 ^ (h + 1) = 2 * r := Nat.div_mul_cancel hdvd'
  have hw2 : 2 * r / 2 ^ (h + 1) * 2 ^ h = r := by
    have e : ∀ w : ℕ, w * 2 ^ (h + 1) = w * 2 ^ h * 2 := fun w => by ring
    rw [e] at hw1; linarith
  have h2r : 2 * r / 2 ^ h = 2 * (2 * r / 2 ^ (h + 1)) := two_r_div_succ hdvd'
  have hdn' : dg es i (n ^^^ 2 ^ (off es i + h)) = dg es i n ^^^ 2 ^ h := dg_xor_self es hh n
  have hdj : ∀ j, j ≠ i → dg es j (n ^^^ 2 ^ (off es i + h)) = dg es j n :=
    fun j hj => dg_xor_ne es hh hj n
  have hb1 := bit_le_one (dg es i n) h
  have h1 : ∀ x,
      AgrO es m' n x ∧ dg es i x / 2 ^ h % 2 = dg es i n / 2 ^ h % 2 ↔ AgrO es m n x := by
    intro x
    unfold AgrO
    constructor
    · rintro ⟨hA, hbx⟩ j hj
      rcases eq_or_ne j i with rfl | hji
      · rw [hm]
        exact (div_eq_iff_succ _ _ _).mpr ⟨by simpa [hm'] using hA j hj, hbx⟩
      · rw [← hmm j hji]; exact hA j hj
    · intro hA
      have hAi := (div_eq_iff_succ _ _ _).mp (by simpa [hm] using hA i hi)
      refine ⟨fun j hj => ?_, hAi.2⟩
      rcases eq_or_ne j i with rfl | hji
      · rw [hm']; exact hAi.1
      · rw [hmm j hji]; exact hA j hj
  have h2 : ∀ x, AgrO es m' n x ∧ ¬ dg es i x / 2 ^ h % 2 = dg es i n / 2 ^ h % 2 ↔
      AgrO es m (n ^^^ 2 ^ (off es i + h)) x := by
    intro x
    have hbx := bit_le_one (dg es i x) h
    unfold AgrO
    constructor
    · rintro ⟨hA, hbx'⟩ j hj
      rcases eq_or_ne j i with rfl | hji
      · rw [hm, hdn']
        refine (div_eq_iff_succ _ _ _).mpr ⟨?_, ?_⟩
        · rw [xor_two_pow_div_succ]; simpa [hm'] using hA j hj
        · rw [xor_two_pow_bit]; omega
      · rw [← hmm j hji, hdj j hji]; exact hA j hj
    · intro hA
      have hAi := (div_eq_iff_succ _ _ _).mp (by simpa [hm, hdn'] using hA i hi)
      rw [xor_two_pow_div_succ, xor_two_pow_bit] at hAi
      refine ⟨fun j hj => ?_, by omega⟩
      rcases eq_or_ne j i with rfl | hji
      · rw [hm']; exact hAi.1
      · rw [hmm j hji, ← hdj j hji]; exact hA j hj
  -- the exponent of the processed state against that of either input class
  have hE : ∀ n₀ x, (∀ j, j ≠ i → dg es j n₀ = dg es j n) → dg es i n₀ % 2 ^ h = dg es i n % 2 ^ h →
      dg es i n₀ / 2 ^ h % 2 = dg es i x / 2 ^ h % 2 →
      ExO es r m' n x = ExO es r m n₀ x + (twA es r h i n₀ +
        dg es i n / 2 ^ h % 2 * (dg es i x / 2 ^ h % 2) * r +
          2 * r * (dg es i n / 2 ^ h % 2 * bitrev h (dg es i x))) := by
    intro n₀ x hj0 hl0 hb0
    unfold ExO
    apply sum_eq_add_of_ne (Finset.mem_range.mpr hi)
    · intro j _ hji; rw [hmm j hji, hj0 j hji]
    · rw [hm', hm, bitrev_succ, Nat.mod_pow_succ, h2r, hl0]
      unfold twA
      rw [hl0, hb0]
      exact twiddle_decomp_opp hw2
  have hdep : depO es m' = depO es m + 1 := by
    unfold depO
    apply sum_eq_add_of_ne (Finset.mem_range.mpr hi)
    · intro j _ hji; rw [hmm j hji]
    · rw [hm', hm]
  set sg : ℂ := if n.testBit (off es i + h) then -1 else 1 with hsg
  have hsg' : sg = if dg es i n / 2 ^ h % 2 = 1 then -1 else 1 := by
    rw [hsg, testBit_off es n hh]; simp
  have hs1 : ∀ x ∈ (Finset.range (2 ^ es.sum)).filter (AgrO es m n),
      shiftNegZ (ExO es r m' n x) (w x) =
        shiftNegZ (twA es r h i n) (sg • shiftNegZ (ExO es r m n x) (w x)) := by
    intro x hx
    have hA := (h1 x).mpr (Finset.mem_filter.mp hx).2
    rw [hE n x (fun _ _ => rfl) rfl hA.2.symm, hA.2,
      show ∀ a b c d : ℕ, a + (b + c + d) = (b + (c + a)) + d by intros; ring,
      shiftNegZ_add_two_r_mul, ← shiftNegZ_add, ← shiftNegZ_add,
      show dg es i n / 2 ^ h % 2 * (dg es i n / 2 ^ h % 2) = dg es i n / 2 ^ h % 2 by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with e | e <;> rw [e],
      shiftNegZ_bit_r hb1, hsg']
  have hs2 : ∀ x ∈ (Finset.range (2 ^ es.sum)).filter (AgrO es m (n ^^^ 2 ^ (off es i + h))),
      shiftNegZ (ExO es r m' n x) (w x) =
        shiftNegZ (twA es r h i (n ^^^ 2 ^ (off es i + h)))
          (shiftNegZ (ExO es r m (n ^^^ 2 ^ (off es i + h)) x) (w x)) := by
    intro x hx
    have hA := (h2 x).mpr (Finset.mem_filter.mp hx).2
    have hbx := bit_le_one (dg es i x) h
    have hAi : dg es i x / 2 ^ h = (dg es i n ^^^ 2 ^ h) / 2 ^ h := by
      have := (Finset.mem_filter.mp hx).2 i hi; rwa [hm, hdn'] at this
    have hz : dg es i n / 2 ^ h % 2 * (dg es i x / 2 ^ h % 2) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with e | e <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbx with e' | e' <;> simp_all
    rw [hE (n ^^^ 2 ^ (off es i + h)) x (fun j hj => hdj j hj) (by rw [hdn', xor_two_pow_mod])
      (by rw [hdn', hAi]), hz,
      show ∀ a b d : ℕ, a + (b + 0 * r + d) = (b + a) + d by intros; ring,
      shiftNegZ_add_two_r_mul, ← shiftNegZ_add]
  simp only [SO, mulY, bfly]
  rw [hdep, sum_filter_split _ _ _ _ _ h1 h2, Finset.sum_congr rfl hs1, Finset.sum_congr rfl hs2,
    ← shiftNegZ_sum, ← shiftNegZ_sum, ← Finset.smul_sum, ← hsg]
  simp only [shiftNegZ_smul, smul_add, smul_smul]
  congr 2 <;> ring

/-- The axis steps of one opposite round, grouped: the combined inverse twiddle, then the
butterflies on the axes `l`. -/
theorem SO_list (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (w : Recs r) (h : ℕ) :
    ∀ (l : List ℕ) (m : ℕ → ℕ), l.Nodup → (∀ i ∈ l, h < ax es i ∧ m i = h) →
      SO es w (fun j => if j ∈ l then h + 1 else m j) =
        bflyL (l.map fun i => off es i + h) (mulY (twE es r h l) (SO es w m))
  | [], m, _, _ => by
    funext n
    simp [twE, bflyL, mulY, shiftNegZ_zero]
  | i :: l, m, hnd, hl => by
    rw [List.nodup_cons] at hnd
    have ih := SO_list hr w h l m hnd.2 (fun j hj => hl j (by simp [hj]))
    have hi := hl i (by simp)
    have step := SO_step es hr w (m := fun j => if j ∈ l then h + 1 else m j)
      (m' := fun j => if j ∈ i :: l then h + 1 else m j) hi.1 (by simp [hnd.1, hi.2]) (by simp)
      (by intro j hj; simp [hj])
    have hinv : ∀ q ∈ l.map (fun i => off es i + h), ∀ n,
        twA es r h i (n ^^^ 2 ^ q) = twA es r h i n := by
      intro q hq n
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact twA_xor_ne es (hl j (by simp [hj])).1 (fun e => hnd.1 (by rw [e]; exact hj)) n
    rw [step, ih, mulY_bflyL hinv]
    show bfly _ (bflyL _ _) = bfly _ (bflyL _ _)
    congr 2
    funext n
    simp only [mulY, twE, List.map_cons, List.sum_cons, shiftNegZ_add]

/-- The opposite round at `h` takes the depths `min aᵢ h` to `min aᵢ (h + 1)`. -/
theorem oppRound_SO (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (w : Recs r) (h : ℕ) :
    oppRound es h (SO es w fun j => min (ax es j) h) = SO es w fun j => min (ax es j) (h + 1) := by
  have hl := SO_list es hr w h (parts es h) (fun j => min (ax es j) h) (parts_nodup es h)
    (by intro i hi; rw [mem_parts] at hi; omega)
  have e : (fun j => if j ∈ parts es h then h + 1 else min (ax es j) h) =
      fun j => min (ax es j) (h + 1) := by
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

/-- The opposite rounds at `h = 0, …, k - 1` take the depths `0` to `min aᵢ k`. -/
theorem oppRounds_SO (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (w : Recs r) :
    ∀ k, oppRounds es k (SO es w fun _ => 0) = SO es w fun j => min (ax es j) k
  | 0 => by simp [oppRounds]
  | k + 1 => by
    rw [oppRounds, oppRounds_SO hr w k, oppRound_SO es hr w k]

/-- No bit processed: the input. -/
theorem SO_bot (w : Recs r) {n : ℕ} (hn : n < 2 ^ es.sum) : SO es w (fun _ => 0) n = w n := by
  have hpos : ∀ t ∈ tsOf es, 0 < t := by
    intro t ht; obtain ⟨e, -, rfl⟩ := List.mem_map.mp ht; positivity
  have hfil : (Finset.range (2 ^ es.sum)).filter (AgrO es (fun _ => 0) n) = {n} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hA⟩
      rw [← tsOf_prod] at hk hn
      apply digits_eq hpos hk hn
      intro i hi
      rw [tsOf_length] at hi
      simpa [dg] using hA i hi
    · rintro rfl; exact ⟨hn, fun _ _ => rfl⟩
  have hdep : depO es (fun _ => 0) = 0 := by simp [depO]
  have hE : ExO es r (fun _ => 0) n n = 0 := by simp [ExO, bitrev_zero]
  simp only [SO, hfil, hdep, hE, Finset.sum_singleton, shiftNegZ_zero, pow_zero, div_one, one_smul]

/-- All bits processed: `F⁺ B⁻¹`. -/
theorem SO_top (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) (w : Recs r) (n : ℕ) :
    SO es w (ax es) n = oppT (tsOf es) (fun j => w (bitrevAddr (tsOf es) j)) n := by
  have hP := powAxes_tsOf es hr
  have hfil : (Finset.range (2 ^ es.sum)).filter (AgrO es (ax es) n) =
      Finset.range (2 ^ es.sum) :=
    Finset.filter_true_of_mem fun k _ i _ => by
      rw [Nat.div_eq_of_lt (dg_lt es i k), Nat.div_eq_of_lt (dg_lt es i n)]
  have hdep : depO es (ax es) = es.sum := by simp [depO, sum_range_getD]
  have hE : ∀ x, ExO es r (ax es) n x =
      synthExpL r (tsOf es) n (bitrevAddr (tsOf es) x) := by
    intro x
    unfold ExO synthExpL
    rw [list_sum_range, tsOf_length]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [tsOf_getD, digit_bitrevAddr hP x (by rw [tsOf_length]; exact hi), tsOf_getD,
      Nat.log_pow (by norm_num), Nat.mod_eq_of_lt (dg_lt es i n)]
    simp [dg]
  simp only [SO, oppT, hfil, hdep, tsOf_prod]
  push_cast
  congr 1
  rw [← tsOf_prod]
  apply Finset.sum_nbij' (bitrevAddr (tsOf es)) (bitrevAddr (tsOf es))
  · intro x _; exact Finset.mem_range.mpr (bitrevAddr_lt hP x)
  · intro x _; exact Finset.mem_range.mpr (bitrevAddr_lt hP x)
  · intro x hx; exact bitrevAddr_bitrevAddr hP (Finset.mem_range.mp hx)
  · intro x hx; exact bitrevAddr_bitrevAddr hP (Finset.mem_range.mp hx)
  · intro x hx
    rw [hE, bitrevAddr_bitrevAddr hP (Finset.mem_range.mp hx)]

end Opposite

/-- The opposite rounds at `h = 0, …, A - 1` compute `F⁺ B⁻¹`: `F⁺` of the array whose entry `j`
is the record stored at `B j`, with the `1/M` normalization of `oppT`. -/
theorem oppRounds_eq {r : ℕ} [NeZero r] (es : List ℕ) (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) {A : ℕ}
    (hA : ∀ e ∈ es, e ≤ A) (w : Recs r) {n : ℕ} (hn : n < (tsOf es).prod) :
    oppRounds es A w n = oppT (tsOf es) (fun j => w (bitrevAddr (tsOf es) j)) n := by
  rw [tsOf_prod] at hn
  have hm : (fun j => min (ax es j) A) = ax es := by
    funext j
    by_cases hj : j < es.length
    · have := hA _ (ax_mem es hj); omega
    · have : ax es j = 0 := List.getD_eq_default _ _ (by omega)
      rw [this]; simp
  have hloc : EqBelow es.sum w (SO es w fun _ => 0) := fun n hn => (SO_bot es w hn).symm
  rw [oppRounds_eqBelow es hloc A n hn, oppRounds_SO es hr w A, hm, SO_top es hr]

end IntegerMultBounds.MathlibTM2.Mult.Rounds
