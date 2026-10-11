module

public import IntegerMultBounds.Schoenhage.Dif

/-! The in-place rounds on several axes. An axis of length `2^a` whose
address bits sit above `o` lower bits has its rounds at bits `o + a - 1, …, o`
(`difAllAt`), each pairing on its bit and twisting by the axis bits below it.
On a slice through the other axes these are the one-axis rounds
(`difAllAt_slice`). Running every axis in turn, first axis first, computes the
normalized transform over all axes with every axis address bit-reversed
(`difAxes_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ} [NeZero r]

/-- A round of the axis whose bits start at `o`, at its slot `h`. -/
noncomputable def difRoundAt (o h : ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ := fun x =>
  if bitAt x (o + h) = 0 then (1 / 2 : ℂ) • (z x + z (x + 2 ^ (o + h)))
  else shiftInv (2 * r / 2 ^ (h + 1) * (x / 2 ^ o % 2 ^ h)) ((1 / 2 : ℂ) • (z (x - 2 ^ (o + h)) - z x))

/-- The axis's rounds from its top slot down. -/
noncomputable def difAllAt (o : ℕ) : ℕ → (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ
  | 0, z => z
  | a + 1, z => difAllAt o a (difRoundAt o a z)

/-! ### Slices -/

theorem div_slice (o a hi k lo : ℕ) (hlo : lo < 2 ^ o) :
    (hi * 2 ^ (o + a) + k * 2 ^ o + lo) / 2 ^ o = hi * 2 ^ a + k := by
  rw [show hi * 2 ^ (o + a) + k * 2 ^ o + lo = lo + 2 ^ o * (hi * 2 ^ a + k) by ring,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]

theorem bitAt_slice {o a h hi k lo : ℕ} (hlo : lo < 2 ^ o) (hh : h < a) :
    bitAt (hi * 2 ^ (o + a) + k * 2 ^ o + lo) (o + h) = bitAt k h := by
  unfold bitAt
  rw [show (2 : ℕ) ^ (o + h) = 2 ^ o * 2 ^ h from pow_add 2 o h, ← Nat.div_div_eq_div_mul,
    div_slice o a hi k lo hlo, Nat.add_comm]
  have := bitAt_add_mul (x := k) (h := h) (m := hi * 2 ^ a)
    (Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _)
  exact this

theorem mod_slice {o a h hi k lo : ℕ} (hlo : lo < 2 ^ o) (hh : h < a) :
    (hi * 2 ^ (o + a) + k * 2 ^ o + lo) / 2 ^ o % 2 ^ h = k % 2 ^ h := by
  rw [div_slice o a hi k lo hlo, Nat.add_comm]
  exact mod_add_mul (Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _)

theorem difRoundAt_slice {o a h hi lo : ℕ} (hlo : lo < 2 ^ o) (hh : h < a) (z : ℕ → Fin r → ℂ) (k : ℕ) :
    difRoundAt o h z (hi * 2 ^ (o + a) + k * 2 ^ o + lo) =
      difRound h (fun k' => z (hi * 2 ^ (o + a) + k' * 2 ^ o + lo)) k := by
  unfold difRoundAt difRound
  rw [bitAt_slice hlo hh, mod_slice hlo hh]
  split_ifs with hb
  · congr 3
    rw [pow_add]; ring
  · have := le_of_bitAt hb
    obtain ⟨k', rfl⟩ : ∃ k', k = 2 ^ h + k' := ⟨k - 2 ^ h, by omega⟩
    show shiftInv _ ((1 / 2 : ℂ) • (z _ - z _)) = shiftInv _ ((1 / 2 : ℂ) • (z _ - z _))
    rw [Nat.add_sub_cancel_left,
      show hi * 2 ^ (o + a) + (2 ^ h + k') * 2 ^ o + lo = (hi * 2 ^ (o + a) + k' * 2 ^ o + lo) + 2 ^ (o + h) by
        rw [pow_add]; ring, Nat.add_sub_cancel]

theorem difAllAt_slice {o a hi lo : ℕ} (hlo : lo < 2 ^ o) :
    ∀ b, b ≤ a → ∀ (z : ℕ → Fin r → ℂ) (k : ℕ),
      difAllAt o b z (hi * 2 ^ (o + a) + k * 2 ^ o + lo) =
        difAll b (fun k' => z (hi * 2 ^ (o + a) + k' * 2 ^ o + lo)) k
  | 0, _, z, k => rfl
  | b + 1, hb, z, k => by
    simp only [difAllAt, difAll]
    rw [difAllAt_slice hlo b (by omega) _ k]
    congr 1
    funext k'
    exact difRoundAt_slice hlo (by omega) z k'

/-! ### Shifts by whole blocks -/

theorem difRoundAt_shift (o h m : ℕ) (hm : 2 ^ (o + h + 1) ∣ m) (z : ℕ → Fin r → ℂ) (y : ℕ) :
    difRoundAt o h (fun x => z (x + m)) y = difRoundAt o h z (y + m) := by
  unfold difRoundAt
  dsimp only
  have hb : bitAt (y + m) (o + h) = bitAt y (o + h) := bitAt_add_mul hm
  obtain ⟨c, rfl⟩ := hm
  have hd : (y + 2 ^ (o + h + 1) * c) / 2 ^ o % 2 ^ h = y / 2 ^ o % 2 ^ h := by
    rw [show 2 ^ (o + h + 1) * c = 2 ^ o * (2 ^ (h + 1) * c) by ring, Nat.add_mul_div_left _ _ (by positivity)]
    exact mod_add_mul (dvd_mul_right _ _)
  rw [hb, hd]
  split_ifs with h0
  · rw [show y + 2 ^ (o + h) + 2 ^ (o + h + 1) * c = y + 2 ^ (o + h + 1) * c + 2 ^ (o + h) by ring]
  · have := le_of_bitAt h0
    rw [show y - 2 ^ (o + h) + 2 ^ (o + h + 1) * c = y + 2 ^ (o + h + 1) * c - 2 ^ (o + h) by omega]

theorem difAllAt_shift (o : ℕ) : ∀ (a m : ℕ), 2 ^ (o + a) ∣ m → ∀ (z : ℕ → Fin r → ℂ) (y : ℕ),
    difAllAt o a (fun x => z (x + m)) y = difAllAt o a z (y + m)
  | 0, m, _, z, y => rfl
  | a + 1, m, hm, z, y => by
    simp only [difAllAt]
    have e : difRoundAt o a (fun x => z (x + m)) = fun x => difRoundAt o a z (x + m) :=
      funext fun x => difRoundAt_shift o a m (by rwa [← Nat.add_assoc] at hm) z x
    rw [e]
    exact difAllAt_shift o a m (dvd_trans (pow_dvd_pow 2 (by omega)) hm) _ y

/-! ### All axes -/

/-- The rounds of every axis, first axis first. -/
noncomputable def difAxes : List ℕ → (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ
  | [], z => z
  | t :: ts, z => difAxes ts (difAllAt (Nat.log 2 ts.prod) (Nat.log 2 t) z)

omit [NeZero r] in
theorem powAxes_cons {t : ℕ} {ts : List ℕ} (h : PowAxes r (t :: ts)) : PowAxes r ts :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

omit [NeZero r] in
theorem powAxes_prod_pow {ts : List ℕ} (h : PowAxes r ts) : ts.prod = 2 ^ Nat.log 2 ts.prod := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨a, rfl, -⟩ := h t (by simp)
    rw [List.prod_cons, ih (powAxes_cons h), ← pow_add, Nat.log_pow (by norm_num)]

theorem difAxes_shift : ∀ (ts : List ℕ), PowAxes r ts → ∀ (m : ℕ), ts.prod ∣ m →
    ∀ (z : ℕ → Fin r → ℂ) (y : ℕ), difAxes ts (fun x => z (x + m)) y = difAxes ts z (y + m)
  | [], _, m, _, z, y => rfl
  | t :: ts, h, m, hm, z, y => by
    simp only [difAxes]
    obtain ⟨a, rfl, -⟩ := h t (by simp)
    have hP := powAxes_prod_pow (powAxes_cons h)
    have e : difAllAt (Nat.log 2 ts.prod) (Nat.log 2 (2 ^ a)) (fun x => z (x + m)) =
        fun x => difAllAt (Nat.log 2 ts.prod) (Nat.log 2 (2 ^ a)) z (x + m) := by
      funext x
      apply difAllAt_shift
      rw [Nat.log_pow (by norm_num), pow_add, ← hP, mul_comm]
      simpa [List.prod_cons] using hm
    rw [e]
    exact difAxes_shift ts (powAxes_cons h) m (dvd_trans (by simp [List.prod_cons]) hm) _ y

omit [NeZero r] in
theorem synthExpL_cons (t : ℕ) (ts : List ℕ) {J k K B : ℕ} (hJ : J < t) (hk : k < t) (hK : K < ts.prod)
    (hB : B < ts.prod) :
    synthExpL r (t :: ts) (J * ts.prod + K) (k * ts.prod + B) = 2 * r / t * J * k + synthExpL r ts K B := by
  simp only [synthExpL, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
  congr 1
  · rw [List.getD_cons_zero, digit_cons_zero, digit_cons_zero, Nat.add_comm (J * _), Nat.add_comm (k * _),
      Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hK,
      Nat.div_eq_of_lt hB, zero_add, zero_add, Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hk]
  · congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ, digit_cons_succ]
    rw [← digit_mod ts i (J * _ + K), ← digit_mod ts i (k * _ + B), Nat.add_comm (J * _),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK, Nat.add_comm (k * _), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hB]

theorem shiftInv_sum {ι : Type*} (e : ℕ) (s : Finset ι) (f : ι → Fin r → ℂ) :
    shiftInv e (∑ i ∈ s, f i) = ∑ i ∈ s, shiftInv e (f i) := by
  simp only [shiftInv_clm, map_sum]

/-- Separability: the transform over `t :: ts` is the length-`t` transform of the transforms over `ts`. -/
theorem fwdT_cons (t : ℕ) (ts : List ℕ) (_ht : 0 < t) (_hP : 0 < ts.prod) (z : ℕ → Fin r → ℂ) {J K : ℕ}
    (hJ : J < t) (hK : K < ts.prod) :
    fwdT (t :: ts) z (J * ts.prod + K) =
      fwdT ts (fun B => fwdT [t] (fun k => z (k * ts.prod + B)) J) K := by
  simp only [fwdT_single]
  simp only [fwdT, List.prod_cons]
  rw [sum_range_mul _ ts.prod t, Nat.mod_eq_of_lt hJ]
  simp only [Finset.smul_sum, shiftInv_smul, shiftInv_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < t := Finset.mem_range.mp hk
  have hB' : B < ts.prod := Finset.mem_range.mp hB
  rw [synthExpL_cons t ts hJ hk' hK hB', Nat.mod_eq_of_lt hk', Nat.add_comm, shiftInv_add, smul_smul]
  congr 1
  push_cast
  field_simp

theorem bitrevAddr_cons (t : ℕ) (ts : List ℕ) {A B : ℕ} (hA : A < t) (hB : B < ts.prod) :
    bitrevAddr (t :: ts) (A * ts.prod + B) = bitrev (Nat.log 2 t) A * ts.prod + bitrevAddr ts B := by
  simp only [bitrevAddr]
  rw [undigits_cons, List.getD_cons_zero, digit_cons_zero, Nat.add_comm (A * _),
    Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hB, zero_add, Nat.mod_eq_of_lt hA]
  congr 1
  apply undigits_congr
  intro i _
  simp only [List.getD_cons_succ, digit_cons_succ]
  rw [← digit_mod ts i (B + _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]

theorem fwdT_congr (ts : List ℕ) {z w : ℕ → Fin r → ℂ} (h : ∀ k < ts.prod, z k = w k) (j : ℕ) :
    fwdT ts z j = fwdT ts w j := by
  simp only [fwdT]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

/-- `difAxes_eq`: the rounds of all axes compute `F⁻` with every axis address bit-reversed. -/
theorem difAxes_eq : ∀ (ts : List ℕ), PowAxes r ts → ∀ (z : ℕ → Fin r → ℂ) (x : ℕ), x < ts.prod →
    difAxes ts z x = fwdT ts z (bitrevAddr ts x)
  | [], _, z, x, hx => by
    have : x = 0 := by simpa using hx
    subst this
    simp [difAxes, fwdT, bitrevAddr, undigits, synthExpL, shiftInv_zero]
  | t :: ts, h, z, x, hx => by
    obtain ⟨a, rfl, ha⟩ := h t (by simp)
    have hts := powAxes_cons h
    have hP := powAxes_prod_pow hts
    set P := ts.prod
    set o := Nat.log 2 P
    have hPpos : 0 < P := by rw [hP]; positivity
    simp only [List.prod_cons] at hx
    set A := x / P
    set B := x % P
    have hB : B < P := Nat.mod_lt _ hPpos
    have hA : A < 2 ^ a := by
      simp only [A]; rw [Nat.div_lt_iff_lt_mul hPpos]; simpa [P, mul_comm] using hx
    have hxAB : x = B + A * P := by simp only [A, B]; rw [Nat.mod_add_div']
    simp only [difAxes]
    rw [hxAB, ← difAxes_shift ts hts (A * P) (dvd_mul_left _ _), difAxes_eq ts hts _ B hB,
      Nat.add_comm B, bitrevAddr_cons _ ts hA hB, Nat.log_pow (by norm_num),
      fwdT_cons _ ts (by positivity) hPpos z (bitrev_lt a A) (bitrevAddr_lt hts B)]
    apply fwdT_congr
    intro B' hB'
    have hlo : B' < 2 ^ o := by rw [← hP]; exact hB'
    have e := difAllAt_slice (r := r) (hi := 0) (a := a) hlo a le_rfl z A
    simp only [zero_mul, zero_add] at e
    rw [← hP] at e
    rw [Nat.add_comm, e, difAll_eq a ha _ A hA]

end IntegerMultBounds.Schoenhage
