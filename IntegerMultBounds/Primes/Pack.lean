module

public import IntegerMultBounds.Primes.SourcePrimes

/-!
# The packed source lengths

The parameter table keeps all `d` source lengths in one word, the mixed-radix value
`packVal s t m = Σ_{i<m} s_i P_i` with weights `P_i = packW t i = ∏_{j<i} t_j`. With digits
`s_i < t_i` every digit is `(packVal s t m / P_i) mod t_i` (`packVal_digit`): a reader with
`P_i` and `t_i` at hand recovers `s_i` in two atoms.

* `ptRunC`, `ptRunC_do`: add the `m` primes above `lo` to a packed value, with weights `P₀ t^k`.
* `ptPackC`, `ptPackC_do`: both runs, `a` primes above `winLo d R` with radix `R` and `d - a`
  above `winLo d (2R)` with radix `2R`, giving `packVal (primeSrc d a R) (pmTv a R (2R)) d`
  (`packVal_primeSrc`), within `ptPackAtoms d a R ≤ 64 (d + 1) 4^k` atoms for `2R ≤ 2^k`
  (`ptPackAtoms_le`).
* `ptProdPC`, `ptProdPC_do`: the product `∏_{i<d} s_i` of the digits of a packed value.
* `ptEmitPC`, `ptEmitPC_do`: the emission of the digits, `(pmEmitList A w s d).reverse`.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast.TableVM Finset

/-! ### Mixed radix -/

/-- The weight `P_i = ∏_{j<i} t_j` of digit `i`. -/
def packW (t : ℕ → ℕ) (i : ℕ) : ℕ := ∏ j ∈ range i, t j

/-- The mixed-radix value `Σ_{i<m} s_i P_i`. -/
def packVal (s t : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ range m, s i * packW t i

theorem packW_succ (t : ℕ → ℕ) (i : ℕ) : packW t (i + 1) = packW t i * t i :=
  prod_range_succ _ _

theorem packVal_succ (s t : ℕ → ℕ) (m : ℕ) :
    packVal s t (m + 1) = packVal s t m + s m * packW t m :=
  sum_range_succ _ _

theorem packW_dvd (t : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) : packW t i ∣ packW t j :=
  prod_dvd_prod_of_subset _ _ _ (range_subset_range.2 hij)

theorem packW_const (t k : ℕ) : packW (fun _ => t) k = t ^ k := by simp [packW]

theorem packVal_congr {s s' t : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, s i = s' i) :
    packVal s t m = packVal s' t m :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

/-- With digits `s_i < t_i` the value is below the next weight. -/
theorem packVal_lt {s t : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, s i < t i) : packVal s t m < packW t m := by
  induction m with
  | zero => simp [packVal, packW]
  | succ m ih =>
    have hV := ih fun i hi => h i (by omega)
    have hm : s m + 1 ≤ t m := h m (by omega)
    have h1 : (s m + 1) * packW t m ≤ t m * packW t m := Nat.mul_le_mul_right _ hm
    have e : (s m + 1) * packW t m = s m * packW t m + packW t m := by ring
    rw [packVal_succ, packW_succ, Nat.mul_comm (packW t m)]
    omega

theorem packW_pos {s t : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, s i < t i) {i : ℕ} (hi : i ≤ m) :
    0 < packW t i := by
  have := packVal_lt (s := s) (t := t) (m := i) fun j hj => h j (by omega)
  omega

theorem packW_le {s t : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, s i < t i) {i : ℕ} (hi : i ≤ m) :
    packW t i ≤ packW t m :=
  Nat.le_of_dvd (packW_pos h le_rfl) (packW_dvd t hi)

/-- **Digit extraction.** With digits `s_i < t_i`, digit `i` is `(packVal / P_i) mod t_i`. -/
theorem packVal_digit {s t : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, s i < t i) {i : ℕ} (hi : i < m) :
    packVal s t m / packW t i % t i = s i := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h' : ∀ j < m, s j < t j := fun j hj => h j (by omega)
    have hP : 0 < packW t i := packW_pos h (by omega)
    rw [packVal_succ]
    rcases Nat.lt_or_ge i m with him | him
    · obtain ⟨c, hc⟩ := packW_dvd t (show i + 1 ≤ m by omega)
      rw [packW_succ] at hc
      have e : s m * packW t m = packW t i * (t i * (c * s m)) := by rw [hc]; ring
      rw [e, Nat.add_mul_div_left _ _ hP, Nat.add_mul_mod_self_left]
      exact ih h' him
    · obtain rfl : i = m := by omega
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt (packVal_lt h'), Nat.zero_add,
        Nat.mod_eq_of_lt (h i (by omega))]

/-! ### Two radices -/

theorem pmTv_of_lt {a R r i : ℕ} (hi : i < a) : pmTv a R r i = R := by simp [pmTv, hi]

theorem pmTv_of_ge {a R r i : ℕ} (hi : a ≤ i) : pmTv a R r i = r := by
  simp [pmTv, Nat.not_lt.2 hi]

theorem packW_pmTv_le {a R r i : ℕ} (hi : i ≤ a) : packW (pmTv a R r) i = R ^ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [packW_succ, ih (by omega), pmTv_of_lt (by omega), pow_succ]

theorem packW_pmTv_add (a R r i : ℕ) : packW (pmTv a R r) (a + i) = R ^ a * r ^ i := by
  induction i with
  | zero => simpa using packW_pmTv_le (r := r) (le_refl a)
  | succ i ih =>
    rw [← Nat.add_assoc, packW_succ, ih, pmTv_of_ge (by omega), pow_succ, Nat.mul_assoc]

/-- The packed prime source lengths split into the two windows. -/
theorem packVal_primeSrc {d a R : ℕ} (had : a ≤ d) :
    packVal (primeSrc d a R) (pmTv a R (2 * R)) d =
      packVal (windowPrime (winLo d R)) (fun _ => R) a +
        R ^ a * packVal (windowPrime (winLo d (2 * R))) (fun _ => 2 * R) (d - a) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = a + m := ⟨d - a, by omega⟩
  rw [Nat.add_sub_cancel_left, packVal, sum_range_add]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [packW_pmTv_le hi'.le, packW_const]
    simp [primeSrc, hi']
  · rw [packVal, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [packW_pmTv_add, packW_const]
    simp only [primeSrc, show ¬ a + j < a by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    ring

/-! ### The packing program -/

variable {A W w : ℕ}

/-- The next-prime registers inside a run. -/
def ptRunReg : Fin 7 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6]

theorem ptRunReg_injective : Function.Injective ptRunReg := by decide

/-- Add the `m` primes above register `0` to the packed value: the weight in `9`, the radix in
`10`, the value in `11`, `m` in `8`, the counter in `7`. -/
def ptRunC : TblCode 12 :=
  tblFor 7 8 (ptNextC.rename ptRunReg ;; tblBlock 12 [.mul 0 9 2, .add 11 2 11] (.mul 9 10 9))

/-- The atoms of `ptRunC`. -/
def ptRunAtoms (lo hi m : ℕ) : ℕ := 1 + (m * ((ptGapAtoms lo hi + 3) + 1 + 2) + 2)

theorem ptNextAtoms_le {lo hi c : ℕ} (hclo : lo ≤ c) (hc : nextPrimeAfter c ≤ hi) :
    ptNextAtoms c ≤ ptGapAtoms lo hi := by
  have hcn : c < nextPrimeAfter c := lt_nextPrimeAfter c
  have hgap : nextPrimeAfter c - c ≤ hi - lo := by omega
  have hpa : ptPrimeAtoms (nextPrimeAfter c) ≤ ptPrimeAtoms hi := ptPrimeAtoms_mono hc
  have := Nat.mul_le_mul hgap (by omega : 1 + ptPrimeAtoms (nextPrimeAfter c) + 2 ≤
    3 + ptPrimeAtoms hi)
  unfold ptNextAtoms ptGapAtoms
  omega

/-- **One run.** From `lo` in `0`, `m` in `8`, the weight `P₀` in `9`, the radix `t` in `10`
and the value `V₀` in `11`, when `(lo, hi]` holds at least `m` primes and `hi < t`, the run adds
`P₀ Σ_{k<m} windowPrime lo k · t^k` to the value and leaves the weight `P₀ t^m`. -/
theorem ptRunC_do (st : TblSt 12 A) {lo hi m P₀ t V₀ : ℕ} (hlo : st.val 0 = lo)
    (hm : st.val 8 = m) (hP : st.val 9 = P₀) (ht : st.val 10 = t) (hV : st.val 11 = V₀)
    (hcount : m ≤ ((Finset.Ioc lo hi).filter Nat.Prime).card) (hhi : hi < t)
    (hW : 3 * hi + 4 < 2 ^ W) (hmW : m < 2 ^ W) (hVW : V₀ + P₀ * t ^ m < 2 ^ W) :
    TblDo A W w ptRunC st (fun s => s.val 8 = m ∧ s.val 9 = P₀ * t ^ m ∧ s.val 10 = t ∧
      s.val 11 = V₀ + P₀ * packVal (windowPrime lo) (fun _ => t) m ∧ s.acc = st.acc)
      (ptRunAtoms lo hi m) := by
  refine TblDo.for m (ptGapAtoms lo hi + 3) hm hmW (by decide)
    (fun j s => s.val 0 = nextPrimeAfter^[j] lo ∧ s.val 9 = P₀ * t ^ j ∧ s.val 10 = t ∧
      s.val 11 = V₀ + P₀ * packVal (windowPrime lo) (fun _ => t) j ∧ s.acc = st.acc)
    ⟨by simp [hlo], by simp [hP], by simp [ht], by simp [hV, packVal], rfl⟩ ?_ ?_
  · rintro j hj s ⟨e0, e9, e10, e11, ea⟩ e7 e8
    set c := nextPrimeAfter^[j] lo with hc
    have hwp : nextPrimeAfter c = windowPrime lo j := by
      rw [windowPrime_eq_iterate, Function.iterate_succ_apply']
    have hwhi : windowPrime lo j ≤ hi := windowPrime_le_of_card (by omega)
    have hclo : lo ≤ c := le_iterate_nextPrimeAfter lo j
    have hnext := TblDo.rename (f := ptRunReg) ptRunReg_injective
      (ptNextC_do (A := A) (W := W) (w := w) (s.restrict ptRunReg) (x := c)
        (by simp [ptRunReg, e0, hc]) (by rw [hwp]; omega))
    have hbound : ptNextAtoms c ≤ ptGapAtoms lo hi := ptNextAtoms_le hclo (by rw [hwp]; exact hwhi)
    -- the word bounds
    set x := windowPrime lo j with hx
    set pv := packVal (windowPrime lo) (fun _ => t) j with hpv
    have hpvt : pv < t ^ j := by
      have := packVal_lt (s := windowPrime lo) (t := fun _ => t) (m := j) fun i hi' => by
        have := windowPrime_le_of_card (lo := lo) (hi := hi) (k := i) (by omega)
        omega
      rwa [packW_const] at this
    have htm : P₀ * t ^ (j + 1) ≤ P₀ * t ^ m :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hxt : x * t ^ j + pv ≤ t ^ (j + 1) := by
      have : (x + 1) * t ^ j ≤ t * t ^ j := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ]
      nlinarith
    have hxP : x * (P₀ * t ^ j) + P₀ * pv ≤ P₀ * t ^ (j + 1) := by
      have := Nat.mul_le_mul_left P₀ hxt
      rw [Nat.mul_add] at this
      calc x * (P₀ * t ^ j) + P₀ * pv = P₀ * (x * t ^ j) + P₀ * pv := by ring
        _ ≤ P₀ * t ^ (j + 1) := this
    have hPt : P₀ * t ^ j * t = P₀ * t ^ (j + 1) := by rw [pow_succ]; ring
    refine (hnext.seq (K₂ := 3) (fun s₁ ⟨⟨f0, _, fa⟩, hrest⟩ => ?_)).mono (fun _ h => h)
      (by omega)
    have hout : ∀ y : Fin 12, 7 ≤ y.val → ∀ z, ptRunReg z ≠ y := by
      intro y hy z
      fin_cases z <;> simp [ptRunReg] <;> omega
    have f0' : s₁.val 0 = x := by simpa [ptRunReg, hwp] using f0
    have f7 : s₁.val 7 = j := by rw [hrest 7 (hout 7 (by decide)), e7]
    have f8 : s₁.val 8 = m := by rw [hrest 8 (hout 8 (by decide)), e8]
    have f9 : s₁.val 9 = P₀ * t ^ j := by rw [hrest 9 (hout 9 (by decide)), e9]
    have f10 : s₁.val 10 = t := by rw [hrest 10 (hout 10 (by decide)), e10]
    have f11 : s₁.val 11 = V₀ + P₀ * pv := by rw [hrest 11 (hout 11 (by decide)), e11]
    have fa' : s₁.acc = s.acc := by simpa using fa
    refine TblDo.block _ _ ?_ ?_
    · simp only [tblFitsList, TblIns.fits, TblIns.exact, List.cons_append, List.nil_append,
        Function.update_apply]
      simp only [show (11 : Fin 12) ≠ 2 by decide, show (9 : Fin 12) ≠ 2 by decide,
        show (10 : Fin 12) ≠ 2 by decide, show (9 : Fin 12) ≠ 11 by decide,
        show (10 : Fin 12) ≠ 11 by decide, ↓reduceIte, f0', f9, f10, f11]
      refine ⟨by omega, by omega, by omega, trivial⟩
    · simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append]
      refine ⟨by simp [f7], by simp [f8], ?_, ?_, ?_, ?_, ?_⟩
      · simp [f0', hx, windowPrime_eq_iterate, Function.iterate_succ_apply']
      · simp [f9, f10, hPt]
      · simp [f10]
      · simp [f0', f9, f11, hpv, packVal_succ, packW_const]
        ring
      · simp [fa', ea]
  · rintro s ⟨-, e9, e10, e11, ea⟩ - e8
    exact ⟨e8, e9, e10, e11, ea⟩

/-- The run registers inside the packing program. -/
def ptPackReg : Fin 12 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- The registers of `winLoC`: `t ↦ 13`, `d ↦ 14`, `lo ↦ 0`, scratch on `1 … 4`. -/
def ptPackLoReg : Fin 7 → Fin 17 := ![13, 14, 0, 1, 2, 3, 4]

theorem ptPackReg_injective : Function.Injective ptPackReg := by decide

theorem ptPackLoReg_injective : Function.Injective ptPackLoReg := by decide

/-- Pack the prime source lengths into register `11`: `R` in `12`, `2R` in `13`, `d` in `14`,
`a` in `15`, `winLo d R` in `16`. -/
def ptPackC : TblCode 17 :=
  tblBlock 17 [.copy 16 0, .zero 9, .inc 9, .zero 11, .copy 15 8] (.copy 12 10) ;;
  ptRunC.rename ptPackReg ;; winLoC.rename ptPackLoReg ;;
  tblBlock 17 [.sub 14 15 8] (.copy 13 10) ;; ptRunC.rename ptPackReg

/-- The atoms of `ptPackC`. -/
def ptPackAtoms (d a R : ℕ) : ℕ :=
  6 + (ptRunAtoms (winLo d R) (winHi d R) a + (7 + (2 +
    ptRunAtoms (winLo d (2 * R)) (winHi d (2 * R)) (d - a))))

/-- The inputs of `ptPackC`. -/
def PtPackIn (R d a : ℕ) (s : TblSt 17 A) : Prop :=
  s.val 12 = R ∧ s.val 13 = 2 * R ∧ s.val 14 = d ∧ s.val 15 = a ∧ s.val 16 = winLo d R

theorem ptPackIn_of_eq {R d a : ℕ} {s s' : TblSt 17 A} (h : PtPackIn R d a s)
    (h' : ∀ y : Fin 17, 12 ≤ y.val → s'.val y = s.val y) : PtPackIn R d a s' := by
  obtain ⟨g12, g13, g14, g15, g16⟩ := h
  exact ⟨by rw [h' 12 (by decide), g12], by rw [h' 13 (by decide), g13],
    by rw [h' 14 (by decide), g14], by rw [h' 15 (by decide), g15],
    by rw [h' 16 (by decide), g16]⟩

/-- **The packed prime source lengths.** From `R ≥ 1`, `d ≥ 1`, `a ≤ d`, when the window below
`R` holds at least `a` primes and the window below `2R` at least `d - a`, register `11` ends as
`packVal (primeSrc d a R) (pmTv a R (2R)) d`, with words `6R + 4 < 2^W`, `2R + 2d < 2^W` and
twice the weight of all `d` digits below `2^W`. -/
theorem ptPackC_do (st : TblSt 17 A) {R d a : ℕ} (hin : PtPackIn R d a st) (hd1 : 1 ≤ d)
    (had : a ≤ d) (hR : 1 ≤ R)
    (h₁ : a ≤ ((Ioc (winLo d R) (winHi d R)).filter Nat.Prime).card)
    (h₂ : d - a ≤ ((Ioc (winLo d (2 * R)) (winHi d (2 * R))).filter Nat.Prime).card)
    (hW : 6 * R + 4 < 2 ^ W) (hWd : 2 * R + 2 * d < 2 ^ W)
    (hWP : 2 * packW (pmTv a R (2 * R)) d < 2 ^ W) :
    TblDo A W w ptPackC st (fun s => PtPackIn R d a s ∧
      s.val 11 = packVal (primeSrc d a R) (pmTv a R (2 * R)) d ∧ s.acc = st.acc)
      (ptPackAtoms d a R) := by
  have hW1 : W ≠ 0 := by
    rintro rfl
    simp at hW
  have hhi₁ : winHi d R < R := winHi_lt hd1 hR
  have hhi₂ : winHi d (2 * R) < 2 * R := winHi_lt hd1 (by omega)
  -- the weights
  have hPd : packW (pmTv a R (2 * R)) d = R ^ a * (2 * R) ^ (d - a) := by
    rw [← packW_pmTv_add, Nat.add_sub_cancel' had]
  have hRa : R ^ a ≤ packW (pmTv a R (2 * R)) d := by
    rw [hPd]
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have hdig₁ : ∀ i < a, windowPrime (winLo d R) i < R := fun i hi => by
    have := windowPrime_le_of_card (lo := winLo d R) (hi := winHi d R) (k := i) (by omega)
    omega
  have hV₁ : packVal (windowPrime (winLo d R)) (fun _ => R) a < R ^ a := by
    have := packVal_lt (t := fun _ => R) hdig₁
    rwa [packW_const] at this
  have hreg : ∀ y : Fin 17, 12 ≤ y.val → ∀ z, ptPackReg z ≠ y := by
    intro y hy z
    fin_cases z <;> simp [ptPackReg] <;> omega
  have hlo_out : ∀ y : Fin 17, 8 ≤ y.val → y ≠ 13 → y ≠ 14 → ∀ z, ptPackLoReg z ≠ y := by
    intro y hy h13 h14 z
    fin_cases z <;> simp [ptPackLoReg] <;> omega
  -- 1: `x := winLo d R`, `P := 1`, `V := 0`, `m := a`, `t := R`
  obtain ⟨g12, g13, g14, g15, g16⟩ := hin
  refine (TblDo.block (P := fun s => PtPackIn R d a s ∧ s.val 0 = winLo d R ∧ s.val 8 = a ∧
      s.val 9 = 1 ∧ s.val 10 = R ∧ s.val 11 = 0 ∧ s.acc = st.acc) _ _ ?_ ?_).seq
    (fun s₁ ⟨k₁, x₁, m₁, p₁, t₁, v₁, a₁⟩ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hW1]
  · simp [tblExactList, TblIns.exact, PtPackIn, g12, g13, g14, g15, g16]
  -- 2: the first run
  have hrun₁ := TblDo.rename (f := ptPackReg) ptPackReg_injective
    (ptRunC_do (A := A) (W := W) (w := w) (s₁.restrict ptPackReg) (lo := winLo d R)
      (hi := winHi d R) (m := a) (P₀ := 1) (t := R) (V₀ := 0)
      (by simp [ptPackReg, x₁]) (by simp [ptPackReg, m₁]) (by simp [ptPackReg, p₁])
      (by simp [ptPackReg, t₁]) (by simp [ptPackReg, v₁]) h₁ hhi₁ (by omega) (by omega)
      (by omega))
  refine hrun₁.seq (fun s₂ ⟨⟨m₂, p₂, t₂, v₂, a₂⟩, r₂⟩ => ?_)
  have k₂ : PtPackIn R d a s₂ := ptPackIn_of_eq k₁ fun y hy => r₂ y (hreg y hy)
  have p₂' : s₂.val 9 = R ^ a := by simpa [ptPackReg] using p₂
  have v₂' : s₂.val 11 = packVal (windowPrime (winLo d R)) (fun _ => R) a := by
    simpa [ptPackReg] using v₂
  have a₂' : s₂.acc = st.acc := by rw [← a₁]; simpa using a₂
  -- 3: `x := winLo d (2R)`
  have hlo₂ := TblDo.rename (f := ptPackLoReg) ptPackLoReg_injective
    (winLoC_do (A := A) (W := W) (w := w) (s₂.restrict ptPackLoReg) (t := 2 * R) (d := d)
      (by simp [ptPackLoReg, k₂.2.1]) (by simp [ptPackLoReg, k₂.2.2.1]) hd1 hWd)
  refine hlo₂.seq (fun s₃ ⟨⟨y₀, y₁, x₃, a₃⟩, r₃⟩ => ?_)
  have k₃ : PtPackIn R d a s₃ := by
    refine ⟨?_, by simpa [ptPackLoReg] using y₀, by simpa [ptPackLoReg] using y₁, ?_, ?_⟩
    · rw [r₃ 12 (hlo_out 12 (by decide) (by decide) (by decide)), k₂.1]
    · rw [r₃ 15 (hlo_out 15 (by decide) (by decide) (by decide)), k₂.2.2.2.1]
    · rw [r₃ 16 (hlo_out 16 (by decide) (by decide) (by decide)), k₂.2.2.2.2]
  have x₃' : s₃.val 0 = winLo d (2 * R) := by simpa [ptPackLoReg] using x₃
  have p₃ : s₃.val 9 = R ^ a := by
    rw [r₃ 9 (hlo_out 9 (by decide) (by decide) (by decide)), p₂']
  have v₃ : s₃.val 11 = packVal (windowPrime (winLo d R)) (fun _ => R) a := by
    rw [r₃ 11 (hlo_out 11 (by decide) (by decide) (by decide)), v₂']
  have a₃' : s₃.acc = st.acc := by rw [← a₂']; simpa using a₃
  -- 4: `m := d - a`, `t := 2R`
  refine (TblDo.block (P := fun s => PtPackIn R d a s ∧ s.val 0 = winLo d (2 * R) ∧
      s.val 8 = d - a ∧ s.val 9 = R ^ a ∧ s.val 10 = 2 * R ∧
      s.val 11 = packVal (windowPrime (winLo d R)) (fun _ => R) a ∧ s.acc = st.acc) _ _ ?_ ?_).seq
    (fun s₄ ⟨k₄, x₄, m₄, p₄, t₄, v₄, a₄⟩ => ?_)
  · simp [tblFitsList, TblIns.fits, k₃.2.2.1, k₃.2.2.2.1]
    omega
  · obtain ⟨g12, g13, g14, g15, g16⟩ := k₃
    simp [tblExactList, TblIns.exact, PtPackIn, g12, g13, g14, g15, g16, x₃', p₃, v₃, a₃']
  -- 5: the second run
  have hV₂ : packVal (windowPrime (winLo d R)) (fun _ => R) a + R ^ a * (2 * R) ^ (d - a) <
      2 ^ W := by
    rw [← hPd]
    omega
  have hrun₂ := TblDo.rename (f := ptPackReg) ptPackReg_injective
    (ptRunC_do (A := A) (W := W) (w := w) (s₄.restrict ptPackReg) (lo := winLo d (2 * R))
      (hi := winHi d (2 * R)) (m := d - a) (P₀ := R ^ a) (t := 2 * R)
      (V₀ := packVal (windowPrime (winLo d R)) (fun _ => R) a)
      (by simp [ptPackReg, x₄]) (by simp [ptPackReg, m₄]) (by simp [ptPackReg, p₄])
      (by simp [ptPackReg, t₄]) (by simp [ptPackReg, v₄]) h₂ hhi₂ (by omega) (by omega) hV₂)
  refine hrun₂.mono (fun s₅ ⟨⟨_, _, _, v₅, a₅⟩, r₅⟩ => ⟨ptPackIn_of_eq k₄ fun y hy => r₅ y (hreg y hy),
    ?_, ?_⟩) le_rfl
  · rw [packVal_primeSrc had]
    simpa [ptPackReg] using v₅
  · rw [← a₄]; simpa using a₅

/-- One run below `2^k` uses at most `34 (m + 1) 4^k` atoms. -/
theorem ptRunAtoms_le {lo hi m k : ℕ} (hlh : lo ≤ hi) (hhi : hi ≤ 2 ^ k) :
    ptRunAtoms lo hi m ≤ 34 * (m + 1) * 4 ^ k := by
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h4 : 4 ^ k = 2 ^ k * 2 ^ k := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hPP : 1 ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hP hP
  have hsq : Nat.sqrt hi ≤ 2 ^ k := (Nat.sqrt_le_self hi).trans hhi
  have hpa : 3 + ptPrimeAtoms hi ≤ 23 * 2 ^ k := by
    unfold ptPrimeAtoms
    omega
  have hgap : (hi - lo) * (3 + ptPrimeAtoms hi) ≤ 2 ^ k * (23 * 2 ^ k) :=
    Nat.mul_le_mul (by omega) hpa
  have e3 : 2 ^ k * (23 * 2 ^ k) = 23 * (2 ^ k * 2 ^ k) := by ring
  have hg : ptGapAtoms lo hi + 3 + 1 + 2 ≤ 34 * 4 ^ k := by
    unfold ptGapAtoms
    rw [h4]
    omega
  have e2 : 34 * (m + 1) * 4 ^ k = m * (34 * 4 ^ k) + 34 * 4 ^ k := by ring
  have hm := Nat.mul_le_mul_left m hg
  have h41 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  unfold ptRunAtoms
  rw [e2]
  omega

/-- The packing below `2R ≤ 2^k` uses at most `100 (d + 1) 4^k` atoms. -/
theorem ptPackAtoms_le {d a R k : ℕ} (hd : 1 ≤ d) (had : a ≤ d) (hR : 2 * R ≤ 2 ^ k) :
    ptPackAtoms d a R ≤ 100 * (d + 1) * 4 ^ k := by
  have h₁ := ptRunAtoms_le (m := a) (winLo_le_winHi hd R)
    (((Nat.sub_le _ _).trans (by omega : R ≤ 2 * R)).trans hR)
  have h₂ := ptRunAtoms_le (m := d - a) (winLo_le_winHi hd (2 * R)) ((Nat.sub_le _ _).trans hR)
  have h41 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have e1 : 34 * (a + 1) * 4 ^ k = 34 * a * 4 ^ k + 34 * 4 ^ k := by ring
  have e2 : 34 * (d - a + 1) * 4 ^ k = 34 * (d - a) * 4 ^ k + 34 * 4 ^ k := by ring
  have e3 : 100 * (d + 1) * 4 ^ k = 100 * d * 4 ^ k + 100 * 4 ^ k := by ring
  have hsum : 34 * a * 4 ^ k + 34 * (d - a) * 4 ^ k = 34 * d * 4 ^ k := by
    rw [← Nat.add_mul, ← Nat.mul_add, Nat.add_sub_cancel' had]
  have hd4 : 34 * d * 4 ^ k ≤ 100 * d * 4 ^ k := Nat.mul_le_mul_right _ (by omega)
  unfold ptPackAtoms
  omega

/-! ### Reading the digits -/

/-- The product of the digits of a packed value: the counter in `0`, `d` in `1`, `a` in `2`,
`R` in `3`, `r` in `4`, the packed value in `5`, the product in `6`, the weight in `7`, the
radix in `8`, the digit in `9`. -/
def ptProdPC : TblCode 10 :=
  tblBlock 10 [.zero 6, .inc 6, .zero 7] (.inc 7) ;;
  tblFor 0 1 (.ite 0 2 (.ins (.copy 3 8)) (.ins (.copy 4 8)) ;;
    tblBlock 10 [.div 5 7 9, .mod 9 8 9, .mul 6 9 6] (.mul 7 8 7))

/-- **The product of the digits.** From `d`, `a`, `R`, `r` and a packed value with digits
`v i < pmTv a R r i`, `v i ≥ 1`, register `6` ends as `∏_{i<d} v i`, in `9 d + 7` atoms. -/
theorem ptProdPC_do (st : TblSt 10 A) {d a R r : ℕ} {v : ℕ → ℕ} (h1 : st.val 1 = d)
    (h2 : st.val 2 = a) (h3 : st.val 3 = R) (h4 : st.val 4 = r)
    (h5 : st.val 5 = packVal v (pmTv a R r) d) (hdig : ∀ i < d, v i < pmTv a R r i)
    (hpos : ∀ i < d, 1 ≤ v i) (hdW : d < 2 ^ W) (hPW : packW (pmTv a R r) d < 2 ^ W)
    (hSW : ∏ i ∈ range d, v i < 2 ^ W) :
    TblDo A W w ptProdPC st (fun s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧
      s.val 5 = packVal v (pmTv a R r) d ∧ s.val 6 = ∏ i ∈ range d, v i ∧ s.acc = st.acc)
      (9 * d + 7) := by
  have hSpos : 0 < ∏ i ∈ range d, v i := prod_pos fun i hi => hpos i (mem_range.1 hi)
  have hW1 : W ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hSW
    omega
  set V := packVal v (pmTv a R r) d with hV
  refine ((TblDo.block (P := fun s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧
      s.val 5 = V ∧ s.val 6 = 1 ∧ s.val 7 = 1 ∧ s.acc = st.acc) _ _ ?_ ?_).seq (K₁ := 4)
    (P₂ := fun s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧ s.val 5 = V ∧
      s.val 6 = ∏ i ∈ range d, v i ∧ s.acc = st.acc) (K₂ := 1 + (d * (6 + 1 + 2) + 2))
    (fun s₁ ⟨e1, e2, e3, e4, e5, e6, e7, ea⟩ => ?_)).mono (fun _ h => h) (by omega)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hW1]
  · simp [tblExactList, TblIns.exact, h1, h2, h3, h4, h5]
  refine TblDo.for d 6 e1 hdW (by decide)
    (fun j s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧ s.val 5 = V ∧
      s.val 6 = ∏ i ∈ range j, v i ∧ s.val 7 = packW (pmTv a R r) j ∧ s.acc = st.acc)
    ⟨by simp [e1], by simp [e2], by simp [e3], by simp [e4], by simp [e5], by simp [e6],
      by simp [e7, packW], by simp [ea]⟩ ?_ ?_
  · rintro j hj s ⟨i1, i2, i3, i4, i5, i6, i7, ia⟩ i0 -
    have hite : TblDo A W w (.ite 0 2 (.ins (.copy 3 8)) (.ins (.copy 4 8))) s
        (fun s' => s' = ⟨Function.update s.val 8 (pmTv a R r j), s.acc⟩) 2 := by
      by_cases hja : j < a
      · refine TblDo.iteT (by rw [i0, i2]; exact hja) (TblDo.ins _ ?_)
        simp [TblIns.run, i3, pmTv_of_lt hja]
      · refine TblDo.iteF (by rw [i0, i2]; exact hja) (TblDo.ins _ ?_)
        simp [TblIns.run, i4, pmTv_of_ge (Nat.not_lt.1 hja)]
    have hdj : V / packW (pmTv a R r) j % pmTv a R r j = v j := packVal_digit hdig hj
    have hSj : (∏ i ∈ range j, v i) * v j ≤ ∏ i ∈ range d, v i := by
      rw [← prod_range_succ]
      exact Nat.le_of_dvd hSpos (prod_dvd_prod_of_subset _ _ _ (range_subset_range.2 hj))
    have hPj : packW (pmTv a R r) j * pmTv a R r j ≤ packW (pmTv a R r) d := by
      rw [← packW_succ]
      exact packW_le hdig hj
    refine (hite.seq (K₂ := 4) fun s' hs' => ?_).mono (fun _ h => h) (by norm_num)
    subst hs'
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, i5, i6, i7, hdj]
      omega
    · simp [tblExactList, TblIns.exact, i0, i1, i2, i3, i4, i5, i6, i7, hdj, ia,
        prod_range_succ, packW_succ]
  · rintro s ⟨i1, i2, i3, i4, i5, i6, -, ia⟩ - -
    exact ⟨i1, i2, i3, i4, i5, i6, ia⟩

/-- The emission of the digits of a packed value: the counter in `0`, `d` in `1`, `a` in `2`,
`R` in `3`, `r` in `4`, the packed value in `5`, the weight in `6`, the radix in `7`, the digit
in `8`. -/
def ptEmitPC : TblCode 9 :=
  tblBlock 9 [.zero 6] (.inc 6) ;;
  tblFor 0 1 (.ite 0 2 (.ins (.copy 3 7)) (.ins (.copy 4 7)) ;;
    tblBlock 9 [.div 5 6 8, .mod 8 7 8, .emit 8 8] (.mul 6 7 6))

/-- **The emission of the digits.** From `d`, `a`, `R`, `r` and a packed value with digits
`v i < pmTv a R r i`, the program emits `v 0, …, v (d - 1)` in the format of the parameter
program, in `9 d + 5` atoms. -/
theorem ptEmitPC_do (st : TblSt 9 A) {d a R r : ℕ} {v : ℕ → ℕ} (h1 : st.val 1 = d)
    (h2 : st.val 2 = a) (h3 : st.val 3 = R) (h4 : st.val 4 = r)
    (h5 : st.val 5 = packVal v (pmTv a R r) d) (hdig : ∀ i < d, v i < pmTv a R r i)
    (hdW : d < 2 ^ W) (hPW : packW (pmTv a R r) d < 2 ^ W) :
    TblDo A W w ptEmitPC st (fun s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧
      s.val 5 = packVal v (pmTv a R r) d ∧ s.acc = (pmEmitList A w v d).reverse ++ st.acc)
      (9 * d + 5) := by
  have hPpos : 0 < packW (pmTv a R r) d := packW_pos hdig le_rfl
  have hW1 : W ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hPW
    omega
  set V := packVal v (pmTv a R r) d with hV
  refine ((TblDo.block (P := fun s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧
      s.val 5 = V ∧ s.val 6 = 1 ∧ s.acc = st.acc) _ _ ?_ ?_).seq (K₁ := 2)
    (P₂ := fun s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧ s.val 5 = V ∧
      s.acc = (pmEmitList A w v d).reverse ++ st.acc) (K₂ := 1 + (d * (6 + 1 + 2) + 2))
    (fun s₁ ⟨e1, e2, e3, e4, e5, e6, ea⟩ => ?_)).mono (fun _ h => h) (by omega)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hW1]
  · simp [tblExactList, TblIns.exact, h1, h2, h3, h4, h5]
  refine TblDo.for d 6 e1 hdW (by decide)
    (fun j s => s.val 1 = d ∧ s.val 2 = a ∧ s.val 3 = R ∧ s.val 4 = r ∧ s.val 5 = V ∧
      s.val 6 = packW (pmTv a R r) j ∧ s.acc = (pmEmitList A w v j).reverse ++ st.acc)
    ⟨by simp [e1], by simp [e2], by simp [e3], by simp [e4], by simp [e5], by simp [e6, packW],
      by simp [ea, pmEmitList]⟩ ?_ ?_
  · rintro j hj s ⟨i1, i2, i3, i4, i5, i6, ia⟩ i0 -
    have hite : TblDo A W w (.ite 0 2 (.ins (.copy 3 7)) (.ins (.copy 4 7))) s
        (fun s' => s' = ⟨Function.update s.val 7 (pmTv a R r j), s.acc⟩) 2 := by
      by_cases hja : j < a
      · refine TblDo.iteT (by rw [i0, i2]; exact hja) (TblDo.ins _ ?_)
        simp [TblIns.run, i3, pmTv_of_lt hja]
      · refine TblDo.iteF (by rw [i0, i2]; exact hja) (TblDo.ins _ ?_)
        simp [TblIns.run, i4, pmTv_of_ge (Nat.not_lt.1 hja)]
    have hdj : V / packW (pmTv a R r) j % pmTv a R r j = v j := packVal_digit hdig hj
    have hPj : packW (pmTv a R r) j * pmTv a R r j ≤ packW (pmTv a R r) d := by
      rw [← packW_succ]
      exact packW_le hdig hj
    refine (hite.seq (K₂ := 4) fun s' hs' => ?_).mono (fun _ h => h) (by norm_num)
    subst hs'
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, i6]
      omega
    · simp [tblExactList, TblIns.exact, i0, i1, i2, i3, i4, i5, i6, hdj, ia, packW_succ,
        pmEmitList_succ, List.reverse_append]
  · rintro s ⟨i1, i2, i3, i4, i5, -, ia⟩ - -
    exact ⟨i1, i2, i3, i4, i5, ia⟩

end IntegerMultBounds.Primes
