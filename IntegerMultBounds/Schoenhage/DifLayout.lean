module

public import IntegerMultBounds.Schoenhage.DifSchedule

/-! Layouts as permutations of address bits. With `σ` a permutation of the
bit positions `[0, n)`, the logical address of the record stored at physical
address `y` has bit `P` equal to bit `σ P` of `y` (`logi σ n y`). On the
stored array a butterfly on logical bit `P` is the butterfly on physical bit
`σ P`, and a twist reads the logical address (`bfly_logi`, `twist_logi`); so
running the slot-major schedule on physical bits computes, at physical
address `y`, the entry `(F⁻ z)_(B (logi y))` of the transform of the logical
array (`physSchedule_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-! ### Numbers from bits -/

/-- The number with bits `f 0, …, f (n-1)`. -/
def ofBits : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => ofBits n f + f n % 2 * 2 ^ n

theorem ofBits_lt : ∀ (n : ℕ) (f : ℕ → ℕ), ofBits n f < 2 ^ n
  | 0, _ => by simp [ofBits]
  | n + 1, f => by
    have := ofBits_lt n f
    have : f n % 2 ≤ 1 := by omega
    simp only [ofBits, pow_succ]; nlinarith

theorem bitAt_ofBits : ∀ (n : ℕ) (f : ℕ → ℕ) (Q : ℕ), Q < n → bitAt (ofBits n f) Q = f Q % 2
  | 0, _, _, h => absurd h (by omega)
  | n + 1, f, Q, h => by
    simp only [ofBits]
    rcases Nat.lt_or_ge Q n with hQ | hQ
    · rw [← bitAt_ofBits n f Q hQ]
      unfold bitAt
      have e : f n % 2 * 2 ^ n = 2 ^ Q * (2 * (f n % 2 * 2 ^ (n - Q - 1))) := by
        have : 2 ^ n = 2 ^ Q * 2 * 2 ^ (n - Q - 1) := by rw [← pow_succ, ← pow_add]; congr 1; omega
        rw [this]; ring
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
    · have hQn : Q = n := by omega
      subst hQn
      unfold bitAt
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (ofBits_lt Q f), zero_add, Nat.mod_mod]

theorem ofBits_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ Q < n, f Q % 2 = g Q % 2) : ofBits n f = ofBits n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ofBits, ih (fun Q hQ => h Q (by omega)), h n (by omega)]

theorem ofBits_bitAt : ∀ (n x : ℕ), x < 2 ^ n → ofBits n (bitAt x) = x
  | 0, x, h => by simp at h; simp [ofBits, h]
  | n + 1, x, h => by
    simp only [ofBits]
    have hm : x % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
    rw [ofBits_congr (g := bitAt (x % 2 ^ n)) (fun Q hQ => by rw [bitAt, bitAt, bit_mod_pow hQ]),
      ofBits_bitAt n _ hm]
    have hd : x / 2 ^ n < 2 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at h; omega
    unfold bitAt
    rw [Nat.mod_mod, Nat.mod_eq_of_lt hd]
    exact Nat.mod_add_div' x (2 ^ n)

/-- Setting a zero bit adds its power. -/
theorem ofBits_set {n P : ℕ} (hP : P < n) {f g : ℕ → ℕ} (hfg : ∀ Q < n, Q ≠ P → f Q % 2 = g Q % 2)
    (hf : f P % 2 = 0) (hg : g P % 2 = 1) : ofBits n g = ofBits n f + 2 ^ P := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [ofBits]
    rcases Nat.lt_or_ge P n with h | h
    · rw [ih h (fun Q hQ hne => hfg Q (by omega) hne), hfg n (by omega) (by omega)]; ring
    · have : P = n := by omega
      subst this
      rw [ofBits_congr (g := f) (fun Q hQ => (hfg Q (by omega) (by omega)).symm), hf, hg]; ring

/-! ### Physical and logical addresses -/

/-- A permutation of the bit positions `[0, n)` with inverse `τ`. -/
structure BitPerm (n : ℕ) where
  σ : ℕ → ℕ
  τ : ℕ → ℕ
  σ_lt : ∀ P < n, σ P < n
  τ_lt : ∀ Q < n, τ Q < n
  τσ : ∀ P < n, τ (σ P) = P
  στ : ∀ Q < n, σ (τ Q) = Q

/-- The logical address of the record at physical address `y`. -/
def BitPerm.logi {n : ℕ} (π : BitPerm n) (y : ℕ) : ℕ := ofBits n fun P => bitAt y (π.σ P)

/-- The physical address of the record with logical address `x`. -/
def BitPerm.phys {n : ℕ} (π : BitPerm n) (x : ℕ) : ℕ := ofBits n fun Q => bitAt x (π.τ Q)

theorem BitPerm.bitAt_logi {n : ℕ} (π : BitPerm n) (y : ℕ) {P : ℕ} (hP : P < n) :
    bitAt (π.logi y) P = bitAt y (π.σ P) := by
  rw [BitPerm.logi, bitAt_ofBits n _ P hP, Nat.mod_eq_of_lt (bitAt_lt_two _ _)]

theorem BitPerm.logi_lt {n : ℕ} (π : BitPerm n) (y : ℕ) : π.logi y < 2 ^ n := ofBits_lt _ _

theorem BitPerm.logi_phys {n : ℕ} (π : BitPerm n) {x : ℕ} (hx : x < 2 ^ n) : π.logi (π.phys x) = x := by
  unfold BitPerm.logi
  conv_rhs => rw [← ofBits_bitAt n x hx]
  apply ofBits_congr
  intro P hP
  rw [BitPerm.phys, bitAt_ofBits n _ _ (π.σ_lt P hP), π.τσ P hP, Nat.mod_mod]

theorem BitPerm.phys_lt {n : ℕ} (π : BitPerm n) (x : ℕ) : π.phys x < 2 ^ n := ofBits_lt _ _

theorem BitPerm.phys_logi {n : ℕ} (π : BitPerm n) {y : ℕ} (hy : y < 2 ^ n) : π.phys (π.logi y) = y := by
  unfold BitPerm.phys
  conv_rhs => rw [← ofBits_bitAt n y hy]
  apply ofBits_congr
  intro Q hQ
  rw [π.bitAt_logi y (π.τ_lt Q hQ), π.στ Q hQ]

theorem add_pow_lt {y Q n : ℕ} (hy : y < 2 ^ n) (hQ : Q < n) (h : bitAt y Q = 0) : y + 2 ^ Q < 2 ^ n := by
  have e : 2 ^ n = 2 ^ (n - Q - 1) * 2 ^ (Q + 1) := by rw [← pow_add]; congr 1; omega
  have h1 : y / 2 ^ (Q + 1) < 2 ^ (n - Q - 1) := by rw [Nat.div_lt_iff_lt_mul (by positivity), ← e]; exact hy
  rw [← div_succ_add h] at h1
  rw [e]; exact (Nat.div_lt_iff_lt_mul (by positivity)).mp h1

theorem BitPerm.logi_add {n : ℕ} (π : BitPerm n) {y P : ℕ} (hP : P < n) (h : bitAt y (π.σ P) = 0) :
    π.logi (y + 2 ^ π.σ P) = π.logi y + 2 ^ P := by
  unfold BitPerm.logi
  apply ofBits_set hP
  · intro Q hQ hne
    rw [Nat.mod_eq_of_lt (bitAt_lt_two _ _), Nat.mod_eq_of_lt (bitAt_lt_two _ _)]
    exact (bitAt_add_ne (fun e => hne (by rw [← π.τσ Q hQ, ← π.τσ P hP, e])) h).symm
  · rw [Nat.mod_eq_of_lt (bitAt_lt_two _ _)]; exact h
  · rw [bitAt_add_pow_self h]

theorem BitPerm.logi_sub {n : ℕ} (π : BitPerm n) {y P : ℕ} (hP : P < n) (h : bitAt y (π.σ P) ≠ 0) :
    π.logi (y - 2 ^ π.σ P) = π.logi y - 2 ^ P := by
  have h0 := bitAt_sub_pow_self h
  have e := π.logi_add hP h0
  rw [Nat.sub_add_cancel (le_of_bitAt h)] at e
  omega

/-! ### Rounds on the stored array -/

variable {r : ℕ} [NeZero r]

/-- Two arrays agree on the first `2^n` entries. -/
def Agree (n : ℕ) (w v : ℕ → Fin r → ℂ) : Prop := ∀ y < 2 ^ n, w y = v y

omit [NeZero r] in
theorem bfly_logi {n : ℕ} (π : BitPerm n) {P : ℕ} (hP : P < n) {w : ℕ → Fin r → ℂ} {z : ℕ → Fin r → ℂ}
    (h : Agree n w fun y => z (π.logi y)) : Agree n (bfly (π.σ P) w) fun y => bfly P z (π.logi y) := by
  intro y hy
  unfold bfly
  dsimp only
  rw [π.bitAt_logi y hP]
  split_ifs with hb
  · rw [h y hy, h (y + 2 ^ π.σ P) (add_pow_lt hy (π.σ_lt P hP) hb)]
    beta_reduce
    rw [π.logi_add hP hb]
  · have hle := le_of_bitAt hb
    rw [h y hy, h (y - 2 ^ π.σ P) (lt_of_le_of_lt (Nat.sub_le _ _) hy)]
    beta_reduce
    rw [π.logi_sub hP hb]

theorem twist_logi {n : ℕ} (π : BitPerm n) (f : ℕ → ℕ) {w z : ℕ → Fin r → ℂ}
    (h : Agree n w fun y => z (π.logi y)) :
    Agree n (twist (fun y => f (π.logi y)) w) fun y => twist f z (π.logi y) := by
  intro y hy
  simp only [twist, h y hy]

/-- A round of the schedule on physical bits. -/
noncomputable def physRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (i h : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  fun w => twist (fun y => rexp r (axOff ts i) h (π.logi y)) (bfly (π.σ (axOff ts i + h)) w)

theorem physRound_agree {n : ℕ} (π : BitPerm n) (ts : List ℕ) {i h : ℕ} (hih : axOff ts i + h < n)
    {w z : ℕ → Fin r → ℂ} (hw : Agree n w fun y => z (π.logi y)) :
    Agree n (physRound π ts i h w) fun y => axRound ts i h z (π.logi y) := by
  intro y hy
  unfold physRound axRound
  rw [difRoundAt_eq]
  exact twist_logi π _ (bfly_logi π hih hw) y hy

theorem run_physM {n : ℕ} (π : BitPerm n) (ts : List ℕ) (a : ℕ → ℕ) (hab : ∀ i < ts.length, ∀ h < a i, axOff ts i + h < n) :
    ∀ (D _H : ℕ), D ≤ ts.length → ∀ (sched : List (ℕ × ℕ)),
      (∀ p ∈ sched, p.1 < ts.length ∧ p.2 < a p.1) →
      ∀ (w z : ℕ → Fin r → ℂ), (Agree n w fun y => z (π.logi y)) →
        Agree n (run (sched.map fun p => physRound π ts p.1 p.2) w)
          fun y => run (sched.map fun p => axRound ts p.1 p.2) z (π.logi y)
  | _, _, _, [], _, w, z, hw => hw
  | D, H, hD, p :: sched, hs, w, z, hw => by
    simp only [List.map_cons, run]
    exact run_physM π ts a hab D H hD sched (fun q hq => hs q (by simp [hq])) _ _
      (physRound_agree π ts (hab _ (hs p (by simp)).1 _ (hs p (by simp)).2) hw)

/-- The paper's schedule as (axis, slot) pairs. -/
def slotPairs (ts : List ℕ) (H : ℕ) : List (ℕ × ℕ) :=
  (List.range H).reverse.flatMap fun h => ((List.range ts.length).filter fun i => h < axLen ts i).map fun i => (i, h)

theorem slotM_eq_pairs (ts : List ℕ) (H : ℕ) :
    slotM (axRound (r := r) ts) (axLen ts) ts.length H = (slotPairs ts H).map fun p => axRound ts p.1 p.2 := by
  simp [slotM, slotPairs, List.map_flatMap, List.map_map, Function.comp_def]

omit [NeZero r] in
theorem axOff_add_len_le {ts : List ℕ} (hts : PowAxes r ts) {i : ℕ} (hi : i < ts.length) :
    axOff ts i + axLen ts i ≤ Nat.log 2 ts.prod := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := ⟨ts.head (by rintro rfl; simp at hi), ts.tail, by simp⟩
    rw [log_prod_cons hts]
    simp [axOff, axLen]; omega
  · have h1 := axOff_le hts hpos hi
    have h2 : axOff ts 0 + axLen ts 0 ≤ Nat.log 2 ts.prod := by
      obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := ⟨ts.head (by rintro rfl; simp at hi), ts.tail, by simp⟩
      rw [log_prod_cons hts]
      simp [axOff, axLen]; omega
    omega

/-- `physSchedule_eq`: with the records stored in layout `π`, the paper's schedule on physical bits leaves,
at physical address `y`, the transform's entry at the bit-reversed logical address of `y`. -/
theorem physSchedule_eq {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n) (π : BitPerm n)
    {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (z : ℕ → Fin r → ℂ) {y : ℕ} (hy : y < 2 ^ n) :
    run ((slotPairs ts H).map fun p => physRound π ts p.1 p.2) (fun y => z (π.logi y)) y =
      fwdT ts z (bitrevAddr ts (π.logi y)) := by
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  have hab : ∀ i < ts.length, ∀ h < axLen ts i, axOff ts i + h < n := fun i hi h hh => by
    have := axOff_add_len_le hts hi; omega
  have ag := run_physM π ts (axLen ts) hab 0 0 (Nat.zero_le _) (slotPairs ts H)
    (fun p hp => by
      simp only [slotPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at hp
      obtain ⟨h, -, i, ⟨hi, hih⟩, rfl⟩ := hp
      exact ⟨hi, hih⟩)
    (fun y => z (π.logi y)) z (fun _ _ => rfl)
  rw [ag y hy, ← slotM_eq_pairs]
  exact slotMajor_eq hts hH z (by rw [hn]; exact π.logi_lt y)

end IntegerMultBounds.Schoenhage
