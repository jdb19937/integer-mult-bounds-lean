module

public import IntegerMultBounds.Primes.NextPrime
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-!
# Trial division and the next prime on the table machine

Two table programs on seven registers.

* `ptPrimeC`: with `x` in register `0`, register `1` ends as `1` if `x` is prime and `0`
  otherwise, after one trial division by each `y` with `2 ≤ y ≤ ⌊√x⌋`. It uses
  `ptPrimeAtoms x = 13 + 7 (⌊√x⌋ - 1)` atoms and words with `3x + 4 < 2^W` (`ptPrimeC_do`).
* `ptNextC`: register `0` steps from `x` to `nextPrimeAfter x`, testing each candidate with
  `ptPrimeC`. It uses `ptNextAtoms x` atoms and words with `3 nextPrimeAfter x + 4 < 2^W`
  (`ptNextC_do`).

The registers are `x` (0), the flag (1), the divisor `y` (2), `y²` (3), `x + 1` (4), the
remainder (5) and the constant one (6). The loop of `ptPrimeC` runs `⌊√x⌋ - 1` times, with no
early exit; `TrialOk x m` records that no `z ∈ [2, m)` divides `x`, and
`TrialOk x (⌊√x⌋ + 1) ↔ x.Prime` (`trialOk_sqrt`).
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! ### Trial division -/

/-- `2 ≤ x`, and no `z ∈ [2, m)` divides `x`. -/
def TrialOk (x m : ℕ) : Prop := 2 ≤ x ∧ ∀ z, 2 ≤ z → z < m → ¬ z ∣ x

theorem trialOk_two {x : ℕ} : TrialOk x 2 ↔ 2 ≤ x :=
  ⟨fun h => h.1, fun h => ⟨h, fun z hz hz2 => absurd hz2 (by omega)⟩⟩

theorem trialOk_succ {x m : ℕ} (hm : 2 ≤ m) : TrialOk x (m + 1) ↔ TrialOk x m ∧ ¬ m ∣ x := by
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨⟨h2, fun z hz hzm => h z hz (by omega)⟩, h m hm (by omega)⟩
  · rintro ⟨⟨h2, h⟩, hm'⟩
    refine ⟨h2, fun z hz hzm => ?_⟩
    rcases Nat.lt_or_ge z m with hlt | hge
    · exact h z hz hlt
    · obtain rfl : z = m := by omega
      exact hm'

theorem trialOk_sqrt {x : ℕ} : TrialOk x (Nat.sqrt x + 1) ↔ x.Prime := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hms => h m hm (by omega)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun z hz hzs => h z hz (by omega)⟩

theorem trialOk_zero (m : ℕ) : ¬ TrialOk 0 m := fun h => absurd h.1 (by omega)

theorem sqrt_succ_sq_le (x : ℕ) : (Nat.sqrt x + 1) * (Nat.sqrt x + 1) ≤ 3 * x + 1 := by
  have h1 := Nat.sqrt_le x
  have h2 := Nat.sqrt_le_self x
  nlinarith

variable {A W w : ℕ}

/-- Trial division of register `0`; register `1` ends as the primality flag. -/
def ptPrimeC : TblCode 7 :=
  tblBlock 7 [.zero 6, .inc 6, .copy 0 4, .inc 4, .zero 2, .inc 2, .inc 2, .mul 2 2 3] (.zero 1) ;;
    .ite 6 0 (.ins (.inc 1)) (.ins (.zero 5)) ;;
      .loop 3 4 (.ins (.mod 0 2 5) ;; .ite 5 6 (.ins (.zero 1)) (.ins (.zero 5)) ;;
        tblBlock 7 [.inc 2] (.mul 2 2 3))

/-- The atoms of `ptPrimeC` on `x`. -/
def ptPrimeAtoms (x : ℕ) : ℕ := 13 + 7 * (Nat.sqrt x - 1)

theorem ptPrimeAtoms_mono {x y : ℕ} (h : x ≤ y) : ptPrimeAtoms x ≤ ptPrimeAtoms y := by
  have := Nat.sqrt_le_sqrt h
  unfold ptPrimeAtoms
  omega

/-- The state of `ptPrimeC` before the trial division by `j + 2`. -/
def PtInv (x : ℕ) (acc : List (Fin (A + 4))) (j : ℕ) (s : TblSt 7 A) : Prop :=
  s.val 0 = x ∧ (s.val 1 = 1 ↔ TrialOk x (j + 2)) ∧ s.val 1 ≤ 1 ∧ s.val 2 = j + 2 ∧
    s.val 3 = (j + 2) * (j + 2) ∧ s.val 4 = x + 1 ∧ s.val 6 = 1 ∧ s.acc = acc

/-- **Trial division.** Register `1` ends as `1` exactly when `x` is prime; registers `0` and
`6` hold `x` and `1`. -/
theorem ptPrimeC_do (st : TblSt 7 A) {x : ℕ} (hx : st.val 0 = x) (hW : 3 * x + 4 < 2 ^ W) :
    TblDo A W w ptPrimeC st (fun s => s.val 0 = x ∧ s.val 1 = (if x.Prime then 1 else 0) ∧
      s.val 6 = 1 ∧ s.acc = st.acc) (ptPrimeAtoms x) := by
  set N := Nat.sqrt x - 1 with hN
  have hsq := sqrt_succ_sq_le x
  have hW1 : W ≠ 0 := by
    rintro rfl
    norm_num at hW
  have hblock : TblDo A W w
      (tblBlock 7 [.zero 6, .inc 6, .copy 0 4, .inc 4, .zero 2, .inc 2, .inc 2, .mul 2 2 3]
        (.zero 1)) st
      (fun s => s.val 0 = x ∧ s.val 1 = 0 ∧ s.val 2 = 2 ∧ s.val 3 = 4 ∧ s.val 4 = x + 1 ∧
        s.val 6 = 1 ∧ s.acc = st.acc) 9 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hx]
      omega
    · simp [tblExactList, TblIns.exact, hx]
  refine (hblock.seq (K₂ := 2 + (N * (5 + 2) + 2)) (fun s₁ ⟨h0, h1, h2, h3, h4, h6, ha⟩ => ?_)).mono
    (fun _ h => h) (by unfold ptPrimeAtoms; omega)
  have hite : TblDo A W w (.ite 6 0 (.ins (.inc 1)) (.ins (.zero 5))) s₁
      (PtInv x st.acc 0) 2 := by
    by_cases hx2 : 1 < x
    · refine TblDo.iteT (by rw [h6, h0]; exact hx2)
        (TblDo.insX (.inc 1) (by show s₁.val 1 + 1 < 2 ^ W; rw [h1]; omega) ?_)
      simp only [PtInv, TblIns.exact, Function.update_apply]
      simp [h0, h1, h2, h3, h4, h6, ha, trialOk_two]
      omega
    · refine TblDo.iteF (by rw [h6, h0]; exact hx2) (TblDo.ins (.zero 5) ?_)
      simp only [PtInv, TblIns.run, Function.update_apply]
      simp [h0, h1, h2, h3, h4, h6, ha, trialOk_two]
      omega
  refine hite.seq (K₂ := N * (5 + 2) + 2) (fun s₂ hs₂ => ?_)
  refine TblDo.loop (PtInv x st.acc) N 5 hs₂ ?_ ?_
  · rintro j hj s ⟨e0, e1, e1le, e2, e3, e4, e6, ea⟩
    have hjs : j + 2 ≤ Nat.sqrt x := by omega
    have hjx : (j + 2) * (j + 2) ≤ x := Nat.le_sqrt.mp hjs
    have hj3 : (j + 3) * (j + 3) ≤ 3 * x + 1 :=
      (Nat.mul_le_mul (by omega : j + 3 ≤ Nat.sqrt x + 1) (by omega)).trans hsq
    refine ⟨by rw [e3, e4]; omega, ?_⟩
    refine (TblDo.ins (.mod 0 2 5) (P := fun s' => s' = TblIns.run A W w (.mod 0 2 5) s) rfl).seq
      (K₂ := 4) (fun s₃ hs₃ => ?_)
    subst hs₃
    have f0 : (TblIns.run A W w (.mod 0 2 5) s).val 0 = x := by simp [TblIns.run, e0]
    have f5 : (TblIns.run A W w (.mod 0 2 5) s).val 5 = x % (j + 2) := by
      simp [TblIns.run, e0, e2]
    have f6 : (TblIns.run A W w (.mod 0 2 5) s).val 6 = 1 := by simp [TblIns.run, e6]
    have hsx := Nat.sqrt_le_self x
    have htail : ∀ s₄ : TblSt 7 A, s₄.val 0 = x → (s₄.val 1 = 1 ↔ TrialOk x (j + 1 + 2)) →
        s₄.val 1 ≤ 1 → s₄.val 2 = j + 2 → s₄.val 4 = x + 1 → s₄.val 6 = 1 → s₄.acc = st.acc →
        TblDo A W w (tblBlock 7 [.inc 2] (.mul 2 2 3)) s₄ (PtInv x st.acc (j + 1)) 2 := by
      intro s₄ g0 g1 g1le g2 g4 g6 ga
      show TblDo A W w (.seq (.ins (.inc 2)) (.ins (.mul 2 2 3))) s₄ _ (1 + 1)
      refine (TblDo.insX (.inc 2) (by show s₄.val 2 + 1 < 2 ^ W; rw [g2]; omega)
        (P := fun s' => s' = TblIns.exact A w (.inc 2) s₄) rfl).seq (K₂ := 1) (fun s₅ hs₅ => ?_)
      subst hs₅
      have k2 : (TblIns.exact A w (.inc 2) s₄).val 2 = j + 3 := by simp [TblIns.exact, g2]
      refine TblDo.insX (.mul 2 2 3)
        (by show (TblIns.exact A w (.inc 2) s₄).val 2 * (TblIns.exact A w (.inc 2) s₄).val 2 < 2 ^ W
            rw [k2]; omega) ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [TblIns.exact, g0]
      · simpa [TblIns.exact] using g1
      · simpa [TblIns.exact] using g1le
      · simp [TblIns.exact, g2]
      · simp [TblIns.exact, g2]
      · simp [TblIns.exact, g4]
      · simp [TblIns.exact, g6]
      · simp [TblIns.exact, ga]
    refine TblDo.seq (K₁ := 2) (K₂ := 2)
      (P₁ := fun s₄ => s₄.val 0 = x ∧ (s₄.val 1 = 1 ↔ TrialOk x (j + 1 + 2)) ∧ s₄.val 1 ≤ 1 ∧
        s₄.val 2 = j + 2 ∧ s₄.val 4 = x + 1 ∧ s₄.val 6 = 1 ∧ s₄.acc = st.acc) ?_
      (fun s₄ ⟨g0, g1, g1le, g2, g4, g6, ga⟩ => htail s₄ g0 g1 g1le g2 g4 g6 ga)
    by_cases hdiv : x % (j + 2) < 1
    · have hd : (j + 2) ∣ x := Nat.dvd_of_mod_eq_zero (by omega)
      refine TblDo.iteT (by rw [f5, f6]; exact hdiv) (TblDo.ins (.zero 1) ?_)
      refine ⟨by simp [TblIns.run, e0], ?_, by simp [TblIns.run], by simp [TblIns.run, e2],
        by simp [TblIns.run, e4], by simp [TblIns.run, e6], by simp [TblIns.run, ea]⟩
      have hno : ¬ TrialOk x (j + 1 + 2) := by
        rw [show j + 1 + 2 = (j + 2) + 1 by ring, trialOk_succ (by omega)]
        exact fun h => h.2 hd
      simp [TblIns.run, hno]
    · have hnd : ¬ (j + 2) ∣ x := fun hd => hdiv (by rw [Nat.mod_eq_zero_of_dvd hd]; omega)
      refine TblDo.iteF (by rw [f5, f6]; exact hdiv) (TblDo.ins (.zero 5) ?_)
      refine ⟨by simp [TblIns.run, e0], ?_, by simp [TblIns.run, e1le], by simp [TblIns.run, e2],
        by simp [TblIns.run, e4], by simp [TblIns.run, e6], by simp [TblIns.run, ea]⟩
      have hiff : TrialOk x (j + 1 + 2) ↔ TrialOk x (j + 2) := by
        rw [show j + 1 + 2 = (j + 2) + 1 by ring, trialOk_succ (by omega)]
        exact ⟨fun h => h.1, fun h => ⟨h, hnd⟩⟩
      simp only [TblIns.run, Function.update_apply]
      simp [e1, hiff]
  · rintro s ⟨e0, e1, e1le, e2, e3, e4, e6, ea⟩
    have hlt : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
    have hle : Nat.sqrt x + 1 ≤ N + 2 := by omega
    have hsqN : (Nat.sqrt x + 1) * (Nat.sqrt x + 1) ≤ (N + 2) * (N + 2) := Nat.mul_le_mul hle hle
    refine ⟨by rw [e3, e4]; omega, e0, ?_, e6, ea⟩
    have hprime : TrialOk x (N + 2) ↔ x.Prime := by
      rcases Nat.eq_zero_or_pos x with hx0 | hx0
      · subst hx0
        exact ⟨fun h => absurd h (trialOk_zero _), fun h => absurd h Nat.not_prime_zero⟩
      · have : N + 2 = Nat.sqrt x + 1 := by
          have : 1 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
          omega
        rw [this]
        exact trialOk_sqrt
    rw [hprime] at e1
    split_ifs with hp
    · exact e1.mpr hp
    · have : s.val 1 ≠ 1 := fun h => hp (e1.mp h)
      omega

/-! ### The next prime -/

/-- Register `0` steps to the least prime above it. -/
def ptNextC : TblCode 7 :=
  tblBlock 7 [.zero 1, .zero 6] (.inc 6) ;; .loop 1 6 (.ins (.inc 0) ;; ptPrimeC)

/-- The atoms of `ptNextC` from `x`. -/
def ptNextAtoms (x : ℕ) : ℕ :=
  3 + ((nextPrimeAfter x - x) * (1 + ptPrimeAtoms (nextPrimeAfter x) + 2) + 2)

/-- **The next prime.** Register `0` steps from `x` to `nextPrimeAfter x`, register `6` holds
`1`, and the accumulator is unchanged. -/
theorem ptNextC_do (st : TblSt 7 A) {x : ℕ} (hx : st.val 0 = x)
    (hW : 3 * nextPrimeAfter x + 4 < 2 ^ W) :
    TblDo A W w ptNextC st (fun s => s.val 0 = nextPrimeAfter x ∧ s.val 6 = 1 ∧
      s.acc = st.acc) (ptNextAtoms x) := by
  have hxp : x < nextPrimeAfter x := lt_nextPrimeAfter x
  have hW1 : W ≠ 0 := by
    rintro rfl
    norm_num at hW
  have hblock : TblDo A W w (tblBlock 7 [.zero 1, .zero 6] (.inc 6)) st
      (fun s => s.val 0 = x ∧ s.val 1 = 0 ∧ s.val 6 = 1 ∧ s.acc = st.acc) 3 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact]
      omega
    · simp [tblExactList, TblIns.exact, hx]
  refine hblock.seq
    (K₂ := (nextPrimeAfter x - x) * (1 + ptPrimeAtoms (nextPrimeAfter x) + 2) + 2)
    (fun s₁ ⟨h0, h1, h6, ha⟩ => ?_)
  refine TblDo.loop (fun j s => s.val 0 = x + j ∧ s.val 6 = 1 ∧
      s.val 1 = (if 0 < j ∧ (x + j).Prime then 1 else 0) ∧ s.acc = st.acc) (nextPrimeAfter x - x)
      (1 + ptPrimeAtoms (nextPrimeAfter x)) ⟨by rw [h0]; rfl, h6, by simp [h1], ha⟩ ?_ ?_
  · rintro j hj s ⟨e0, e6, e1, ea⟩
    have hj' : j + x < nextPrimeAfter x := Nat.lt_sub_iff_add_lt.mp hj
    have hfalse : ¬ (0 < j ∧ (x + j).Prime) := by
      rintro ⟨hj0, hpr⟩
      exact not_prime_of_lt_nextPrimeAfter (x := x) (by omega) (by omega) hpr
    refine ⟨by rw [e1, e6]; simp [hfalse], ?_⟩
    have hfit : x + j + 1 < 2 ^ W := by omega
    refine (TblDo.insX (.inc 0) (by show s.val 0 + 1 < 2 ^ W; rw [e0]; omega)
      (P := fun s' => s' = TblIns.exact A w (.inc 0) s) rfl).seq (fun s₂ hs₂ => ?_)
    subst hs₂
    have g0 : (TblIns.exact A w (.inc 0) s).val 0 = x + j + 1 := by simp [TblIns.exact, e0]
    refine (ptPrimeC_do (TblIns.exact A w (.inc 0) s) g0 (by omega)).mono ?_
      (ptPrimeAtoms_mono (by omega))
    rintro s' ⟨f0, f1, f6, fa⟩
    refine ⟨by rw [f0]; ring, f6, ?_, by rw [fa]; simp [TblIns.exact, ea]⟩
    rw [f1]
    have : x + (j + 1) = x + j + 1 := by ring
    simp [this]
  · rintro s ⟨e0, e6, e1, ea⟩
    have hxN : x + (nextPrimeAfter x - x) = nextPrimeAfter x := by omega
    have hpos : 0 < nextPrimeAfter x - x := by omega
    have hpr : (x + (nextPrimeAfter x - x)).Prime := by rw [hxN]; exact nextPrimeAfter_prime x
    refine ⟨by rw [e1, e6]; simp [hpos, hpr], by rw [e0, hxN], e6, ea⟩

end IntegerMultBounds.Primes
