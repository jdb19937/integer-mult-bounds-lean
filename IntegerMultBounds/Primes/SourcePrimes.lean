module

public import IntegerMultBounds.Primes.WindowEmit
public import IntegerMultBounds.Primes.Moduli

/-!
# Emitting the prime source lengths

A table program for the prime source lengths `primeSrc d a R` of `Primes/Moduli.lean`.

* `winLoC`, `winLoC_do`: a seven-atom table program computing `winLo d t` from `t` and `d`.
* `ptSrcC`, `ptSrcC_do`: a table program that computes both lower window ends (`winLoC`) and
  emits all `d` source lengths in order, in the format of the parameter program:
  `(pmEmitList A w (primeSrc d a R) d).reverse` in front of the accumulator.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast.TableVM Finset

/-! ### The emission list -/

theorem pmEmitList_congr {A w : ℕ} {v v' : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, v i = v' i) :
    pmEmitList A w v m = pmEmitList A w v' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pmEmitList_succ, pmEmitList_succ, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem pmEmitList_add (A w : ℕ) (v : ℕ → ℕ) (a m : ℕ) :
    pmEmitList A w v (a + m) = pmEmitList A w v a ++ pmEmitList A w (fun j => v (a + j)) m := by
  induction m with
  | zero => simp [pmEmitList]
  | succ m ih => rw [← Nat.add_assoc, pmEmitList_succ, ih, pmEmitList_succ, List.append_assoc]

/-- The emission of the prime source lengths splits at `a`. -/
theorem pmEmitList_primeSrc (A w : ℕ) {d a : ℕ} (ha : a ≤ d) (R : ℕ) :
    pmEmitList A w (primeSrc d a R) d =
      pmEmitList A w (windowPrime (winLo d R)) a ++
        pmEmitList A w (windowPrime (winLo d (2 * R))) (d - a) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = a + m := ⟨d - a, by omega⟩
  rw [pmEmitList_add, Nat.add_sub_cancel_left]
  congr 1
  · exact pmEmitList_congr fun i hi => by simp [primeSrc, hi]
  · exact pmEmitList_congr fun j _ => by simp [primeSrc]

/-! ### The program -/

variable {A W w : ℕ}

/-- `lo := t - (t + 2d - 1)/(2d)`: `t` in `0`, `d` in `1`, `lo` in `2`; `2d` in `3`, `t + 2d - 1`
in `4`, the constant one in `5`, the quotient in `6`. -/
def winLoC : TblCode 7 :=
  tblBlock 7 [.add 1 1 3, .add 0 3 4, .zero 5, .inc 5, .sub 4 5 4, .div 4 3 6] (.sub 0 6 2)

/-- **The lower window end.** From `t` and `d ≥ 1`, with `t + 2d < 2^W`, register `2` ends as
`winLo d t`, in seven atoms. -/
theorem winLoC_do (st : TblSt 7 A) {t d : ℕ} (ht : st.val 0 = t) (hd : st.val 1 = d)
    (hd1 : 1 ≤ d) (hW : t + 2 * d < 2 ^ W) :
    TblDo A W w winLoC st (fun s => s.val 0 = t ∧ s.val 1 = d ∧ s.val 2 = winLo d t ∧
      s.acc = st.acc) 7 := by
  have hq := ceil_le_self (k := 2 * d) (by omega) t
  have hq' : (t + (d + d) - 1) / (d + d) ≤ t := by rwa [← two_mul]
  have hW1 : W ≠ 0 := by
    rintro rfl
    simp at hW
    omega
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, ht, hd, hq']
    omega
  · simp [tblExactList, TblIns.exact, ht, hd, winLo, winFloor, two_mul]

/-- The registers of `winLoC`: `t ↦ 12`, `d ↦ 10`, `lo ↦ 0`, scratch on `1 … 4`. -/
def ptLoReg : Fin 7 → Fin 14 := ![12, 10, 0, 1, 2, 3, 4]

/-- The registers of `ptEmitC`: `0 … 8`. -/
def ptSrcReg : Fin 9 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem ptLoReg_injective : Function.Injective ptLoReg := by decide

theorem ptSrcReg_injective : Function.Injective ptSrcReg := by decide

/-- Emit the prime source lengths: `R` in `9`, `d` in `10`, `a` in `11`, the current axis
length in `12`. -/
def ptSrcC : TblCode 14 :=
  .ins (.copy 9 12) ;; winLoC.rename ptLoReg ;; .ins (.copy 11 8) ;; ptEmitC.rename ptSrcReg ;;
    .ins (.add 9 9 12) ;; winLoC.rename ptLoReg ;; .ins (.sub 10 11 8) ;; ptEmitC.rename ptSrcReg

/-- The atoms of `ptSrcC`. -/
def ptSrcAtoms (d a R : ℕ) : ℕ :=
  1 + (7 + (1 + (ptEmitAtoms (winLo d R) (winHi d R) a + (1 + (7 + (1 +
    ptEmitAtoms (winLo d (2 * R)) (winHi d (2 * R)) (d - a)))))))

/-- The registers `9`, `10`, `11` hold `R`, `d`, `a`. -/
def PtKeep (R d a : ℕ) (s : TblSt 14 A) : Prop := s.val 9 = R ∧ s.val 10 = d ∧ s.val 11 = a

/-- **The prime source lengths.** From `R`, `d ≥ 1`, `a ≤ d`, when the window below `R` holds
at least `a` primes and the window below `2R` at least `d - a`, the program emits
`primeSrc d a R 0, …, primeSrc d a R (d - 1)` with words `6R + 4 < 2^W`, `2R + 2d < 2^W`. -/
theorem ptSrcC_do (st : TblSt 14 A) {R d a : ℕ} (hR : st.val 9 = R) (hd : st.val 10 = d)
    (ha : st.val 11 = a) (hd1 : 1 ≤ d) (had : a ≤ d)
    (h₁ : a ≤ ((Ioc (winLo d R) (winHi d R)).filter Nat.Prime).card)
    (h₂ : d - a ≤ ((Ioc (winLo d (2 * R)) (winHi d (2 * R))).filter Nat.Prime).card)
    (hW : 6 * R + 4 < 2 ^ W) (hWd : 2 * R + 2 * d < 2 ^ W) :
    TblDo A W w ptSrcC st (fun s => PtKeep R d a s ∧
      s.acc = (pmEmitList A w (primeSrc d a R) d).reverse ++ st.acc) (ptSrcAtoms d a R) := by
  have hhi₁ : winHi d R ≤ R := Nat.sub_le _ _
  have hhi₂ : winHi d (2 * R) ≤ 2 * R := Nat.sub_le _ _
  have hout_lo : ∀ x : Fin 14, x = 9 ∨ x = 11 ∨ (5 ≤ x.val ∧ x.val ≤ 8) ∨ x = 13 →
      ∀ y, ptLoReg y ≠ x := by
    intro x hx y
    fin_cases y <;> simp [ptLoReg] <;> omega
  have hout_src : ∀ x : Fin 14, 9 ≤ x.val → ∀ y, ptSrcReg y ≠ x := by
    intro x hx y
    fin_cases y <;> simp [ptSrcReg] <;> omega
  -- the lower window end of the axis length in register `12`
  have hlo : ∀ (s : TblSt 14 A) (T : ℕ), PtKeep R d a s → s.val 12 = T → T + 2 * d < 2 ^ W →
      TblDo A W w (winLoC.rename ptLoReg) s (fun s' => PtKeep R d a s' ∧ s'.val 0 = winLo d T ∧
        s'.acc = s.acc) 7 := by
    intro s T hk hT hTW
    refine (TblDo.rename ptLoReg_injective (winLoC_do (A := A) (W := W) (w := w)
      (s.restrict ptLoReg) (t := T) (d := d) (by simp [ptLoReg, hT]) (by simp [ptLoReg, hk.2.1])
      hd1 hTW)).mono ?_ le_rfl
    rintro s' ⟨⟨-, g1, g2, ga⟩, hrest⟩
    refine ⟨⟨?_, by simpa [ptLoReg] using g1, ?_⟩, by simpa [ptLoReg] using g2, by simpa using ga⟩
    · rw [hrest 9 (hout_lo 9 (by simp)), hk.1]
    · rw [hrest 11 (hout_lo 11 (by simp)), hk.2.2]
  -- the emission of `m` primes above register `0`
  have hem : ∀ (s : TblSt 14 A) (lo hi m : ℕ), PtKeep R d a s → s.val 0 = lo → s.val 8 = m →
      m ≤ ((Ioc lo hi).filter Nat.Prime).card → 3 * hi + 4 < 2 ^ W → m < 2 ^ W →
      TblDo A W w (ptEmitC.rename ptSrcReg) s (fun s' => PtKeep R d a s' ∧
        s'.acc = (pmEmitList A w (windowPrime lo) m).reverse ++ s.acc) (ptEmitAtoms lo hi m) := by
    intro s lo hi m hk h0 h8 hm hhW hmW
    refine (TblDo.rename ptSrcReg_injective (ptEmitC_do (A := A) (W := W) (w := w)
      (s.restrict ptSrcReg) (lo := lo) (hi := hi) (d := m) (by simp [ptSrcReg, h0])
      (by simp [ptSrcReg, h8]) hm hhW hmW)).mono ?_ le_rfl
    rintro s' ⟨⟨-, -, ga⟩, hrest⟩
    refine ⟨⟨?_, ?_, ?_⟩, by simpa using ga⟩
    · rw [hrest 9 (hout_src 9 (by simp)), hk.1]
    · rw [hrest 10 (hout_src 10 (by simp)), hk.2.1]
    · rw [hrest 11 (hout_src 11 (by simp)), hk.2.2]
  have hk0 : PtKeep R d a st := ⟨hR, hd, ha⟩
  -- 1: register `12 := R`
  refine (TblDo.ins (.copy 9 12) (P := fun s => PtKeep R d a s ∧ s.val 12 = R ∧
    s.acc = st.acc) ⟨by simp [PtKeep, TblIns.run, hR, hd, ha], by simp [TblIns.run, hR], rfl⟩).seq
    (fun s₁ ⟨k₁, r₁, a₁⟩ => ?_)
  -- 2: register `0 := winLo d R`
  refine (hlo s₁ R k₁ r₁ (by omega)).seq (fun s₂ ⟨k₂, r₂, a₂⟩ => ?_)
  -- 3: register `8 := a`
  refine (TblDo.ins (.copy 11 8) (P := fun s => PtKeep R d a s ∧ s.val 0 = winLo d R ∧
    s.val 8 = a ∧ s.acc = s₂.acc) ⟨?_, by simp [TblIns.run, r₂], by simp [TblIns.run, k₂.2.2],
      rfl⟩).seq (fun s₃ ⟨k₃, r₃, c₃, a₃⟩ => ?_)
  · obtain ⟨g9, g10, g11⟩ := k₂
    exact ⟨by simp [TblIns.run, g9], by simp [TblIns.run, g10], by simp [TblIns.run, g11]⟩
  -- 4: emit the first window
  refine (hem s₃ (winLo d R) (winHi d R) a k₃ r₃ c₃ h₁ (by omega) (by omega)).seq
    (fun s₄ ⟨k₄, a₄⟩ => ?_)
  -- 5: register `12 := 2R`
  refine (TblDo.insX (.add 9 9 12) (by show s₄.val 9 + s₄.val 9 < 2 ^ W; rw [k₄.1]; omega)
    (P := fun s => PtKeep R d a s ∧ s.val 12 = 2 * R ∧ s.acc = s₄.acc) ?_).seq
    (fun s₅ ⟨k₅, r₅, a₅⟩ => ?_)
  · obtain ⟨g9, g10, g11⟩ := k₄
    refine ⟨⟨by simp [TblIns.exact, g9], by simp [TblIns.exact, g10], by simp [TblIns.exact, g11]⟩,
      by simp [TblIns.exact, g9]; ring, rfl⟩
  -- 6: register `0 := winLo d (2R)`
  refine (hlo s₅ (2 * R) k₅ r₅ (by omega)).seq (fun s₆ ⟨k₆, r₆, a₆⟩ => ?_)
  -- 7: register `8 := d - a`
  refine (TblDo.insX (.sub 10 11 8) (by
      show s₆.val 11 ≤ s₆.val 10 ∧ s₆.val 10 < 2 ^ W
      rw [k₆.2.1, k₆.2.2]; omega)
    (P := fun s => PtKeep R d a s ∧ s.val 0 = winLo d (2 * R) ∧ s.val 8 = d - a ∧
      s.acc = s₆.acc) ?_).seq (fun s₇ ⟨k₇, r₇, c₇, a₇⟩ => ?_)
  · obtain ⟨g9, g10, g11⟩ := k₆
    exact ⟨⟨by simp [TblIns.exact, g9], by simp [TblIns.exact, g10], by simp [TblIns.exact, g11]⟩,
      by simp [TblIns.exact, r₆], by simp [TblIns.exact, g10, g11], rfl⟩
  -- 8: emit the second window
  refine (hem s₇ (winLo d (2 * R)) (winHi d (2 * R)) (d - a) k₇ r₇ c₇ h₂ (by omega)
    (by omega)).mono ?_ le_rfl
  rintro s₈ ⟨k₈, a₈⟩
  refine ⟨k₈, ?_⟩
  rw [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, pmEmitList_primeSrc A w had R, List.reverse_append,
    List.append_assoc]

end IntegerMultBounds.Primes
