module

public import IntegerMultBounds.MathlibTM2.Fast.ParamMath
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-!
# Small parameter programs

Table programs (`TblCode`) on a few variables, each with a `TblDo` contract in exact natural
arithmetic: the output variable ends holding the stated value, the input variables and `acc`
are kept, and the atom count is explicit. `Fast/ParamProg.lean` renames them into the parameter
machine (`TblCode.rename`, `TblDo.rename`).

* Searches and loops:
  * `pmClogC`: `c := ⌈log₂ x⌉` by doubling, `4 ⌈log₂ x⌉ + 5` atoms.
  * `pmIrootC k`: `y := iroot (2^k) x`, the largest `y` with `y^(2^k) ≤ x`, by a linear search
    whose test `(y + 1)^(2^k) ≤ x` runs `k` capped squarings `z ↦ min (z²) (x + 1)`
    (`pmCapPowC`, `pmSqStepC`), so every value stays at most `(x + 1)²`;
    `7 k + 11 + iroot (2^k) x · (6 k + 8)` atoms.
  * `pmQuartC`: the least `a` with `t ≤ a^4` (`PmQuart`), `5 a + 4` atoms.
  * `pmSqrtC`: `y := ⌊√x⌋`, `6 ⌊√x⌋ + 7` atoms.
  * `pmOddC`: `N := oddProd d`, `12 d + 6` atoms.
  * `pmModC`: one source length `Moduli.modulus N x₀ a i`, `9` atoms; `pmProdSC`:
    `∏_{i < d} modulus N x₀ a i` (`pmSProd`), `13 d + 5` atoms.
  * Emission: `pmEmitTC` emits the axis lengths `pmTv a R r i` (`R` below `a`, `r` above),
    `6 d + 3` atoms; `pmEmitSC` emits the source lengths, `13 d + 3` atoms. Each value goes out
    as `w` pair symbols with equal parts (`pmEmitList`).
* Straight-line forms: `pmLinC k₁ k₂` (`k₁ (a + k₂)`), `pmLin2C k₁ k₂` (`k₁ (a + b + k₂)`),
  `pmCeilDivC k` (`(k a + b - 1) / b`), `pmSubKC k` (`a - k`), `pmMulSubC` (`a b - c`),
  `pmSqC` (`a²`), `pmGammaC` (`d (2 a + 2)`), `pmStartC` (`Moduli.start d N R`).
* Composite forms: `pmLogTC` (`⌈log₂ ((4 n + b - 1) / b)⌉`), `pmAlphaC` (the least `α` with
  `12 d² b ≤ α^4`), `pmClogAddC k` (`⌈log₂ x⌉ + k`), `pmWinAC` (`⌊√(p a)⌋ + 1`), `pmWinBC`
  (`⌊√p⌋ / (2 a) + 1`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli Finset


variable {A W w : ℕ}

theorem pm_W_ne {W : ℕ} (h : 2 ≤ 2 ^ W) : W ≠ 0 := by
  rintro rfl; simp at h

/-- The length of a straight-line block with constant loads. -/
macro "pm_len" : tactic => `(tactic| (simp only [List.length_append, length_tblConstL,
  List.length_cons, List.length_nil] <;> omega))

/-! ### `⌈log₂ x⌉` -/

/-- `c := ⌈log₂ x⌉`: `x` in `0`, `c` in `1`, the power `2^c` in `2`. -/
def pmClogC : TblCode 3 :=
  tblBlock 3 [.zero 1, .zero 2] (.inc 2) ;; .loop 2 0 (tblBlock 3 [.add 2 2 2] (.inc 1))

theorem pmClogC_do (st : TblSt 3 A) {x : ℕ} (hx : st.val 0 = x) (hW : 2 * x + 2 ≤ 2 ^ W) :
    TblDo A W w pmClogC st (fun s => s.val 0 = x ∧ s.val 1 = Nat.clog 2 x ∧ s.acc = st.acc)
      (4 * Nat.clog 2 x + 5) := by
  set N := Nat.clog 2 x
  have hW0 : W ≠ 0 := pm_W_ne (by omega)
  have hblock : TblDo A W w (tblBlock 3 [.zero 1, .zero 2] (.inc 2)) st
      (fun s => s.val 0 = x ∧ s.val 1 = 0 ∧ s.val 2 = 1 ∧ s.acc = st.acc) 3 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact]; omega
    · simp [tblExactList, TblIns.exact, hx]
  refine (hblock.seq (K₂ := N * (2 + 2) + 2) (fun s ⟨h0, h1, h2, ha⟩ => ?_)).mono (fun _ h => h)
    (le_of_eq (by ring))
  refine TblDo.loop (fun j s => s.val 0 = x ∧ s.val 1 = j ∧ s.val 2 = 2 ^ j ∧ s.acc = st.acc) N 2
    ⟨h0, h1, by simp [h2], ha⟩ ?_ ?_
  · intro j hj s ⟨h0, h1, h2, ha⟩
    have hp := pm_pow_lt_of_lt_clog hj
    have hj' : j < 2 ^ j := Nat.lt_two_pow_self
    refine ⟨by rw [h2, h0]; exact hp, TblDo.block _ _ ?_ ?_⟩
    · simp [tblFitsList, TblIns.fits, TblIns.exact, h1, h2]; omega
    · simp [tblExactList, TblIns.exact, h0, h1, h2, ha, pow_succ]; ring
  · intro s ⟨h0, h1, h2, ha⟩
    have : x ≤ 2 ^ N := Nat.le_pow_clog one_lt_two x
    exact ⟨by rw [h2, h0]; omega, h0, h1, ha⟩

/-! ### Integer roots by capped squaring -/

/-- One capped squaring of variable `3` against the cap in `2`: `z := min (z²) c`. -/
def pmSqStepC : TblCode 6 := .ins (.mul 3 3 3) ;; .ite 2 3 (.ins (.copy 2 3)) (.ins (.copy 3 3))

theorem pmSqStepC_do (s : TblSt 6 A) {c z : ℕ} (hc : s.val 2 = c) (hz : s.val 3 = z)
    (hzc : z ≤ c) (hW : c * c < 2 ^ W) :
    TblDo A W w pmSqStepC s (fun s' => s'.val 3 = pmSq c z ∧
      (∀ i, i ≠ 3 → s'.val i = s.val i) ∧ s'.acc = s.acc) 3 := by
  have hzz : z * z ≤ c * c := Nat.mul_le_mul hzc hzc
  refine ((TblDo.insX (W := W) (w := w) (.mul 3 3 3) (by simp [TblIns.fits, hz]; omega)
    (P := fun s' => s' = TblIns.exact A w (.mul 3 3 3) s) rfl).seq (K₂ := 2)
      (fun s₁ hs₁ => ?_)).mono (fun _ h => h) le_rfl
  subst hs₁
  have hv2 : (TblIns.exact A w (.mul 3 3 3) s).val 2 = c := by simp [TblIns.exact, hc]
  have hv3 : (TblIns.exact A w (.mul 3 3 3) s).val 3 = z * z := by simp [TblIns.exact, hz]
  by_cases hlt : c < z * z
  · refine TblDo.iteT (by rw [hv2, hv3]; exact hlt) (TblDo.insX _ trivial ?_)
    refine ⟨?_, fun i hi => ?_, by simp [TblIns.exact]⟩
    · simp [TblIns.exact, hc, pmSq]; omega
    · simp [TblIns.exact, Function.update_of_ne hi]
  · refine TblDo.iteF (by rw [hv2, hv3]; exact hlt) (TblDo.insX _ trivial ?_)
    refine ⟨?_, fun i hi => ?_, by simp [TblIns.exact]⟩
    · simp [TblIns.exact, hz, pmSq]; omega
    · simp [TblIns.exact, Function.update_of_ne hi]

/-- `z := min ((y + 1)^(2^k)) c`, with `y` in `1`, `c` in `2`, `z` in `3`, the counter in `4` and
`k` in `5`. -/
def pmCapPowC : TblCode 6 := tblBlock 6 [.copy 1 3] (.inc 3) ;; tblFor 4 5 pmSqStepC

theorem pmCapPowC_do (s : TblSt 6 A) {y c k : ℕ} (hy : s.val 1 = y) (hc : s.val 2 = c)
    (hk : s.val 5 = k) (hyc : y + 1 ≤ c) (hW : c * c < 2 ^ W) (hkW : k < 2 ^ W) :
    TblDo A W w pmCapPowC s (fun s' => s'.val 3 = min ((y + 1) ^ 2 ^ k) c ∧
      (∀ i, i ≠ 3 → i ≠ 4 → s'.val i = s.val i) ∧ s'.acc = s.acc) (6 * k + 5) := by
  have hcc : c ≤ c * c := Nat.le_mul_self c
  have hblock : TblDo A W w (tblBlock 6 [.copy 1 3] (.inc 3)) s
      (fun s' => s'.val 3 = y + 1 ∧ (∀ i, i ≠ 3 → s'.val i = s.val i) ∧ s'.acc = s.acc) 2 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hy]; omega
    · refine ⟨by simp [tblExactList, TblIns.exact, hy], fun i hi => ?_, by
        simp [tblExactList, TblIns.exact]⟩
      simp [tblExactList, TblIns.exact, Function.update_of_ne hi]
  refine (hblock.seq (K₂ := 1 + (k * (3 + 1 + 2) + 2)) (fun s₁ ⟨h3, hfr, ha⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  have hk₁ : s₁.val 5 = k := by rw [hfr 5 (by decide), hk]
  refine TblDo.for k 3 hk₁ hkW (by decide)
    (fun j s' => s'.val 3 = (pmSq c)^[j] (y + 1) ∧ (∀ i, i ≠ 3 → i ≠ 4 → s'.val i = s.val i) ∧
      s'.acc = s.acc) ⟨?_, fun i hi3 hi4 => ?_, ha⟩ ?_ ?_
  · simp [h3]
  · simp [Function.update_of_ne hi4, hfr i hi3]
  · intro j hj s' ⟨hz, hfr', ha'⟩ hi hn
    have hc' : s'.val 2 = c := by rw [hfr' 2 (by decide) (by decide), hc]
    refine (pmSqStepC_do s' hc' hz (pmSq_iter_le (by omega) j) hW).mono ?_ le_rfl
    rintro s'' ⟨h3'', hfr'', ha''⟩
    refine ⟨by rw [hfr'' 4 (by decide), hi], by rw [hfr'' 5 (by decide), hn], ?_, fun i hi3 hi4 => ?_,
      by simp [ha'', ha']⟩
    · simp [h3'',
        Function.iterate_succ_apply']
    · simp [Function.update_of_ne hi4, hfr'' i hi3, hfr' i hi3 hi4]
  · rintro s' ⟨hz, hfr', ha'⟩ - -
    exact ⟨by rw [hz, pmSq_iter (by omega)], hfr', ha'⟩

/-- `y := iroot (2^k) x`: `x` in `0`, `y` in `1`, `x + 1` in `2`, the capped power in `3`, the
counter in `4`, `k` in `5`. The search runs while `(y + 1)^(2^k) ≤ x`. -/
def pmIrootC (k : ℕ) : TblCode 6 :=
  tblBlock 6 ([.copy 0 2, .inc 2] ++ tblConstL 5 k) (.zero 1) ;; pmCapPowC ;;
    .loop 3 2 (.ins (.inc 1) ;; pmCapPowC)

theorem pmIrootC_do (k : ℕ) (st : TblSt 6 A) {x : ℕ} (hx : st.val 0 = x)
    (hW : (x + 1) * (x + 1) < 2 ^ W) (hkW : k < 2 ^ W) :
    TblDo A W w (pmIrootC k) st (fun s => s.val 0 = x ∧ s.val 1 = iroot (2 ^ k) x ∧
      s.acc = st.acc) (7 * k + 11 + iroot (2 ^ k) x * (6 * k + 8)) := by
  set N := iroot (2 ^ k) x
  have hNx : N ≤ x := iroot_le_self (by positivity) x
  have hx1 : x + 1 ≤ (x + 1) * (x + 1) := Nat.le_mul_self _
  have hblock : TblDo A W w (tblBlock 6 ([.copy 0 2, .inc 2] ++ tblConstL 5 k) (.zero 1)) st
      (fun s => s.val 0 = x ∧ s.val 1 = 0 ∧ s.val 2 = x + 1 ∧ s.val 5 = k ∧ s.acc = st.acc)
      (k + 4) := by
    refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
      (by pm_len)
    · rw [List.append_assoc]
      refine tblFitsList_append _ _ _ (by simp [tblFitsList, TblIns.fits, TblIns.exact, hx]; omega) ?_
      refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ hkW) ?_
      simp [tblFitsList, TblIns.fits]
    · rw [List.append_assoc, tblExactList_append, tblExactList_append, tblExactList_const]
      simp [tblExactList, TblIns.exact, hx]
  refine (hblock.seq (K₂ := (6 * k + 5) + (N * ((1 + (6 * k + 5)) + 2) + 2))
    (fun s₁ ⟨h0, h1, h2, h5, ha⟩ => ?_)).mono (fun _ h => h) (le_of_eq (by ring))
  refine (pmCapPowC_do s₁ h1 h2 h5 (by omega) hW hkW).seq (fun s₂ ⟨h3, hfr, ha₂⟩ => ?_)
  have Inv0 : s₂.val 0 = x ∧ s₂.val 1 = 0 ∧ s₂.val 2 = x + 1 ∧ s₂.val 5 = k ∧
      s₂.val 3 = min ((0 + 1) ^ 2 ^ k) (x + 1) ∧ s₂.acc = st.acc :=
    ⟨by rw [hfr 0 (by decide) (by decide), h0], by rw [hfr 1 (by decide) (by decide), h1],
      by rw [hfr 2 (by decide) (by decide), h2], by rw [hfr 5 (by decide) (by decide), h5],
      by rw [h3], by rw [ha₂, ha]⟩
  refine TblDo.loop (fun j s => s.val 0 = x ∧ s.val 1 = j ∧ s.val 2 = x + 1 ∧ s.val 5 = k ∧
      s.val 3 = min ((j + 1) ^ 2 ^ k) (x + 1) ∧ s.acc = st.acc) N (1 + (6 * k + 5)) Inv0 ?_ ?_
  · rintro j hj s ⟨h0, h1, h2, h5, h3, ha⟩
    have hpow : (j + 1) ^ 2 ^ k ≤ x := pm_pow_le_of_iroot (by positivity) hj
    refine ⟨by rw [h3, h2]; omega, ?_⟩
    refine (TblDo.insX (W := W) (w := w) (.inc 1) (by simp [TblIns.fits, h1]; omega)
      (P := fun s' => s' = TblIns.exact A w (.inc 1) s) rfl).seq (fun s₁ hs₁ => ?_)
    subst hs₁
    have e1 : (TblIns.exact A w (.inc 1) s).val 1 = j + 1 := by simp [TblIns.exact, h1]
    have e2 : (TblIns.exact A w (.inc 1) s).val 2 = x + 1 := by simp [TblIns.exact, h2]
    have e5 : (TblIns.exact A w (.inc 1) s).val 5 = k := by simp [TblIns.exact, h5]
    refine (pmCapPowC_do _ e1 e2 e5 (by omega) hW hkW).mono ?_ le_rfl
    rintro s' ⟨h3', hfr', ha'⟩
    refine ⟨?_, ?_, by rw [hfr' 2 (by decide) (by decide), e2],
      by rw [hfr' 5 (by decide) (by decide), e5], h3', by rw [ha']; simp [TblIns.exact, ha]⟩
    · rw [hfr' 0 (by decide) (by decide)]; simp [TblIns.exact, h0]
    · rw [hfr' 1 (by decide) (by decide), e1]
  · rintro s ⟨h0, h1, h2, h5, h3, ha⟩
    have hlt : x < (N + 1) ^ 2 ^ k := lt_succ_iroot_pow (by positivity) x
    exact ⟨by rw [h3, h2]; omega, h0, h1, ha⟩

/-! ### Searches -/

/-- The least `a` with `t ≤ a^4`: `t` in `0`, `a` in `1`, `a^4` in `2`. -/
def pmQuartC : TblCode 3 :=
  tblBlock 3 [.zero 1] (.zero 2) ;; .loop 2 0 (tblBlock 3 [.inc 1, .mul 1 1 2] (.mul 2 2 2))

theorem pmQuartC_do (st : TblSt 3 A) {t a : ℕ} (ht : st.val 0 = t) (ha : PmQuart t a)
    (hW : a ^ 4 < 2 ^ W) :
    TblDo A W w pmQuartC st (fun s => s.val 0 = t ∧ s.val 1 = a ∧ s.acc = st.acc)
      (5 * a + 4) := by
  have hblock : TblDo A W w (tblBlock 3 [.zero 1] (.zero 2)) st
      (fun s => s.val 0 = t ∧ s.val 1 = 0 ∧ s.val 2 = 0 ^ 4 ∧ s.acc = st.acc) 2 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits]
    · simp [tblExactList, TblIns.exact, ht]
  refine (hblock.seq (K₂ := a * (3 + 2) + 2) (fun s ⟨h0, h1, h2, hac⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  refine TblDo.loop (fun j s => s.val 0 = t ∧ s.val 1 = j ∧ s.val 2 = j ^ 4 ∧ s.acc = st.acc) a 3
    ⟨h0, h1, h2, hac⟩ ?_ ?_
  · rintro j hj s ⟨h0, h1, h2, hac⟩
    have hlt := ha.2 j hj
    have h4 : (j + 1) ^ 4 ≤ a ^ 4 := Nat.pow_le_pow_left hj 4
    have h1' : j + 1 ≤ (j + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
    have h2' : (j + 1) * (j + 1) ≤ (j + 1) ^ 4 := by
      have : (j + 1) * (j + 1) ≤ (j + 1) * (j + 1) * ((j + 1) * (j + 1)) :=
        Nat.le_mul_of_pos_right _ (by positivity)
      calc (j + 1) * (j + 1) ≤ _ := this
        _ = (j + 1) ^ 4 := by ring
    have e4 : (j + 1) * (j + 1) * ((j + 1) * (j + 1)) = (j + 1) ^ 4 := by ring
    refine ⟨by rw [h2, h0]; exact hlt, TblDo.block _ _ ?_ ?_⟩
    · simp [tblFitsList, TblIns.fits, TblIns.exact, h1, e4]; omega
    · simp [tblExactList, TblIns.exact, h0, h1, hac]; ring
  · rintro s ⟨h0, h1, h2, hac⟩
    exact ⟨by rw [h2, h0]; have := ha.1; omega, h0, h1, hac⟩

/-- `y := ⌊√x⌋`: `x` in `0`, `y` in `1`, `x + 1` in `2`, `(y + 1)²` in `3`. -/
def pmSqrtC : TblCode 4 :=
  tblBlock 4 [.copy 0 2, .inc 2, .zero 1, .zero 3] (.inc 3) ;;
    .loop 3 2 (tblBlock 4 [.inc 1, .copy 1 3, .inc 3] (.mul 3 3 3))

theorem pmSqrtC_do (st : TblSt 4 A) {x : ℕ} (hx : st.val 0 = x) (hW : 3 * x + 2 ≤ 2 ^ W) :
    TblDo A W w pmSqrtC st (fun s => s.val 0 = x ∧ s.val 1 = Nat.sqrt x ∧ s.acc = st.acc)
      (6 * Nat.sqrt x + 7) := by
  set N := Nat.sqrt x
  have hsq : (N + 1) * (N + 1) ≤ 3 * x + 1 := pm_sqrt_succ_sq_le x
  have hNx : N ≤ x := Nat.sqrt_le_self x
  have hW0 : W ≠ 0 := pm_W_ne (by omega)
  have hblock : TblDo A W w (tblBlock 4 [.copy 0 2, .inc 2, .zero 1, .zero 3] (.inc 3)) st
      (fun s => s.val 0 = x ∧ s.val 1 = 0 ∧ s.val 2 = x + 1 ∧ s.val 3 = (0 + 1) * (0 + 1) ∧
        s.acc = st.acc) 5 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hx]; omega
    · simp [tblExactList, TblIns.exact, hx]
  refine (hblock.seq (K₂ := N * (4 + 2) + 2) (fun s ⟨h0, h1, h2, h3, hac⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  refine TblDo.loop (fun j s => s.val 0 = x ∧ s.val 1 = j ∧ s.val 2 = x + 1 ∧
    s.val 3 = (j + 1) * (j + 1) ∧ s.acc = st.acc) N 4 ⟨h0, h1, h2, h3, hac⟩ ?_ ?_
  · rintro j hj s ⟨h0, h1, h2, h3, hac⟩
    have hle : (j + 1) * (j + 1) ≤ x := Nat.le_sqrt.1 hj
    have h22 : (j + 1 + 1) * (j + 1 + 1) ≤ (N + 1) * (N + 1) := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨by rw [h3, h2]; omega, TblDo.block _ _ ?_ ?_⟩
    · simp [tblFitsList, TblIns.fits, TblIns.exact, h1]; omega
    · simp [tblExactList, TblIns.exact, h0, h1, h2, hac]
  · rintro s ⟨h0, h1, h2, h3, hac⟩
    have hlt : x < (N + 1) * (N + 1) := Nat.lt_succ_sqrt x
    refine ⟨?_, h0, h1, hac⟩
    rw [h3, h2]
    omega

/-! ### `oddProd` -/

/-- The partial product `∏_{i < j} (2 i + 1)`. -/
def pmOddPart (j : ℕ) : ℕ := ∏ i ∈ range j, (2 * i + 1)

theorem pmOddPart_succ (j : ℕ) : pmOddPart (j + 1) = pmOddPart j * (2 * j + 1) :=
  Finset.prod_range_succ _ _

theorem pmOddPart_mono {j m : ℕ} (h : j ≤ m) : pmOddPart j ≤ pmOddPart m :=
  Finset.prod_le_prod_of_subset_of_one_le (Finset.range_subset_range.2 h) (fun _ _ _ => by omega)

/-- `N := oddProd d`: `d` in `0`, `N` in `1`, the counter in `2`, `2d` in `3`, `2i + 1` in `4`. -/
def pmOddC : TblCode 5 :=
  tblBlock 5 [.add 0 0 3, .zero 1] (.inc 1) ;;
    tblFor 2 3 (tblBlock 5 [.add 2 2 4, .inc 4] (.mul 1 4 1))

theorem pmOddC_do (st : TblSt 5 A) {d : ℕ} (hd : st.val 0 = d)
    (hW : oddProd d + 4 * d + 2 ≤ 2 ^ W) :
    TblDo A W w pmOddC st (fun s => s.val 0 = d ∧ s.val 1 = oddProd d ∧ s.acc = st.acc)
      (12 * d + 6) := by
  have hW0 : W ≠ 0 := pm_W_ne (by omega)
  have hblock : TblDo A W w (tblBlock 5 [.add 0 0 3, .zero 1] (.inc 1)) st
      (fun s => s.val 0 = d ∧ s.val 1 = 1 ∧ s.val 3 = 2 * d ∧ s.acc = st.acc) 3 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hd]; omega
    · simp [tblExactList, TblIns.exact, hd]; ring
  refine (hblock.seq (K₂ := 1 + (2 * d * (3 + 1 + 2) + 2)) (fun s ⟨h0, h1, h3, hac⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  refine TblDo.for (2 * d) 3 h3 (by omega) (by decide)
    (fun j s => s.val 0 = d ∧ s.val 1 = pmOddPart j ∧ s.val 3 = 2 * d ∧
      s.acc = st.acc) ⟨by simp [h0], by simp [h1, pmOddPart], by simp [h3], hac⟩ ?_ ?_
  · rintro j hj s ⟨h0, h1, h3, hac⟩ hi hn
    have hm := pmOddPart_mono (show j + 1 ≤ 2 * d by omega)
    rw [pmOddPart_succ] at hm
    have hodd : oddProd d = pmOddPart (2 * d) := rfl
    have e : j + j + 1 = 2 * j + 1 := by ring
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hi, h1, e]
      omega
    · simp [tblExactList, TblIns.exact, hi, hn, h0, h1, hac, e, pmOddPart_succ]
  · rintro s ⟨h0, h1, h3, hac⟩ - -
    exact ⟨h0, h1, hac⟩

/-! ### The source lengths -/

/-- One source length: `out := modulus N x₀ a i`, with `N` in `0`, `x₀` in `1`, `a` in `2`, `i` in
`3`, `out` in `4` and scratch `5`. -/
def pmModC : TblCode 6 :=
  .ite 3 2 (tblBlock 6 [.add 3 3 5, .add 1 5 5, .mul 0 5 4] (.inc 4))
    (tblBlock 6 [.sub 3 2 5, .add 5 5 5, .add 1 1 4, .add 4 5 5, .inc 5, .mul 0 5 4, .inc 4]
      (.inc 4))

theorem pmModC_do (st : TblSt 6 A) {N x₀ a i : ℕ} (h0 : st.val 0 = N) (h1 : st.val 1 = x₀)
    (h2 : st.val 2 = a) (h3 : st.val 3 = i) (hN : 1 ≤ N) (hW : pmModBound N x₀ i < 2 ^ W) :
    TblDo A W w pmModC st (fun s => s.val 4 = modulus N x₀ a i ∧
      (∀ j, j ≠ 4 → j ≠ 5 → s.val j = st.val j) ∧ s.acc = st.acc) 9 := by
  unfold pmModBound at hW
  by_cases hia : i < a
  · refine (TblDo.iteT (by rw [h3, h2]; exact hia) (TblDo.block _ _ ?_ ?_)).mono (fun _ h => h)
      (by norm_num)
    · have e1 : x₀ + (i + i) ≤ N * (x₀ + (i + i)) := Nat.le_mul_of_pos_left _ hN
      have e2 : N * (x₀ + (i + i)) + 1 < N * (2 * x₀ + 2 * i + 1) + 2 := by nlinarith
      simp [tblFitsList, TblIns.fits, TblIns.exact, h0, h1, h3]
      omega
    · refine ⟨?_, fun j hj4 hj5 => ?_, ?_⟩
      · simp [tblExactList, TblIns.exact, h0, h1, h3, modulus, hia, modA, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
        ring
      · simp [tblExactList, TblIns.exact, Function.update_of_ne hj4, Function.update_of_ne hj5]
      · simp [tblExactList, TblIns.exact]
  · obtain ⟨k, rfl⟩ : ∃ k, i = a + k := ⟨i - a, by omega⟩
    refine (TblDo.iteF (by rw [h3, h2]; exact hia) (TblDo.block _ _ ?_ ?_)).mono (fun _ h => h)
      le_rfl
    · have e1 : x₀ + x₀ + (k + k) + 1 ≤ N * (x₀ + x₀ + (k + k) + 1) := Nat.le_mul_of_pos_left _ hN
      have e2 : N * (x₀ + x₀ + (k + k) + 1) + 1 < N * (2 * x₀ + 2 * (a + k) + 1) + 2 := by
        nlinarith
      have e3 : a + k < 2 ^ W := by nlinarith
      simp [tblFitsList, TblIns.fits, TblIns.exact, h0, h1, h2, h3]
      omega
    · refine ⟨?_, fun j hj4 hj5 => ?_, ?_⟩
      · simp [tblExactList, TblIns.exact, h0, h1, h2, h3, modulus, hia, modB, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
        ring
      · simp [tblExactList, TblIns.exact, Function.update_of_ne hj4, Function.update_of_ne hj5]
      · simp [tblExactList, TblIns.exact]

/-- `∏_{i < d} modulus N x₀ a i`. -/
def pmSProd (N x₀ a d : ℕ) : ℕ := ∏ i ∈ range d, modulus N x₀ a i

theorem pmSProd_succ (N x₀ a d : ℕ) :
    pmSProd N x₀ a (d + 1) = pmSProd N x₀ a d * modulus N x₀ a d := Finset.prod_range_succ _ _

theorem pmSProd_mono (N x₀ a : ℕ) {j m : ℕ} (h : j ≤ m) : pmSProd N x₀ a j ≤ pmSProd N x₀ a m :=
  Finset.prod_le_prod_of_subset_of_one_le (Finset.range_subset_range.2 h)
    (fun _ _ _ => pm_one_le_modulus _ _ _ _)

theorem pmSProd_pos (N x₀ a d : ℕ) : 0 < pmSProd N x₀ a d :=
  Finset.prod_pos fun _ _ => pm_one_le_modulus _ _ _ _

/-- `S := ∏_{i < d} modulus N x₀ a i`: `N` in `0`, `x₀` in `1`, `a` in `2`, `d` in `3`, `S` in
`4`, the counter in `5`, the modulus in `6`, scratch `7`. -/
def pmProdSC : TblCode 8 :=
  tblBlock 8 [.zero 4] (.inc 4) ;;
    tblFor 5 3 (pmModC.rename ![0, 1, 2, 5, 6, 7] ;; .ins (.mul 4 6 4))

theorem pmProdSC_do (st : TblSt 8 A) {N x₀ a d : ℕ} (h0 : st.val 0 = N) (h1 : st.val 1 = x₀)
    (h2 : st.val 2 = a) (h3 : st.val 3 = d) (hN : 1 ≤ N)
    (hW1 : ∀ i < d, pmModBound N x₀ i < 2 ^ W) (hW2 : pmSProd N x₀ a d < 2 ^ W)
    (hdW : d < 2 ^ W) :
    TblDo A W w pmProdSC st (fun s => s.val 0 = N ∧ s.val 1 = x₀ ∧ s.val 2 = a ∧ s.val 3 = d ∧
      s.val 4 = pmSProd N x₀ a d ∧ s.acc = st.acc) (13 * d + 5) := by
  have hpos := pmSProd_pos N x₀ a d
  have hW0 : W ≠ 0 := pm_W_ne (by omega)
  have hblock : TblDo A W w (tblBlock 8 [.zero 4] (.inc 4)) st
      (fun s => s.val 0 = N ∧ s.val 1 = x₀ ∧ s.val 2 = a ∧ s.val 3 = d ∧ s.val 4 = 1 ∧
        s.acc = st.acc) 2 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact]; omega
    · simp [tblExactList, TblIns.exact, h0, h1, h2, h3]
  refine (hblock.seq (K₂ := 1 + (d * (10 + 1 + 2) + 2)) (fun s ⟨h0, h1, h2, h3, h4, hac⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  have hf : Function.Injective (![0, 1, 2, 5, 6, 7] : Fin 6 → Fin 8) := by decide
  refine TblDo.for d 10 h3 hdW (by decide)
    (fun j s => s.val 0 = N ∧ s.val 1 = x₀ ∧ s.val 2 = a ∧ s.val 3 = d ∧
      s.val 4 = pmSProd N x₀ a j ∧ s.acc = st.acc)
    ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4, pmSProd], hac⟩ ?_ ?_
  · rintro j hj s ⟨h0, h1, h2, h3, h4, hac⟩ hi hn
    have hmod := pmModC_do (A := A) (W := W) (w := w) (N := N) (x₀ := x₀) (a := a) (i := j)
      (s.restrict ![0, 1, 2, 5, 6, 7])
      (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [hi]) hN (hW1 j hj)
    refine ((TblDo.rename hf hmod).seq (K₂ := 1) (fun s₁ ⟨⟨hv, hfr, hac₁⟩, hout⟩ => ?_)).mono
      (fun _ h => h) le_rfl
    simp only [TblSt.restrict_val, TblSt.restrict_acc] at hv hfr hac₁
    have e0 : s₁.val 0 = N := by have := hfr 0 (by decide) (by decide); simp at this; rw [this, h0]
    have e1 : s₁.val 1 = x₀ := by have := hfr 1 (by decide) (by decide); simp at this; rw [this, h1]
    have e2 : s₁.val 2 = a := by have := hfr 2 (by decide) (by decide); simp at this; rw [this, h2]
    have e5 : s₁.val 5 = j := by have := hfr 3 (by decide) (by decide); simp at this; rw [this, hi]
    have e6 : s₁.val 6 = modulus N x₀ a j := by simpa using hv
    have e3 : s₁.val 3 = d := by rw [hout 3 (by decide), h3]
    have e4 : s₁.val 4 = pmSProd N x₀ a j := by rw [hout 4 (by decide), h4]
    have hm := pmSProd_mono N x₀ a (show j + 1 ≤ d by omega)
    rw [pmSProd_succ] at hm
    refine TblDo.insX _ (by simp [TblIns.fits, e4, e6]; omega) ?_
    refine ⟨by simp [TblIns.exact, e5], by simp [TblIns.exact, e3], ?_⟩
    simp [TblIns.exact, e0, e1, e2, e3, e4, e6, hac₁, hac, pmSProd_succ]
  · rintro s ⟨h0, h1, h2, h3, h4, hac⟩ - -
    exact ⟨h0, h1, h2, h3, h4, hac⟩

/-! ### Emission -/

/-- The axis length of axis `i`: `R` on the first `a` axes, `r` on the others. -/
def pmTv (a R r i : ℕ) : ℕ := if i < a then R else r

/-- The emitted symbols of the values `v 0, …, v (d - 1)`, each as `w` pair symbols with equal
parts, in emission order. -/
def pmEmitList (A w : ℕ) (v : ℕ → ℕ) (d : ℕ) : List (Fin (A + 4)) :=
  (List.range d).flatMap fun i => tblPairs A w (v i) (v i)

theorem pmEmitList_succ (A w : ℕ) (v : ℕ → ℕ) (d : ℕ) :
    pmEmitList A w v (d + 1) = pmEmitList A w v d ++ tblPairs A w (v d) (v d) := by
  simp [pmEmitList, List.range_succ, List.flatMap_append]

/-- Emit the axis lengths: `d` in `0`, `a` in `1`, `R` in `2`, `r` in `3`, the counter in `4`,
the value in `5`. -/
def pmEmitTC : TblCode 6 :=
  tblFor 4 0 (.ite 4 1 (.ins (.copy 2 5)) (.ins (.copy 3 5)) ;; .ins (.emit 5 5))

theorem pmEmitTC_do (st : TblSt 6 A) {d a R r : ℕ} (h0 : st.val 0 = d) (h1 : st.val 1 = a)
    (h2 : st.val 2 = R) (h3 : st.val 3 = r) (hdW : d < 2 ^ W) :
    TblDo A W w pmEmitTC st (fun s => s.val 0 = d ∧ s.val 1 = a ∧ s.val 2 = R ∧ s.val 3 = r ∧
      s.acc = (pmEmitList A w (pmTv a R r) d).reverse ++ st.acc) (6 * d + 3) := by
  let Inv : ℕ → TblSt 6 A → Prop := fun j s => s.val 0 = d ∧ s.val 1 = a ∧ s.val 2 = R ∧
    s.val 3 = r ∧ s.acc = (pmEmitList A w (pmTv a R r) j).reverse ++ st.acc
  refine (TblDo.for d 3 h0 hdW (by decide) Inv
    ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [pmEmitList]⟩ ?_ ?_).mono
    (fun _ h => h) (le_of_eq (by ring))
  · rintro j hj s ⟨h0, h1, h2, h3, hac⟩ hi hn
    have hpost : ∀ s' : TblSt 6 A, s'.val 5 = pmTv a R r j → (∀ k, k ≠ 5 → s'.val k = s.val k) →
        s'.acc = s.acc → TblDo A W w (.ins (.emit 5 5)) s' (fun s'' => s''.val 4 = j ∧
          s''.val 0 = d ∧ Inv (j + 1) ⟨Function.update s''.val 4 (j + 1), s''.acc⟩) 1 := by
      intro s' hv hfr hac'
      refine TblDo.ins _ ?_
      simp only [TblIns.run]
      refine ⟨by rw [hfr 4 (by decide), hi], by rw [hfr 0 (by decide), h0], ?_, ?_, ?_, ?_, ?_⟩
      · simp [hfr 0 (by decide), h0]
      · simp [hfr 1 (by decide), h1]
      · simp [hfr 2 (by decide), h2]
      · simp [hfr 3 (by decide), h3]
      · simp [hv, hac', hac, pmEmitList_succ]
    by_cases hja : j < a
    · refine ((TblDo.iteT (a := 4) (b := 1) (by rw [hi, h1]; exact hja) (TblDo.ins _ rfl)).seq
        (K₂ := 1) (fun s' hs' => ?_)).mono (fun _ h => h) (by norm_num)
      subst hs'
      exact hpost _ (by simp [TblIns.run, h2, pmTv, hja])
        (fun k hk => by simp [TblIns.run, Function.update_of_ne hk]) (by simp [TblIns.run])
    · refine ((TblDo.iteF (a := 4) (b := 1) (by rw [hi, h1]; exact hja) (TblDo.ins _ rfl)).seq
        (K₂ := 1) (fun s' hs' => ?_)).mono (fun _ h => h) (by norm_num)
      subst hs'
      exact hpost _ (by simp [TblIns.run, h3, pmTv, hja])
        (fun k hk => by simp [TblIns.run, Function.update_of_ne hk]) (by simp [TblIns.run])
  · rintro s ⟨h0, h1, h2, h3, hac⟩ - -
    exact ⟨h0, h1, h2, h3, hac⟩

/-- Emit the source lengths: `N` in `0`, `x₀` in `1`, `a` in `2`, `d` in `3`, the counter in `4`,
the value in `5`, scratch `6`. -/
def pmEmitSC : TblCode 7 :=
  tblFor 4 3 (pmModC.rename ![0, 1, 2, 4, 5, 6] ;; .ins (.emit 5 5))

theorem pmEmitSC_do (st : TblSt 7 A) {N x₀ a d : ℕ} (h0 : st.val 0 = N) (h1 : st.val 1 = x₀)
    (h2 : st.val 2 = a) (h3 : st.val 3 = d) (hN : 1 ≤ N)
    (hW1 : ∀ i < d, pmModBound N x₀ i < 2 ^ W) (hdW : d < 2 ^ W) :
    TblDo A W w pmEmitSC st (fun s => s.val 0 = N ∧ s.val 1 = x₀ ∧ s.val 2 = a ∧ s.val 3 = d ∧
      s.acc = (pmEmitList A w (modulus N x₀ a) d).reverse ++ st.acc) (13 * d + 3) := by
  have hf : Function.Injective (![0, 1, 2, 4, 5, 6] : Fin 6 → Fin 7) := by decide
  refine (TblDo.for d 10 h3 hdW (by decide)
    (fun j s => s.val 0 = N ∧ s.val 1 = x₀ ∧ s.val 2 = a ∧ s.val 3 = d ∧
      s.acc = (pmEmitList A w (modulus N x₀ a) j).reverse ++ st.acc)
    ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [pmEmitList]⟩ ?_ ?_).mono
    (fun _ h => h) (le_of_eq (by ring))
  · rintro j hj s ⟨h0, h1, h2, h3, hac⟩ hi hn
    have hmod := pmModC_do (A := A) (W := W) (w := w) (N := N) (x₀ := x₀) (a := a) (i := j)
      (s.restrict ![0, 1, 2, 4, 5, 6])
      (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [hi]) hN (hW1 j hj)
    refine ((TblDo.rename hf hmod).seq (K₂ := 1) (fun s₁ ⟨⟨hv, hfr, hac₁⟩, hout⟩ => ?_)).mono
      (fun _ h => h) le_rfl
    simp only [TblSt.restrict_val, TblSt.restrict_acc] at hv hfr hac₁
    have e0 : s₁.val 0 = N := by have := hfr 0 (by decide) (by decide); simp at this; rw [this, h0]
    have e1 : s₁.val 1 = x₀ := by have := hfr 1 (by decide) (by decide); simp at this; rw [this, h1]
    have e2 : s₁.val 2 = a := by have := hfr 2 (by decide) (by decide); simp at this; rw [this, h2]
    have e4 : s₁.val 4 = j := by have := hfr 3 (by decide) (by decide); simp at this; rw [this, hi]
    have e5 : s₁.val 5 = modulus N x₀ a j := by simpa using hv
    have e3 : s₁.val 3 = d := by rw [hout 3 (by decide), h3]
    refine TblDo.ins _ ?_
    simp only [TblIns.run]
    refine ⟨e4, e3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [e0]
    · simp [e1]
    · simp [e2]
    · simp [e3]
    · simp [e5, hac₁, hac, pmEmitList_succ]
  · rintro s ⟨h0, h1, h2, h3, hac⟩ - -
    exact ⟨h0, h1, h2, h3, hac⟩

/-! ### Straight-line forms -/

section Straight

variable {m : ℕ}

theorem pm_fits_const (c : Fin m) (k : ℕ) (l : List (TblIns m)) (st : TblSt m A) (hk : k < 2 ^ W)
    (h : tblFitsList A W w l ⟨Function.update st.val c k, st.acc⟩) :
    tblFitsList A W w (tblConstL c k ++ l) st :=
  tblFitsList_append _ _ _ (tblFitsList_const _ _ _ hk) (by rw [tblExactList_const]; exact h)

theorem pm_exact_const (c : Fin m) (k : ℕ) (l : List (TblIns m)) (st : TblSt m A) :
    tblExactList A w (tblConstL c k ++ l) st =
      tblExactList A w l ⟨Function.update st.val c k, st.acc⟩ := by
  rw [tblExactList_append, tblExactList_const]

end Straight

/-- `c := k₁ (a + k₂)`: `a` in `0`, `c` in `1`, scratch `2`, `3`. -/
def pmLinC (k₁ k₂ : ℕ) : TblCode 4 :=
  tblBlock 4 (tblConstL 2 k₂ ++ tblConstL 3 k₁ ++ [.add 0 2 1]) (.mul 3 1 1)

theorem pmLinC_do (k₁ k₂ : ℕ) (st : TblSt 4 A) {a : ℕ} (ha : st.val 0 = a)
    (hW : (k₁ + 1) * (a + k₂ + 1) ≤ 2 ^ W) :
    TblDo A W w (pmLinC k₁ k₂) st (fun s => s.val 0 = a ∧ s.val 1 = k₁ * (a + k₂) ∧
      s.acc = st.acc) (k₁ + k₂ + 4) := by
  have h1 : a + k₂ < 2 ^ W := by nlinarith
  have h2 : k₁ < 2 ^ W := by nlinarith
  have h3 : k₁ * (a + k₂) < 2 ^ W := by nlinarith
  refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
    (by pm_len)
  · rw [List.append_assoc, List.append_assoc]
    refine pm_fits_const _ _ _ _ (by omega) (pm_fits_const _ _ _ _ h2 ?_)
    simp [tblFitsList, TblIns.fits, TblIns.exact, ha]; omega
  · rw [List.append_assoc, List.append_assoc, pm_exact_const, pm_exact_const]
    simp [tblExactList, TblIns.exact, ha]

/-- `c := k₁ (a + b + k₂)`: `a` in `0`, `b` in `1`, `c` in `2`, scratch `3`, `4`. -/
def pmLin2C (k₁ k₂ : ℕ) : TblCode 5 :=
  tblBlock 5 (tblConstL 3 k₂ ++ tblConstL 4 k₁ ++ [.add 0 1 2, .add 2 3 2]) (.mul 4 2 2)

theorem pmLin2C_do (k₁ k₂ : ℕ) (st : TblSt 5 A) {a b : ℕ} (ha : st.val 0 = a)
    (hb : st.val 1 = b) (hW : (k₁ + 1) * (a + b + k₂ + 1) ≤ 2 ^ W) :
    TblDo A W w (pmLin2C k₁ k₂) st (fun s => s.val 0 = a ∧ s.val 1 = b ∧
      s.val 2 = k₁ * (a + b + k₂) ∧ s.acc = st.acc) (k₁ + k₂ + 5) := by
  have h1 : a + b + k₂ < 2 ^ W := by nlinarith
  have h2 : k₁ < 2 ^ W := by nlinarith
  have h3 : k₁ * (a + b + k₂) < 2 ^ W := by nlinarith
  refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
    (by pm_len)
  · rw [List.append_assoc, List.append_assoc]
    refine pm_fits_const _ _ _ _ (by omega) (pm_fits_const _ _ _ _ h2 ?_)
    simp [tblFitsList, TblIns.fits, TblIns.exact, ha, hb]; omega
  · rw [List.append_assoc, List.append_assoc, pm_exact_const, pm_exact_const]
    simp [tblExactList, TblIns.exact, ha, hb]

/-- `c := (k a + b - 1) / b`: `a` in `0`, `b` in `1`, `c` in `2`, scratch `3`. -/
def pmCeilDivC (k : ℕ) : TblCode 4 :=
  tblBlock 4 (tblConstL 3 k ++ [.mul 3 0 2, .add 2 1 2, .zero 3, .inc 3, .sub 2 3 2]) (.div 2 1 2)

theorem pmCeilDivC_do (k : ℕ) (st : TblSt 4 A) {a b : ℕ} (ha : st.val 0 = a) (hb : st.val 1 = b)
    (hb1 : 1 ≤ b) (hW : k * a + b + k + 2 ≤ 2 ^ W) :
    TblDo A W w (pmCeilDivC k) st (fun s => s.val 0 = a ∧ s.val 1 = b ∧
      s.val 2 = (k * a + b - 1) / b ∧ s.acc = st.acc) (k + 7) := by
  have hW0 : W ≠ 0 := pm_W_ne (by omega)
  refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
    (by pm_len)
  · rw [List.append_assoc]
    refine pm_fits_const _ _ _ _ (by omega) ?_
    simp [tblFitsList, TblIns.fits, TblIns.exact, ha, hb]; omega
  · rw [List.append_assoc, pm_exact_const]
    simp [tblExactList, TblIns.exact, ha, hb]

/-- `c := a - k`: `a` in `0`, `c` in `1`, scratch `2`. -/
def pmSubKC (k : ℕ) : TblCode 3 := tblBlock 3 (tblConstL 2 k) (.sub 0 2 1)

theorem pmSubKC_do (k : ℕ) (st : TblSt 3 A) {a : ℕ} (ha : st.val 0 = a) (hka : k ≤ a)
    (hW : a < 2 ^ W) :
    TblDo A W w (pmSubKC k) st (fun s => s.val 0 = a ∧ s.val 1 = a - k ∧ s.acc = st.acc)
      (k + 2) := by
  refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
    (by pm_len)
  · rw [show tblConstL (2 : Fin 3) k ++ [TblIns.sub 0 2 1] =
      tblConstL (2 : Fin 3) k ++ ([TblIns.sub 0 2 1] : List (TblIns 3)) from rfl]
    refine pm_fits_const _ _ _ _ (by omega) ?_
    simp [tblFitsList, TblIns.fits, ha]; omega
  · rw [pm_exact_const]
    simp [tblExactList, TblIns.exact, ha]

/-- `out := a b - c`: `a` in `0`, `b` in `1`, `c` in `2`, `out` in `3`. -/
def pmMulSubC : TblCode 4 := tblBlock 4 [.mul 0 1 3] (.sub 3 2 3)

theorem pmMulSubC_do (st : TblSt 4 A) {a b c : ℕ} (ha : st.val 0 = a) (hb : st.val 1 = b)
    (hc : st.val 2 = c) (hca : c ≤ a * b) (hW : a * b < 2 ^ W) :
    TblDo A W w pmMulSubC st (fun s => (∀ i, i ≠ 3 → s.val i = st.val i) ∧
      s.val 3 = a * b - c ∧ s.acc = st.acc) 2 := by
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, ha, hb, hc]; omega
  · refine ⟨fun i hi => ?_, ?_, ?_⟩
    · simp [tblExactList, TblIns.exact, Function.update_of_ne hi]
    · simp [tblExactList, TblIns.exact, ha, hb, hc]
    · simp [tblExactList, TblIns.exact]

/-- `c := a²`: `a` in `0`, `c` in `1`. -/
def pmSqC : TblCode 2 := tblBlock 2 [] (.mul 0 0 1)

theorem pmSqC_do (st : TblSt 2 A) {a : ℕ} (ha : st.val 0 = a) (hW : a * a < 2 ^ W) :
    TblDo A W w pmSqC st (fun s => s.val 0 = a ∧ s.val 1 = a ^ 2 ∧ s.acc = st.acc) 1 := by
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, ha]; omega
  · simp [tblExactList, TblIns.exact, ha, sq]

/-- `g := d (2 a + 2)`: `d` in `0`, `a` in `1`, `g` in `2`, scratch `3`. -/
def pmGammaC : TblCode 4 := tblBlock 4 [.add 1 1 3, .add 3 1 3, .inc 3, .inc 3] (.mul 0 3 2)

theorem pmGammaC_do (st : TblSt 4 A) {d a : ℕ} (hd : st.val 0 = d) (ha : st.val 1 = a)
    (hW : (d + 1) * (3 * a + 3) ≤ 2 ^ W) :
    TblDo A W w pmGammaC st (fun s => s.val 0 = d ∧ s.val 1 = a ∧ s.val 2 = d * (3 * a + 2) ∧
      s.acc = st.acc) 5 := by
  have h1 : d * (3 * a + 2) < 2 ^ W := by nlinarith
  have h2 : 3 * a + 2 < 2 ^ W := by nlinarith
  have e : a + a + a + 1 + 1 = 3 * a + 2 := by ring
  have e' : a + a + a = 3 * a := by ring
  have e3 : 3 * a + 1 + 1 = 3 * a + 2 := by ring
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hd, ha, e', e3]; omega
  · simp [tblExactList, TblIns.exact, hd, ha, e', e3]

/-- `x₀ := start d N R = 2 ((2d - 1) R / (4 d N) + 1)`: `d` in `0`, `R` in `1`, `N` in `2`, `x₀`
in `3`, scratch `4`, `5`. -/
def pmStartC : TblCode 6 :=
  tblBlock 6 [.add 0 0 4, .zero 5, .inc 5, .sub 4 5 4, .mul 4 1 4, .add 0 0 5, .add 5 5 5,
    .mul 5 2 5, .div 4 5 4, .inc 4] (.add 4 4 3)

theorem pmStartC_do (st : TblSt 6 A) {d R N : ℕ} (hd : st.val 0 = d) (hR : st.val 1 = R)
    (hN : st.val 2 = N) (hd1 : 1 ≤ d) (hN1 : 1 ≤ N) (hW : 4 * d * N + 4 * d * R + 4 ≤ 2 ^ W) :
    TblDo A W w pmStartC st (fun s => s.val 0 = d ∧ s.val 1 = R ∧ s.val 2 = N ∧
      s.val 3 = start d N R ∧ s.acc = st.acc) 11 := by
  have e1 : (d + d - 1) * R ≤ 4 * d * R := by
    have : d + d - 1 ≤ 4 * d := by omega
    exact Nat.mul_le_mul_right _ this
  have e2 : (d + d + (d + d)) * N = 4 * d * N := by ring
  have e3 : (d + d - 1) * R / (4 * d * N) ≤ (d + d - 1) * R := Nat.div_le_self _ _
  have e4 : d + d + (d + d) ≤ 4 * d * N := by nlinarith
  have e6 : (d + d - 1) * R / (4 * d * N) ≤ R := by
    apply Nat.div_le_of_le_mul
    have : d + d ≤ 4 * d * N := by nlinarith
    have : d + d - 1 ≤ 4 * d * N := by omega
    calc (d + d - 1) * R ≤ 4 * d * N * R := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  have e7 : 2 * R ≤ 4 * d * R := by nlinarith
  have hW0 : W ≠ 0 := pm_W_ne (by omega)
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hd, hR, hN, e2]; omega
  · have e5 : d + d - 1 = 2 * d - 1 := by omega
    simp [tblExactList, TblIns.exact, hd, hR, hN, e2, e5, start]
    ring

/-! ### Composite forms -/

theorem pm_clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le

/-- `L := ⌈log₂ ((4 n + b - 1) / b)⌉`: `n` in `0`, `b` in `1`, `L` in `2`, scratch `3`, `4`. -/
def pmLogTC : TblCode 5 := (pmCeilDivC 4).rename ![0, 1, 3, 4] ;; pmClogC.rename ![3, 2, 4]

theorem pmLogTC_do (st : TblSt 5 A) {n b : ℕ} (hn : st.val 0 = n) (hb : st.val 1 = b)
    (hb1 : 1 ≤ b) (hW : 2 * (4 * n + b) + 8 ≤ 2 ^ W) :
    TblDo A W w pmLogTC st (fun s => s.val 0 = n ∧ s.val 1 = b ∧
      s.val 2 = Nat.clog 2 ((4 * n + b - 1) / b) ∧ s.acc = st.acc)
      (4 * Nat.clog 2 ((4 * n + b - 1) / b) + 16) := by
  have hf1 : Function.Injective (![0, 1, 3, 4] : Fin 4 → Fin 5) := by decide
  have hf2 : Function.Injective (![3, 2, 4] : Fin 3 → Fin 5) := by decide
  have h1 := pmCeilDivC_do (A := A) (W := W) (w := w) 4 (st.restrict ![0, 1, 3, 4]) (a := n)
    (b := b) (by simp [hn]) (by simp [hb]) hb1 (by omega)
  refine ((TblDo.rename hf1 h1).seq (K₂ := 4 * Nat.clog 2 ((4 * n + b - 1) / b) + 5)
    (fun s₁ ⟨⟨e0, e1, e2, ea⟩, hout⟩ => ?_)).mono (fun _ h => h) (le_of_eq (by ring))
  simp at e0 e1 e2 ea
  have hm : (4 * n + b - 1) / b ≤ 4 * n + b := (Nat.div_le_self _ _).trans (by omega)
  have h2 := pmClogC_do (A := A) (W := W) (w := w) (s₁.restrict ![3, 2, 4])
    (x := (4 * n + b - 1) / b) (by simp [e2]) (by omega)
  refine (TblDo.rename hf2 h2).mono (fun s₂ ⟨⟨f0, f1, fa⟩, hout2⟩ => ?_) le_rfl
  simp at f0 f1 fa
  exact ⟨by rw [hout2 0 (by decide), e0], by rw [hout2 1 (by decide), e1], f1, by rw [fa, ea]⟩

/-- `c := ⌈log₂ x⌉ + k`: `x` in `0`, `c` in `1`, scratch `2`, `3`. -/
def pmClogAddC (k : ℕ) : TblCode 4 :=
  pmClogC.rename ![0, 1, 2] ;; tblBlock 4 (tblConstL 3 k) (.add 1 3 1)

theorem pmClogAddC_do (k : ℕ) (st : TblSt 4 A) {x : ℕ} (hx : st.val 0 = x)
    (hW : 2 * x + k + 2 ≤ 2 ^ W) :
    TblDo A W w (pmClogAddC k) st (fun s => s.val 0 = x ∧ s.val 1 = Nat.clog 2 x + k ∧
      s.acc = st.acc) (4 * Nat.clog 2 x + k + 7) := by
  have hf : Function.Injective (![0, 1, 2] : Fin 3 → Fin 4) := by decide
  have hc := pm_clog_le_self x
  have h1 := pmClogC_do (A := A) (W := W) (w := w) (st.restrict ![0, 1, 2]) (x := x)
    (by simp [hx]) (by omega)
  refine ((TblDo.rename hf h1).seq (K₂ := k + 2) (fun s₁ ⟨⟨e0, e1, ea⟩, hout⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  simp at e0 e1 ea
  refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
    (by pm_len)
  · refine pm_fits_const _ _ _ _ (by omega) ?_
    simp [tblFitsList, TblIns.fits, e1]; omega
  · rw [pm_exact_const]
    simp [tblExactList, TblIns.exact, e0, e1, ea]

/-- `α :=` the least `a` with `u² ≤ a^4`, `u = ⌈log₂ p⌉ + 3`: `p` in `0`, `α` in `2`, `u²` in
`3`, scratch `1`, `4`. -/
def pmAlphaC : TblCode 5 :=
  (pmClogAddC 3).rename ![0, 3, 1, 4] ;; tblBlock 5 [] (.mul 3 3 3) ;; pmQuartC.rename ![3, 2, 4]

theorem pmAlphaC_do (st : TblSt 5 A) {p α : ℕ} (hp : st.val 0 = p)
    (hα : PmQuart ((Nat.clog 2 p + 3) ^ 2) α) (hW1 : 2 * p + 5 ≤ 2 ^ W)
    (hW2 : α ^ 4 < 2 ^ W) (hW3 : (Nat.clog 2 p + 3) ^ 2 < 2 ^ W) :
    TblDo A W w pmAlphaC st (fun s => s.val 0 = p ∧ s.val 2 = α ∧ s.acc = st.acc)
      (4 * Nat.clog 2 p + 5 * α + 15) := by
  have hf : Function.Injective (![0, 3, 1, 4] : Fin 4 → Fin 5) := by decide
  have hg : Function.Injective (![3, 2, 4] : Fin 3 → Fin 5) := by decide
  set u := Nat.clog 2 p + 3 with hu
  have h1 := pmClogAddC_do (A := A) (W := W) (w := w) 3 (st.restrict ![0, 3, 1, 4]) (x := p)
    (by simp [hp]) (by omega)
  refine ((TblDo.rename hf h1).seq (K₂ := 1 + (5 * α + 4))
    (fun s₁ ⟨⟨e0, e1, ea⟩, hout⟩ => ?_)).mono (fun _ h => h) (le_of_eq (by ring))
  simp at e0 e1 ea
  have hsq : TblDo A W w (tblBlock 5 [] (.mul 3 3 3)) s₁
      (fun s => s.val 0 = p ∧ s.val 3 = u ^ 2 ∧ s.acc = st.acc) 1 := by
    refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h) (by simp)
    · simp [tblFitsList, TblIns.fits, e1, ← hu]; rw [← sq]; exact hW3
    · simp [tblExactList, TblIns.exact, e1, ea, ← hu, sq, e0]
  refine (hsq.seq (K₂ := 5 * α + 4) (fun s₂ ⟨f0, f3, fa⟩ => ?_)).mono (fun _ h => h) le_rfl
  have h2 := pmQuartC_do (A := A) (W := W) (w := w) (s₂.restrict ![3, 2, 4]) (t := u ^ 2)
    (by simp [f3]) hα hW2
  refine (TblDo.rename hg h2).mono (fun s₃ ⟨⟨g0, g1, ga⟩, hout'⟩ => ?_) le_rfl
  simp at g0 g1 ga
  exact ⟨by rw [hout' 0 (by decide), f0], g1, by rw [ga, fa]⟩

/-- `out := ⌊√(p a)⌋ + 1`: `p` in `0`, `a` in `1`, `out` in `2`, scratch `3`, `4`, `5`. -/
def pmWinAC : TblCode 6 := .ins (.mul 0 1 3) ;; (pmSqrtC.rename ![3, 2, 4, 5] ;; .ins (.inc 2))

theorem pmWinAC_do (st : TblSt 6 A) {p a : ℕ} (hp : st.val 0 = p) (ha : st.val 1 = a)
    (hW : 3 * (p * a) + 2 ≤ 2 ^ W) :
    TblDo A W w pmWinAC st (fun s => s.val 0 = p ∧ s.val 1 = a ∧
      s.val 2 = Nat.sqrt (p * a) + 1 ∧ s.acc = st.acc) (6 * Nat.sqrt (p * a) + 9) := by
  have hf : Function.Injective (![3, 2, 4, 5] : Fin 4 → Fin 6) := by decide
  have hs := Nat.sqrt_le_self (p * a)
  refine ((TblDo.insX (W := W) (w := w) (.mul 0 1 3) (by simp [TblIns.fits, hp, ha]; omega)
    (P := fun s' => s' = TblIns.exact A w (.mul 0 1 3) st) rfl).seq
    (K₂ := (6 * Nat.sqrt (p * a) + 7) + 1) (fun s₁ hs₁ => ?_)).mono (fun _ h => h)
    (le_of_eq (by ring))
  subst hs₁
  have h2 := pmSqrtC_do (A := A) (W := W) (w := w)
    ((TblIns.exact A w (.mul 0 1 3) st).restrict ![3, 2, 4, 5]) (x := p * a)
    (by simp [TblIns.exact, hp, ha]) hW
  refine (TblDo.rename hf h2).seq (K₂ := 1) (fun s₂ ⟨⟨f0, f1, fa⟩, hout⟩ => ?_)
  simp at f0 f1 fa
  refine TblDo.insX _ (by simp [TblIns.fits, f1]; omega) ⟨?_, ?_, ?_, ?_⟩
  · simp [TblIns.exact, hout 0 (by decide), hp]
  · simp [TblIns.exact, hout 1 (by decide), ha]
  · simp [TblIns.exact, f1]
  · simp [TblIns.exact, fa]

/-- `out := ⌊√p⌋ / (2 a) + 1`: `p` in `0`, `a` in `1`, `out` in `2`, scratch `3` to `6`. -/
def pmWinBC : TblCode 7 :=
  pmSqrtC.rename ![0, 3, 4, 5] ;; tblBlock 7 [.add 1 1 6, .div 3 6 2] (.inc 2)

theorem pmWinBC_do (st : TblSt 7 A) {p a : ℕ} (hp : st.val 0 = p) (ha : st.val 1 = a)
    (hW : 3 * p + 2 * a + 2 ≤ 2 ^ W) :
    TblDo A W w pmWinBC st (fun s => s.val 0 = p ∧ s.val 1 = a ∧
      s.val 2 = Nat.sqrt p / (2 * a) + 1 ∧ s.acc = st.acc) (6 * Nat.sqrt p + 10) := by
  have hf : Function.Injective (![0, 3, 4, 5] : Fin 4 → Fin 7) := by decide
  have hs := Nat.sqrt_le_self p
  have hq : Nat.sqrt p / (a + a) ≤ Nat.sqrt p := Nat.div_le_self _ _
  have h1 := pmSqrtC_do (A := A) (W := W) (w := w) (st.restrict ![0, 3, 4, 5]) (x := p)
    (by simp [hp]) (by omega)
  refine ((TblDo.rename hf h1).seq (K₂ := 3) (fun s₁ ⟨⟨e0, e1, ea⟩, hout⟩ => ?_)).mono
    (fun _ h => h) (le_of_eq (by ring))
  simp at e0 e1 ea
  have e1' : s₁.val 1 = a := by rw [hout 1 (by decide), ha]
  have e2 : a + a = 2 * a := by ring
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, e1, e1']; omega
  · simp [tblExactList, TblIns.exact, e0, e1, e1', ea, e2]

end IntegerMultBounds.MathlibTM2.Fast.TableVM