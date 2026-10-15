module

public import IntegerMultBounds.MathlibTM2.Fast.DistLoop
public import IntegerMultBounds.MathlibTM2.Fast.DistWidth
public import IntegerMultBounds.MathlibTM2.Fast.CRTMachine

/-!
# The parameters of the CRT machines

A second axis loop on the parameter layout (`ds_gloop`) computes, for `j = 0, …, d - 1`:
the source length `s_j` (`pmModC`), the offset `μ_j = (∏_{i<j} s_i)⁻¹ mod s_j` (`crtMu`) by a
search over `x = 1, 2, …` for `x ∏_{i<j} s_i ≡ 1 (mod s_j)`, and the running values
`S_j = ∏_{i<j} s_i`, `P_j = ∏_{i<j} t_i = 2^{crtPre a j}`, `sig_j = Σ_{i<j} s_i P_i`
(`crtSig`), `msk_j = Σ_{i<j} P_{i+1}/2` (`crtMask`), with `a = srcAx n` (`aᵢ = log₂ tᵢ`).
Each iteration pushes the entry `crtEnt μ_j` (`DsMode.ent`).

## States

* `dsCV n j`: the parameters, `j` in `31`, `S_j, P_j, sig_j, msk_j` in `32 … 35`, `0` in
  `36 … 39`.
* `dsCW n j`: after the axis code `dsCC₁`: `s_j` in `36`, `1` in `37`, `μ_j` in `38`, `1` in
  `39`.

`dsCC₁_do`, `dsCC₂_do`: the two codes; `ds_crt_sig`, `ds_crt_msk`, `ds_crt_mu`: the values are
the fields of `SrcCrtBase` (`Fast/SrcStage.lean`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli IntegerMultBounds.MathlibTM2.Fast

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### Values -/

section Values

/-- `S_j = ∏_{i<j} s_i`. -/
def dsSP (n j : ℕ) : ℕ := ∏ i ∈ Finset.range j, dsS n i

/-- `sig_j = Σ_{i<j} s_i P_i`. -/
def dsSig (n j : ℕ) : ℕ := ∑ i ∈ Finset.range j, dsS n i * dsP n i

/-- `msk_j = Σ_{i<j} P_{i+1} / 2`. -/
def dsMsk (n j : ℕ) : ℕ := ∑ i ∈ Finset.range j, dsP n (i + 1) / 2

/-- `μ_j`, the representative of `crtMu` below `s_j`. -/
noncomputable def dsMu (n j : ℕ) : ℕ :=
  if h : j < d n then (crtMu (s n) (Pipeline.s_pairwise n) ⟨j, h⟩ : ZMod (s n ⟨j, h⟩)).val else 0

variable {n : ℕ}

theorem dsS_ge (n i : ℕ) : 3 ≤ dsS n i := by
  have hx : 2 ≤ pmX0 n := by
    unfold pmX0 start
    exact (fun x => by omega : ∀ x : ℕ, 2 ≤ 2 * (x + 1)) _
  have hN := pm_one_le_N n
  unfold dsS modulus modA modB
  split_ifs <;> nlinarith

theorem dsSP_succ (n j : ℕ) : dsSP n (j + 1) = dsSP n j * dsS n j := Finset.prod_range_succ _ _

theorem dsSig_succ (n j : ℕ) : dsSig n (j + 1) = dsSig n j + dsS n j * dsP n j :=
  Finset.sum_range_succ _ _

theorem dsMsk_succ (n j : ℕ) : dsMsk n (j + 1) = dsMsk n j + dsP n (j + 1) / 2 :=
  Finset.sum_range_succ _ _

theorem dsSP_pos (n j : ℕ) : 0 < dsSP n j :=
  Finset.prod_pos fun i _ => by have := dsS_ge n i; omega

theorem dsSP_le {j : ℕ} (hj : j ≤ d n) : dsSP n j ≤ S n := by
  have e : S n = dsSP n (d n) := by
    rw [pm_S_prod, dsSP]; rfl
  rw [e]
  exact Nat.le_of_dvd (dsSP_pos n _)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_subset_range.2 hj))

theorem ds_s_lt_t (hbig : Big n) {i : ℕ} (hi : i < d n) : dsS n i < dsT n i := by
  have := hbig.good.lt ⟨i, hi⟩
  rw [dsT_eq n ⟨i, hi⟩]; exact this

theorem dsSig_le (hbig : Big n) : ∀ j, j ≤ d n → dsSig n j ≤ dsP n j
  | 0, _ => by simp [dsSig, dsP]
  | j + 1, hj => by
    rw [dsSig_succ, dsP_succ]
    have h1 := dsSig_le hbig j (by omega)
    have h2 := ds_s_lt_t hbig (show j < d n by omega)
    nlinarith

theorem ds_two_le_t (hbig : Big n) (i : ℕ) : 2 ≤ dsT n i := by
  have := hbig.two_le_ℓ
  rw [dsT_pow]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ dsL n i := Nat.pow_le_pow_right (by norm_num) (by unfold dsL; split_ifs <;> omega)

theorem dsMsk_le (hbig : Big n) : ∀ j, dsMsk n j ≤ dsP n j
  | 0 => by simp [dsMsk, dsP]
  | j + 1 => by
    rw [dsMsk_succ, dsP_succ]
    have h1 := dsMsk_le hbig j
    have h2 := ds_two_le_t hbig j
    have h3 : dsP n j * 2 ≤ dsP n j * dsT n j := Nat.mul_le_mul_left _ h2
    have h4 : dsP n j ≤ dsP n j * dsT n j / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; exact h3
    have h5 : dsP n j * dsT n j / 2 * 2 ≤ dsP n j * dsT n j := Nat.div_mul_le_self _ _
    omega

theorem dsMu_lt (n j : ℕ) (hj : j < d n) : dsMu n j < dsS n j := by
  unfold dsMu
  rw [dif_pos hj]
  have : NeZero (s n ⟨j, hj⟩) := ⟨by have := dsS_ge n j; rw [dsS_eq n ⟨j, hj⟩] at this; omega⟩
  exact ZMod.val_lt _

theorem dsSP_crtProd (n : ℕ) : ∀ m, m ≤ d n → dsSP n m = crtProd (s n) m
  | 0, _ => by simp [dsSP]
  | m + 1, hm => by
    rw [dsSP_succ, crtProd_succ (s n) (show m < d n by omega), dsSP_crtProd n m (by omega),
      dsS_eq n ⟨m, by omega⟩]

theorem dsSP_prefix (n j : ℕ) (hj : j < d n) :
    dsSP n j = prefixProd (s n) ⟨j, hj⟩ := by
  rw [dsSP_crtProd n j hj.le, crtProd_eq_prefixProd (s n) hj]

/-- **The search for `μ_j`.** `μ_j ≥ 1`, `μ_j S_j ≡ 1 (mod s_j)`, and every `x` in `[1, μ_j)`
gives a residue `x S_j mod s_j` above `1`. -/
theorem ds_mu_spec (n j : ℕ) (hj : j < d n) :
    1 ≤ dsMu n j ∧ dsMu n j * dsSP n j % dsS n j = 1 ∧
      ∀ x, 1 ≤ x → x < dsMu n j → 1 < x * dsSP n j % dsS n j := by
  set i : Fin (d n) := ⟨j, hj⟩
  have hs3 := dsS_ge n j
  have hsi : dsS n j = s n i := dsS_eq n i
  have hcop : Nat.Coprime (dsSP n j) (dsS n j) := by
    rw [dsSP_prefix n j hj, hsi]; exact coprime_prefixProd (Pipeline.s_pairwise n) i
  have hmu : ((dsMu n j : ℕ) : ZMod (dsS n j)) * (dsSP n j : ZMod (dsS n j)) = 1 := by
    have h := crtMu_mul_prefixProd (Pipeline.s_pairwise n) i
    rw [← dsSP_prefix n j hj] at h
    unfold dsMu
    rw [dif_pos hj]
    revert h
    rw [hsi]
    intro h
    rw [ZMod.natCast_zmod_val]
    exact h
  have h1 : Fact (1 < dsS n j) := ⟨by omega⟩
  have hres : ∀ x : ℕ, x * dsSP n j % dsS n j = ((x : ZMod (dsS n j)) * dsSP n j).val := by
    intro x; rw [← Nat.cast_mul, ZMod.val_natCast]
  have hlt := dsMu_lt n j hj
  refine ⟨?_, ?_, fun x hx1 hx2 => ?_⟩
  · by_contra h0
    have : dsMu n j = 0 := by omega
    rw [this, Nat.cast_zero, zero_mul] at hmu
    exact zero_ne_one hmu
  · rw [hres, hmu, ZMod.val_one]
  · have hxs : x < dsS n j := by omega
    by_contra hle
    push Not at hle
    rcases Nat.lt_or_ge (x * dsSP n j % dsS n j) 1 with h0 | h0
    · -- residue 0
      have hdvd : dsS n j ∣ x * dsSP n j := Nat.dvd_of_mod_eq_zero (by omega)
      have := (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd)
      have := Nat.le_of_dvd (by omega) this
      omega
    · -- residue 1
      have h1' : x * dsSP n j % dsS n j = 1 := by omega
      rw [hres] at h1'
      have hx1 : ((x : ZMod (dsS n j)) * dsSP n j) = 1 := by
        rw [← ZMod.val_one (dsS n j)] at h1'
        exact ZMod.val_injective _ h1'
      have : (x : ZMod (dsS n j)) = (dsMu n j : ZMod (dsS n j)) := by
        have e1 : (x : ZMod (dsS n j)) = x * (dsSP n j * dsMu n j) := by
          rw [mul_comm (dsSP n j : ZMod (dsS n j)), hmu, mul_one]
        rw [e1, ← mul_assoc, hx1, one_mul]
      have := congrArg ZMod.val this
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hxs, Nat.mod_eq_of_lt hlt] at this
      omega

end Values

/-! ### States and codes -/

section Codes

variable {A w : ℕ}

/-- The variables of the CRT loop before iteration `j`. -/
def dsCV (n j : ℕ) (x : Fin pmNV) : ℕ :=
  if x.val < 31 then pmVal n x else if x.val = 31 then j else if x.val = 32 then dsSP n j
  else if x.val = 33 then dsP n j else if x.val = 34 then dsSig n j
  else if x.val = 35 then dsMsk n j else 0

/-- The variables after the axis code: `s_j`, `1`, `μ_j`, `1` in `36 … 39`. -/
noncomputable def dsCW (n j : ℕ) (x : Fin pmNV) : ℕ :=
  if x.val = 36 then dsS n j else if x.val = 37 then 1 else if x.val = 38 then dsMu n j
  else if x.val = 39 then 1 else dsCV n j x

/-- The axis code: `s_j` (`pmModC`), `x := 1`, `y := x S mod s`, and `x := x + 1`,
`y := x S mod s` while `1 < y`. -/
def dsCC₁ : TblCode pmNV :=
  pmModC.rename ![16, 17, 11, 31, 36, 39] ;;
  tblBlock pmNV [.zero 37, .inc 37, .zero 38, .inc 38, .mul 38 32 39] (.mod 39 36 39) ;;
  .loop 37 39 (tblBlock pmNV [.inc 38, .mul 38 32 39] (.mod 39 36 39))

/-- The update code: `sig += s P`, `S := S s`, `P := P t`, `msk += P / 2`, scratch cleared,
`j := j + 1`. -/
def dsCC₂ : TblCode pmNV :=
  tblBlock pmNV [.mul 36 33 39, .add 34 39 34] (.mul 32 36 32) ;;
  .ite 31 11 (.ins (.copy 10 37)) (.ins (.copy 8 37)) ;;
  tblBlock pmNV [.mul 33 37 39, .copy 39 33, .zero 38, .inc 38, .inc 38, .div 39 38 39,
    .add 35 39 35, .zero 36, .zero 37, .zero 38, .inc 31] (.zero 39)

/-- The atoms of `dsCC₁`. -/
def dsCK₁ (n : ℕ) : ℕ := 5 * (2 * r n + 23) + 20

/-- The search predicate. -/
def DsC1 (n j k : ℕ) (s : TblSt pmNV A) : Prop :=
  s.acc = [] ∧ s.val 36 = dsS n j ∧ s.val 37 = 1 ∧ s.val 38 = k + 1 ∧
    s.val 39 = (k + 1) * dsSP n j % dsS n j ∧ ∀ x : Fin pmNV, x.val < 36 → s.val x = dsCV n j x

variable {n : ℕ}

theorem ds_crt_bound (hn : 2 ≤ n) {j : ℕ} (hj : j < d n) : dsSP n (j + 1) < 2 ^ pmW n := by
  have h1 := dsSP_le (n := n) (j := j + 1) (by omega)
  have h2 := pm_S_lt hn
  have h3 : 2 ^ (3 * b n + 6) ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
  omega

theorem dsCC₁_do (hn : 2 ≤ n) {j : ℕ} (hj : j < d n) :
    TblDo A (pmW n) w dsCC₁ ⟨dsCV n j, []⟩ (· = ⟨dsCW n j, []⟩) (dsCK₁ n) := by
  have hf : Function.Injective (![16, 17, 11, 31, 36, 39] : Fin 6 → Fin pmNV) := by decide
  have hB : pmModBound (N n) (pmX0 n) j < 2 ^ pmW n :=
    (pm_modBound_lt hn hj).trans_le (pm_two_pow_le (by have := pmW_ge n; omega))
  obtain ⟨hmu1, hmu2, hmu3⟩ := ds_mu_spec n j hj
  have hmus := dsMu_lt n j hj
  have hSj := ds_crt_bound hn hj
  rw [dsSP_succ] at hSj
  have hs3 := dsS_ge n j
  have hW1 : 1 < 2 ^ pmW n := Nat.one_lt_two_pow (by have := pmW_ge n; omega)
  -- `s_j`
  have hM := pmModC_do (A := A) (W := pmW n) (w := w) (N := N n) (x₀ := pmX0 n)
    (a := numHalf n) (i := j) ((⟨dsCV n j, []⟩ : TblSt pmNV A).restrict ![16, 17, 11, 31, 36, 39])
    (by simp [dsCV, pmVal, pmNV]) (by simp [dsCV, pmVal, pmNV]) (by simp [dsCV, pmVal, pmNV])
    (by simp [dsCV, pmVal, pmNV]) (pm_one_le_N n) hB
  have hA : TblDo A (pmW n) w (pmModC.rename ![16, 17, 11, 31, 36, 39]) ⟨dsCV n j, []⟩
      (fun s => s.acc = [] ∧ s.val 36 = dsS n j ∧
        ∀ x : Fin pmNV, x.val < 36 → s.val x = dsCV n j x) 9 := by
    refine (TblDo.rename hf hM).mono (fun s ⟨⟨hv, hfr, hac⟩, hout⟩ => ⟨?_, ?_, fun x hx => ?_⟩) le_rfl
    · simpa using hac
    · simpa [dsS] using hv
    · by_cases hex : ∃ y, (![16, 17, 11, 31, 36, 39] : Fin 6 → Fin pmNV) y = x
      · obtain ⟨y, rfl⟩ := hex
        fin_cases y
        · simpa using hfr 0 (by decide) (by decide)
        · simpa using hfr 1 (by decide) (by decide)
        · simpa using hfr 2 (by decide) (by decide)
        · simpa using hfr 3 (by decide) (by decide)
        · simp [pmNV] at hx
        · simp [pmNV] at hx
      · push Not at hex
        exact hout x hex
  -- `x := 1`, `y := S mod s`
  have hBk : ∀ s : TblSt pmNV A, (s.acc = [] ∧ s.val 36 = dsS n j ∧
      ∀ x : Fin pmNV, x.val < 36 → s.val x = dsCV n j x) →
      TblDo A (pmW n) w (tblBlock pmNV [.zero 37, .inc 37, .zero 38, .inc 38, .mul 38 32 39]
        (.mod 39 36 39)) s (DsC1 n j 0) 6 := by
    rintro s ⟨h1, h2, h3⟩
    have h32 : s.val 32 = dsSP n j := by rw [h3 32 (by decide)]; simp [dsCV, pmNV]
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, h32]
      refine ⟨by have := pmW_ge n; omega, ?_⟩
      calc dsSP n j ≤ dsSP n j * dsS n j := Nat.le_mul_of_pos_right _ (by omega)
        _ < _ := hSj
    · refine ⟨by simpa [tblExactList, TblIns.exact] using h1, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
      · simp [tblExactList, TblIns.exact, h2]
      · simp [tblExactList, TblIns.exact]
      · simp [tblExactList, TblIns.exact]
      · simp [tblExactList, TblIns.exact, h32, h2]
      · have h37 : x ≠ 37 := by rintro rfl; simp [pmNV] at hx
        have h38 : x ≠ 38 := by rintro rfl; simp [pmNV] at hx
        have h39 : x ≠ 39 := by rintro rfl; simp [pmNV] at hx
        simp [tblExactList, TblIns.exact, Function.update_of_ne h37, Function.update_of_ne h38,
          Function.update_of_ne h39, h3 x hx]
  -- the search
  have hL : ∀ s : TblSt pmNV A, DsC1 n j 0 s →
      TblDo A (pmW n) w (.loop 37 39 (tblBlock pmNV [.inc 38, .mul 38 32 39] (.mod 39 36 39))) s
        (· = ⟨dsCW n j, []⟩) ((dsMu n j - 1) * (3 + 2) + 2) := by
    intro s hs
    refine TblDo.loop (fun k s => DsC1 n j k s) (dsMu n j - 1) 3 hs ?_ ?_
    · rintro k hk s ⟨h1, h2, h3, h4, h5, h6⟩
      have h32 : s.val 32 = dsSP n j := by rw [h6 32 (by decide)]; simp [dsCV, pmNV]
      refine ⟨by rw [h3, h5]; exact hmu3 (k + 1) (by omega) (by omega), ?_⟩
      refine TblDo.block _ _ ?_ ?_
      · simp [tblFitsList, TblIns.fits, TblIns.exact, h4, h32]
        have : dsS n j ≤ dsSP n j * dsS n j := Nat.le_mul_of_pos_left _ (dsSP_pos n j)
        refine ⟨by omega, ?_⟩
        calc (k + 1 + 1) * dsSP n j ≤ dsS n j * dsSP n j := Nat.mul_le_mul_right _ (by omega)
          _ = dsSP n j * dsS n j := by ring
          _ < _ := hSj
      · refine ⟨by simpa [tblExactList, TblIns.exact] using h1, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
        · simp [tblExactList, TblIns.exact, h2]
        · simp [tblExactList, TblIns.exact, h3]
        · simp [tblExactList, TblIns.exact, h4]
        · simp [tblExactList, TblIns.exact, h4, h32, h2]
        · have h38 : x ≠ 38 := by rintro rfl; simp [pmNV] at hx
          have h39 : x ≠ 39 := by rintro rfl; simp [pmNV] at hx
          simp [tblExactList, TblIns.exact, Function.update_of_ne h38,
            Function.update_of_ne h39, h6 x hx]
    · rintro s ⟨h1, h2, h3, h4, h5, h6⟩
      have e : dsMu n j - 1 + 1 = dsMu n j := by omega
      rw [e] at h4 h5
      refine ⟨by rw [h3, h5, hmu2]; omega, ?_⟩
      cases s with
      | mk val acc =>
        simp only at h1 h2 h3 h4 h5 h6
        subst h1
        congr 1
        funext x
        unfold dsCW
        split_ifs with g1 g2 g3 g4
        · rw [← h2]; congr 1; exact Fin.ext g1
        · rw [← h3]; congr 1; exact Fin.ext g2
        · rw [← h4]; congr 1; exact Fin.ext g3
        · rw [← hmu2, ← h5]; congr 1; exact Fin.ext g4
        · by_cases hx : x.val < 36
          · exact h6 x hx
          · have h40 : 40 ≤ x.val := by omega
            have := x.isLt
            simp only [pmNV] at this
            omega
  refine ((hA.seq fun s hs => (hBk s hs).seq fun s hs => hL s hs)).mono (fun _ h => h) ?_
  unfold dsCK₁
  have := dsS_le hn hj
  omega

theorem dsCC₂_do (hbig : Big n) {j : ℕ} (hj : j < d n) :
    TblDo A (pmW n) w dsCC₂ ⟨dsCW n j, []⟩ (· = ⟨dsCV n (j + 1), []⟩) 17 := by
  have hn := hbig.1
  have hT := ds_T_lt hn
  have hd := ds_d_lt hn
  have hP1 : dsP n (j + 1) ≤ T n := dsP_le hn (by omega)
  have hst := ds_s_lt_t hbig hj
  have hsP : dsS n j * dsP n j ≤ dsP n (j + 1) := by
    rw [dsP_succ, mul_comm]; exact Nat.mul_le_mul_left _ hst.le
  have hsig := dsSig_le hbig (j + 1) (by omega)
  have hmsk := dsMsk_le hbig (j + 1)
  rw [dsSig_succ] at hsig
  rw [dsMsk_succ] at hmsk
  have hSj := ds_crt_bound hn hj
  rw [dsSP_succ] at hSj
  have hW1 : 2 < 2 ^ pmW n := by
    have : 2 ^ 2 ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
    omega
  set σ1 : Fin pmNV → ℕ := Function.update (Function.update (Function.update (dsCW n j) 39
    (dsS n j * dsP n j)) 34 (dsSig n j + dsS n j * dsP n j)) 32 (dsSP n j * dsS n j) with hσ1
  set σ2 : Fin pmNV → ℕ := Function.update σ1 37 (dsT n j) with hσ2
  have hB1 : TblDo A (pmW n) w (tblBlock pmNV [.mul 36 33 39, .add 34 39 34] (.mul 32 36 32))
      ⟨dsCW n j, []⟩ (· = ⟨σ1, []⟩) 3 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, dsCW, dsCV, pmNV]
      exact ⟨by omega, by omega, hSj⟩
    · simp [tblExactList, TblIns.exact, σ1, dsCW, dsCV, pmNV]
  have hI : TblDo A (pmW n) w (.ite 31 11 (.ins (.copy 10 37)) (.ins (.copy 8 37))) ⟨σ1, []⟩
      (· = ⟨σ2, []⟩) 2 := by
    by_cases h : j < numHalf n
    · refine TblDo.iteT (by simp [σ1, dsCW, dsCV, pmNV, pmVal, h]) (TblDo.ins _ ?_)
      simp [TblIns.run, σ2, σ1, dsCW, dsCV, pmNV, pmVal, dsT, pmTv, h]
    · refine TblDo.iteF (by simp [σ1, dsCW, dsCV, pmNV, pmVal, h]) (TblDo.ins _ ?_)
      simp [TblIns.run, σ2, σ1, dsCW, dsCV, pmNV, pmVal, dsT, pmTv, h]
  have hB2 : TblDo A (pmW n) w (tblBlock pmNV [.mul 33 37 39, .copy 39 33, .zero 38, .inc 38,
      .inc 38, .div 39 38 39, .add 35 39 35, .zero 36, .zero 37, .zero 38, .inc 31] (.zero 39))
      ⟨σ2, []⟩ (· = ⟨dsCV n (j + 1), []⟩) 12 := by
    have e1 : dsP n j * dsT n j = dsP n (j + 1) := (dsP_succ n j).symm
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, σ2, σ1, dsCW, dsCV, pmNV, e1]
      exact ⟨by omega, by have := pmW_ge n; omega, hW1, by omega, by omega⟩
    · simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append]
      congr 1
      funext x
      fin_cases x <;> simp [σ2, σ1, dsCW, dsCV, Function.update_apply, Fin.ext_iff, pmNV, e1,
        dsSP_succ, dsSig_succ, dsMsk_succ]
  exact ((hB1.seq fun s hs => hs ▸ (hI.seq fun s hs => hs ▸ hB2))).mono (fun _ h => h)
    (by norm_num)

theorem dsCV_lt (hbig : Big n) {j : ℕ} (hj : j ≤ d n) (x : Fin pmNV) :
    dsCV n j x < 2 ^ pmW n := by
  have hn := hbig.1
  have hT := ds_T_lt hn
  have hd := ds_d_lt hn
  have hP := dsP_le hn hj
  have hS := dsSP_le (n := n) hj
  have hS2 := pm_S_lt hn
  have hS3 : 2 ^ (3 * b n + 6) ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
  have hsig := dsSig_le hbig j hj
  have hmsk := dsMsk_le hbig j
  unfold dsCV
  split_ifs
  · exact ds_pmVal_lt hn x
  all_goals omega

theorem dsCW_lt (hbig : Big n) {j : ℕ} (hj : j < d n) (x : Fin pmNV) :
    dsCW n j x < 2 ^ pmW n := by
  have hn := hbig.1
  have hs := dsS_lt hn hj
  have hmu := dsMu_lt n j hj
  have hW1 : 1 < 2 ^ pmW n := Nat.one_lt_two_pow (by have := pmW_ge n; omega)
  unfold dsCW
  split_ifs
  · exact hs
  · exact hW1
  · omega
  · exact hW1
  · exact dsCV_lt hbig hj.le x

end Codes

/-! ### The loop and its outputs -/

section Out

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T} {n : ℕ}

/-- The pushes of the CRT loop: the entry of `μ_j` onto `o`. -/
def dsLC (o : Fin T) : List (Fin T × Fin pmNV × DsMode) := [(o, 38, .ent)]

/-- **The CRT loop.** -/
theorem ds_crtLoop (hrg : Function.Injective rg) {uD tm o : Fin T} (huD : ∀ r, rg r ≠ uD)
    (htm : ∀ r, rg r ≠ tm) (hut : uD ≠ tm) (ho : ∀ r, rg r ≠ o) (hou : o ≠ uD) (hot : o ≠ tm)
    (hbig : Big n) (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (R : Regs T A)
    (hRu : (R uD).length = d n) (hRt : R tm = []) :
    dsRuns body (dsGLoop rg uD tm dsCC₁ dsCC₂ (dsLC o))
      (dsOv rg R (tblRho (pmW n) wl wl ⟨dsCV n 0, []⟩))
      (dsGPsi rg R (dsCV n) (dsCW n) (dsLC o) (pmW n) wl wl (d n))
      (dsGCost (pmW n) (pmW n) (dsCK₁ n + 17) (dsCW n) (dsLC o) (d n)) :=
  ds_gloop hrg huD htm hut wl wl hwl hwl le_rfl (fun j hj => dsCC₁_do hbig.1 hj)
    (fun j hj => dsCC₂_do hbig hj) (fun j hj => dsCV_lt hbig hj.le) (fun j hj => dsCW_lt hbig hj)
    (dsLC o) (by simp [dsLC, ho]) (by simp [dsLC, hou]) (by simp [dsLC, hot]) R hRu hRt

/-- The axis widths `aᵢ = log₂ tᵢ` of the CRT box. -/
def dsAx (n : ℕ) : Fin (d n) → ℕ := fun j => Nat.log 2 (t n j)

theorem ds_crtPre (n : ℕ) : ∀ j, j ≤ d n → crtPre (dsAx n) j = ∑ i ∈ Finset.range j, dsL n i
  | 0, _ => by simp
  | j + 1, hj => by
    rw [crtPre_succ (dsAx n) (show j < d n by omega), ds_crtPre n j (by omega),
      Finset.sum_range_succ]
    congr 1
    exact ds_log_t n ⟨j, by omega⟩

theorem ds_crtPre_pow (n : ℕ) {j : ℕ} (hj : j ≤ d n) : 2 ^ crtPre (dsAx n) j = dsP n j := by
  rw [ds_crtPre n j hj, dsP_pow]

theorem ds_crtPre_d (hn : 2 ≤ n) : crtPre (dsAx n) (d n) = logT n := by
  have h := ds_crtPre_pow n (le_refl (d n))
  rw [dsP_d hn, T] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem ds_crtSig (n : ℕ) : ∀ j, j ≤ d n → crtSig (dsAx n) (s n) j = dsSig n j
  | 0, _ => by simp [dsSig]
  | j + 1, hj => by
    rw [crtSig_succ (dsAx n) (s n) (show j < d n by omega), ds_crtSig n j (by omega), dsSig_succ,
      ds_crtPre_pow n (by omega)]
    rfl

theorem ds_crtMask (hbig : Big n) : ∀ j, j ≤ d n → crtMask (dsAx n) j = dsMsk n j
  | 0, _ => by simp [dsMsk]
  | j + 1, hj => by
    rw [crtMask_succ (dsAx n) (show j < d n by omega), ds_crtMask hbig j (by omega), dsMsk_succ]
    congr 1
    have h1 : 1 ≤ dsAx n ⟨j, by omega⟩ := by
      show 1 ≤ Nat.log 2 _
      rw [ds_log_t]; have := hbig.two_le_ℓ; unfold dsL; split_ifs <;> omega
    rw [← ds_crtPre_pow n (show j + 1 ≤ d n by omega), crtPre_succ (dsAx n) (show j < d n by omega)]
    obtain ⟨e, he⟩ : ∃ e, crtPre (dsAx n) j + dsAx n ⟨j, by omega⟩ = e + 1 :=
      ⟨crtPre (dsAx n) j + dsAx n ⟨j, by omega⟩ - 1, by omega⟩
    rw [he, Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- The entries of the CRT loop are the list `mT` of the CRT machines. -/
theorem ds_crt_mT {o : Fin T} : ∀ j, j ≤ d n →
    dsGAcc (A := A) (dsCW n) (dsLC o) j o =
      crtEnts ((crtRevAx j).map fun i : Fin (d n) =>
        (crtMu (s n) (Pipeline.s_pairwise n) i : ZMod (s n i)).val)
  | 0, _ => by simp [dsGAcc]
  | j + 1, hj => by
    rw [dsGAcc_succ, ds_crt_mT j (by omega), crtRevAx_succ (show j < d n by omega), List.map_cons,
      crtEnts_cons]
    congr 1
    simp [dsOut, dsLC, dsBlk, dsCW, pmNV, dsMu, show j < d n by omega, crtEnt, crtSep, dsFld]

end Out

end IntegerMultBounds.MathlibTM2.Fast.TableVM
