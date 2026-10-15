module

public import IntegerMultBounds.MathlibTM2.Fast.ParamSub
public import IntegerMultBounds.MathlibTM2.Fast.CompactDyadicParamStageCore
public import IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom

/-!
# The parameter program

`pmCode1` and `pmCode2` are table programs (`TblCode pmNV`, `pmNV = 40` variables) computing,
from the operand length `n ≥ 2` in variable `0`, every parameter of the numeric pipeline
exactly, in words of `W ≥ 4 b + 32` bits (`b = ⌈log₂ n⌉`). Variable `i < 31` ends holding
`pmVal n i`; the scratch variables `31, …, 39` end at `0`.

| var | value | source |
|---|---|---|
| 0 | `n` | input |
| 1 | `b = ⌈log₂ n⌉` | `Sizes.b` |
| 2 | `p = 6 b` | `Sizes.p` |
| 3 | `d = iroot 64 (b^9)` | `Sizes.d` |
| 4 | `K = iroot (2^32) d` | `Sizes.K` |
| 5 | `log₂ T` | `Sizes.logT` |
| 6 | `T` | `Sizes.T` |
| 7 | `ℓ` | `Sizes.ℓ` |
| 8 | `r = 2^ℓ` | `Sizes.r` |
| 9 | `ℓ - 1` | `Moduli.box` exponent |
| 10 | `R = 2^(ℓ-1)` | `Moduli.src` |
| 11 | `numHalf` | `Sizes.numHalf` |
| 12 | `α` | `Sizes.alpha` |
| 13 | `α²` | Neumann steps of `Pipeline.lineB` |
| 14 | `γ` | `Sizes.gamma` |
| 15 | `q` | `Sizes.q` |
| 16 | `N = oddProd d` | `Sizes.N` |
| 17 | `x₀ = start d N R` | `Moduli.start` |
| 18 | `S` | `Sizes.S` |
| 19 | `windowA p α` | `Pipeline.windowA` |
| 20 | `fastWindow p α` | `FastB0.fastWindow` |
| 21 | `g = chirpGuard d` | `Chirp.chirpGuard` |
| 22 | `taylorTerms p 0` | twist Taylor terms |
| 23 | `taylorGuard p 0` | twist guard bits |
| 24 | `p + 2 + taylorGuard p 0` | twist Taylor precision |
| 25 | `5 (p + 4)` | twist angle precision |
| 26 | `taylorTerms p g` | chirp Taylor terms |
| 27 | `taylorGuard p g` | chirp guard bits |
| 28 | `p + g` | chirp table and product precision |
| 29 | `p + g + 2 + taylorGuard p g` | chirp Taylor precision |
| 30 | `5 · anglePrec p g` | chirp angle precision |

Each stage is a small program of `Fast/ParamSub.lean` renamed into the parameter state
(`pm_stage`): the facts `PmF n j acc` (variables below `j` correct, `acc` fixed) become
`PmF n (j + 1) acc'`. `pmCode1` runs the 30 stages, emits the axis lengths `t_i` (`pmEmitTC`) and
clears the scratch; `pmCode2` emits the source lengths `s_i` (`pmEmitSC`) and clears the scratch.

`pmCode1_do`, `pmCode2_do`: the contracts, within `pmAtoms1 n` and `pmAtoms2 n` atoms, at most
`2500 (b + 1)²` and `25 (b + 1)²` (`pmAtoms1_le`, `pmAtoms2_le`). The value lemmas `pm_b_eq`,
`pm_d_eq`, …, `pm_chAngle_eq` name each entry of `pmVals n`; `pm_t_box`, `pmTv_eq`, `pm_s_modulus`,
`pm_S_prod`, `pm_R_half` relate the emitted lengths to `Sizes.t`, `Sizes.s` and `Moduli`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli IntegerMultBounds.MathlibTM2.Mult.Chirp IntegerMultBounds.MathlibTM2.Mult.Pipeline
  IntegerMultBounds.MathlibTM2.Mult.FastB0 Finset

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

variable {A W w : ℕ}

/-! ### Variables and values -/

/-- The number of variables of the parameter machine. -/
abbrev pmNV : ℕ := 40

/-- The value of variable `i` at the end of the parameter program. -/
def pmVal (n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => b n
  | 2 => p n
  | 3 => d n
  | 4 => K n
  | 5 => logT n
  | 6 => T n
  | 7 => ℓ n
  | 8 => r n
  | 9 => ℓ n - 1
  | 10 => 2 ^ (ℓ n - 1)
  | 11 => numHalf n
  | 12 => alpha n
  | 13 => alpha n ^ 2
  | 14 => gamma n
  | 15 => q n
  | 16 => N n
  | 17 => pmX0 n
  | 18 => S n
  | 19 => windowA (p n) (alpha n)
  | 20 => fastWindow (p n) (alpha n)
  | 21 => chirpGuard (d n)
  | 22 => taylorTerms (p n) 0
  | 23 => taylorGuard (p n) 0
  | 24 => p n + 2 + taylorGuard (p n) 0
  | 25 => 5 * (p n + 4)
  | 26 => taylorTerms (p n) (chirpGuard (d n))
  | 27 => taylorGuard (p n) (chirpGuard (d n))
  | 28 => p n + chirpGuard (d n)
  | 29 => p n + chirpGuard (d n) + 2 + taylorGuard (p n) (chirpGuard (d n))
  | 30 => 5 * anglePrec (p n) (chirpGuard (d n))
  | _ => 0

/-- The final variable values. -/
def pmVals (n : ℕ) (i : Fin pmNV) : ℕ := pmVal n i

/-- The parameter facts: `acc` is `acc₀` and every variable below `k` holds its value. -/
def PmF (n k : ℕ) (acc₀ : List (Fin (A + 4))) (s : TblSt pmNV A) : Prop :=
  s.acc = acc₀ ∧ ∀ i : Fin pmNV, i.val < k → s.val i = pmVal n i

/-- **A stage.** A small program `c` renamed by `f`, writing the parameter `j` into `f out` and
keeping the variables of `f` below `j`. -/
theorem pm_stage {m : ℕ} {f : Fin m → Fin pmNV} (hf : Function.Injective f) {c : TblCode m}
    {n j K : ℕ} {acc acc' : List (Fin (A + 4))} (out : Fin m) (hout : (f out).val = j)
    (hsmall : ∀ s : TblSt pmNV A, PmF n j acc s → TblDo A W w c (s.restrict f)
      (fun s' => s'.acc = acc' ∧ s'.val out = pmVal n j ∧
        ∀ y, (f y).val < j → s'.val y = pmVal n (f y)) K) :
    ∀ s, PmF n j acc s → TblDo A W w (c.rename f) s (PmF n (j + 1) acc') K := by
  intro s hs
  refine (TblDo.rename hf (hsmall s hs)).mono ?_ le_rfl
  rintro s' ⟨⟨hacc, hv, hin⟩, hfr⟩
  refine ⟨hacc, fun i hi => ?_⟩
  by_cases hij : i.val = j
  · have : i = f out := Fin.ext (hij.trans hout.symm)
    subst this
    rw [hij]
    exact hv
  · have hi' : i.val < j := by omega
    by_cases hex : ∃ y, f y = i
    · obtain ⟨y, rfl⟩ := hex
      exact hin y hi'
    · push Not at hex
      rw [hfr i hex]
      exact hs.2 i hi'

/-- A stage that changes only `acc`. -/
theorem pm_stage_acc {m : ℕ} {f : Fin m → Fin pmNV} (hf : Function.Injective f) {c : TblCode m}
    {n j K : ℕ} {acc acc' : List (Fin (A + 4))}
    (hsmall : ∀ s : TblSt pmNV A, PmF n j acc s → TblDo A W w c (s.restrict f)
      (fun s' => s'.acc = acc' ∧ ∀ y, (f y).val < j → s'.val y = pmVal n (f y)) K) :
    ∀ s, PmF n j acc s → TblDo A W w (c.rename f) s (PmF n j acc') K := by
  intro s hs
  refine (TblDo.rename hf (hsmall s hs)).mono ?_ le_rfl
  rintro s' ⟨⟨hacc, hin⟩, hfr⟩
  refine ⟨hacc, fun i hi => ?_⟩
  by_cases hex : ∃ y, f y = i
  · obtain ⟨y, rfl⟩ := hex
    exact hin y hi
  · push Not at hex
    rw [hfr i hex]
    exact hs.2 i hi

theorem pm_seq {c d : TblCode pmNV} {n j k l K₁ K₂ : ℕ} {a₁ a₂ a₃ : List (Fin (A + 4))}
    (h₁ : ∀ s, PmF n j a₁ s → TblDo A W w c s (PmF n k a₂) K₁)
    (h₂ : ∀ s, PmF n k a₂ s → TblDo A W w d s (PmF n l a₃) K₂) :
    ∀ s, PmF n j a₁ s → TblDo A W w (c ;; d) s (PmF n l a₃) (K₁ + K₂) :=
  fun s hs => (h₁ s hs).seq h₂

theorem PmF.val {n k : ℕ} {acc : List (Fin (A + 4))} {s : TblSt pmNV A} (h : PmF n k acc s)
    (i : Fin pmNV) (hi : i.val < k := by decide) : s.val i = pmVal n i := h.2 i hi

/-! ### Size bounds in words of `W ≥ 4 b + 32` bits -/

section Bounds

variable {n : ℕ}

theorem pm_W_pow (hW : 4 * b n + 32 ≤ W) {k : ℕ} (hk : k ≤ 4 * b n + 32) : 2 ^ k ≤ 2 ^ W :=
  pm_two_pow_le (hk.trans hW)

theorem pm_n_le (n : ℕ) : n ≤ 2 ^ b n := le_two_pow_b n

theorem pm_b_lt (n : ℕ) : b n < 2 ^ b n := Nat.lt_two_pow_self

theorem pm_two_le_t (hn : 2 ≤ n) : 2 ≤ 2 ^ b n := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ b n := pm_two_pow_le (one_le_b hn)

end Bounds

/-! ### The stages -/

section Stages

variable {n : ℕ} {acc : List (Fin (A + 4))}

theorem pm_s1 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 1 acc s → TblDo A W w (pmClogC.rename ![0, 1, 31]) s (PmF n 2 acc)
      (4 * b n + 5) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![0, 1, 31]).val 0 = n := by simpa [pmVal, pmNV] using hs.val 0
    have hb := pm_W_pow hW (k := b n + 2) (by omega)
    have e : 2 ^ (b n + 2) = 4 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_n_le n
    have := pm_two_le_t hn
    refine (pmClogC_do _ h0 (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, e1, fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s2 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 2 acc s → TblDo A W w ((pmLinC 6 0).rename ![1, 2, 31, 32]) s (PmF n 3 acc) 10 :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![1, 2, 31, 32]).val 0 = b n := by simpa [pmVal, pmNV] using hs.val 1
    have hb := pm_W_pow hW (k := b n + 3) (by omega)
    have e : 2 ^ (b n + 3) = 8 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_b_lt n
    refine (pmLinC_do 6 0 _ h0 (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, p], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_sq_lt (hW : 4 * b n + 32 ≤ W) {x : ℕ} (hx : x ≤ b n) : (x + 1) * (x + 1) < 2 ^ W := by
  have h1 : x + 1 ≤ 2 ^ b n := by have := pm_b_lt n; omega
  have h2 : (x + 1) * (x + 1) ≤ 2 ^ b n * 2 ^ b n := Nat.mul_le_mul h1 h1
  have e : 2 ^ (2 * b n + 1) = 2 * (2 ^ b n * 2 ^ b n) := by rw [pow_succ, two_mul, pow_add]; ring
  have := pm_W_pow hW (k := 2 * b n + 1) (by omega)
  have : 1 ≤ 2 ^ b n * 2 ^ b n := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

theorem pm_const_lt (hW : 4 * b n + 32 ≤ W) {k : ℕ} (hk : k < 2 ^ 16) : k < 2 ^ W :=
  lt_of_lt_of_le hk (pm_W_pow hW (by omega))

/-- The new root computation fits the existing parameter-stage budget. -/
theorem pm_s3 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 3 acc s → TblDo A W w compactDyadicParamStage s
      (PmF n 4 acc) (7 * 30 + 11 + d n * (6 * 30 + 8)) := by
  intro s hs
  have hb : s.val 1 = b n := by simpa [pmVal, pmNV] using hs.2 1 (by decide)
  have hfit : (b n ^ 9 + 1)^2 < 2^W :=
    (CompactDyadicRootRoom.squared_ninth_cap_lt (b n)).trans_le
      (Nat.pow_le_pow_right (by decide) hW)
  refine (compactDyadicParamStage_do s hb hfit (pm_const_lt hW (by norm_num))).mono ?_ ?_
  · intro z hz
    refine ⟨hz.2.trans hs.1, fun i hi => ?_⟩
    rw [hz.1]
    by_cases hi3 : i = 3
    · subst i
      simp [compactDyadicParamVals, pmVal, pmNV, d, rootExp, rootNumerator]
    · have hi3v : i.val ≠ 3 := fun h => hi3 (Fin.ext h)
      have hil : i.val < 3 := by omega
      have hscratch : ¬ (31 ≤ i.val ∧ i.val ≤ 35) := by omega
      simpa [compactDyadicParamVals, hi3, hscratch] using hs.2 i hil
  · simpa [compactDyadicParamAtoms, d, rootExp, rootNumerator] using
      compactDyadicParamAtoms_le (b n)

theorem pm_s4 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 4 acc s → TblDo A W w ((pmIrootC 32).rename ![3, 4, 31, 32, 33, 34]) s
      (PmF n 5 acc) (7 * 34 + 11 + K n * (6 * 34 + 8)) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![3, 4, 31, 32, 33, 34]).val 0 = d n := by simpa [pmVal, pmNV] using hs.val 3
    refine (pmIrootC_do 32 _ h0 (pm_sq_lt hW (d_le_b n)) (pm_const_lt hW (by norm_num))).mono ?_
      (by change 7 * 32 + 11 + K n * (6 * 32 + 8) ≤ 7 * 34 + 11 + K n * (6 * 34 + 8); omega)
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; rfl, fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s5 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 5 acc s → TblDo A W w (pmLogTC.rename ![0, 1, 5, 31, 32]) s (PmF n 6 acc)
      (4 * logT n + 16) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![0, 1, 5, 31, 32]).val 0 = n := by simpa [pmVal, pmNV] using hs.val 0
    have h1 : (s.restrict ![0, 1, 5, 31, 32]).val 1 = b n := by simpa [pmVal, pmNV] using hs.val 1
    have hb := pm_W_pow hW (k := b n + 4) (by omega)
    have e : 2 ^ (b n + 4) = 16 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_n_le n
    have := pm_b_lt n
    have := pm_two_le_t hn
    refine (pmLogTC_do _ h0 h1 (one_le_b hn) (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; rfl, fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_pow2_stage {j : ℕ} {e c t : Fin pmNV} (hf : Function.Injective ![e, c, t])
    (hc : c.val = j) (he : e.val < j) (ht : j < t.val) {v : ℕ} (hv : pmVal n e = v)
    (hval : pmVal n j = 2 ^ v) (hW : v < W) :
    ∀ s, PmF n j acc s → TblDo A W w ((tblPow2 1 0 2).rename ![e, c, t]) s (PmF n (j + 1) acc)
      (4 * v + 5) :=
  pm_stage hf 1 hc fun s hs => by
    have h0 : (s.restrict ![e, c, t]).val 0 = v := by
      simpa [hv] using hs.2 e he
    refine (tblPow2_do (c := 1) (e := 0) (i := 2) (by decide) (by decide) (by decide) _
      (by rw [h0]; exact hW)).mono ?_ (by rw [h0])
    rintro s' ⟨e1, -, efr, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1, h0, hval], fun y hy => ?_⟩
    fin_cases y
    · show s'.val 0 = pmVal n e
      rw [efr 0 (by decide) (by decide)]; simpa [hv] using h0
    · change c.val < j at hy; omega
    · change t.val < j at hy; omega

theorem pm_s6 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 6 acc s → TblDo A W w ((tblPow2 1 0 2).rename ![5, 6, 31]) s (PmF n 7 acc)
      (4 * logT n + 5) :=
  pm_pow2_stage (e := 5) (c := 6) (t := 31) (j := 6) (v := logT n) (by decide) rfl (by decide)
    (by decide) rfl rfl (by have := pm_logT_le hn; omega)

theorem pm_s7 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 7 acc s → TblDo A W w ((pmCeilDivC 1).rename ![5, 3, 7, 31]) s (PmF n 8 acc) 8 :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![5, 3, 7, 31]).val 0 = logT n := by simpa [pmVal, pmNV] using hs.val 5
    have h1 : (s.restrict ![5, 3, 7, 31]).val 1 = d n := by simpa [pmVal, pmNV] using hs.val 3
    have hb := pm_W_pow hW (k := b n + 3) (by omega)
    have e : 2 ^ (b n + 3) = 8 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_b_lt n
    have := pm_logT_le hn
    have := d_le_b n
    refine (pmCeilDivC_do 1 _ h0 h1 (one_le_d hn) (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV, ℓ], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s8 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 8 acc s → TblDo A W w ((tblPow2 1 0 2).rename ![7, 8, 31]) s (PmF n 9 acc)
      (4 * ℓ n + 5) :=
  pm_pow2_stage (e := 7) (c := 8) (t := 31) (j := 8) (v := ℓ n) (by decide) rfl (by decide)
    (by decide) rfl rfl (by have := pm_ℓ_le hn; omega)

theorem pm_s9 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 9 acc s → TblDo A W w ((pmSubKC 1).rename ![7, 9, 31]) s (PmF n 10 acc) 3 :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![7, 9, 31]).val 0 = ℓ n := by simpa [pmVal, pmNV] using hs.val 7
    have hb := pm_W_pow hW (k := b n + 2) (by omega)
    have e : 2 ^ (b n + 2) = 4 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_b_lt n
    have := pm_ℓ_le hn
    refine (pmSubKC_do 1 _ h0 (pm_one_le_ℓ hn) (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s10 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 10 acc s → TblDo A W w ((tblPow2 1 0 2).rename ![9, 10, 31]) s (PmF n 11 acc)
      (4 * (ℓ n - 1) + 5) :=
  pm_pow2_stage (e := 9) (c := 10) (t := 31) (j := 10) (v := ℓ n - 1) (by decide) rfl (by decide)
    (by decide) rfl rfl (by have := pm_ℓ_le hn; omega)

theorem pm_s11 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 11 acc s → TblDo A W w (pmMulSubC.rename ![3, 7, 5, 11]) s (PmF n 12 acc) 2 :=
  pm_stage (by decide) 3 rfl fun s hs => by
    have h0 : (s.restrict ![3, 7, 5, 11]).val 0 = d n := by simpa [pmVal, pmNV] using hs.val 3
    have h1 : (s.restrict ![3, 7, 5, 11]).val 1 = ℓ n := by simpa [pmVal, pmNV] using hs.val 7
    have h2 : (s.restrict ![3, 7, 5, 11]).val 2 = logT n := by simpa [pmVal, pmNV] using hs.val 5
    have hdl : d n * ℓ n ≤ 2 ^ b n * 2 ^ (b n + 2) := Nat.mul_le_mul
      ((d_le_b n).trans (pm_b_lt n).le) (by have := pm_ℓ_le hn; have := pm_b_lt n
                                            rw [pow_add]; omega)
    have e : 2 ^ b n * 2 ^ (b n + 2) = 2 ^ (2 * b n + 2) := by rw [← pow_add]; ring_nf
    have hb := pm_W_pow hW (k := 2 * b n + 3) (by omega)
    have e2 : 2 ^ (2 * b n + 3) = 2 * 2 ^ (2 * b n + 2) := by rw [pow_succ]; ring
    have : 1 ≤ 2 ^ (2 * b n + 2) := Nat.one_le_two_pow
    refine (pmMulSubC_do _ h0 h1 h2 (logT_le_dℓ (one_le_d hn)) (by omega)).mono ?_ le_rfl
    rintro s' ⟨efr, e3, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e3]; simp [pmVal, pmNV, numHalf], fun y hy => ?_⟩
    fin_cases y
    · show s'.val 0 = pmVal n 3
      rw [efr 0 (by decide), h0]; simp [pmVal]
    · show s'.val 1 = pmVal n 7
      rw [efr 1 (by decide), h1]; simp [pmVal]
    · show s'.val 2 = pmVal n 5
      rw [efr 2 (by decide), h2]; simp [pmVal]
    · simp [pmNV] at hy

theorem pm_s12 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 12 acc s → TblDo A W w (pmAlphaC.rename ![3, 1, 12, 31, 32]) s (PmF n 13 acc)
      (5 * alpha n + 20) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![3, 1, 12, 31, 32]).val 0 = d n := by simpa [pmVal, pmNV] using hs.val 3
    have h1 : (s.restrict ![3, 1, 12, 31, 32]).val 1 = b n := by simpa [pmVal, pmNV] using hs.val 1
    have hd := d_le_b n
    have hbt := pm_b_lt n
    have h3 : d n ^ 2 * b n ≤ 2 ^ b n * 2 ^ b n * 2 ^ b n := by
      rw [sq]; exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hbt.le
    have e : 2 ^ (3 * b n + 5) = 32 * (2 ^ b n * 2 ^ b n * 2 ^ b n) := by
      rw [show 3 * b n + 5 = 5 + (b n + b n + b n) by ring, pow_add, pow_add, pow_add]; ring
    have hb := pm_W_pow hW (k := 3 * b n + 5) (by omega)
    have h4 : 1 ≤ 2 ^ b n * 2 ^ b n * 2 ^ b n := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e2 : 12 * d n ^ 2 * b n = 12 * (d n ^ 2 * b n) := by ring
    refine (pmAlphaC_do _ h0 h1 (one_le_b hn) (pmQuart_alpha n) (by omega)
      (lt_of_lt_of_le (pm_alpha_four_lt hn) (pm_W_pow hW (by omega)))).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s13 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 13 acc s → TblDo A W w (pmSqC.rename ![12, 13]) s (PmF n 14 acc) 1 :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![12, 13]).val 0 = alpha n := by simpa [pmVal, pmNV] using hs.val 12
    have h1 := pm_alpha_sq_le n
    have h2 := lt_of_lt_of_le (pm_alpha_four_lt hn) (pm_W_pow hW (by omega))
    refine (pmSqC_do _ h0 (by rw [← sq]; omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s14 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 14 acc s → TblDo A W w (pmGammaC.rename ![3, 13, 14, 31]) s (PmF n 15 acc) 4 :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![3, 13, 14, 31]).val 0 = d n := by simpa [pmVal, pmNV] using hs.val 3
    have h1 : (s.restrict ![3, 13, 14, 31]).val 1 = alpha n ^ 2 := by
      simpa [pmVal, pmNV] using hs.val 13
    have hα := pm_alpha_sq_le n
    have hα4 := pm_alpha_four_lt hn
    have hd1 : d n + 1 ≤ 2 ^ b n := by have := d_le_b n; have := pm_b_lt n; omega
    have e : 2 ^ (3 * b n + 10) = 4 * 2 ^ (3 * b n + 8) := by
      rw [show 3 * b n + 10 = 2 + (3 * b n + 8) by ring, pow_add]; norm_num
    have h2 : 2 * alpha n ^ 2 + 3 ≤ 2 ^ (3 * b n + 10) := by omega
    have e2 : 2 ^ b n * 2 ^ (3 * b n + 10) = 2 ^ (4 * b n + 10) := by rw [← pow_add]; ring_nf
    have hb := pm_W_pow hW (k := 4 * b n + 10) (by omega)
    refine (pmGammaC_do _ h0 h1 ?_).mono ?_ le_rfl
    · calc (d n + 1) * (2 * alpha n ^ 2 + 3) ≤ 2 ^ b n * 2 ^ (3 * b n + 10) :=
            Nat.mul_le_mul hd1 h2
        _ ≤ 2 ^ W := by rw [e2]; exact hb
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV, gamma], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s15 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 15 acc s → TblDo A W w ((pmCeilDivC 1).rename ![0, 1, 15, 31]) s
      (PmF n 16 acc) 8 :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![0, 1, 15, 31]).val 0 = n := by simpa [pmVal, pmNV] using hs.val 0
    have h1 : (s.restrict ![0, 1, 15, 31]).val 1 = b n := by simpa [pmVal, pmNV] using hs.val 1
    have hb := pm_W_pow hW (k := b n + 3) (by omega)
    have e : 2 ^ (b n + 3) = 8 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_n_le n
    have := pm_b_lt n
    refine (pmCeilDivC_do 1 _ h0 h1 (one_le_b hn) (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV, q], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s16 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 16 acc s → TblDo A W w (pmOddC.rename ![3, 16, 31, 32, 33]) s (PmF n 17 acc)
      (12 * d n + 6) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![3, 16, 31, 32, 33]).val 0 = d n := by simpa [pmVal, pmNV] using hs.val 3
    have hb := pm_W_pow hW (k := b n + 5) (by omega)
    have e : 2 ^ (b n + 5) = 2 * 2 ^ (b n + 4) := by rw [pow_succ]; ring
    have e2 : 2 ^ (b n + 4) = 16 * 2 ^ b n := by rw [pow_add]; ring
    have := pm_N_le hn
    have := d_le_b n
    have := pm_b_lt n
    have hN : N n = oddProd (d n) := rfl
    refine (pmOddC_do _ h0 (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, N], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s17 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 17 acc s → TblDo A W w (pmStartC.rename ![3, 10, 16, 17, 31, 32]) s
      (PmF n 18 acc) 11 :=
  pm_stage (by decide) 3 rfl fun s hs => by
    have h0 : (s.restrict ![3, 10, 16, 17, 31, 32]).val 0 = d n := by
      simpa [pmVal, pmNV] using hs.val 3
    have h1 : (s.restrict ![3, 10, 16, 17, 31, 32]).val 1 = 2 ^ (ℓ n - 1) := by
      simpa [pmVal, pmNV] using hs.val 10
    have h2 : (s.restrict ![3, 10, 16, 17, 31, 32]).val 2 = N n := by
      simpa [pmVal, pmNV] using hs.val 16
    have hd : d n ≤ 2 ^ b n := (d_le_b n).trans (pm_b_lt n).le
    have hN := pm_N_le hn
    have hR : 2 ^ (ℓ n - 1) ≤ 2 ^ (b n + 1) := pm_two_pow_le (by have := pm_ℓ_le hn; omega)
    have h3 : d n * N n ≤ 2 ^ b n * 2 ^ (b n + 4) := Nat.mul_le_mul hd hN
    have h4 : d n * 2 ^ (ℓ n - 1) ≤ 2 ^ b n * 2 ^ (b n + 1) := Nat.mul_le_mul hd hR
    have e3 : 2 ^ b n * 2 ^ (b n + 4) = 16 * 2 ^ (2 * b n) := by
      rw [← pow_add, show b n + (b n + 4) = 4 + 2 * b n by ring, pow_add]; norm_num
    have e4 : 2 ^ b n * 2 ^ (b n + 1) = 2 * 2 ^ (2 * b n) := by
      rw [← pow_add, show b n + (b n + 1) = 1 + 2 * b n by ring, pow_add]; norm_num
    have e5 : 2 ^ (2 * b n + 7) = 128 * 2 ^ (2 * b n) := by rw [pow_add]; ring
    have hb := pm_W_pow hW (k := 2 * b n + 7) (by omega)
    have h6 : 1 ≤ 2 ^ (2 * b n) := Nat.one_le_two_pow
    have e6 : 4 * d n * N n = 4 * (d n * N n) := by ring
    have e7 : 4 * d n * 2 ^ (ℓ n - 1) = 4 * (d n * 2 ^ (ℓ n - 1)) := by ring
    refine (pmStartC_do _ h0 h1 h2 (one_le_d hn) (pm_one_le_N n) (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, e3, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e3]; simp [pmVal, pmNV, pmX0], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s18 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 18 acc s → TblDo A W w (pmProdSC.rename ![16, 17, 11, 3, 18, 31, 32, 33]) s
      (PmF n 19 acc) (13 * d n + 5) :=
  pm_stage (by decide) 4 rfl fun s hs => by
    have h0 : (s.restrict ![16, 17, 11, 3, 18, 31, 32, 33]).val 0 = N n := by
      simpa [pmVal, pmNV] using hs.val 16
    have h1 : (s.restrict ![16, 17, 11, 3, 18, 31, 32, 33]).val 1 = pmX0 n := by
      simpa [pmVal, pmNV] using hs.val 17
    have h2 : (s.restrict ![16, 17, 11, 3, 18, 31, 32, 33]).val 2 = numHalf n := by
      simpa [pmVal, pmNV] using hs.val 11
    have h3 : (s.restrict ![16, 17, 11, 3, 18, 31, 32, 33]).val 3 = d n := by
      simpa [pmVal, pmNV] using hs.val 3
    have hS : pmSProd (N n) (pmX0 n) (numHalf n) (d n) = S n := (pm_S_prod n).symm
    refine (pmProdSC_do _ h0 h1 h2 h3 (pm_one_le_N n)
      (fun i hi => lt_of_lt_of_le (pm_modBound_lt hn hi) (pm_W_pow hW (by omega)))
      (by rw [hS]; exact lt_of_lt_of_le (pm_S_lt hn) (pm_W_pow hW (by omega)))
      (lt_of_lt_of_le ((d_le_b n).trans_lt (pm_b_lt n)) (pm_W_pow hW (by omega)))).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, e3, e4, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e4, hS]; simp [pmVal, pmNV], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s19 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 19 acc s → TblDo A W w (pmWinAC.rename ![2, 13, 19, 31, 32, 33]) s
      (PmF n 20 acc) (6 * Nat.sqrt (p n * alpha n ^ 2) + 9) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![2, 13, 19, 31, 32, 33]).val 0 = p n := by simpa [pmVal, pmNV] using hs.val 2
    have h1 : (s.restrict ![2, 13, 19, 31, 32, 33]).val 1 = alpha n ^ 2 := by
      simpa [pmVal, pmNV] using hs.val 13
    have h2 := pm_p_alpha_sq_lt hn
    have e : 2 ^ (4 * b n + 13) = 4 * 2 ^ (4 * b n + 11) := by
      rw [show 4 * b n + 13 = 2 + (4 * b n + 11) by ring, pow_add]; norm_num
    have hb := pm_W_pow hW (k := 4 * b n + 13) (by omega)
    refine (pmWinAC_do _ h0 h1 (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV, windowA], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s20 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 20 acc s → TblDo A W w (pmWinBC.rename ![2, 12, 20, 31, 32, 33, 34]) s
      (PmF n 21 acc) (6 * Nat.sqrt (p n) + 10) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![2, 12, 20, 31, 32, 33, 34]).val 0 = p n := by
      simpa [pmVal, pmNV] using hs.val 2
    have h1 : (s.restrict ![2, 12, 20, 31, 32, 33, 34]).val 1 = alpha n := by
      simpa [pmVal, pmNV] using hs.val 12
    have hα4 := pm_alpha_four_lt hn
    have hα : alpha n ≤ alpha n ^ 4 := Nat.le_self_pow (by norm_num) _
    have hp : p n = 6 * b n := rfl
    have := pm_b_lt n
    have e : 2 ^ (3 * b n + 10) = 4 * 2 ^ (3 * b n + 8) := by
      rw [show 3 * b n + 10 = 2 + (3 * b n + 8) by ring, pow_add]; norm_num
    have e2 : 2 ^ (b n + 5) ≤ 2 ^ (3 * b n + 8) := pm_two_pow_le (by omega)
    have e3 : 2 ^ (b n + 5) = 32 * 2 ^ b n := by rw [pow_add]; ring
    have hb := pm_W_pow hW (k := 3 * b n + 10) (by omega)
    refine (pmWinBC_do _ h0 h1 (by omega)).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV, fastWindow], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

/-- Bounds for the precision stages: every value at most `64 b + 64`. -/
theorem pm_small_lt (hW : 4 * b n + 32 ≤ W) {x : ℕ} (hx : x ≤ 64 * b n + 64) : x < 2 ^ W := by
  have hb := pm_W_pow hW (k := b n + 7) (by omega)
  have e : 2 ^ (b n + 7) = 128 * 2 ^ b n := by rw [pow_add]; ring
  have := pm_b_lt n
  omega

theorem pm_g_le (n : ℕ) : chirpGuard (d n) ≤ b n + 4 := by
  unfold chirpGuard
  have := pm_clog_le_self (d n)
  have := d_le_b n
  omega

theorem pm_tg_le (p g : ℕ) : taylorGuard p g ≤ p + g + 18 := by
  unfold taylorGuard taylorTerms
  have := pm_clog_le_self (p + g + 14)
  omega

theorem pm_s21 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 21 acc s → TblDo A W w ((pmClogAddC 4).rename ![3, 21, 31, 32]) s (PmF n 22 acc)
      (4 * Nat.clog 2 (d n) + 4 + 7) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![3, 21, 31, 32]).val 0 = d n := by simpa [pmVal, pmNV] using hs.val 3
    have := d_le_b n
    refine (pmClogAddC_do 4 _ h0 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, chirpGuard], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s22 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 22 acc s → TblDo A W w ((pmLinC 1 14).rename ![2, 22, 31, 32]) s (PmF n 23 acc)
      (1 + 14 + 4) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![2, 22, 31, 32]).val 0 = p n := by simpa [pmVal, pmNV] using hs.val 2
    have hp : p n = 6 * b n := rfl
    refine (pmLinC_do 1 14 _ h0 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, taylorTerms], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s23 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 23 acc s → TblDo A W w ((pmClogAddC 4).rename ![22, 23, 31, 32]) s
      (PmF n 24 acc) (4 * Nat.clog 2 (taylorTerms (p n) 0) + 4 + 7) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![22, 23, 31, 32]).val 0 = taylorTerms (p n) 0 := by
      simpa [pmVal, pmNV] using hs.val 22
    have hp : taylorTerms (p n) 0 = 6 * b n + 0 + 14 := rfl
    refine (pmClogAddC_do 4 _ h0 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, taylorGuard], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s24 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 24 acc s → TblDo A W w ((pmLin2C 1 2).rename ![2, 23, 24, 31, 32]) s
      (PmF n 25 acc) (1 + 2 + 5) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![2, 23, 24, 31, 32]).val 0 = p n := by simpa [pmVal, pmNV] using hs.val 2
    have h1 : (s.restrict ![2, 23, 24, 31, 32]).val 1 = taylorGuard (p n) 0 := by
      simpa [pmVal, pmNV] using hs.val 23
    have hp : p n = 6 * b n := rfl
    have := pm_tg_le (p n) 0
    refine (pmLin2C_do 1 2 _ h0 h1 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV]; ring, fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s25 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 25 acc s → TblDo A W w ((pmLinC 5 4).rename ![2, 25, 31, 32]) s (PmF n 26 acc)
      (5 + 4 + 4) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![2, 25, 31, 32]).val 0 = p n := by simpa [pmVal, pmNV] using hs.val 2
    have hp : p n = 6 * b n := rfl
    refine (pmLinC_do 5 4 _ h0 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s26 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 26 acc s → TblDo A W w ((pmLin2C 1 14).rename ![2, 21, 26, 31, 32]) s
      (PmF n 27 acc) (1 + 14 + 5) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![2, 21, 26, 31, 32]).val 0 = p n := by simpa [pmVal, pmNV] using hs.val 2
    have h1 : (s.restrict ![2, 21, 26, 31, 32]).val 1 = chirpGuard (d n) := by
      simpa [pmVal, pmNV] using hs.val 21
    have hp : p n = 6 * b n := rfl
    have := pm_g_le n
    refine (pmLin2C_do 1 14 _ h0 h1 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV, taylorTerms], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s27 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 27 acc s → TblDo A W w ((pmClogAddC 4).rename ![26, 27, 31, 32]) s
      (PmF n 28 acc) (4 * Nat.clog 2 (taylorTerms (p n) (chirpGuard (d n))) + 4 + 7) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![26, 27, 31, 32]).val 0 = taylorTerms (p n) (chirpGuard (d n)) := by
      simpa [pmVal, pmNV] using hs.val 26
    have hp : taylorTerms (p n) (chirpGuard (d n)) = 6 * b n + chirpGuard (d n) + 14 := rfl
    have := pm_g_le n
    refine (pmClogAddC_do 4 _ h0 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, taylorGuard], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s28 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 28 acc s → TblDo A W w ((pmLin2C 1 0).rename ![2, 21, 28, 31, 32]) s
      (PmF n 29 acc) (1 + 0 + 5) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![2, 21, 28, 31, 32]).val 0 = p n := by simpa [pmVal, pmNV] using hs.val 2
    have h1 : (s.restrict ![2, 21, 28, 31, 32]).val 1 = chirpGuard (d n) := by
      simpa [pmVal, pmNV] using hs.val 21
    have hp : p n = 6 * b n := rfl
    have := pm_g_le n
    refine (pmLin2C_do 1 0 _ h0 h1 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s29 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 29 acc s → TblDo A W w ((pmLin2C 1 2).rename ![28, 27, 29, 31, 32]) s
      (PmF n 30 acc) (1 + 2 + 5) :=
  pm_stage (by decide) 2 rfl fun s hs => by
    have h0 : (s.restrict ![28, 27, 29, 31, 32]).val 0 = p n + chirpGuard (d n) := by
      simpa [pmVal, pmNV] using hs.val 28
    have h1 : (s.restrict ![28, 27, 29, 31, 32]).val 1 = taylorGuard (p n) (chirpGuard (d n)) := by
      simpa [pmVal, pmNV] using hs.val 27
    have hp : p n = 6 * b n := rfl
    have := pm_g_le n
    have := pm_tg_le (p n) (chirpGuard (d n))
    refine (pmLin2C_do 1 2 _ h0 h1 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e2]; simp [pmVal, pmNV]; ring, fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s30 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 30 acc s → TblDo A W w ((pmLinC 5 4).rename ![28, 30, 31, 32]) s (PmF n 31 acc)
      (5 + 4 + 4) :=
  pm_stage (by decide) 1 rfl fun s hs => by
    have h0 : (s.restrict ![28, 30, 31, 32]).val 0 = p n + chirpGuard (d n) := by
      simpa [pmVal, pmNV] using hs.val 28
    have hp : p n = 6 * b n := rfl
    have := pm_g_le n
    refine (pmLinC_do 5 4 _ h0 (pm_small_lt hW (by omega)).le).mono ?_ le_rfl
    rintro s' ⟨e0, e1, ea⟩
    refine ⟨by rw [ea]; exact hs.1, by rw [e1]; simp [pmVal, pmNV, anglePrec], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

/-- The emitted axis lengths `t_0, …, t_{d-1}`, as pair symbols. -/
def pmTList (A w n : ℕ) : List (Fin (A + 4)) :=
  pmEmitList A w (pmTv (numHalf n) (2 ^ (ℓ n - 1)) (r n)) (d n)

/-- The emitted source lengths `s_0, …, s_{d-1}`, as pair symbols. -/
def pmSList (A w n : ℕ) : List (Fin (A + 4)) :=
  pmEmitList A w (modulus (N n) (pmX0 n) (numHalf n)) (d n)

theorem pm_s31 (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 31 acc s → TblDo A W w (pmEmitTC.rename ![3, 11, 10, 8, 31, 32]) s
      (PmF n 31 ((pmTList A w n).reverse ++ acc)) (6 * d n + 3) :=
  pm_stage_acc (by decide) fun s hs => by
    have h0 : (s.restrict ![3, 11, 10, 8, 31, 32]).val 0 = d n := by
      simpa [pmVal, pmNV] using hs.val 3
    have h1 : (s.restrict ![3, 11, 10, 8, 31, 32]).val 1 = numHalf n := by
      simpa [pmVal, pmNV] using hs.val 11
    have h2 : (s.restrict ![3, 11, 10, 8, 31, 32]).val 2 = 2 ^ (ℓ n - 1) := by
      simpa [pmVal, pmNV] using hs.val 10
    have h3 : (s.restrict ![3, 11, 10, 8, 31, 32]).val 3 = r n := by
      simpa [pmVal, pmNV] using hs.val 8
    have hd : d n < 2 ^ W := lt_of_lt_of_le ((d_le_b n).trans_lt (pm_b_lt n)) (pm_W_pow hW (by omega))
    refine (pmEmitTC_do _ h0 h1 h2 h3 hd).mono ?_ le_rfl
    rintro s' ⟨e0, e1, e2, e3, ea⟩
    refine ⟨by rw [ea]; simp [hs.1, pmTList], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

theorem pm_s32 (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 31 acc s → TblDo A W w (pmEmitSC.rename ![16, 17, 11, 3, 31, 32, 33]) s
      (PmF n 31 ((pmSList A w n).reverse ++ acc)) (13 * d n + 3) :=
  pm_stage_acc (by decide) fun s hs => by
    have h0 : (s.restrict ![16, 17, 11, 3, 31, 32, 33]).val 0 = N n := by
      simpa [pmVal, pmNV] using hs.val 16
    have h1 : (s.restrict ![16, 17, 11, 3, 31, 32, 33]).val 1 = pmX0 n := by
      simpa [pmVal, pmNV] using hs.val 17
    have h2 : (s.restrict ![16, 17, 11, 3, 31, 32, 33]).val 2 = numHalf n := by
      simpa [pmVal, pmNV] using hs.val 11
    have h3 : (s.restrict ![16, 17, 11, 3, 31, 32, 33]).val 3 = d n := by
      simpa [pmVal, pmNV] using hs.val 3
    have hd : d n < 2 ^ W := lt_of_lt_of_le ((d_le_b n).trans_lt (pm_b_lt n)) (pm_W_pow hW (by omega))
    refine (pmEmitSC_do _ h0 h1 h2 h3 (pm_one_le_N n)
      (fun i hi => lt_of_lt_of_le (pm_modBound_lt hn hi) (pm_W_pow hW (by omega))) hd).mono ?_
      le_rfl
    rintro s' ⟨e0, e1, e2, e3, ea⟩
    refine ⟨by rw [ea]; simp [hs.1, pmSList], fun y hy => ?_⟩
    fin_cases y <;> simp [pmVal, pmNV] at hy ⊢ <;> assumption

/-- Clear the scratch variables `31, …, 39`. -/
def pmClearC : TblCode pmNV :=
  tblBlock pmNV [.zero 31, .zero 32, .zero 33, .zero 34, .zero 35, .zero 36, .zero 37, .zero 38]
    (.zero 39)

theorem pmVal_ge (n k : ℕ) (hk : 31 ≤ k) : pmVal n k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 31 := ⟨k - 31, by omega⟩
  rfl

theorem pm_clear_do (s : TblSt pmNV A) (hs : PmF n 31 acc s) :
    TblDo A W w pmClearC s (fun s' => s'.val = pmVals n ∧ s'.acc = acc) 9 := by
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ⟨funext fun i => ?_, ?_⟩
  · by_cases hi : i.val < 31
    · have hne : ∀ c : Fin pmNV, 31 ≤ c.val → i ≠ c := fun c hc h => by subst h; omega
      simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append, pmVals]
      rw [Function.update_of_ne (hne 39 (by decide)), Function.update_of_ne (hne 38 (by decide)),
        Function.update_of_ne (hne 37 (by decide)), Function.update_of_ne (hne 36 (by decide)),
        Function.update_of_ne (hne 35 (by decide)), Function.update_of_ne (hne 34 (by decide)),
        Function.update_of_ne (hne 33 (by decide)), Function.update_of_ne (hne 32 (by decide)),
        Function.update_of_ne (hne 31 (by decide))]
      exact hs.2 i hi
    · obtain ⟨k, hk⟩ := i
      simp only at hi
      rw [pmVals, pmVal_ge n k (by omega)]
      simp [pmNV] at hk
      interval_cases k <;> simp [tblExactList, TblIns.exact, Function.update_apply, Fin.ext_iff, pmNV]
  · simp [tblExactList, TblIns.exact, hs.1]

end Stages

/-! ### The programs -/

/-- The 30 parameter stages. -/
def pmStages : TblCode pmNV :=
  pmClogC.rename ![0, 1, 31] ;;
  (pmLinC 6 0).rename ![1, 2, 31, 32] ;;
  compactDyadicParamStage ;;
  (pmIrootC 32).rename ![3, 4, 31, 32, 33, 34] ;;
  pmLogTC.rename ![0, 1, 5, 31, 32] ;;
  (tblPow2 1 0 2).rename ![5, 6, 31] ;;
  (pmCeilDivC 1).rename ![5, 3, 7, 31] ;;
  (tblPow2 1 0 2).rename ![7, 8, 31] ;;
  (pmSubKC 1).rename ![7, 9, 31] ;;
  (tblPow2 1 0 2).rename ![9, 10, 31] ;;
  pmMulSubC.rename ![3, 7, 5, 11] ;;
  pmAlphaC.rename ![3, 1, 12, 31, 32] ;;
  pmSqC.rename ![12, 13] ;;
  pmGammaC.rename ![3, 13, 14, 31] ;;
  (pmCeilDivC 1).rename ![0, 1, 15, 31] ;;
  pmOddC.rename ![3, 16, 31, 32, 33] ;;
  pmStartC.rename ![3, 10, 16, 17, 31, 32] ;;
  pmProdSC.rename ![16, 17, 11, 3, 18, 31, 32, 33] ;;
  pmWinAC.rename ![2, 13, 19, 31, 32, 33] ;;
  pmWinBC.rename ![2, 12, 20, 31, 32, 33, 34] ;;
  (pmClogAddC 4).rename ![3, 21, 31, 32] ;;
  (pmLinC 1 14).rename ![2, 22, 31, 32] ;;
  (pmClogAddC 4).rename ![22, 23, 31, 32] ;;
  (pmLin2C 1 2).rename ![2, 23, 24, 31, 32] ;;
  (pmLinC 5 4).rename ![2, 25, 31, 32] ;;
  (pmLin2C 1 14).rename ![2, 21, 26, 31, 32] ;;
  (pmClogAddC 4).rename ![26, 27, 31, 32] ;;
  (pmLin2C 1 0).rename ![2, 21, 28, 31, 32] ;;
  (pmLin2C 1 2).rename ![28, 27, 29, 31, 32] ;;
  (pmLinC 5 4).rename ![28, 30, 31, 32]

/-- The first parameter program: the stages, the emission of the axis lengths, the cleanup. -/
def pmCode1 : TblCode pmNV := pmStages ;; pmEmitTC.rename ![3, 11, 10, 8, 31, 32] ;; pmClearC

/-- The second parameter program: the emission of the source lengths, the cleanup. -/
def pmCode2 : TblCode pmNV := pmEmitSC.rename ![16, 17, 11, 3, 31, 32, 33] ;; pmClearC

/-- The atoms of `pmCode1`. -/
def pmAtoms1 (n : ℕ) : ℕ :=
  1204 + 4 * b n + 489 * d n + 344 * K n + 8 * logT n + 8 * ℓ n + 5 * alpha n +
    6 * Nat.sqrt (p n * alpha n ^ 2) + 6 * Nat.sqrt (p n) + 4 * Nat.clog 2 (d n) +
    4 * Nat.clog 2 (taylorTerms (p n) 0) + 4 * Nat.clog 2 (taylorTerms (p n) (chirpGuard (d n)))

/-- The atoms of `pmCode2`. -/
def pmAtoms2 (n : ℕ) : ℕ := 13 * d n + 12

section Main

variable {n : ℕ} {acc : List (Fin (A + 4))}

theorem pmStages_do (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) :
    ∀ s, PmF n 1 acc s → TblDo A W w pmStages s (PmF n 31 acc)
      ((4 * b n + 5) + (10 + ((7 * 30 + 11 + d n * (6 * 30 + 8)) +
        ((7 * 34 + 11 + K n * (6 * 34 + 8)) + ((4 * logT n + 16) + ((4 * logT n + 5) + (8 +
        ((4 * ℓ n + 5) + (3 + ((4 * (ℓ n - 1) + 5) + (2 + ((5 * alpha n + 20) + (1 + (4 + (8 +
        ((12 * d n + 6) + (11 + ((13 * d n + 5) + ((6 * Nat.sqrt (p n * alpha n ^ 2) + 9) +
        ((6 * Nat.sqrt (p n) + 10) + ((4 * Nat.clog 2 (d n) + 4 + 7) + ((1 + 14 + 4) +
        ((4 * Nat.clog 2 (taylorTerms (p n) 0) + 4 + 7) + ((1 + 2 + 5) + ((5 + 4 + 4) +
        ((1 + 14 + 5) + ((4 * Nat.clog 2 (taylorTerms (p n) (chirpGuard (d n))) + 4 + 7) +
        ((1 + 0 + 5) + ((1 + 2 + 5) + (5 + 4 + 4)))))))))))))))))))))))))))))) :=
  pm_seq (pm_s1 hn hW) <| pm_seq (pm_s2 hW) <| pm_seq (pm_s3 hW) <| pm_seq (pm_s4 hW) <|
  pm_seq (pm_s5 hn hW) <| pm_seq (pm_s6 hn hW) <| pm_seq (pm_s7 hn hW) <|
  pm_seq (pm_s8 hn hW) <| pm_seq (pm_s9 hn hW) <| pm_seq (pm_s10 hn hW) <|
  pm_seq (pm_s11 hn hW) <| pm_seq (pm_s12 hn hW) <| pm_seq (pm_s13 hn hW) <|
  pm_seq (pm_s14 hn hW) <| pm_seq (pm_s15 hn hW) <| pm_seq (pm_s16 hn hW) <|
  pm_seq (pm_s17 hn hW) <| pm_seq (pm_s18 hn hW) <| pm_seq (pm_s19 hn hW) <|
  pm_seq (pm_s20 hn hW) <| pm_seq (pm_s21 hW) <| pm_seq (pm_s22 hW) <| pm_seq (pm_s23 hW) <|
  pm_seq (pm_s24 hW) <| pm_seq (pm_s25 hW) <| pm_seq (pm_s26 hW) <| pm_seq (pm_s27 hW) <|
  pm_seq (pm_s28 hW) <| pm_seq (pm_s29 hW) (pm_s30 hW)

/-- **The first parameter program.** From `n ≥ 2` in variable `0` (`PmF n 1 acc`) and words of
`W ≥ 4 b + 32` bits, `pmCode1` ends with every variable `i` holding `pmVals n i` and the axis
lengths emitted in front of `acc`, within `pmAtoms1 n` atoms. -/
theorem pmCode1_do (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) (st : TblSt pmNV A)
    (hst : PmF n 1 acc st) :
    TblDo A W w pmCode1 st (fun s => s.val = pmVals n ∧ s.acc = (pmTList A w n).reverse ++ acc)
      (pmAtoms1 n) := by
  refine ((pmStages_do hn hW st hst).seq (fun s hs => (pm_s31 hW s hs).seq
    (fun s' hs' => pm_clear_do s' hs'))).mono (fun _ h => h) ?_
  have hl : 4 * (ℓ n - 1) ≤ 4 * ℓ n := by omega
  unfold pmAtoms1
  linarith

/-- **The second parameter program.** From the final state of `pmCode1` with `acc` emptied,
`pmCode2` ends in the same values with the source lengths emitted, within `pmAtoms2 n` atoms. -/
theorem pmCode2_do (hn : 2 ≤ n) (hW : 4 * b n + 32 ≤ W) (st : TblSt pmNV A)
    (hst : PmF n 31 acc st) :
    TblDo A W w pmCode2 st (fun s => s.val = pmVals n ∧ s.acc = (pmSList A w n).reverse ++ acc)
      (pmAtoms2 n) :=
  ((pm_s32 hn hW st hst).seq (fun s hs => pm_clear_do s hs)).mono (fun _ h => h)
    (by unfold pmAtoms2; omega)

end Main

/-! ### Atom counts -/

theorem pm_alpha_le (hn : 2 ≤ n) : alpha n ≤ 4 * b n := by
  by_contra h
  have h1 : (4 * b n + 1) ^ 4 ≤ alpha n ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 := alpha_pow_four_le hn
  have h3 : d n ^ 2 * b n ≤ b n ^ 3 := by
    calc d n ^ 2 * b n ≤ b n ^ 2 * b n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (d_le_b n) 2)
      _ = b n ^ 3 := by ring
  have h4 : 192 * b n ^ 3 < (4 * b n + 1) ^ 4 := by
    have := one_le_b hn
    nlinarith [pow_pos (show 0 < b n by omega) 3, pow_pos (show 0 < b n by omega) 4]
  have e : 192 * d n ^ 2 * b n = 192 * (d n ^ 2 * b n) := by ring
  omega

theorem pm_sqrt_le (hn : 2 ≤ n) : Nat.sqrt (p n * alpha n ^ 2) ≤ 24 * b n ^ 2 := by
  have h1 : p n * alpha n ^ 2 ≤ (p n * alpha n) ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have h2 : Nat.sqrt (p n * alpha n ^ 2) ≤ p n * alpha n := by
    calc Nat.sqrt (p n * alpha n ^ 2) ≤ Nat.sqrt ((p n * alpha n) ^ 2) := Nat.sqrt_le_sqrt h1
      _ = p n * alpha n := Nat.sqrt_eq' _
  have h3 : p n * alpha n ≤ 6 * b n * (4 * b n) := Nat.mul_le_mul_left _ (pm_alpha_le hn)
  have e : 6 * b n * (4 * b n) = 24 * b n ^ 2 := by ring
  omega

/-- `pmAtoms1 n ≤ 2500 (b + 1)²`. -/
theorem pmAtoms1_le (hn : 2 ≤ n) : pmAtoms1 n ≤ 2500 * (b n + 1) ^ 2 := by
  have hd := d_le_b n
  have hK := K_le_d n
  have hL := pm_logT_le hn
  have hl := pm_ℓ_le hn
  have ha := pm_alpha_le hn
  have hs := pm_sqrt_le hn
  have hp : Nat.sqrt (p n) ≤ 6 * b n := (Nat.sqrt_le_self _).trans le_rfl
  have hc1 : Nat.clog 2 (d n) ≤ b n := (pm_clog_le_self _).trans hd
  have hc2 : Nat.clog 2 (taylorTerms (p n) 0) ≤ 6 * b n + 14 :=
    (pm_clog_le_self _).trans (by unfold taylorTerms p; omega)
  have hc3 : Nat.clog 2 (taylorTerms (p n) (chirpGuard (d n))) ≤ 7 * b n + 18 :=
    (pm_clog_le_self _).trans (by have := pm_g_le n; unfold taylorTerms p; omega)
  have e : (b n + 1) ^ 2 = b n ^ 2 + 2 * b n + 1 := by ring
  unfold pmAtoms1
  nlinarith

/-- `pmAtoms2 n ≤ 25 (b + 1)²`. -/
theorem pmAtoms2_le (n : ℕ) : pmAtoms2 n ≤ 25 * (b n + 1) ^ 2 := by
  have hd := d_le_b n
  have e : (b n + 1) ^ 2 = b n ^ 2 + 2 * b n + 1 := by ring
  unfold pmAtoms2
  nlinarith

/-! ### The values -/

/-- Variable names. -/
abbrev pmIn : Fin pmNV := 0
abbrev pmIb : Fin pmNV := 1
abbrev pmIp : Fin pmNV := 2
abbrev pmId : Fin pmNV := 3
abbrev pmIK : Fin pmNV := 4
abbrev pmIlogT : Fin pmNV := 5
abbrev pmIT : Fin pmNV := 6
abbrev pmIℓ : Fin pmNV := 7
abbrev pmIr : Fin pmNV := 8
abbrev pmIe : Fin pmNV := 9
abbrev pmIR : Fin pmNV := 10
abbrev pmInumHalf : Fin pmNV := 11
abbrev pmIalpha : Fin pmNV := 12
abbrev pmIalphaSq : Fin pmNV := 13
abbrev pmIgamma : Fin pmNV := 14
abbrev pmIq : Fin pmNV := 15
abbrev pmIN : Fin pmNV := 16
abbrev pmIx0 : Fin pmNV := 17
abbrev pmIS : Fin pmNV := 18
abbrev pmIwinA : Fin pmNV := 19
abbrev pmIwinB : Fin pmNV := 20
abbrev pmIg : Fin pmNV := 21
abbrev pmItwTerms : Fin pmNV := 22
abbrev pmItwGuard : Fin pmNV := 23
abbrev pmItwPrec : Fin pmNV := 24
abbrev pmItwAngle : Fin pmNV := 25
abbrev pmIchTerms : Fin pmNV := 26
abbrev pmIchGuard : Fin pmNV := 27
abbrev pmIchRound : Fin pmNV := 28
abbrev pmIchPrec : Fin pmNV := 29
abbrev pmIchAngle : Fin pmNV := 30

theorem pm_n_eq (n : ℕ) : pmVals n pmIn = n := rfl
theorem pm_b_eq (n : ℕ) : pmVals n pmIb = b n := rfl
theorem pm_p_eq (n : ℕ) : pmVals n pmIp = p n := rfl
theorem pm_d_eq (n : ℕ) : pmVals n pmId = d n := rfl
theorem pm_K_eq (n : ℕ) : pmVals n pmIK = K n := rfl
theorem pm_logT_eq (n : ℕ) : pmVals n pmIlogT = logT n := rfl
theorem pm_T_eq (n : ℕ) : pmVals n pmIT = T n := rfl
theorem pm_ℓ_eq (n : ℕ) : pmVals n pmIℓ = ℓ n := rfl
theorem pm_r_eq (n : ℕ) : pmVals n pmIr = r n := rfl
theorem pm_e_eq (n : ℕ) : pmVals n pmIe = ℓ n - 1 := rfl
theorem pm_R_eq (n : ℕ) : pmVals n pmIR = 2 ^ (ℓ n - 1) := rfl
theorem pm_numHalf_eq (n : ℕ) : pmVals n pmInumHalf = numHalf n := rfl
theorem pm_alpha_eq (n : ℕ) : pmVals n pmIalpha = alpha n := rfl
theorem pm_alphaSq_eq (n : ℕ) : pmVals n pmIalphaSq = alpha n ^ 2 := rfl
theorem pm_gamma_eq (n : ℕ) : pmVals n pmIgamma = gamma n := rfl
theorem pm_q_eq (n : ℕ) : pmVals n pmIq = q n := rfl
theorem pm_N_eq (n : ℕ) : pmVals n pmIN = N n := rfl
theorem pm_x0_eq (n : ℕ) : pmVals n pmIx0 = start (d n) (N n) (2 ^ (ℓ n - 1)) := rfl
theorem pm_S_eq (n : ℕ) : pmVals n pmIS = S n := rfl
theorem pm_windowA_eq (n : ℕ) : pmVals n pmIwinA = windowA (p n) (alpha n) := rfl
theorem pm_fastWindow_eq (n : ℕ) : pmVals n pmIwinB = fastWindow (p n) (alpha n) := rfl
theorem pm_chirpGuard_eq (n : ℕ) : pmVals n pmIg = chirpGuard (d n) := rfl
theorem pm_twTerms_eq (n : ℕ) : pmVals n pmItwTerms = taylorTerms (p n) 0 := rfl
theorem pm_twGuard_eq (n : ℕ) : pmVals n pmItwGuard = taylorGuard (p n) 0 := rfl
theorem pm_twPrec_eq (n : ℕ) : pmVals n pmItwPrec = p n + 2 + taylorGuard (p n) 0 := rfl
theorem pm_twAngle_eq (n : ℕ) : pmVals n pmItwAngle = 5 * (p n + 4) := rfl
theorem pm_chTerms_eq (n : ℕ) : pmVals n pmIchTerms = taylorTerms (p n) (chirpGuard (d n)) := rfl
theorem pm_chGuard_eq (n : ℕ) : pmVals n pmIchGuard = taylorGuard (p n) (chirpGuard (d n)) := rfl
theorem pm_chRound_eq (n : ℕ) : pmVals n pmIchRound = p n + chirpGuard (d n) := rfl
theorem pm_chPrec_eq (n : ℕ) :
    pmVals n pmIchPrec = p n + chirpGuard (d n) + 2 + taylorGuard (p n) (chirpGuard (d n)) := rfl
theorem pm_chAngle_eq (n : ℕ) : pmVals n pmIchAngle = 5 * anglePrec (p n) (chirpGuard (d n)) := rfl
theorem pm_scratch_eq (n : ℕ) (i : Fin pmNV) (hi : 31 ≤ i.val) : pmVals n i = 0 := pmVal_ge n i hi

/-- `R = r / 2` for `n ≥ 2`. -/
theorem pm_R_half (hn : 2 ≤ n) : 2 ^ (ℓ n - 1) = r n / 2 := by
  have := pm_one_le_ℓ hn
  unfold r
  rw [show ℓ n = ℓ n - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
  simp

/-- The axis lengths are the box of the moduli: `t n = Moduli.box d numHalf (ℓ - 1)`. -/
theorem pm_t_box (hn : 2 ≤ n) : t n = Moduli.box (d n) (numHalf n) (ℓ n - 1) :=
  t_eq_box (pm_one_le_ℓ hn)

/-- The emitted axis value of axis `i` is `t_i`. -/
theorem pmTv_eq (n : ℕ) (i : Fin (d n)) : pmTv (numHalf n) (2 ^ (ℓ n - 1)) (r n) i = t n i := by
  unfold pmTv t r
  rfl

end IntegerMultBounds.MathlibTM2.Fast.TableVM
