module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineDriver
public import IntegerMultBounds.MathlibTM2.Mult.BandSolveFold

/-!
# What the banded line computes

The tape line `band_line_runs` writes `bandOutVec` of `bandSolveVec` of `bandInVec`. With the
factor tables of the folded Gaussian window matrix, the input constant `2^(2P-p-1)`, the output
constant `2^(p-j)` and the diagonal table `D · 2^(P-p)`, entry `ℓ` is the numerator of
`resampB₀Of p (bandJtX p j X) df` at `ℓ` for the machine solver `X = machSolveT` of the window
matrix (`bandLine_spec`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.BandList

theorem bandSolveVec_re (P B : ℕ) (Lc Uc : List (List ℤ)) (rcs : List ℤ) (b : List GaussianInt) :
    (bandSolveVec P B Lc Uc rcs b).map (·.re) =
      (bwdZ P Uc rcs ((fwdZ P Lc (b.map (·.re) ++ List.replicate B 0)).reverse ++
        List.replicate B 0)).reverse := by
  simp [bandSolveVec, List.map_reverse, bwdZC_re, fwdZC_re, List.map_append]

theorem bandSolveVec_im (P B : ℕ) (Lc Uc : List (List ℤ)) (rcs : List ℤ) (b : List GaussianInt) :
    (bandSolveVec P B Lc Uc rcs b).map (·.im) =
      (bwdZ P Uc rcs ((fwdZ P Lc (b.map (·.im) ++ List.replicate B 0)).reverse ++
        List.replicate B 0)).reverse := by
  simp [bandSolveVec, List.map_reverse, bwdZC_im, fwdZC_im, List.map_append]

/-- The window factorization of the folded matrix. -/
def bandFac (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) : List (List ℤ × List ℤ) :=
  factorRowsZ P K (windowZ (2 * w + 1) (foldZ s w aZ)) (inputsZ (2 * w + 1) (foldZ s w aZ) s)

/-- The forward table: the multiplier columns. -/
def bandLc (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) : List (List ℤ) :=
  (bandFac P K w s aZ).map Prod.fst

/-- The backward table: the transposed pivot rows, last pivot first. -/
def bandUc (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) : List (List ℤ) :=
  (List.range' 0 s).reverse.map (ucolZ (2 * w + 1) ((bandFac P K w s aZ).map Prod.snd))

/-- The Newton reciprocals of the pivots, last pivot first. -/
def bandRcs (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) : List ℤ :=
  (((bandFac P K w s aZ).map Prod.snd).map fun r => newtonZ P (r.headD 0) K).reverse

theorem bandSolveVec_re_eq (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) (b : List GaussianInt) :
    (bandSolveVec P (2 * w + 1) (bandLc P K w s aZ) (bandUc P K w s aZ) (bandRcs P K w s aZ) b).map
      (·.re) = lineSolveZ P K (2 * w + 1) s (foldZ s w aZ) (b.map (·.re)) := by
  rw [bandSolveVec_re]; rfl

theorem bandSolveVec_im_eq (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) (b : List GaussianInt) :
    (bandSolveVec P (2 * w + 1) (bandLc P K w s aZ) (bandUc P K w s aZ) (bandRcs P K w s aZ) b).map
      (·.im) = lineSolveZ P K (2 * w + 1) s (foldZ s w aZ) (b.map (·.im)) := by
  rw [bandSolveVec_im]; rfl

/-! ### The tables the preparation writes -/

section Tables

variable (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ)

/-- The initial window of the folded matrix. -/
def bandRows : List (List ℤ) := windowZ (2 * w + 1) (foldZ s w aZ)

/-- The factorization inputs of the folded matrix. -/
def bandInputs : List (List ℤ) := inputsZ (2 * w + 1) (foldZ s w aZ) s

theorem length_bandInputs : (bandInputs w s aZ).length = s := by simp [bandInputs, inputsZ]

theorem bandFac_eq : bandFac P K w s aZ = (List.range s).map fun j =>
    (lcolZ P K (facState P K (bandRows w s aZ) (bandInputs w s aZ) j),
      (facState P K (bandRows w s aZ) (bandInputs w s aZ) j).headD []) := by
  rw [bandFac, factorRowsZ_facState, ← bandRows, ← bandInputs, length_bandInputs]

/-- The forward table of the preparation is the multiplier columns `bandLc`. -/
theorem prep_bo_eq : (facLf P K (bandRows w s aZ) (bandInputs w s aZ) s).map
    (fun x => (⟨x, 0⟩ : GaussianInt)) = ((bandLc P K w s aZ).map colC).flatten := by
  simp [facLf, bandLc, bandFac_eq, colC, List.map_flatten, List.map_map, Function.comp_def]

theorem facUr_eq : facUr P K (bandRows w s aZ) (bandInputs w s aZ) s =
    (bandFac P K w s aZ).map Prod.snd := by
  simp [facUr, bandFac_eq, List.map_map, Function.comp_def]

/-- The backward table of the preparation is the transposed rows `bandUc`. -/
theorem prep_hf_eq : ((List.range s).reverse.map fun m =>
    colC (ucolZ (2 * w + 1) (facUr P K (bandRows w s aZ) (bandInputs w s aZ) s) m)).flatten =
      ((bandUc P K w s aZ).map colC).flatten := by
  rw [facUr_eq, bandUc, List.map_map, List.range_eq_range']; rfl

/-- The reciprocal table of the preparation is `bandRcs`. -/
theorem prep_df_eq : (List.range s).reverse.map (fun j =>
    (⟨newtonZ P (facPiv (facState P K (bandRows w s aZ) (bandInputs w s aZ) j)) K, 0⟩ :
      GaussianInt)) = (bandRcs P K w s aZ).map fun x => (⟨x, 0⟩ : GaussianInt) := by
  simp [bandRcs, bandFac_eq, List.map_reverse, List.map_map, Function.comp_def, facPiv]

end Tables

/-! ### Exact rescalings -/

theorem tdiv_pow_mul (x : ℤ) (a b : ℕ) : (x * 2 ^ a).tdiv (2 ^ (a + b)) = x.tdiv (2 ^ b) := by
  rw [pow_add, mul_comm x, Int.mul_tdiv_mul_of_pos _ _ (by positivity)]

theorem mul_real_re (z : GaussianInt) (c : ℤ) : (z * ⟨c, 0⟩).re = z.re * c := by
  simp [Zsqrtd.re_mul]

theorem mul_real_im (z : GaussianInt) (c : ℤ) : (z * ⟨c, 0⟩).im = z.im * c := by
  simp [Zsqrtd.im_mul]

/-- Scaling up by `2^(2P-p-1)` at precision `P` is exact. -/
theorem tdivN_scale_in (P p : ℕ) (h : p + 1 ≤ P) (z : GaussianInt) :
    tdivN P (z * ⟨2 ^ (2 * P - p - 1), 0⟩) = z * ⟨2 ^ (P - p - 1), 0⟩ := by
  have e : (2 : ℤ) ^ (2 * P - p - 1) = 2 ^ (P - p - 1) * 2 ^ P := by
    rw [← pow_add]; congr 1; omega
  have key : ∀ x : ℤ, (x * 2 ^ (2 * P - p - 1)).tdiv (2 ^ P) = x * 2 ^ (P - p - 1) := by
    intro x; rw [e, ← mul_assoc, Int.mul_tdiv_cancel _ (by positivity)]
  ext
  · rw [tdivN_re, mul_real_re, mul_real_re, key]
  · rw [tdivN_im, mul_real_im, mul_real_im, key]

/-- Scaling by `2^(p-j)` at precision `P` is a truncated division by `2^(P-p+j)`. -/
theorem tdivN_scale_out (P p j : ℕ) (hj : j ≤ p) (hp : p ≤ P) (z : GaussianInt) :
    tdivN P (z * ⟨2 ^ (p - j), 0⟩) = tdivN (P - p + j) z := by
  have e : (2 : ℤ) ^ P = 2 ^ ((p - j) + (P - p + j)) := by congr 1; omega
  ext
  · rw [tdivN_re, tdivN_re, mul_real_re, e, tdiv_pow_mul]
  · rw [tdivN_im, tdivN_im, mul_real_im, e, tdiv_pow_mul]

/-- A table entry `D · 2^(P-p)` at precision `P` is the entry `D` at precision `p`. -/
theorem tdivN_scale_tab (P p : ℕ) (hp : p ≤ P) (z : GaussianInt) (d : ℤ) :
    tdivN P (z * ⟨d * 2 ^ (P - p), 0⟩) = tdivN p (z * ⟨d, 0⟩) := by
  have e : (2 : ℤ) ^ P = 2 ^ ((P - p) + p) := by congr 1; omega
  ext
  · rw [tdivN_re, tdivN_re, mul_real_re, mul_real_re, e, ← mul_assoc, tdiv_pow_mul]
  · rw [tdivN_im, tdivN_im, mul_real_im, mul_real_im, e, ← mul_assoc, tdiv_pow_mul]

/-- Rounding `2^-j` times a grid value at precision `P` to precision `p`. -/
theorem rhoC_scale (P p j : ℕ) (hp : p ≤ P) (z : GaussianInt) :
    rhoC p (((2 : ℂ) ^ j)⁻¹ * ⟨gv P z.re, gv P z.im⟩) = rsbGrid p (tdivN (P - p + j) z) := by
  have hpos : (0 : ℝ) < 2 ^ P := by positivity
  have key : ∀ x : ℤ, (2 : ℝ) ^ p * ((2 ^ j)⁻¹ * gv P x) = (x : ℝ) / 2 ^ (P - p + j) := by
    intro x
    have e : (2 : ℝ) ^ P = 2 ^ (P - p + j) * 2 ^ p / 2 ^ j := by
      rw [eq_div_iff (by positivity), ← pow_add, ← pow_add]; congr 1; omega
    simp only [gv]; rw [e]; field_simp
  have hc : ((2 : ℂ) ^ j)⁻¹ = (((2 : ℝ) ^ j)⁻¹ : ℝ) := by push_cast; rfl
  rw [hc]
  apply Complex.ext
  · rw [rhoC_re, rsbGrid, two_pow_complex, toComplex_div_re, tdivN_re, tdiv_rho0,
      Complex.re_ofReal_mul, key]
  · rw [rhoC_im, rsbGrid, two_pow_complex, toComplex_div_im, tdivN_im, tdiv_rho0,
      Complex.im_ofReal_mul, key]

/-! ### The line -/

theorem getD_map' {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (a : α) (b : β)
    (h : i < l.length) : (l.map f).getD i b = f (l.getD i a) := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_zipWith' {α β γ : Type*} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ)
    (a : α) (b : β) (c : γ) (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    (List.zipWith f l₁ l₂).getD i c = f (l₁.getD i a) (l₂.getD i b) := by
  simp [List.getD_eq_getElem?_getD, h₁, h₂]

theorem length_unfoldList {α : Type*} (x : List α) : (unfoldList x).length = x.length := by
  simp [unfoldList, length_evens, length_odds]; omega

theorem foldAtN_foldPos (s : ℕ) [NeZero s] (a : ZMod s) : foldAtN s (foldPos s a) = a.val := by
  rw [← foldAt_val_eq s _ (foldPos_lt s a), foldAt_foldPos]

theorem foldPosN_val (s : ℕ) [NeZero s] (ℓ : ZMod s) : foldPosN s ℓ.val = foldPos s ℓ := rfl

/-- **The banded line, entrywise.** With the factor tables of the folded window matrix of the
numerators `aZ`, the constants `2^(2P-p-1)` and `2^(p-j)` and the diagonal table `D · 2^(P-p)`,
the tape line's entry `ℓ` is entry `ℓ` of `B̃₀` built from the machine solve of the window
matrix, on the grid input `N / 2^p`. -/
theorem bandLine_spec (P K w p j s t : ℕ) [NeZero s] [NeZero t] (hp : 1 ≤ p) (hP : p + 1 ≤ P)
    (hjp : j ≤ p)
    (aZ : ZMod s → ℤ → ℤ) (N : ZMod t → GaussianInt) (Dl : List ℤ) (Dp : ZMod s → ℤ)
    (hDl : Dl.length = s) (hD : ∀ ℓ : ZMod s, Dl.getD ℓ.val 0 = Dp ℓ * 2 ^ (P - p))
    (df : ZMod s → ℝ) (hdf : ∀ ℓ, rsbGrid p (rsbReal (Dp ℓ)) = rhoC p (df ℓ)) (ℓ : ZMod s) :
    rsbGrid p ((bandOutVec P (2 ^ (p - j)) Dl (bandSolveVec P (2 * w + 1) (bandLc P K w s aZ)
      (bandUc P K w s aZ) (bandRcs P K w s aZ) (bandInVec P s t (2 ^ (2 * P - p - 1)) N))).getD
        ℓ.val 0) =
      Mult.FastB0.resampB₀Of (t := t) p (Mult.FastB0.bandJtX (s := s) p j
        (Mult.FastB0.machSolveT K (Mult.Sizes.rdP P) (windowMatrix s w fun j k => gv P (aZ j k))))
        df (fun k => rsbGrid p (N k)) ℓ := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hP2 : 2 ≤ P := by omega
  set SL := rsbArr fun ℓ : ZMod s => N (rowIndex s t ℓ) with hSL
  have hSLl : SL.length = s := by rw [hSL, length_rsbArr]
  set b := bandInVec P s t (2 ^ (2 * P - p - 1)) N with hbdef
  have hbl : b.length = s := by simp [hbdef, bandInVec, length_foldList, length_rsbArr]
  -- the input, entrywise
  have hbin : ∀ a : ZMod s, b.getD (foldPos s a) 0 = N (rowIndex s t a) * ⟨2 ^ (P - p - 1), 0⟩ := by
    intro a
    have ha := foldPos_lt s a
    rw [hbdef, bandInVec, getD_map' _ _ _ 0 _ (by rw [length_foldList, hSLl]; exact ha),
      getD_foldList _ _ _ (by rw [hSLl]; exact ha), hSLl, foldAtN_foldPos, tdivN_scale_in P p hP]
    congr 1
    simp [rsbArr, List.getD_eq_getElem?_getD, ZMod.val_lt a]
  have hgv : ∀ (a : ZMod s) (f : GaussianInt → ℤ), (∀ z c, f (z * ⟨c, 0⟩) = f z * c) →
      gv P ((b.map f).getD (foldPos s a) 0) = (f (N (rowIndex s t a)) : ℝ) / 2 ^ p / 2 := by
    intro a f hf
    rw [getD_map' _ _ _ 0 _ (by rw [hbl]; exact foldPos_lt s a), hbin, hf, gv]
    have e : (2 : ℝ) ^ P = 2 ^ (P - p - 1) * 2 ^ p * 2 := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    push_cast; rw [e]; field_simp
  -- the solve, entrywise
  set X := Mult.FastB0.machSolveT K (Mult.Sizes.rdP P) (windowMatrix s w fun j k => gv P (aZ j k))
  set x := bandSolveVec P (2 * w + 1) (bandLc P K w s aZ) (bandUc P K w s aZ) (bandRcs P K w s aZ) b
  have hsolve : ∀ f : GaussianInt → ℤ, (∀ z c, f (z * ⟨c, 0⟩) = f z * c) →
      (x.map f = lineSolveZ P K (2 * w + 1) s (foldZ s w aZ) (b.map f)) →
      x.length = s ∧ gv P (f (x.getD (foldPos s ℓ) 0)) =
        X (fun a => (f (N (rowIndex s t a)) : ℝ) / 2 ^ p / 2) ℓ := by
    intro f hf hx
    have H := lineSolveFold_eq P K s hP2 w aZ (b.map f) (by simp [hbl])
    rw [← hx] at H
    have hlen : x.length = s := by simpa using congrArg List.length H
    refine ⟨hlen, ?_⟩
    have hi := foldPos_lt s ℓ
    have H2 := congrArg (fun l => l[foldPos s ℓ]?) H
    simp only [List.getElem?_map, List.getElem?_range', hi] at H2
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hi)] at H2
    simp only [Option.map_some, Option.some.injEq, zero_add, one_mul, foldAt_foldPos] at H2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi),
      Option.getD_some, H2]
    congr 1
    funext a
    exact hgv a f hf
  obtain ⟨hxl, hre⟩ := hsolve (·.re) (fun z c => mul_real_re z c) (bandSolveVec_re_eq P K w s aZ b)
  obtain ⟨-, him⟩ := hsolve (·.im) (fun z c => mul_real_im z c) (bandSolveVec_im_eq P K w s aZ b)
  -- the output
  have hℓ := ZMod.val_lt ℓ
  rw [bandOutVec, getD_zipWith' _ _ _ _ 0 0 _ (by simp [length_unfoldList, hxl, hℓ])
    (by simp [hDl, hℓ]), getD_map' _ _ _ 0 _ (by simp [length_unfoldList, hxl, hℓ]),
    getD_map' _ _ _ 0 _ (by simp [hDl, hℓ]), getD_unfoldList _ _ _ (by rw [hxl]; exact hℓ), hxl,
    foldPosN_val, hD, tdivN_scale_out P p j hjp (by omega), tdivN_scale_tab P p (by omega),
    ← rhoC_mul_rsbGrid, ← rhoC_scale P p j (by omega)]
  simp only [Mult.FastB0.resampB₀Of, Resampling.TabledMaps.diagW, Mult.FastB0.bandJtX]
  rw [mul_comm, ← hdf]
  have hfre : (fun a => ((N (rowIndex s t a)).re : ℝ) / 2 ^ p / 2) =
      fun k => ((1 / 2 : ℂ) * rowSelect s t (fun k => rsbGrid p (N k)) k).re := by
    funext a
    show _ = ((1 / 2 : ℂ) * rsbGrid p (N (rowIndex s t a))).re
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, rsbGrid,
      two_pow_complex, toComplex_div_re]; ring
  have hfim : (fun a => ((N (rowIndex s t a)).im : ℝ) / 2 ^ p / 2) =
      fun k => ((1 / 2 : ℂ) * rowSelect s t (fun k => rsbGrid p (N k)) k).im := by
    funext a
    show _ = ((1 / 2 : ℂ) * rsbGrid p (N (rowIndex s t a))).im
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul, rsbGrid,
      two_pow_complex, toComplex_div_im]; ring
  rw [hre, him, hfre, hfim]
  rfl

end IntegerMultBounds.MathlibTM2.Fast
