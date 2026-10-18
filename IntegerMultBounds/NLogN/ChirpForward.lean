module

public import IntegerMultBounds.NLogN.ResamplingAssembly
public import IntegerMultBounds.NLogN.ResamplingApprox
public import IntegerMultBounds.NLogN.Approx
public import IntegerMultBounds.NLogN.Clamp
import IntegerMultBounds.NLogN.ResamplingNumeric
import IntegerMultBounds.NLogN.ResamplingNorm
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # The chirped-correlation forward map

`Ã = S/2` with `(S u)_k = α⁻¹ ∑_j exp(-π α⁻² s² (k/t - j/s)²) u_j`. With `σ = t/s`,
`θ = σ - 1` and `λ = (σα)⁻²` the weight is `exp(-πλ (σj - k)²)`. The outputs are cut into blocks
of `m` consecutive indices; the block starting at `k₀` reads the `3m + 1` inputs
`j = j₀ + a` from `j₀ = ⌊s k₀/t⌋ - m`, which contain the truncation window of every output of
the block (`truncWindow_subset_block`), so the block sums are within `3/(α 2^p)` of `S u`
(`resampS_superset_err`). With `y = σ j₀ - k₀` and `k = k₀ + b`, the chirp identity
`(σâ - b)² = σθ â² + σ(â - b)² - θ b²`, `â = a + y/σ`, splits each weight into a growing output
factor `exp(πλθ b²)`, a decaying input factor `exp(-πλσθ â²)` and a correlation kernel
`exp(-πλσ (a - b + y/σ)²)` (`chirp_weight`), so a block is one correlation of short sequences.

`chirpA` computes it from tables within `η` of the factors and kernel: the scaled inputs rounded
once, the exact correlation, the output factor divided by `2^Γ` and multiplied back, the factor
`1/(2α)`, and the final rounding to the `p`-grid. With `exp(πλθ b²) ≤ 2^Γ` on a block and
`2^(p+Γ) (12m + 7) η ≤ 1/2`, it approximates `Ã` with scaled error `4` (`chirpA_approx`),
independently of the window `m`. The output stage `chirpAG` accepts any computed correlation
within `ζ` of the exact one (`chirpAG_approx`), such as the rescaled output of the ring product
(`Mult/ShortConv`). -/
@[expose] public section
namespace IntegerMultBounds.NLogN

open Real Finset

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-! ### Windows containing the truncation window -/

/-- Any finite set of inputs containing the truncation window of row `k` gives a row sum within
`3/(α 2^p)` of `S u`. -/
theorem resampS_superset_err (hα : 0<α) {p m : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m) (u : ZMod s → ℂ)
    (hu : ∀ j, ‖u j‖≤1) (k : ZMod t) (W : Finset ℤ) (hW : truncWindow s t m k⊆W) :
    ‖resampS s t α u k-(1/α : ℂ)*∑ j∈W,
      (Real.exp (-π*α⁻¹^2*s^2*((k.val : ℝ)/t-j/s)^2) : ℂ)*u j‖≤3/(α*2^p) := by
  have hc : 0<π*α⁻¹^2 := by positivity
  set f : ℤ → ℂ := fun j =>
    (Real.exp (-π*α⁻¹^2*s^2*((k.val : ℝ)/t-j/s)^2) : ℂ)*u j with hf
  have hfs : Summable f := summable_resampS_term hα u k
  set g : ℤ → ℝ := fun j => gauss (π*α⁻¹^2) (-(resampCentre s t k)+j) with hg
  have hterm : ∀ j : ℤ, ‖f j‖≤g j := by
    intro j
    simp only [hf, hg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      resamp_weight_eq hα k j]
    unfold resampCentre
    calc gauss (π*α⁻¹^2) (-(s*k.val/t)+j)*‖u j‖
        ≤ gauss (π*α⁻¹^2) (-(s*k.val/t)+j)*1 :=
          mul_le_mul_of_nonneg_left (hu j) (gauss_pos _ _).le
      _ = _ := mul_one _
  have hw : Summable g := summable_gauss_int hc _
  have hfn : Summable (fun j : ℤ => ‖f j‖) := hw.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have h1 : ‖(1/α : ℂ)‖=1/α := by
    rw [show (1/α : ℂ)=((1/α : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hdiff : resampS s t α u k-(1/α : ℂ)*∑ j∈W, f j=(1/α : ℂ)*∑' j : ↑((W : Set ℤ))ᶜ, f j := by
    have h := hfs.sum_add_tsum_compl (s := W)
    show (1/α : ℂ)*∑' j : ℤ, f j-(1/α : ℂ)*∑ j∈W, f j=_
    rw [←mul_sub, ←h]
    ring
  rw [hdiff, norm_mul, h1]
  have hsub : Summable (fun j : ↑((W : Set ℤ))ᶜ => ‖f j‖) := hfn.subtype _
  have hcompl : ∑' j : ↑((W : Set ℤ))ᶜ, g j≤∑' j : ↑((truncWindow s t m k : Set ℤ))ᶜ, g j := by
    rw [tsum_subtype ((W : Set ℤ))ᶜ g, tsum_subtype ((truncWindow s t m k : Set ℤ))ᶜ g]
    refine (hw.indicator _).tsum_le_tsum (fun j => ?_) (hw.indicator _)
    by_cases hj : j∈W
    · rw [Set.indicator_of_notMem (by simpa using hj)]
      exact Set.indicator_nonneg (fun _ _ => (gauss_pos _ _).le) j
    · have hj' : j∉truncWindow s t m k := fun h => hj (hW h)
      rw [Set.indicator_of_mem (by simpa using hj), Set.indicator_of_mem (by simpa using hj')]
  have htr : ∑' j : ↑((truncWindow s t m k : Set ℤ))ᶜ, g j≤
      2*∑' n : ℕ, gauss (π*α⁻¹^2) (m+n) := by
    rw [tsum_subtype ((truncWindow s t m k : Set ℤ))ᶜ g]
    have e : (fun j => ((truncWindow s t m k : Set ℤ))ᶜ.indicator g j)=fun j =>
        if j∈Finset.Icc (⌊resampCentre s t k⌋-m) (⌊resampCentre s t k⌋+m) then 0 else
          gauss (π*α⁻¹^2) (-(resampCentre s t k)+j) := by
      funext j
      unfold truncWindow
      by_cases hj : j∈Finset.Icc (⌊resampCentre s t k⌋-m) (⌊resampCentre s t k⌋+m)
      · rw [Set.indicator_of_notMem (by simpa using hj)]
        simp only [hj, ↓reduceIte]
      · rw [Set.indicator_of_mem (by simpa using hj)]
        simp only [hj, ↓reduceIte, hg]
    rw [e]
    exact tsum_outside_window_le hc _ m
  have htail := gauss_tail_small hα hαp hm hm1
  have h2p : (0 : ℝ)<2^p := by positivity
  calc (1/α)*‖∑' j : ↑((W : Set ℤ))ᶜ, f j‖
      ≤(1/α)*∑' j : ↑((W : Set ℤ))ᶜ, ‖f j‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsub) (by positivity)
    _ ≤(1/α)*∑' j : ↑((W : Set ℤ))ᶜ, g j :=
        mul_le_mul_of_nonneg_left (hsub.tsum_le_tsum (fun j => hterm j) (hw.subtype _))
          (by positivity)
    _ ≤(1/α)*(2*((7/6)/2^p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ =(7/3)/(α*2^p) := by field_simp; ring
    _ ≤3/(α*2^p) := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-! ### Blocks -/

/-- The first input of the block starting at output `k₀`. -/
noncomputable def blockIn (s t m k0 : ℕ) : ℤ := ⌊(s : ℝ)*k0/t⌋-m

theorem image_range_add (j0 : ℤ) (n : ℕ) :
    (range (n+1)).image (fun a : ℕ => j0+a)=Finset.Icc j0 (j0+n) := by
  ext j
  simp only [mem_image, mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro hj; exact ⟨(j-j0).toNat, by omega, by omega⟩

omit [NeZero s] in
/-- The block of an output contains its truncation window. -/
theorem truncWindow_subset_block (hst : s<t) (m : ℕ) (hm1 : 1≤m) (k : ZMod t) :
    truncWindow s t m k⊆Finset.Icc (blockIn s t m (k.val/m*m)) (blockIn s t m (k.val/m*m)+3*m) := by
  have ht : (0 : ℝ)<t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have hk : k.val=k.val/m*m+k.val%m := (Nat.div_add_mod' k.val m).symm
  have hb : k.val%m≤m := (Nat.mod_lt _ (by omega)).le
  set k0 := k.val/m*m
  have hlo : ⌊(s : ℝ)*k0/t⌋≤⌊resampCentre s t k⌋ := by
    apply Int.floor_le_floor
    unfold resampCentre
    rw [div_le_div_iff_of_pos_right ht]
    have : (k0 : ℝ)≤k.val := by exact_mod_cast (by omega : k0≤k.val)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hhi : ⌊resampCentre s t k⌋≤⌊(s : ℝ)*k0/t⌋+m := by
    rw [←Int.floor_add_natCast]
    apply Int.floor_le_floor
    unfold resampCentre
    have hsk : (s : ℝ)*(k.val%m : ℕ)≤t*m := by
      have h1 : (s : ℝ)≤t := by exact_mod_cast hst.le
      have h2 : ((k.val%m : ℕ) : ℝ)≤m := by exact_mod_cast hb
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have e : (s : ℝ)*k.val/t=s*k0/t+s*(k.val%m : ℕ)/t := by
      rw [←add_div, ←mul_add]; congr 2; exact_mod_cast hk
    rw [e]
    have : (s : ℝ)*(k.val%m : ℕ)/t≤m := by rw [div_le_iff₀ ht]; linarith
    linarith
  intro j hj
  unfold truncWindow at hj
  rw [Finset.mem_Icc] at hj ⊢
  unfold blockIn
  constructor <;> omega

/-! ### The chirp split -/

/-- `σ = t/s`. -/
noncomputable def chirpSig (s t : ℕ) : ℝ := (t : ℝ)/s

/-- `θ = σ - 1`. -/
noncomputable def chirpTheta (s t : ℕ) : ℝ := chirpSig s t-1

/-- `λ = (σα)⁻²`. -/
noncomputable def chirpLam (s t : ℕ) (α : ℝ) : ℝ := 1/(chirpSig s t^2*α^2)

/-- The block offset `y = σ j₀ - k₀`. -/
noncomputable def chirpY (s t m k0 : ℕ) : ℝ := chirpSig s t*blockIn s t m k0-k0

/-- The decaying input factor `exp(-πλσθ (a + y/σ)²)`. -/
noncomputable def chirpG (s t : ℕ) (α : ℝ) (m k0 a : ℕ) : ℝ :=
  Real.exp (-π*chirpLam s t α*chirpSig s t*chirpTheta s t*(a+chirpY s t m k0/chirpSig s t)^2)

/-- The correlation kernel `exp(-πλσ (r + y/σ)²)`. -/
noncomputable def chirpK (s t : ℕ) (α : ℝ) (m k0 : ℕ) (r : ℤ) : ℝ :=
  Real.exp (-π*chirpLam s t α*chirpSig s t*(r+chirpY s t m k0/chirpSig s t)^2)

/-- The growing output factor `exp(πλθ b²)`. -/
noncomputable def chirpE (s t : ℕ) (α : ℝ) (b : ℕ) : ℝ :=
  Real.exp (π*chirpLam s t α*chirpTheta s t*b^2)

/-- **The chirp split** of the weight of input `j₀ + a` in output `k₀ + b`. -/
theorem chirp_weight (hα : α≠0) (m k0 b a : ℕ) :
    Real.exp (-π*α⁻¹^2*s^2*(((k0+b : ℕ) : ℝ)/t-((blockIn s t m k0+a : ℤ) : ℝ)/s)^2)=
      chirpE s t α b*(chirpG s t α m k0 a*chirpK s t α m k0 ((a : ℤ)-b)) := by
  have hs : (s : ℝ)≠0 := by exact_mod_cast NeZero.ne s
  have ht : (t : ℝ)≠0 := by exact_mod_cast NeZero.ne t
  unfold chirpE chirpG chirpK
  rw [←Real.exp_add, ←Real.exp_add]
  congr 1
  unfold chirpLam chirpTheta chirpY chirpSig
  push_cast
  field_simp
  ring

omit [NeZero s] [NeZero t] in
theorem chirpTheta_pos (hst : s<t) (hs : 0<s) : 0<chirpTheta s t := by
  unfold chirpTheta chirpSig
  rw [sub_pos, one_lt_div (by exact_mod_cast hs)]
  exact_mod_cast hst

omit [NeZero s] [NeZero t] in
theorem chirpG_pos (m k0 a : ℕ) : 0<chirpG s t α m k0 a := Real.exp_pos _

omit [NeZero s] [NeZero t] in
theorem chirpK_pos (m k0 : ℕ) (r : ℤ) : 0<chirpK s t α m k0 r := Real.exp_pos _

theorem chirpG_le_one (hst : s<t) (m k0 a : ℕ) : chirpG s t α m k0 a≤1 := by
  have hθ := chirpTheta_pos hst (Nat.pos_of_ne_zero (NeZero.ne s))
  have hσ : 0<chirpSig s t := div_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s))
  have hl : 0≤chirpLam s t α := by unfold chirpLam; positivity
  unfold chirpG
  rw [Real.exp_le_one_iff]
  have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pi_pos.le hl) hσ.le) hθ.le)
    (sq_nonneg ((a : ℝ)+chirpY s t m k0/chirpSig s t))
  linarith

theorem chirpK_le_one (m k0 : ℕ) (r : ℤ) : chirpK s t α m k0 r≤1 := by
  have hσ : 0<chirpSig s t := div_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s))
  have hl : 0≤chirpLam s t α := by unfold chirpLam; positivity
  unfold chirpK
  rw [Real.exp_le_one_iff]
  have := mul_nonneg (mul_nonneg (mul_nonneg pi_pos.le hl) hσ.le)
    (sq_nonneg ((r : ℝ)+chirpY s t m k0/chirpSig s t))
  linarith

omit [NeZero s] [NeZero t] in
/-- The output factor is at most `2^Γ` on a block of `m` outputs once `πλθ m² ≤ Γ log 2`. -/
theorem chirpE_le_two_pow (hst : s<t) (hs : 0<s) {m Γ : ℕ}
    (hΓ : π*chirpLam s t α*chirpTheta s t*(m : ℝ)^2≤Γ*Real.log 2) (b : ℕ) (hb : b<m) :
    chirpE s t α b≤2^Γ := by
  have hθ := chirpTheta_pos hst hs
  have hl : 0≤chirpLam s t α := by unfold chirpLam; positivity
  have hbm : (b : ℝ)^2≤(m : ℝ)^2 := by
    have : (b : ℝ)≤m := by exact_mod_cast hb.le
    nlinarith [(Nat.cast_nonneg b : (0 : ℝ)≤b)]
  unfold chirpE
  rw [←Real.exp_log (by positivity : (0 : ℝ)<2^Γ), Real.log_pow, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left hbm (by positivity : 0≤π*chirpLam s t α*chirpTheta s t)
  linarith

/-! ### The computed map -/

/-- The computed input `a` of the block starting at `k₀`: scaled by the table `gt`, rounded. -/
noncomputable def chirpIn (m : ℕ) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (u : ZMod s → ℂ) (k0 a : ℕ) : ℂ :=
  rd ((gt k0 a : ℂ)*u ((blockIn s t m k0+a : ℤ) : ZMod s))

/-- The exact correlation of the computed inputs with the kernel table `kt` at output offset
`b`. -/
noncomputable def chirpCorr (m : ℕ) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (u : ZMod s → ℂ) (k0 b : ℕ) : ℂ :=
  ∑ a∈range (3*m+1), chirpIn (t := t) m rd gt u k0 a*(kt k0 ((a : ℤ)-b) : ℂ)

/-- The output stage of the chirped-correlation `Ã` from any computed correlation
`corr u k₀ b`: the output factor table `et` (the factor divided by `2^Γ`) multiplied and
rounded, the shift by `Γ`, the factor `aN` of `1/(2α)`, and the rounding to the `p`-grid. -/
noncomputable def chirpAG (p m Γ : ℕ) (rd : ℂ → ℂ) (corr : (ZMod s → ℂ) → ℕ → ℕ → ℂ)
    (et : ℕ → ℕ → ℝ) (aN : ℝ) (u : ZMod s → ℂ) (k : ZMod t) : ℂ :=
  rhoC p (rd ((aN : ℂ)*(2^Γ*rd ((et (k.val/m*m) (k.val%m) : ℂ)*corr u (k.val/m*m) (k.val%m)))))

/-- The computed chirped-correlation `Ã` with the exact correlation of the rounded scaled
inputs. -/
noncomputable def chirpA (p m Γ : ℕ) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (et : ℕ → ℕ → ℝ) (aN : ℝ) (u : ZMod s → ℂ) (k : ZMod t) : ℂ :=
  chirpAG (t := t) p m Γ rd (fun u => chirpCorr (t := t) m rd gt kt u) et aN u k

private theorem mul_le_one_of {x y : ℝ} (hx : x≤1) (hy0 : 0≤y) (hy : y≤1) : x*y≤1 := by
  nlinarith

/-- The exact block sum of output `k`. -/
noncomputable def chirpBlock (α : ℝ) (m : ℕ) (u : ZMod s → ℂ) (k : ZMod t) : ℂ :=
  ∑ a∈range (3*m+1),
    (Real.exp (-π*α⁻¹^2*s^2*((k.val : ℝ)/t-((blockIn s t m (k.val/m*m)+a : ℤ) : ℝ)/s)^2) : ℂ)*
      u ((blockIn s t m (k.val/m*m)+a : ℤ) : ZMod s)

/-- The exact correlation of the scaled inputs with the kernel. -/
noncomputable def chirpCorrEx (α : ℝ) (m : ℕ) (u : ZMod s → ℂ) (k0 b : ℕ) : ℂ :=
  ∑ a∈range (3*m+1), (chirpG s t α m k0 a : ℂ)*u ((blockIn s t m k0+a : ℤ) : ZMod s)*
    (chirpK s t α m k0 ((a : ℤ)-b) : ℂ)

theorem chirpBlock_err (hst : s<t) (hα : 0<α) {p m : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖≤1)
    (k : ZMod t) : ‖resampS s t α u k-(1/α : ℂ)*chirpBlock (s := s) α m u k‖≤3/(α*2^p) := by
  have hsup := resampS_superset_err hα hαp hm hm1 u hu k _ (truncWindow_subset_block hst m hm1 k)
  have himg := image_range_add (blockIn s t m (k.val/m*m)) (3*m)
  push_cast at himg
  rw [←himg, sum_image (fun a _ a' _ h => by exact_mod_cast (by omega : (a : ℤ)=a'))] at hsup
  exact hsup

theorem chirpBlock_split (hα : 0<α) (m : ℕ) (u : ZMod s → ℂ) (k : ZMod t) :
    chirpBlock (s := s) α m u k=(chirpE s t α (k.val%m) : ℂ)*
      chirpCorrEx (t := t) α m u (k.val/m*m) (k.val%m) := by
  have hkv : k.val=k.val/m*m+k.val%m := (Nat.div_add_mod' k.val m).symm
  unfold chirpBlock chirpCorrEx
  rw [Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have h := chirp_weight (s := s) (t := t) hα.ne' m (k.val/m*m) (k.val%m) a
  have e : ((k.val/m*m+k.val%m : ℕ) : ℝ)=(k.val : ℝ) := by exact_mod_cast hkv.symm
  rw [e] at h
  rw [h]
  push_cast
  ring

omit [NeZero s] [NeZero t] in
theorem norm_chirpBlock_le (m : ℕ) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖≤1) (k : ZMod t) :
    ‖chirpBlock (s := s) α m u k‖≤3*m+1 := by
  unfold chirpBlock
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a∈range (3*m+1), ‖(Real.exp (-π*α⁻¹^2*s^2*((k.val : ℝ)/t-
          ((blockIn s t m (k.val/m*m)+a : ℤ) : ℝ)/s)^2) : ℂ)*
          u ((blockIn s t m (k.val/m*m)+a : ℤ) : ZMod s)‖≤∑ _a∈range (3*m+1), (1 : ℝ) := by
        refine sum_le_sum fun a _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine mul_le_one_of ?_ (norm_nonneg _) (hu _)
        rw [Real.exp_le_one_iff]
        have := mul_nonneg (mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg α⁻¹))
          (sq_nonneg (s : ℝ))) (sq_nonneg ((k.val : ℝ)/t-((blockIn s t m (k.val/m*m)+a : ℤ) : ℝ)/s))
        linarith
    _ =3*m+1 := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]; push_cast; ring

theorem norm_chirpCorrEx_le (hst : s<t) (m : ℕ) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖≤1)
    (k0 b : ℕ) : ‖chirpCorrEx (t := t) α m u k0 b‖≤3*m+1 := by
  unfold chirpCorrEx
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a∈range (3*m+1), ‖(chirpG s t α m k0 a : ℂ)*u ((blockIn s t m k0+a : ℤ) : ZMod s)*
        (chirpK s t α m k0 ((a : ℤ)-b) : ℂ)‖≤∑ _a∈range (3*m+1), (1 : ℝ) := by
        refine sum_le_sum fun a _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (chirpG_pos m k0 a), abs_of_pos (chirpK_pos m k0 _)]
        exact mul_le_one_of (mul_le_one_of (chirpG_le_one hst m k0 a) (norm_nonneg _) (hu _))
          (chirpK_pos m k0 _).le (chirpK_le_one m k0 _)
    _ =3*m+1 := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]; push_cast; ring

/-- The correlation of the computed inputs is within `(3m + 1) 4η` of the exact one. -/
theorem chirpCorr_err (hst : s<t) (m : ℕ) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖≤1)
    (rd : ℂ → ℂ) (η : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η) (hη1 : η≤1/4)
    (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (hg : ∀ k0 a, |gt k0 a-chirpG s t α m k0 a|≤η)
    (hk : ∀ k0 r, |kt k0 r-chirpK s t α m k0 r|≤η) (k0 b : ℕ) :
    ‖chirpCorr (t := t) m rd gt kt u k0 b-chirpCorrEx (t := t) α m u k0 b‖≤(3*m+1)*(4*η) := by
  have hη : 0≤η := le_trans (norm_nonneg _) (hrd 0)
  have hcnorm (c : ℝ) : ‖(c : ℂ)‖=|c| := by rw [Complex.norm_real, Real.norm_eq_abs]
  unfold chirpCorr chirpCorrEx
  rw [←sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a∈range (3*m+1), ‖chirpIn (t := t) m rd gt u k0 a*(kt k0 ((a : ℤ)-b) : ℂ)-
        (chirpG s t α m k0 a : ℂ)*u ((blockIn s t m k0+a : ℤ) : ZMod s)*
          (chirpK s t α m k0 ((a : ℤ)-b) : ℂ)‖≤∑ _a∈range (3*m+1), 4*η := by
        refine sum_le_sum fun a _ => ?_
        set v := u ((blockIn s t m k0+a : ℤ) : ZMod s)
        have hv : ‖v‖≤1 := hu _
        have hin : ‖chirpIn (t := t) m rd gt u k0 a-(chirpG s t α m k0 a : ℂ)*v‖≤2*η := by
          unfold chirpIn
          have h1 := hrd ((gt k0 a : ℂ)*v)
          have h2 : ‖(gt k0 a : ℂ)*v-(chirpG s t α m k0 a : ℂ)*v‖≤η := by
            rw [←sub_mul, norm_mul, ←Complex.ofReal_sub, hcnorm]
            exact (mul_le_mul (hg k0 a) hv (norm_nonneg _) hη).trans (by linarith)
          calc _=‖(rd ((gt k0 a : ℂ)*v)-(gt k0 a : ℂ)*v)+((gt k0 a : ℂ)*v-(chirpG s t α m k0 a : ℂ)*v)‖ := by
                congr 1; ring
            _ ≤η+η := (norm_add_le _ _).trans (add_le_add h1 h2)
            _ =2*η := by ring
        have hkt : |kt k0 ((a : ℤ)-b)|≤1+η := by
          have h1 := hk k0 ((a : ℤ)-b)
          have h2 := abs_add_le (kt k0 ((a : ℤ)-b)-chirpK s t α m k0 ((a : ℤ)-b))
            (chirpK s t α m k0 ((a : ℤ)-b))
          rw [sub_add_cancel, abs_of_pos (chirpK_pos m k0 _)] at h2
          linarith [chirpK_le_one (s := s) (t := t) (α := α) m k0 ((a : ℤ)-b)]
        have hGv : ‖(chirpG s t α m k0 a : ℂ)*v‖≤1 := by
          rw [norm_mul, hcnorm, abs_of_pos (chirpG_pos m k0 a)]
          exact mul_le_one_of (chirpG_le_one hst m k0 a) (norm_nonneg _) hv
        calc _=‖(chirpIn (t := t) m rd gt u k0 a-(chirpG s t α m k0 a : ℂ)*v)*
              (kt k0 ((a : ℤ)-b) : ℂ)+(chirpG s t α m k0 a : ℂ)*v*
              ((kt k0 ((a : ℤ)-b) : ℂ)-(chirpK s t α m k0 ((a : ℤ)-b) : ℂ))‖ := by
              congr 1; ring
          _ ≤2*η*(1+η)+1*η := by
              refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [norm_mul, hcnorm]
                exact mul_le_mul hin hkt (abs_nonneg _) (by positivity)
              · rw [norm_mul, ←Complex.ofReal_sub, hcnorm]
                exact mul_le_mul hGv (hk k0 _) (abs_nonneg _) zero_le_one
          _ ≤4*η := by nlinarith
    _ =(3*m+1)*(4*η) := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- The output stage: from a correlation within `ζ` of the exact one, the computed output is
within `2/2^p + η (3m + 3) + 2^Γ ((6m + 3) η + ζ)/2 + 3/(2·2^p)` of `Ã u`. -/
theorem chirpAG_row (hst : s<t) (hα : 1≤α) {p m Γ : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖≤1)
    (rd : ℂ → ℂ) (η ζ : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η)
    (corr : (ZMod s → ℂ) → ℕ → ℕ → ℂ) (et : ℕ → ℕ → ℝ) (aN : ℝ)
    (hcorr : ∀ n b, b<m → ‖corr u (n*m) b-chirpCorrEx (t := t) α m u (n*m) b‖≤ζ) (hζ : ζ≤3*m+1)
    (he : ∀ k0, ∀ b<m, |et k0 b-chirpE s t α b/2^Γ|≤η)
    (ha : |aN-1/(2*α)|≤η) (hΓ : ∀ b<m, chirpE s t α b≤2^Γ)
    (hEη : 2^Γ*((6*(m : ℝ)+3)*η+ζ)≤1) (k : ZMod t) :
    ‖chirpAG (s := s) (t := t) p m Γ rd corr et aN u k-resampA s t α u k‖≤
      2/2^p+(η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+ζ)))+3/(2*2^p) := by
  have hα0 : 0<α := by linarith
  have hη : 0≤η := le_trans (norm_nonneg _) (hrd 0)
  have h2p : (0 : ℝ)<2^p := by positivity
  have hcnorm (c : ℝ) : ‖(c : ℂ)‖=|c| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hb : k.val%m<m := Nat.mod_lt _ (by omega)
  have hAk : resampA s t α u k=(1/2 : ℂ)*resampS s t α u k := by
    simp [resampA, resampSCLM_apply hα0]
  unfold chirpAG
  set k0 := k.val/m*m with hk0
  set b := k.val%m with hbdef
  set Bsum := chirpBlock (s := s) α m u k with hBsum
  set cEx := chirpCorrEx (t := t) α m u k0 b with hcEx
  set cr := corr u k0 b with hcrdef
  have hsup := chirpBlock_err hst hα0 hαp hm hm1 u hu k
  have hBE : Bsum=(chirpE s t α b : ℂ)*cEx := chirpBlock_split hα0 m u k
  have hBsum1 : ‖Bsum‖≤3*m+1 := norm_chirpBlock_le m u hu k
  have hcEx1 : ‖cEx‖≤3*m+1 := norm_chirpCorrEx_le hst m u hu k0 b
  have hcr : ‖cr-cEx‖≤ζ := hcorr (k.val/m) b hb
  have hcorr1 : ‖cr‖≤2*(3*m+1) := by
    have := norm_add_le (cr-cEx) cEx
    rw [sub_add_cancel] at this
    linarith
  -- The output factor and the shift.
  set z1 := rd ((et k0 b : ℂ)*cr) with hz1
  have hE1 : chirpE s t α b/2^Γ≤1 := by rw [div_le_one (by positivity)]; exact hΓ b hb
  have hE0 : 0≤chirpE s t α b/2^Γ := by unfold chirpE; positivity
  have hz1e : ‖z1-((chirpE s t α b/2^Γ : ℝ) : ℂ)*cEx‖≤(6*m+3)*η+ζ := by
    have h1 := hrd ((et k0 b : ℂ)*cr)
    have h2 : ‖((et k0 b-chirpE s t α b/2^Γ : ℝ) : ℂ)*cr‖≤η*(2*(3*m+1)) := by
      rw [norm_mul, hcnorm]; exact mul_le_mul (he k0 b hb) hcorr1 (norm_nonneg _) hη
    have h3 : ‖((chirpE s t α b/2^Γ : ℝ) : ℂ)*(cr-cEx)‖≤1*ζ := by
      rw [norm_mul, hcnorm, abs_of_nonneg hE0]
      exact mul_le_mul hE1 hcr (norm_nonneg _) zero_le_one
    calc ‖z1-((chirpE s t α b/2^Γ : ℝ) : ℂ)*cEx‖=‖(rd ((et k0 b : ℂ)*cr)-(et k0 b : ℂ)*cr)+
          ((et k0 b-chirpE s t α b/2^Γ : ℝ) : ℂ)*cr+
          ((chirpE s t α b/2^Γ : ℝ) : ℂ)*(cr-cEx)‖ := by
          rw [hz1]; push_cast; congr 1; ring
      _ ≤η+η*(2*(3*m+1))+1*ζ :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
      _ =(6*m+3)*η+ζ := by ring
  have hshift : ‖(2 : ℂ)^Γ*z1-Bsum‖≤2^Γ*((6*m+3)*η+ζ) := by
    have e : (2 : ℂ)^Γ*z1-Bsum=(2 : ℂ)^Γ*(z1-((chirpE s t α b/2^Γ : ℝ) : ℂ)*cEx) := by
      rw [hBE, mul_sub]
      congr 1
      push_cast
      field_simp
    rw [e, norm_mul, norm_pow, RCLike.norm_two]
    exact mul_le_mul_of_nonneg_left hz1e (by positivity)
  have hz1n : ‖(2 : ℂ)^Γ*z1‖≤3*m+2 := by
    have := norm_add_le ((2 : ℂ)^Γ*z1-Bsum) Bsum
    rw [sub_add_cancel] at this
    linarith
  -- The factor `1/(2α)` and the final rounding.
  set z2 := rd ((aN : ℂ)*((2 : ℂ)^Γ*z1)) with hz2
  have hαi : 1/(2*α)≤1/2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hαi0 : 0≤1/(2*α) := by positivity
  have hz2e : ‖z2-((1/(2*α) : ℝ) : ℂ)*Bsum‖≤η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+ζ)) := by
    have h1 := hrd ((aN : ℂ)*((2 : ℂ)^Γ*z1))
    have h2 : ‖((aN-1/(2*α) : ℝ) : ℂ)*((2 : ℂ)^Γ*z1)‖≤η*(3*m+2) := by
      rw [norm_mul, hcnorm]; exact mul_le_mul ha hz1n (norm_nonneg _) hη
    have h3 : ‖((1/(2*α) : ℝ) : ℂ)*((2 : ℂ)^Γ*z1-Bsum)‖≤1/2*(2^Γ*((6*m+3)*η+ζ)) := by
      rw [norm_mul, hcnorm, abs_of_nonneg hαi0]
      exact mul_le_mul hαi hshift (norm_nonneg _) (by norm_num)
    calc ‖z2-((1/(2*α) : ℝ) : ℂ)*Bsum‖=‖(rd ((aN : ℂ)*((2 : ℂ)^Γ*z1))-(aN : ℂ)*((2 : ℂ)^Γ*z1))+
        ((aN-1/(2*α) : ℝ) : ℂ)*((2 : ℂ)^Γ*z1)+((1/(2*α) : ℝ) : ℂ)*((2 : ℂ)^Γ*z1-Bsum)‖ := by
          rw [hz2]; push_cast; congr 1; ring
      _ ≤η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+ζ)) :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
  have hBA : ‖((1/(2*α) : ℝ) : ℂ)*Bsum-resampA s t α u k‖≤3/(2*2^p) := by
    rw [hAk]
    have e : ((1/(2*α) : ℝ) : ℂ)*Bsum-(1/2 : ℂ)*resampS s t α u k=
        -((1/2 : ℂ)*(resampS s t α u k-(1/α : ℂ)*Bsum)) := by push_cast; ring
    rw [e, norm_neg, norm_mul]
    have h1 : ‖(1/2 : ℂ)‖=1/2 := by norm_num
    rw [h1]
    have h3 : 3/(α*2^p)≤3/2^p := by
      apply div_le_div_of_nonneg_left (by norm_num) h2p
      nlinarith
    calc 1/2*‖resampS s t α u k-(1/α : ℂ)*Bsum‖≤1/2*(3/2^p) :=
          mul_le_mul_of_nonneg_left (hsup.trans h3) (by norm_num)
      _ =3/(2*2^p) := by field_simp
  have hrho := norm_rhoC_sub_le_two p z2
  have h2 := norm_add_le ((rhoC p z2-z2)+(z2-((1/(2*α) : ℝ) : ℂ)*Bsum))
    (((1/(2*α) : ℝ) : ℂ)*Bsum-resampA s t α u k)
  have h3 := norm_add_le (rhoC p z2-z2) (z2-((1/(2*α) : ℝ) : ℂ)*Bsum)
  have e : rhoC p z2-z2+(z2-((1/(2*α) : ℝ) : ℂ)*Bsum)+(((1/(2*α) : ℝ) : ℂ)*Bsum-resampA s t α u k)=
      rhoC p z2-resampA s t α u k := by ring
  rw [e] at h2
  linarith

/-- **The chirped-correlation `Ã` from a computed correlation.** With a correlation within `ζ`
of the exact one and `2^p (η (3m + 3) + 2^Γ ((6m + 3) η + ζ)/2) ≤ 1/2`, the output stage
approximates `Ã = S/2` with scaled error `4`. -/
theorem chirpAG_approx (hst : s<t) (hα : 1≤α) {p m Γ : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m)
    (rd : ℂ → ℂ) (η ζ : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η)
    (corr : (ZMod s → ℂ) → ℕ → ℕ → ℂ) (et : ℕ → ℕ → ℝ) (aN : ℝ)
    (hcorr : ∀ u : ZMod s → ℂ, ‖u‖≤1 → ∀ n b, b<m →
      ‖corr u (n*m) b-chirpCorrEx (t := t) α m u (n*m) b‖≤ζ)
    (hζ : ζ≤3*m+1)
    (he : ∀ k0, ∀ b<m, |et k0 b-chirpE s t α b/2^Γ|≤η)
    (ha : |aN-1/(2*α)|≤η) (hΓ : ∀ b<m, chirpE s t α b≤2^Γ)
    (hEη : 2^Γ*((6*(m : ℝ)+3)*η+ζ)≤1)
    (hsm : 2^p*(η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+ζ)))≤1/2) :
    ApproxMap p (chirpAG (s := s) (t := t) p m Γ rd corr et aN) (resampA s t α) 4 := by
  intro u hu
  have hu' : ∀ j, ‖u j‖≤1 := fun j => (norm_le_pi_norm u j).trans hu
  have h2p : (0 : ℝ)<2^p := by positivity
  have hrow : ∀ k, ‖chirpAG (s := s) (t := t) p m Γ rd corr et aN u k-resampA s t α u k‖≤4/2^p := by
    intro k
    refine (chirpAG_row hst hα hαp hm hm1 u hu' rd η ζ hrd corr et aN (hcorr u hu) hζ he ha hΓ
      hEη k).trans ?_
    have e1 : 2/2^p+(η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+ζ)))+3/(2*2^p)=
        (7/2+2^p*(η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+ζ))))/2^p := by field_simp; ring
    rw [e1, div_le_div_iff_of_pos_right h2p]
    linarith
  have hle : ‖chirpAG (s := s) (t := t) p m Γ rd corr et aN u-resampA s t α u‖≤4/2^p :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => hrow k
  rw [le_div_iff₀ h2p, mul_comm] at hle
  exact hle

/-- **The chirped-correlation `Ã`** approximates `Ã = S/2` with scaled error `4` when the
tables are within `η` of the factors, the output factor is at most `2^Γ` on a block, and
`2^(p+Γ) (12m + 7) η ≤ 1/2`. -/
theorem chirpA_approx (hst : s<t) (hα : 1≤α) {p m Γ : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m)
    (rd : ℂ → ℂ) (η : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η)
    (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (et : ℕ → ℕ → ℝ) (aN : ℝ)
    (hg : ∀ k0 a, |gt k0 a-chirpG s t α m k0 a|≤η)
    (hk : ∀ k0 r, |kt k0 r-chirpK s t α m k0 r|≤η)
    (he : ∀ k0, ∀ b<m, |et k0 b-chirpE s t α b/2^Γ|≤η)
    (ha : |aN-1/(2*α)|≤η) (hΓ : ∀ b<m, chirpE s t α b≤2^Γ)
    (hprec : 2^(p+Γ)*(12*(m : ℝ)+7)*η≤1/2) :
    ApproxMap p (chirpA (s := s) (t := t) p m Γ rd gt kt et aN) (resampA s t α) 4 := by
  have hη : 0≤η := le_trans (norm_nonneg _) (hrd 0)
  have h2p : (0 : ℝ)<2^p := by positivity
  have h2Γ : (1 : ℝ)≤2^Γ := one_le_pow₀ (by norm_num)
  have hm0 : (1 : ℝ)≤m := by exact_mod_cast hm1
  rw [pow_add] at hprec
  have h2p1 : (1 : ℝ)≤2^p := one_le_pow₀ (by norm_num)
  have hX0 : 0≤2^Γ*(12*(m : ℝ)+7)*η := by positivity
  have hX : 2^Γ*(12*(m : ℝ)+7)*η≤1/2 := by
    have := mul_le_mul_of_nonneg_right h2p1 hX0
    nlinarith
  have hη1 : η≤1/4 := by
    have : 19*η≤2^Γ*(12*(m : ℝ)+7)*η :=
      mul_le_mul_of_nonneg_right (by nlinarith) hη
    linarith
  have hζ : (3*(m : ℝ)+1)*(4*η)≤3*m+1 := by
    have := mul_le_mul_of_nonneg_left (by linarith : 4*η≤1) (by positivity : (0 : ℝ)≤3*m+1)
    linarith
  have e18 : (6*(m : ℝ)+3)*η+(3*m+1)*(4*η)=(18*m+7)*η := by ring
  have hEη : 2^Γ*((6*(m : ℝ)+3)*η+(3*m+1)*(4*η))≤1 := by
    rw [e18]
    have : 2^Γ*((18*(m : ℝ)+7)*η)≤2*(2^Γ*(12*(m : ℝ)+7)*η) := by
      have := mul_nonneg (by positivity : (0 : ℝ)≤2^Γ) hη
      nlinarith
    linarith
  have hsm : 2^p*(η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+(3*m+1)*(4*η))))≤1/2 := by
    rw [e18]
    have h1 : η+η*(3*m+2)+1/2*(2^Γ*((18*m+7)*η))≤2^Γ*(12*m+7)*η := by
      have : η*(3*m+3)≤2^Γ*(η*(3*m+3)) := le_mul_of_one_le_left (by positivity) h2Γ
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 h2p.le
    nlinarith
  exact chirpAG_approx hst hα hαp hm hm1 rd η _ hrd _ et aN
    (fun u hu n b _ => chirpCorr_err hst m u (fun j => (norm_le_pi_norm u j).trans hu) rd η hrd
      hη1 gt kt hg hk (n*m) b) hζ he ha hΓ hEη hsm

/-- The clamped chirped-correlation `Ã`: the same error, and it maps into the unit ball, as the
pipeline's `Ã` interface requires. -/
theorem chirpA_clamp (hst : s<t) (hα : 1≤α) {p m Γ : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m)
    (rd : ℂ → ℂ) (η : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η)
    (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (et : ℕ → ℕ → ℝ) (aN : ℝ)
    (hg : ∀ k0 a, |gt k0 a-chirpG s t α m k0 a|≤η)
    (hk : ∀ k0 r, |kt k0 r-chirpK s t α m k0 r|≤η)
    (he : ∀ k0, ∀ b<m, |et k0 b-chirpE s t α b/2^Γ|≤η)
    (ha : |aN-1/(2*α)|≤η) (hΓ : ∀ b<m, chirpE s t α b≤2^Γ)
    (hprec : 2^(p+Γ)*(12*(m : ℝ)+7)*η≤1/2) :
    ApproxMap p (clampV ∘ chirpA (s := s) (t := t) p m Γ rd gt kt et aN) (resampA s t α) 4 ∧
      ∀ u, ‖(clampV ∘ chirpA (s := s) (t := t) p m Γ rd gt kt et aN) u‖≤1 :=
  ⟨approxMap_clamp (opNorm_resampA_le hα)
    (chirpA_approx hst hα hαp hm hm1 rd η hrd gt kt et aN hg hk he ha hΓ hprec),
    fun _ => norm_clampV_le_one _⟩

end IntegerMultBounds.NLogN
