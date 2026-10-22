module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConv
public import IntegerMultBounds.NLogN.ChirpForward
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # The block correlations of the chirped forward map on the ring product

Block `n` (first output `k₀ = n m`) has `3m + 1` computed inputs `g_a` and needs
`c_b = ∑_a g_a K_{a-b}` for `b < m`. With the inputs reversed, `G_i = g_{3m-i}`, and the kernel
shifted, `K'_j = K_{j-(m-1)}` for `j < 4m`, `c_b` is coefficient `4m - 1 - b` of the linear
convolution of `G` and `K'` (`chirpCorr_conv`). One ring record pair of size `2^l ≥ 7m` per block,
both halved into the unit disk, computes it: the rescaled output `4·2^l Q_q(G K' / (4·2^l))` is
within `8·2^l/2^q` of `c_b` (`chirpRingCorr_err`), and the output stage on it approximates `Ã`
(`chirpAR_approx`). -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN Finset

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The reversed, halved inputs of block `n`, zero beyond `3m + 1`. -/
noncomputable def chirpRecIn (m : ℕ) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (u : ZMod s → ℂ)
    (n i : ℕ) : ℂ :=
  if i<3*m+1 then chirpIn (t := t) m rd gt u (n*m) (3*m-i)/2 else 0

/-- The shifted, halved kernel of block `n`, zero beyond `4m`. -/
noncomputable def chirpRecK (m : ℕ) (kt : ℕ → ℤ → ℝ) (n j : ℕ) : ℂ :=
  if j<4*m then (kt (n*m) ((j : ℤ)-(m-1 : ℕ)) : ℂ)/2 else 0

/-- The correlation of block `k₀/m` at offset `b` from the ring product at precision `q` on
records of size `2^l`, rescaled by `4·2^l`. -/
noncomputable def chirpRingCorr (q m l : ℕ) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (u : ZMod s → ℂ) (k0 b : ℕ) : ℂ :=
  (4*2^l : ℂ)*SynthErr.pwC q (fun n => recOf (2^l) (chirpRecIn (t := t) m rd gt u n))
    (fun n => recOf (2^l) (chirpRecK m kt n)) (k0/m)
    ⟨(4*m-1-b)%2^l, Nat.mod_lt _ (by positivity)⟩

omit [NeZero s] [NeZero t] in
/-- The correlation is a coefficient of the linear convolution of the reversed inputs and the
shifted kernel. -/
theorem chirpCorr_conv (m : ℕ) (hm1 : 1≤m) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (u : ZMod s → ℂ) (n b : ℕ) (hb : b<m) :
    chirpCorr (t := t) m rd gt kt u (n*m) b=
      4*∑ i∈range (4*m-1-b+1), chirpRecIn (t := t) m rd gt u n i*chirpRecK m kt n (4*m-1-b-i) := by
  unfold chirpCorr
  -- Reindex `a = 3m - i` and drop the vanishing terms `i > 3m`.
  have hsplit : ∑ i∈range (4*m-1-b+1), chirpRecIn (t := t) m rd gt u n i*chirpRecK m kt n (4*m-1-b-i)=
      ∑ i∈range (3*m+1), chirpRecIn (t := t) m rd gt u n i*chirpRecK m kt n (4*m-1-b-i) := by
    have hsub : range (3*m+1)⊆range (4*m-1-b+1) := by
      intro i hi; simp only [mem_range] at hi ⊢; omega
    rw [←sum_subset hsub]
    intro i hi hni
    simp only [mem_range] at hi hni
    unfold chirpRecIn
    rw [ite_eq_right (by omega), zero_mul]
  rw [hsplit, mul_sum, ←sum_range_reflect]
  refine sum_congr rfl fun a ha => ?_
  simp only [mem_range] at ha
  unfold chirpRecIn chirpRecK
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  have hi : 3*m+1-1-a=3*m-a := by omega
  have hj : (((4*m-1-b-a : ℕ) : ℤ)-((m-1 : ℕ) : ℤ))=((3*m-a : ℕ) : ℤ)-b := by omega
  rw [hi, hj]
  ring

omit [NeZero s] [NeZero t] in
/-- **The ring correlation** is within `8·2^l/2^q` of the exact correlation of the computed
inputs when `7m ≤ 2^l`. -/
theorem chirpRingCorr_err (q m l : ℕ) (hm1 : 1≤m) (hl : 7*m≤2^l) (rd : ℂ → ℂ)
    (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (u : ZMod s → ℂ) (n b : ℕ) (hb : b<m) :
    ‖chirpRingCorr (t := t) q m l rd gt kt u (n*m) b-chirpCorr (t := t) m rd gt kt u (n*m) b‖≤
      8*2^l/2^q := by
  have hm0 : 0<m := by omega
  have hidx : 4*m-1-b<2^l := by omega
  have hk0 : n*m/m=n := Nat.mul_div_cancel n hm0
  unfold chirpRingCorr
  simp only [hk0, Nat.mod_eq_of_lt hidx]
  rw [chirpCorr_conv m hm1 rd gt kt u n b hb]
  have herr := pwC_recOf_err q (fun n => chirpRecIn (t := t) m rd gt u n) (chirpRecK m kt)
    (3*m+1) (4*m) (by omega)
    (fun n i hi => by unfold chirpRecIn; rw [ite_eq_right (by omega)])
    (fun n j hj => by unfold chirpRecK; rw [ite_eq_right (by omega)]) n ⟨4*m-1-b, hidx⟩
  simp only at herr
  have hcast : ((2^l : ℕ) : ℂ)=(2 : ℂ)^l := by push_cast; ring
  rw [hcast] at herr
  set P := SynthErr.pwC q (fun n => recOf (2^l) (chirpRecIn (t := t) m rd gt u n))
    (fun n => recOf (2^l) (chirpRecK m kt n)) n ⟨4*m-1-b, hidx⟩
  set C := ∑ i∈range (4*m-1-b+1), chirpRecIn (t := t) m rd gt u n i*chirpRecK m kt n (4*m-1-b-i)
  have e : (4*2^l : ℂ)*P-4*C=4*((2 : ℂ)^l*P-C) := by ring
  rw [e, norm_mul]
  have h4 : ‖(4 : ℂ)‖=4 := by norm_num
  rw [h4]
  have hc : ((2^l : ℕ) : ℝ)=(2 : ℝ)^l := by push_cast; ring
  rw [hc] at herr
  calc 4*‖(2 : ℂ)^l*P-C‖≤4*(2*2^l/2^q) := mul_le_mul_of_nonneg_left herr (by norm_num)
    _ =8*2^l/2^q := by ring

/-- The ring operands are disk records: the halved computed inputs and kernel table are at most
one when the tables are within `η ≤ 1/2` of factors at most one. -/
theorem norm_chirpRec_le (hst : s<t) (m : ℕ) (rd : ℂ → ℂ) (η : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η)
    (hη1 : η≤1/2) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (hg : ∀ k0 a, |gt k0 a-chirpG s t α m k0 a|≤η)
    (hk : ∀ k0 r, |kt k0 r-chirpK s t α m k0 r|≤η) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖≤1)
    (n i : ℕ) : ‖chirpRecIn (t := t) m rd gt u n i‖≤1 ∧ ‖chirpRecK m kt n i‖≤1 := by
  have hcnorm (c : ℝ) : ‖(c : ℂ)‖=|c| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have habs (x y : ℝ) (hxy : |x-y|≤η) (hy0 : 0≤y) (hy1 : y≤1) : |x|≤2 := by
    have := abs_add_le (x-y) y
    rw [sub_add_cancel, abs_of_nonneg hy0] at this
    linarith
  constructor
  · unfold chirpRecIn
    split
    · rw [norm_div, RCLike.norm_two, div_le_one (by norm_num)]
      unfold chirpIn
      set z := (gt (n*m) (3*m-i) : ℂ)*u ((blockIn s t m (n*m)+(3*m-i : ℕ) : ℤ) : ZMod s)
      have h1 := hrd z
      have h2 : ‖z‖≤1+η := by
        simp only [z]
        rw [norm_mul, hcnorm]
        have hg' : |gt (n*m) (3*m-i)|≤1+η := by
          have := hg (n*m) (3*m-i)
          have := abs_add_le (gt (n*m) (3*m-i)-chirpG s t α m (n*m) (3*m-i)) (chirpG s t α m (n*m) (3*m-i))
          rw [sub_add_cancel, abs_of_pos (chirpG_pos m _ _)] at this
          linarith [chirpG_le_one (α := α) hst m (n*m) (3*m-i)]
        calc |gt (n*m) (3*m-i)| * ‖u _‖≤(1+η)*1 :=
              mul_le_mul hg' (hu _) (norm_nonneg _) (by linarith [abs_nonneg (gt (n*m) (3*m-i))])
          _ =1+η := mul_one _
      have := norm_add_le (rd z-z) z
      rw [sub_add_cancel] at this
      linarith
    · simp
  · unfold chirpRecK
    split
    · rw [norm_div, RCLike.norm_two, div_le_one (by norm_num), hcnorm]
      exact habs _ _ (hk _ _) (chirpK_pos m _ _).le (chirpK_le_one m _ _)
    · simp

/-- The chirped-correlation `Ã` on the ring product. -/
noncomputable def chirpAR (p q m l Γ : ℕ) (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ)
    (et : ℕ → ℕ → ℝ) (aN : ℝ) : (ZMod s → ℂ) → ZMod t → ℂ :=
  chirpAG (t := t) p m Γ rd (fun u => chirpRingCorr (t := t) q m l rd gt kt u) et aN

/-- **The chirped-correlation `Ã` on the ring product** approximates `Ã` with scaled error
`4` once the tables are within `η`, `7m ≤ 2^l`, and the ring precision `q` makes
`ζ = 8·2^l/2^q + (3m + 1) 4η` small in the sense of `chirpAG_approx`. -/
theorem chirpAR_approx (hst : s<t) (hα : 1≤α) {p q m l Γ : ℕ} (hαp : α^2≤p)
    (hm : (p : ℝ)*α^2≤(m : ℝ)^2) (hm1 : 1≤m) (hl : 7*m≤2^l)
    (rd : ℂ → ℂ) (η : ℝ) (hrd : ∀ z, ‖rd z-z‖≤η) (hη1 : η≤1/4)
    (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (et : ℕ → ℕ → ℝ) (aN : ℝ)
    (hg : ∀ k0 a, |gt k0 a-chirpG s t α m k0 a|≤η)
    (hk : ∀ k0 r, |kt k0 r-chirpK s t α m k0 r|≤η)
    (he : ∀ k0, ∀ b<m, |et k0 b-chirpE s t α b/2^Γ|≤η)
    (ha : |aN-1/(2*α)|≤η) (hΓ : ∀ b<m, chirpE s t α b≤2^Γ)
    (hζ : 8*2^l/2^q+(3*(m : ℝ)+1)*(4*η)≤3*m+1)
    (hEη : 2^Γ*((6*(m : ℝ)+3)*η+(8*2^l/2^q+(3*m+1)*(4*η)))≤1)
    (hsm : 2^p*(η+η*(3*m+2)+1/2*(2^Γ*((6*m+3)*η+(8*2^l/2^q+(3*m+1)*(4*η)))))≤1/2) :
    ApproxMap p (chirpAR (s := s) (t := t) p q m l Γ rd gt kt et aN) (resampA s t α) 4 := by
  refine chirpAG_approx hst hα hαp hm hm1 rd η _ hrd _ et aN (fun u hu n b hb => ?_) hζ he ha hΓ
    hEη hsm
  have h1 := chirpRingCorr_err (t := t) q m l hm1 hl rd gt kt u n b hb
  have h2 := chirpCorr_err hst m u (fun j => (norm_le_pi_norm u j).trans hu) rd η hrd hη1 gt kt
    hg hk (n*m) b
  have := norm_add_le (chirpRingCorr (t := t) q m l rd gt kt u (n*m) b-
    chirpCorr (t := t) m rd gt kt u (n*m) b)
    (chirpCorr (t := t) m rd gt kt u (n*m) b-chirpCorrEx (t := t) α m u (n*m) b)
  rw [sub_add_sub_cancel] at this
  linarith

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
