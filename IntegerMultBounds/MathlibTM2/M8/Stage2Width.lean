module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Width selection of the stage-2 supplier

The `F L F` wrapper runs an interchange of `e` digits as the reversed family on `n = ⌊e/w⌋` atoms
of `w` digits, plus a leaf interchange of the `e - n w < w` residual digits. The family costs
`A n + B n^τs L` of the volume with `L ≈ w^τ₁` (`RevBudget.rev97_family`), the leaf `w^τ₁`. With
`e^θ ≤ w ≤ c e^θ` every term is at most a constant times `e^τ₂` for
`τ₂ = (1 - θ) τs + θ τ₁` (`tau2`): the linear terms because `n ≤ e^(1-θ)` (`count_le`), the
family's power term because `n^τs w^τ₁ ≤ e^τs w^(τ₁ - τs)` (`family_le`), the leaf because
`θ τ₁ ≤ τ₂` (`leaf_le`).

The width is `w = 2^⌈size e / K⌉` at `θ = 1/K` (`atomWidth`), which a machine reads off the
length of the binary descriptor of `e`; it satisfies `e^θ ≤ w ≤ 2 e^θ` (`atomWidth_ge`,
`atomWidth_le`). Bit lengths are at most `2 x^τ` for `τ ≥ 1/2` (`size_le`, `succ_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Width

/-- The exponent of the wrapped supplier: `τs` on the atom count `e^(1-θ)`, `τ₁` on the atom
width `e^θ`. -/
def tau2 (θ τs τ₁ : ℝ) : ℝ := (1 - θ) * τs + θ * τ₁

variable {θ τs τ₁ c E w n : ℝ}

/-- The atom count is at most `e^(1-θ)`. -/
theorem count_le (hE : 1 ≤ E) (hw : E ^ θ ≤ w) (hn : n * w ≤ E) : n ≤ E ^ (1 - θ) := by
  have hE0 : 0 < E := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (Real.rpow_pos_of_pos hE0 θ) hw
  have hθ0 : 0 < E ^ θ := Real.rpow_pos_of_pos hE0 θ
  rw [Real.rpow_sub hE0, Real.rpow_one, le_div_iff₀ hθ0]
  nlinarith

/-- The linear terms. -/
theorem linear_le (hE : 1 ≤ E) (hw : E ^ θ ≤ w) (hn : n * w ≤ E) (hτ : 1 - θ ≤ tau2 θ τs τ₁) :
    n ≤ E ^ tau2 θ τs τ₁ :=
  (count_le hE hw hn).trans (Real.rpow_le_rpow_of_exponent_le hE hτ)

/-- **The family's power term.** -/
theorem family_le (hs : 0 ≤ τs) (hs1 : τs ≤ τ₁) (h1 : τ₁ - τs ≤ 1) (hc : 1 ≤ c)
    (hE : 1 ≤ E) (hw : E ^ θ ≤ w) (hw' : w ≤ c * E ^ θ) (hn0 : 0 ≤ n) (hn : n * w ≤ E) :
    n ^ τs * w ^ τ₁ ≤ c * E ^ tau2 θ τs τ₁ := by
  have hE0 : 0 < E := by linarith
  have hθ0 : 0 < E ^ θ := Real.rpow_pos_of_pos hE0 θ
  have hw0 : 0 < w := lt_of_lt_of_le hθ0 hw
  have hnE : n ≤ E / w := by rw [le_div_iff₀ hw0]; exact hn
  have h₁ : n ^ τs ≤ E ^ τs / w ^ τs := by
    rw [← Real.div_rpow hE0.le hw0.le]
    exact Real.rpow_le_rpow hn0 hnE hs
  have h₂ : w ^ (τ₁ - τs) ≤ c * E ^ (θ * (τ₁ - τs)) := by
    calc w ^ (τ₁ - τs) ≤ (c * E ^ θ) ^ (τ₁ - τs) := Real.rpow_le_rpow hw0.le hw' (by linarith)
      _ = c ^ (τ₁ - τs) * E ^ (θ * (τ₁ - τs)) := by
        rw [Real.mul_rpow (by linarith) hθ0.le, ← Real.rpow_mul hE0.le]
      _ ≤ c * E ^ (θ * (τ₁ - τs)) := by
        gcongr
        calc c ^ (τ₁ - τs) ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc h1
          _ = c := Real.rpow_one c
  have hws : 0 < w ^ τs := Real.rpow_pos_of_pos hw0 τs
  calc n ^ τs * w ^ τ₁ ≤ E ^ τs / w ^ τs * w ^ τ₁ :=
        mul_le_mul_of_nonneg_right h₁ (Real.rpow_nonneg hw0.le _)
    _ = E ^ τs * w ^ (τ₁ - τs) := by
        rw [Real.rpow_sub hw0]; field_simp
    _ ≤ E ^ τs * (c * E ^ (θ * (τ₁ - τs))) :=
        mul_le_mul_of_nonneg_left h₂ (Real.rpow_nonneg hE0.le _)
    _ = c * E ^ tau2 θ τs τ₁ := by
        rw [mul_left_comm, ← Real.rpow_add hE0, tau2]
        congr 2
        ring

/-- **The leaf term.** -/
theorem leaf_le (hθ1 : θ ≤ 1) (hs : 0 ≤ τs) (hτ₁ : 0 ≤ τ₁) (hτ1 : τ₁ ≤ 1) (hc : 1 ≤ c)
    (hE : 1 ≤ E) (hw0 : 0 ≤ w) (hw' : w ≤ c * E ^ θ) :
    w ^ τ₁ ≤ c * E ^ tau2 θ τs τ₁ := by
  have hE0 : 0 < E := by linarith
  have hθ0 : 0 < E ^ θ := Real.rpow_pos_of_pos hE0 θ
  calc w ^ τ₁ ≤ (c * E ^ θ) ^ τ₁ := Real.rpow_le_rpow hw0 hw' hτ₁
    _ = c ^ τ₁ * E ^ (θ * τ₁) := by
        rw [Real.mul_rpow (by linarith) hθ0.le, ← Real.rpow_mul hE0.le]
    _ ≤ c * E ^ tau2 θ τs τ₁ := by
        gcongr
        · calc c ^ τ₁ ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hτ1
            _ = c := Real.rpow_one c
        · unfold tau2; nlinarith

/-! ### The atom width -/

/-- `⌈size e / K⌉`. -/
def atomExp (K e : ℕ) : ℕ := (Nat.size e + K - 1) / K

/-- The atom width `2^⌈size e / K⌉` at `θ = 1/K`. -/
def atomWidth (K e : ℕ) : ℕ := 2 ^ atomExp K e

theorem size_le_mul {K : ℕ} (hK : 0 < K) (e : ℕ) : Nat.size e ≤ K * atomExp K e := by
  unfold atomExp
  have := Nat.div_add_mod (Nat.size e + K - 1) K
  have := Nat.mod_lt (Nat.size e + K - 1) hK
  omega

theorem mul_le_size {K : ℕ} (e : ℕ) : K * atomExp K e ≤ Nat.size e + K - 1 := by
  unfold atomExp
  exact Nat.mul_div_le _ _

theorem atomWidth_pos (K e : ℕ) : 0 < atomWidth K e := pow_pos (by norm_num) _

theorem atomWidth_ge {K e : ℕ} (hK : 0 < K) : (e : ℝ) ^ ((K : ℝ)⁻¹) ≤ atomWidth K e := by
  have hlt : e < atomWidth K e ^ K := by
    calc e < 2 ^ Nat.size e := Nat.lt_size_self e
      _ ≤ 2 ^ (K * atomExp K e) := Nat.pow_le_pow_right (by norm_num) (size_le_mul hK e)
      _ = atomWidth K e ^ K := by rw [atomWidth, ← pow_mul, Nat.mul_comm]
  have hK0 : K ≠ 0 := Nat.pos_iff_ne_zero.mp hK
  calc (e : ℝ) ^ ((K : ℝ)⁻¹) ≤ (((atomWidth K e ^ K : ℕ) : ℝ)) ^ ((K : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlt.le) (by positivity)
    _ = atomWidth K e := by
        push_cast
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hK0

theorem atomWidth_le {K e : ℕ} (hK : 0 < K) (he : 1 ≤ e) :
    (atomWidth K e : ℝ) ≤ 2 * (e : ℝ) ^ ((K : ℝ)⁻¹) := by
  have hs : 0 < Nat.size e := Nat.size_pos.mpr he
  have hlow : 2 ^ (Nat.size e - 1) ≤ e := Nat.lt_size.mp (by omega)
  have hpow : atomWidth K e ^ K ≤ e * 2 ^ K := by
    calc atomWidth K e ^ K = 2 ^ (K * atomExp K e) := by rw [atomWidth, ← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (Nat.size e - 1 + K) := Nat.pow_le_pow_right (by norm_num) (by
          have := mul_le_size (K := K) e; omega)
      _ = 2 ^ (Nat.size e - 1) * 2 ^ K := pow_add _ _ _
      _ ≤ e * 2 ^ K := Nat.mul_le_mul_right _ hlow
  have hK0 : K ≠ 0 := Nat.pos_iff_ne_zero.mp hK
  have hinv : (0 : ℝ) ≤ (K : ℝ)⁻¹ := by positivity
  calc (atomWidth K e : ℝ) = (((atomWidth K e ^ K : ℕ) : ℝ)) ^ ((K : ℝ)⁻¹) := by
        push_cast
        exact (Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hK0).symm
    _ ≤ ((e * 2 ^ K : ℕ) : ℝ) ^ ((K : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hpow) hinv
    _ = (e : ℝ) ^ ((K : ℝ)⁻¹) * 2 := by
        push_cast
        rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity),
          Real.pow_rpow_inv_natCast (by norm_num) hK0]
    _ = 2 * (e : ℝ) ^ ((K : ℝ)⁻¹) := by ring

/-- The atom width is at most `e` from two digits on (`n ≥ 1` atoms). -/
theorem atomWidth_le_self {K e : ℕ} (hK : 2 ≤ K) (he : 2 ≤ e) : atomWidth K e ≤ e := by
  have hs : 1 < Nat.size e := Nat.lt_size.mpr (by simpa using he)
  have hlow : 2 ^ (Nat.size e - 1) ≤ e := Nat.lt_size.mp (by omega)
  have hexp : atomExp K e ≤ Nat.size e - 1 := by
    by_contra hc
    have hge : Nat.size e ≤ atomExp K e := by omega
    have h1 := mul_le_size (K := K) e
    have h2 : K * Nat.size e ≤ K * atomExp K e := Nat.mul_le_mul_left _ hge
    have h4 : Nat.size e + K ≤ K * Nat.size e := by nlinarith
    omega
  exact (Nat.pow_le_pow_right (by norm_num) hexp).trans hlow

/-! ### Bit lengths -/

theorem sq_le_pow : ∀ k : ℕ, (k + 1) ^ 2 ≤ 4 * 2 ^ k
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | k + 3 => by
    have ih := sq_le_pow (k + 2)
    rw [pow_succ 2 (k + 2)]
    have h : (k + 3 + 1) ^ 2 ≤ 2 * (k + 2 + 1) ^ 2 := by ring_nf; nlinarith
    omega

/-- `k + 1 ≤ 2 (2^k)^τ` for `τ ≥ 1/2`. -/
theorem succ_le (k : ℕ) {τ : ℝ} (hτ : 1 / 2 ≤ τ) : (k + 1 : ℝ) ≤ 2 * ((2 : ℝ) ^ k) ^ τ := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hsq : ((k + 1 : ℝ)) ^ 2 ≤ 4 * (2 : ℝ) ^ k := by exact_mod_cast sq_le_pow k
  have hhalf : (k + 1 : ℝ) ≤ 2 * ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 2) := by
    have hs : ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 2) = Real.sqrt ((2 : ℝ) ^ k) := (Real.sqrt_eq_rpow _).symm
    rw [hs]
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    exact this
  calc (k + 1 : ℝ) ≤ 2 * ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 2) := hhalf
    _ ≤ 2 * ((2 : ℝ) ^ k) ^ τ := by gcongr

/-- A bit length is at most `2 x^τ` for `τ ≥ 1/2`. -/
theorem size_le {x : ℕ} (hx : 1 ≤ x) {τ : ℝ} (hτ : 1 / 2 ≤ τ) :
    (Nat.size x : ℝ) ≤ 2 * (x : ℝ) ^ τ := by
  have hs : 0 < Nat.size x := Nat.size_pos.mpr hx
  have hlow : 2 ^ (Nat.size x - 1) ≤ x := Nat.lt_size.mp (by omega)
  have h := succ_le (Nat.size x - 1) hτ
  have hcast : ((Nat.size x - 1 : ℕ) : ℝ) + 1 = Nat.size x := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at h
  refine h.trans ?_
  gcongr
  exact_mod_cast hlow


/-! ### The wrapped bound -/

/-- **Width selection.** At `w = atomWidth K e`, `n = e / w` and `L = w^τ₁ + size w`, the
family's hypotheses on `L` hold, and the family's bound `A n + B n^τs L` plus the leaf term
`D w^τ₁` and the linear terms `D size e + D (n + 1)` are at most `(A + 6B + 6D) e^τ₂`. -/
theorem wrapped_le {K : ℕ} (hK : 2 ≤ K) {τs τ₁ : ℝ} (hs : 0 ≤ τs) (hs1 : τs ≤ τ₁) (hτ₁ : τ₁ ≤ 1)
    (hhalf : 1 / 2 ≤ τ₁) (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ τs τ₁) (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ τs τ₁)
    {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) {e : ℕ} (he : 2 ≤ e) :
    1 ≤ (atomWidth K e : ℝ) ^ τ₁ + Nat.size (atomWidth K e) ∧
    (Nat.size (atomWidth K e) : ℝ) ≤ (atomWidth K e : ℝ) ^ τ₁ + Nat.size (atomWidth K e) ∧
    (atomWidth K e : ℝ) ^ τ₁ ≤ (atomWidth K e : ℝ) ^ τ₁ + Nat.size (atomWidth K e) ∧
    A * (e / atomWidth K e : ℕ) + B * ((e / atomWidth K e : ℕ) : ℝ) ^ τs *
        ((atomWidth K e : ℝ) ^ τ₁ + Nat.size (atomWidth K e)) + D * (atomWidth K e : ℝ) ^ τ₁ +
        D * Nat.size e + D * ((e / atomWidth K e : ℕ) + 1) ≤
      (A + 6 * B + 6 * D) * (e : ℝ) ^ tau2 (K : ℝ)⁻¹ τs τ₁ := by
  set w := atomWidth K e
  set n := e / w
  set τ₂ := tau2 (K : ℝ)⁻¹ τs τ₁
  have hK0 : 0 < K := by omega
  have hw1 : 1 ≤ w := atomWidth_pos K e
  have hE : (1 : ℝ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
  have hθ : (0 : ℝ) ≤ (K : ℝ)⁻¹ := by positivity
  have hθ1 : (K : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ K by omega))
  have hge := atomWidth_ge (e := e) hK0
  have hle := atomWidth_le (e := e) hK0 (by omega)
  have hnw : ((n : ℕ) : ℝ) * w ≤ e := by exact_mod_cast Nat.div_mul_le_self e w
  have hτ₁0 : 0 ≤ τ₁ := by linarith
  have hwτ : 1 ≤ (w : ℝ) ^ τ₁ := Real.one_le_rpow (by exact_mod_cast hw1) hτ₁0
  have hsw : (Nat.size w : ℝ) ≤ 2 * (w : ℝ) ^ τ₁ := size_le hw1 hhalf
  have hsw0 : (0 : ℝ) ≤ Nat.size w := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have hEτ : 1 ≤ (e : ℝ) ^ τ₂ := Real.one_le_rpow hE (by linarith)
  have hfam := family_le hs hs1 (by linarith) (by norm_num : (1 : ℝ) ≤ 2) hE hge hle
    (Nat.cast_nonneg n) hnw
  have hleaf := leaf_le hθ1 hs hτ₁0 hτ₁ (by norm_num : (1 : ℝ) ≤ 2) hE (Nat.cast_nonneg w) hle
  have hlin := linear_le hE hge hnw hlin
  have hse : (Nat.size e : ℝ) ≤ 2 * (e : ℝ) ^ τ₂ := size_le (by omega) h2
  have hnτ : 0 ≤ ((n : ℕ) : ℝ) ^ τs := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hL : ((n : ℕ) : ℝ) ^ τs * ((w : ℝ) ^ τ₁ + Nat.size w) ≤ 6 * (e : ℝ) ^ τ₂ := by
    have : ((n : ℕ) : ℝ) ^ τs * ((w : ℝ) ^ τ₁ + Nat.size w) ≤ ((n : ℕ) : ℝ) ^ τs * (3 * (w : ℝ) ^ τ₁) :=
      mul_le_mul_of_nonneg_left (by linarith) hnτ
    nlinarith
  have := mul_le_mul_of_nonneg_left hL hB
  have := mul_le_mul_of_nonneg_left hlin hA
  have := mul_le_mul_of_nonneg_left hleaf hD
  have := mul_le_mul_of_nonneg_left hse hD
  have := mul_le_mul_of_nonneg_left (show ((n : ℕ) : ℝ) + 1 ≤ 2 * (e : ℝ) ^ τ₂ by linarith) hD
  nlinarith

end IntegerMultBounds.MathlibTM2.M8.Stage2Width
