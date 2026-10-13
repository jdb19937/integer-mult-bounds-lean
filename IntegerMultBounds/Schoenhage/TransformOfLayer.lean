module

public import IntegerMultBounds.Schoenhage.TransformDriver
public import IntegerMultBounds.Schoenhage.TwistCost

/-! §6 task 7, the layer calls of the transform. Fixed transform parameters are compatible
with fixed layer parameters when they share the bands for `d`, `r` and `K` and the layer's
size and header constants absorb the transform's (`Compatible`). Then an admissible transform
instance satisfies the layout conditions (`layoutOK_of_admissible`), every chunk-group slot's
layer call is admissible (`layerAdmissible_chunk`), and a program meeting
`prop:simultaneous-layer` meets every chunk-group call of the transform drivers within one
bound (`layerCalls_of_meets`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct

/-- Fixed transform parameters compatible with fixed layer parameters: the same bands for `d`,
`r` and `K`, the layer's size, header and width constants above the transform's, the layer's
exponent `λ'` at most the transform's, the interchange exponent `τ`, and the positivity the
size comparison `w ≤ r` needs. -/
def Compatible (LP : LayerParams) (P : TransformParams) : Prop :=
  P.c = (LP.c : ℝ) ∧ P.ε = (LP.ε : ℝ) ∧ P.ad = LP.ad ∧ P.bd = LP.bd ∧ P.ar = LP.ar ∧ P.br = LP.br ∧
    P.Cl + 1 ≤ LP.CM ∧ (32 * (⌈P.Cl⌉₊ + P.Cw + 1 : ℕ) : ℝ) ≤ LP.Cdesc ∧ (P.Cw : ℝ) ≤ LP.Cw ∧
    (LP.lam' : ℝ) ≤ P.lam' ∧ P.τ = Parameters.tau ∧ P.ε < 1 ∧ 0 < P.ar ∧ 0 < P.bd

/-! ### The layout conditions -/

theorem mem_axisLengths {d ℓ : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) {t : ℕ} (ht : t ∈ ts) :
    t = 2 ^ (ℓ - 1) ∨ t = 2 ^ ℓ := h.2 t ht

/-- An admissible instance has the paper's layout conditions with `r = 2^ℓ`. -/
theorem layoutOK_of_admissible {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (h : Admissible P p d ℓ K w ts) : LayoutOK (2 ^ ℓ) ts ℓ K := by
  obtain ⟨-, -, -, -, -, hℓ, -, -, -, hK, -, hax, -, -⟩ := h
  refine ⟨fun t ht => ?_, fun i hi => ?_, hK, by omega⟩
  · rcases mem_axisLengths hax ht with rfl | rfl
    · exact ⟨ℓ - 1, rfl, by rw [← pow_succ']; exact pow_dvd_pow 2 (by omega)⟩
    · exact ⟨ℓ, rfl, by rw [← pow_succ']; exact pow_dvd_pow 2 (by omega)⟩
  · unfold axLen
    rw [List.getD_eq_getElem _ _ hi]
    rcases mem_axisLengths hax (List.getElem_mem hi) with e | e <;> rw [e, Nat.log_pow (by norm_num)]
    · left; rfl
    · right; rfl

/-! ### Sizes of a chunk-group call -/

theorem longs_length_le (ts : List ℕ) (ℓ : ℕ) : (longs ts ℓ).length ≤ ts.length := by
  unfold longs
  exact (List.length_filter_le _ _).trans (by simp)

/-- The address bits number at most `D ℓ`. -/
theorem addr_le {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) :
    Nat.log 2 ts.prod ≤ ts.length * ℓ := by
  rw [log_prod_layout hL]
  have hL1 := longs_length_le ts ℓ
  have hdm := Nat.div_add_mod (ℓ - 1) K
  have e : ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) = ts.length * (ℓ - 1) := by
    have h' := Nat.div_add_mod' (ℓ - 1) K
    calc ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) =
        ts.length * ((ℓ - 1) / K * K + (ℓ - 1) % K) := by ring
      _ = ts.length * (ℓ - 1) := by rw [h']
  have : ts.length * (ℓ - 1) + ts.length = ts.length * ℓ := by
    have hℓ1 := hL.2.2.2
    rw [← Nat.mul_succ]; congr 1; omega
  omega

/-- A chunk-group slot's group, with the layer's chunks, fits below the address bits. -/
theorem chunk_fits {r : ℕ} {ts : List ℕ} {ℓ K h : ℕ} (hL : LayoutOK r ts ℓ K) (hb : (ℓ - 1) % K ≤ h)
    (hh : h < ℓ - 1) :
    chunkOf ℓ K h * ts.length * K + K * ts.length ≤ Nat.log 2 ts.prod := by
  have hK := hL.2.2.1
  have hdm := Nat.div_add_mod (ℓ - 1) K
  have hc : chunkOf ℓ K h + 1 ≤ (ℓ - 1) / K := by
    unfold chunkOf
    have h1 : h - (ℓ - 1) % K < K * ((ℓ - 1) / K) := by omega
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < K)).mpr (by rw [Nat.mul_comm]; exact h1)
    omega
  rw [log_prod_layout hL]
  have : (chunkOf ℓ K h + 1) * ts.length * K ≤ (ℓ - 1) / K * ts.length * K :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
  have e : chunkOf ℓ K h * ts.length * K + K * ts.length = (chunkOf ℓ K h + 1) * ts.length * K := by ring
  have e2 : (ℓ - 1) / K * ts.length * K = ts.length * ((ℓ - 1) / K) * K := by ring
  omega

/-- The chunk-group call's array has exactly the transform's `2^n` records. -/
theorem chunk_records {r : ℕ} {ts : List ℕ} {ℓ K h : ℕ} (hL : LayoutOK r ts ℓ K) (hb : (ℓ - 1) % K ≤ h)
    (hh : h < ℓ - 1) :
    2 ^ (Nat.log 2 ts.prod - (chunkOf ℓ K h * ts.length * K + K * ts.length)) *
      2 ^ (chunkOf ℓ K h * ts.length * K) * 2 ^ (K * ts.length) = 2 ^ Nat.log 2 ts.prod := by
  have := chunk_fits hL hb hh
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-! ### Admissibility of a chunk-group call -/

theorem hdrGamma_le (v : ℕ) : (gamma v).length ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [gamma, msbBits]
  · rw [length_gamma hv]; have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := v)); omega

theorem hdrGamma_pow (e : ℕ) : (gamma (2 ^ e)).length = 2 * e + 1 := by
  rw [length_gamma Nat.one_le_two_pow, Nat.size_pow]; omega

theorem nat_le_ceil_mul {Cl : ℝ} {x p : ℕ} (h : (x : ℝ) ≤ Cl * p) : x ≤ ⌈Cl⌉₊ * p := by
  have hp : (0 : ℝ) ≤ p := by positivity
  have : (x : ℝ) ≤ (⌈Cl⌉₊ * p : ℕ) := by
    push_cast
    refine h.trans ?_
    by_cases hc : 0 ≤ Cl
    · exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) hp
    · push Not at hc
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌈Cl⌉₊]
  exact_mod_cast this

/-- The address bits and `d` are at most `⌈C_l⌉ p`. -/
theorem admissible_bits {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (h : Admissible P p d ℓ K w ts) :
    Nat.log 2 ts.prod ≤ ⌈P.Cl⌉₊ * p ∧ d ≤ ⌈P.Cl⌉₊ * p ∧ ts.length = d - 1 := by
  have hL := layoutOK_of_admissible h
  obtain ⟨-, -, -, -, hd, hℓ, -, hdl, -, -, -, hax, -, -⟩ := h
  have hdl' := nat_le_ceil_mul hdl
  have hn := addr_le hL
  have hlen := hax.1
  refine ⟨?_, ?_, hlen⟩
  · have : ts.length * ℓ ≤ d * ℓ := Nat.mul_le_mul_right _ (by omega)
    omega
  · have : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- The layer header of a chunk-group call is at most `32 (⌈C_l⌉ + C_w + 1) p` bits long. -/
theorem chunkHdr_length {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hp : 1 ≤ p) {h : ℕ} (hb : (ℓ - 1) % K ≤ h) (hh : h < ℓ - 1) :
    (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).length ≤
      32 * (⌈P.Cl⌉₊ + P.Cw + 1) * p := by
  have hL := layoutOK_of_admissible hadm
  obtain ⟨hn, hdC, hlen⟩ := admissible_bits hadm
  have hfit := chunk_fits hL hb hh
  obtain ⟨-, -, -, -, hd, hℓ, hℓp, -, -, hK, hKℓ, -, -, hw⟩ := hadm
  set C := ⌈P.Cl⌉₊
  unfold chunkHdr layerHeader
  simp only [List.length_append, hdrGamma_pow]
  have g1 := hdrGamma_le p
  have g2 := hdrGamma_le d
  have g3 := hdrGamma_le ts.length
  have g4 := hdrGamma_le K
  have g5 := hdrGamma_le (rhoOf ℓ K h + 1)
  have g6 := hdrGamma_le w
  have hρ : rhoOf ℓ K h + 1 ≤ K := Nat.mod_lt _ (by omega)
  set n := Nat.log 2 ts.prod
  set Cp := C * p
  set Wp := P.Cw * p
  have e : 32 * (C + P.Cw + 1) * p = 32 * Cp + 32 * Wp + 32 * p := by simp only [Cp, Wp]; ring
  rw [e]
  omega

/-- Every chunk-group slot's layer call of an admissible transform instance is admissible for
compatible layer parameters. -/
theorem layerAdmissible_chunk {LP : LayerParams} {P : TransformParams} (hc : Compatible LP P)
    {p d ℓ K w : ℕ} {ts : List ℕ} (hadm : Admissible P p d ℓ K w ts) (hp : 1 ≤ p) {h : ℕ}
    (hb : (ℓ - 1) % K ≤ h) (hh : h < ℓ - 1) :
    LayerAdmissible LP p d (2 ^ ℓ) ts.length
      (2 ^ (Nat.log 2 ts.prod - (chunkOf ℓ K h * ts.length * K + K * ts.length)))
      (2 ^ (chunkOf ℓ K h * ts.length * K)) K (rhoOf ℓ K h) w := by
  have hL := layoutOK_of_admissible hadm
  have hrec := chunk_records hL hb hh
  have hhdr := chunkHdr_length hadm hp hb hh
  have hn := addr_le hL
  obtain ⟨hc1, hε, had, hbd, har, hbr, hCM, hCd, hCw, -, -, -, -, -⟩ := hc
  obtain ⟨h1, h2, h3, h4, hd, hℓ, hℓp, hdl, hKf, hK, hKℓ, hax, hpw, hw⟩ := hadm
  have hlen := hax.1
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  refine ⟨?_, ?_, ?_, ?_, ?_, by omega, by omega, Nat.one_le_two_pow, Nat.one_le_two_pow,
    Nat.mod_lt _ (by omega), ?_, ?_, hpw, ?_⟩
  · rw [← had, ← hε]; exact h1
  · rw [← hbd, ← hε]; exact h2
  · rw [← har]; push_cast; exact h3
  · rw [← hbr]; push_cast; exact h4
  · rw [hKf, hc1]
  · rw [hrec]
    have hnd : (Nat.log 2 ts.prod : ℝ) ≤ P.Cl * p := by
      have : Nat.log 2 ts.prod ≤ d * ℓ :=
        hn.trans (Nat.mul_le_mul_right _ (by omega))
      exact (by exact_mod_cast this : (Nat.log 2 ts.prod : ℝ) ≤ ((d * ℓ : ℕ) : ℝ)).trans hdl
    have hexp : ((Nat.log 2 ts.prod + 1 : ℕ) : ℝ) ≤ LP.CM * p := by
      push_cast
      have : (P.Cl + 1) * p ≤ LP.CM * p := mul_le_mul_of_nonneg_right hCM (by positivity)
      nlinarith
    calc ((2 * 2 ^ Nat.log 2 ts.prod : ℕ) : ℝ) = (2 : ℝ) ^ ((Nat.log 2 ts.prod + 1 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; ring
      _ ≤ (2 : ℝ) ^ (LP.CM * p) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  · have h0 : (((chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).length : ℕ) : ℝ) ≤
        ((32 * (⌈P.Cl⌉₊ + P.Cw + 1) * p : ℕ) : ℝ) := by exact_mod_cast hhdr
    have h1 : ((32 * (⌈P.Cl⌉₊ + P.Cw + 1) * p : ℕ) : ℝ) = 32 * ((⌈P.Cl⌉₊ + P.Cw + 1 : ℕ) : ℝ) * p := by
      push_cast; ring
    rw [h1] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right hCd (by positivity))
  · have : (w : ℝ) ≤ (P.Cw : ℝ) * p := by exact_mod_cast hw
    exact this.trans (mul_le_mul_of_nonneg_right hCw (by positivity))

/-- The bound on one chunk-group layer call for a layer program with time constant `C`. -/
noncomputable def layerCL (LP : LayerParams) (C : ℝ) (p d ℓ w : ℕ) (ts : List ℕ) : ℕ :=
  ⌈C * layerCost LP d (2 ^ ℓ) (2 ^ Nat.log 2 ts.prod) w +
    4 * (LP.Cdesc * p + 2 * (2 * 2 ^ ℓ * w * 2 ^ Nat.log 2 ts.prod : ℕ)) + 40⌉₊

/-- `layerCalls_of_meets`: a program meeting `prop:simultaneous-layer` on every admissible call
beyond `p₀` meets every chunk-group call of an admissible transform instance within `layerCL`. -/
theorem layerCalls_of_meets {LP : LayerParams} {P : TransformParams} (hc : Compatible LP P)
    {tL q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) {C : ℝ} {p₀ : ℕ}
    (hM : ∀ p d r D Pa S K ρ w, p₀ ≤ p → LayerAdmissible LP p d r D Pa S K ρ w →
      MeetsLayer LP M C p d r D Pa S K ρ w)
    {p d ℓ K w : ℕ} {ts : List ℕ} (hp0 : p₀ ≤ p) (hp : 1 ≤ p) (hadm : Admissible P p d ℓ K w ts) :
    LayerCalls M ht (2 ^ ℓ) p d w ts ℓ K (layerCL LP C p d ℓ w ts) := by
  intro h hb hh zs hzl hzd
  have hL := layoutOK_of_admissible hadm
  have hrec := chunk_records hL hb hh
  have hadmL := layerAdmissible_chunk hc hadm hp hb hh
  have hhdr := hadmL.2.2.2.2.2.2.2.2.2.2.2.1
  have hmeets := hM _ _ _ _ _ _ _ _ _ hp0 hadmL
  have hpow := powAxes_prod_pow hL.1
  have hzl' : zs.length = 2 ^ (Nat.log 2 ts.prod - (chunkOf ℓ K h * ts.length * K + K * ts.length)) *
      2 ^ (chunkOf ℓ K h * ts.length * K) * 2 ^ (K * ts.length) := by rw [hrec, hzl]; exact hpow
  obtain ⟨k, hk, hH⟩ := layer_call ht hmeets zs hzl' hzd
  rw [hrec] at hk hH
  refine ⟨k, ?_, hH⟩
  have hzn : (zs.length : ℝ) = (2 ^ Nat.log 2 ts.prod : ℕ) := by rw [hzl, ← hpow]
  have hX : (k : ℝ) ≤ C * layerCost LP d (2 ^ ℓ) (2 ^ Nat.log 2 ts.prod) w +
      4 * (LP.Cdesc * p + 2 * (2 * 2 ^ ℓ * w * 2 ^ Nat.log 2 ts.prod : ℕ)) + 40 := by
    refine hk.trans ?_
    rw [hzn]
    push_cast
    unfold chunkHdr at hhdr
    nlinarith
  unfold layerCL
  exact (Nat.cast_le (α := ℝ)).mp (hX.trans (Nat.le_ceil _))

end IntegerMultBounds.Schoenhage
