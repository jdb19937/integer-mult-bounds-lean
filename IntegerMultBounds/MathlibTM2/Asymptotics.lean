module

public import IntegerMultBounds.Assembly
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Vector

/-!
# Time bounds for the simulated machine

A simulation of an `IntegerMultBounds.Machine.Program` on inputs of total length `N` takes a
linear number of steps plus a fixed multiple of the multitape time at some padded length
`n ≤ N + 1`. `bridgeTime` bounds this by the supremum of the multitape time over all such
lengths. Since `targetTime κ` is monotone, this supremum is `O(N (log N)^(1-κ))` whenever the
multitape time is eventually `O(targetTime κ)`.

`runsWithin_of_computesWithin` turns the eventual bound of `ComputesWithin` into a bound at
every length: below the threshold there are finitely many inputs of each length, and the
bound there is the largest of their halting times.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine IntegerMultBounds.Assembly Filter Asymptotics

/-- Worst-case bound used for the simulated machine: linear overhead plus the multitape time at
every padded length up to `N + 1`. -/
noncomputable def bridgeTime (C₁ C₂ : ℕ) (total : ℕ → ℝ) (N : ℕ) : ℕ :=
  C₁ * (N + 1) + C₂ * ((Finset.range (N + 2)).sup fun n => ⌈total n⌉₊)

/-- Each `total n` with `n ≤ N + 1` is below the supremum term of `bridgeTime`. -/
lemma le_bridgeTime_sup (_C₁ _C₂ : ℕ) (total : ℕ → ℝ) {n N : ℕ} (hn : n ≤ N + 1) :
    ⌈total n⌉₊ ≤ (Finset.range (N + 2)).sup fun n => ⌈total n⌉₊ :=
  Finset.le_sup (f := fun n => ⌈total n⌉₊) (Finset.mem_range.2 (by omega))

/-- `bridgeTime` is monotone in `N`. -/
lemma bridgeTime_mono (C₁ C₂ : ℕ) (total : ℕ → ℝ) : Monotone (bridgeTime C₁ C₂ total) := by
  intro N M h
  have hs : ((Finset.range (N + 2)).sup fun n => ⌈total n⌉₊) ≤
      (Finset.range (M + 2)).sup fun n => ⌈total n⌉₊ :=
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hs)

/-- From the eventual bound of `ComputesWithin` to a bound at every length. -/
theorem runsWithin_of_computesWithin {t q a : ℕ} {M : Program t q a} {κ : ℝ}
    (h : ComputesWithin M κ) :
    ∃ (total : ℕ → ℝ) (C : ℝ) (n₀ : ℕ), RunsWithin M total ∧
      ∀ n, n₀ ≤ n → total n ≤ C * targetTime κ n := by
  obtain ⟨C, n₀, -, hM⟩ := h
  have hex : ∀ (n : ℕ) (x y : List Bool), ∃ k : ℕ,
      1 ≤ n → x.length = n → y.length = n → ∃ c : Config t q a,
        run M k (input M x y) = some c ∧ step M c = none ∧
        outputCorrect M n x y c ∧ (n₀ ≤ n → (k : ℝ) ≤ C * targetTime κ n) := by
    intro n x y
    by_cases hc : 1 ≤ n ∧ x.length = n ∧ y.length = n
    · obtain ⟨k, c, hc'⟩ := hM n hc.1 x y hc.2.1 hc.2.2
      exact ⟨k, fun _ _ _ => ⟨c, hc'⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
  choose K hK using hex
  -- The largest chosen halting time over the inputs of length `n`.
  let small : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Bool n × List.Vector Bool n)).sup
      fun p => K n p.1.toList p.2.toList
  refine ⟨fun n => if n₀ ≤ n then C * targetTime κ n else (small n : ℝ), C, n₀, ?_, ?_⟩
  · intro n hn x y hx hy
    obtain ⟨c, hrun, hstep, hout, hk⟩ := hK n x y hn hx hy
    refine ⟨K n x y, c, hrun, hstep, hout, ?_⟩
    beta_reduce
    split_ifs with h₀
    · exact hk h₀
    · have : K n x y ≤ small n :=
        Finset.le_sup (f := fun p : List.Vector Bool n × List.Vector Bool n =>
          K n p.1.toList p.2.toList) (b := (⟨x, hx⟩, ⟨y, hy⟩)) (Finset.mem_univ _)
      exact_mod_cast this
  · intro n hn
    simp only [hn, ↓reduceIte, le_refl]

/-- `targetTime κ` is monotone for `κ ≤ 1`. -/
lemma targetTime_mono {κ : ℝ} (hκ1 : κ ≤ 1) : Monotone (targetTime κ) := by
  intro m n h
  unfold targetTime
  have hlg : (lg m : ℝ) ≤ lg n := by
    have : lg m ≤ lg n := max_le_max (Nat.clog_mono_right 2 h) le_rfl
    exact_mod_cast this
  have hm : (m : ℝ) ≤ n := by exact_mod_cast h
  exact mul_le_mul hm (Real.rpow_le_rpow (by positivity) hlg (by linarith)) (by positivity)
    (by positivity)

/-- The target time at `N + 1` is `O(N (log N)^(1-κ))`, with an explicit constant. -/
lemma targetTime_succ_le {κ : ℝ} (hκ1 : κ ≤ 1) {N : ℕ} (hN : 3 ≤ N) :
    targetTime κ (N + 1) ≤
      2 * (4 / Real.log 2) ^ (1 - κ) * ((N : ℝ) * Real.log N ^ (1 - κ)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlg := IntegerMultBounds.TimeBound.lg_le_log (N + 1) (by omega)
  have hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have hsq : Real.log ((N : ℝ) ^ 2) = 2 * Real.log N := by
      rw [Real.log_pow]; norm_num
    rw [← hsq]
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith
  have hlg' : (lg (N + 1) : ℝ) ≤ 4 / Real.log 2 * Real.log N := by
    calc (lg (N + 1) : ℝ) ≤ 2 * (Real.log ((N + 1 : ℕ) : ℝ) / Real.log 2) := hlg
      _ ≤ 2 * (2 * Real.log N / Real.log 2) := by gcongr
      _ = 4 / Real.log 2 * Real.log N := by ring
  have hpow : (lg (N + 1) : ℝ) ^ (1 - κ) ≤
      (4 / Real.log 2) ^ (1 - κ) * Real.log N ^ (1 - κ) := by
    rw [← Real.mul_rpow (by positivity) hlogN]
    exact Real.rpow_le_rpow (by positivity) hlg' (by linarith)
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith
  unfold targetTime
  calc ((N + 1 : ℕ) : ℝ) * (lg (N + 1) : ℝ) ^ (1 - κ)
      ≤ (2 * N) * ((4 / Real.log 2) ^ (1 - κ) * Real.log N ^ (1 - κ)) :=
        mul_le_mul hN1 hpow (by positivity) (by positivity)
    _ = _ := by ring

/-- `1 ≤ log N` for `N ≥ 3`. -/
lemma one_le_log_of_three_le {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have he := Real.exp_one_lt_d9
  norm_num at he
  have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ N)
  rwa [Real.log_exp] at this

/-- The bridge time is `O(N (log N)^(1-κ))` when the multitape time is eventually
`O(targetTime κ)`, for `0 < κ ≤ 1`. -/
theorem isBigO_bridgeTime (C₁ C₂ : ℕ) (total : ℕ → ℝ) {κ : ℝ} (_hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {C : ℝ} {n₀ : ℕ} (hC : ∀ n, n₀ ≤ n → total n ≤ C * targetTime κ n) :
    (fun N : ℕ => (bridgeTime C₁ C₂ total N : ℝ)) =O[atTop]
      fun N : ℕ => (N : ℝ) * Real.log N ^ (1 - κ) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = (Finset.range n₀).sup fun n => ⌈total n⌉₊ := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 0 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * (4 / Real.log 2) ^ (1 - κ) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := hC' ▸ le_max_right _ _
  have hsup : ∀ N, ((Finset.range (N + 2)).sup fun n => ⌈total n⌉₊) ≤
      B + ⌈C' * targetTime κ (N + 1)⌉₊ := by
    intro N
    apply Finset.sup_le
    intro n hn
    rw [Finset.mem_range] at hn
    by_cases h₀ : n < n₀
    · exact hB ▸ (Finset.le_sup (f := fun n => ⌈total n⌉₊) (Finset.mem_range.2 h₀)).trans
        (Nat.le_add_right _ _)
    · refine le_trans ?_ (Nat.le_add_left _ _)
      apply Nat.ceil_mono
      calc total n ≤ C * targetTime κ n := hC n (by omega)
        _ ≤ C' * targetTime κ n :=
          mul_le_mul_of_nonneg_right (hC' ▸ le_max_left _ _)
            (IntegerMultBounds.TimeBound.targetTime_nonneg κ n)
        _ ≤ C' * targetTime κ (N + 1) :=
          mul_le_mul_of_nonneg_left (targetTime_mono hκ1 (by omega)) hC'0
  refine IsBigO.of_bound (2 * C₁ + C₂ * (B + 1) + C₂ * C' * K) ?_
  rw [eventually_atTop]
  refine ⟨3, fun N hN => ?_⟩
  have hlogN1 := one_le_log_of_three_le hN
  have hpow1 : 1 ≤ Real.log N ^ (1 - κ) := Real.one_le_rpow hlogN1 (by linarith)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (N : ℝ) * Real.log N ^ (1 - κ) := ⟨_, rfl⟩
  have hNg : (N : ℝ) ≤ g := by
    rw [hg]
    nlinarith
  have h1g : 1 ≤ g := by linarith
  have hT : targetTime κ (N + 1) ≤ K * g := hK ▸ hg ▸ targetTime_succ_le hκ1 hN
  have hT0 := IntegerMultBounds.TimeBound.targetTime_nonneg κ (N + 1)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), ← hg, Real.norm_of_nonneg (by linarith)]
  have hb : bridgeTime C₁ C₂ total N ≤ C₁ * (N + 1) + C₂ * (B + ⌈C' * targetTime κ (N + 1)⌉₊) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (hsup N)) _
  have hb' : (bridgeTime C₁ C₂ total N : ℝ) ≤
      C₁ * ((N : ℝ) + 1) + C₂ * ((B : ℝ) + ⌈C' * targetTime κ (N + 1)⌉₊) := by
    exact_mod_cast hb
  have e1 : (C₁ : ℝ) * ((N : ℝ) + 1) ≤ C₁ * (2 * g) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have e2 : ((B : ℝ) + ⌈C' * targetTime κ (N + 1)⌉₊) ≤ (B + 1) * g + C' * K * g := by
    have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ C' * targetTime κ (N + 1))).le
    have hCT : C' * targetTime κ (N + 1) ≤ C' * (K * g) := mul_le_mul_of_nonneg_left hT hC'0
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    nlinarith
  calc (bridgeTime C₁ C₂ total N : ℝ)
      ≤ C₁ * ((N : ℝ) + 1) + C₂ * ((B : ℝ) + ⌈C' * targetTime κ (N + 1)⌉₊) := hb'
    _ ≤ C₁ * (2 * g) + C₂ * ((B + 1) * g + C' * K * g) :=
        add_le_add e1 (mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg _))
    _ = (2 * C₁ + C₂ * (B + 1) + C₂ * C' * K) * g := by ring

/-- The supremum term of `bridgeTime` for the quadratic cost `40 (n² + n + 1)`. -/
lemma sup_sq_le (N : ℕ) :
    ((Finset.range (N + 2)).sup fun n => ⌈(((40 * (n ^ 2 + n + 1) : ℕ) : ℝ))⌉₊) ≤
      40 * ((N + 1) ^ 2 + (N + 1) + 1) := by
  apply Finset.sup_le
  intro n hn
  rw [Finset.mem_range] at hn
  rw [Nat.ceil_natCast]
  have h1 : n ≤ N + 1 := by omega
  have h2 : n ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left h1 2
  omega

/-- Quadratic version, for the vendored elementary multiplier whose cost is `40 (n² + n + 1)`. -/
theorem isBigO_bridgeTime_sq (C₁ C₂ : ℕ) :
    (fun N : ℕ => (bridgeTime C₁ C₂ (fun n => ((40 * (n ^ 2 + n + 1) : ℕ) : ℝ)) N : ℝ))
      =O[atTop] fun N : ℕ => (N : ℝ) ^ 2 := by
  refine IsBigO.of_bound ((2 * C₁ + 280 * C₂ : ℕ) : ℝ) ?_
  rw [eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have hb : bridgeTime C₁ C₂ (fun n => ((40 * (n ^ 2 + n + 1) : ℕ) : ℝ)) N ≤
      (2 * C₁ + 280 * C₂) * N ^ 2 := by
    have hs := sup_sq_le N
    have h1 : C₁ * (N + 1) ≤ C₁ * (2 * N ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    have h3 : 40 * ((N + 1) ^ 2 + (N + 1) + 1) ≤ 280 * N ^ 2 := by nlinarith
    have h2 := Nat.mul_le_mul_left C₂ (hs.trans h3)
    unfold bridgeTime
    calc C₁ * (N + 1) + C₂ * ((Finset.range (N + 2)).sup fun n =>
          ⌈(((40 * (n ^ 2 + n + 1) : ℕ) : ℝ))⌉₊)
        ≤ C₁ * (2 * N ^ 2) + C₂ * (280 * N ^ 2) := Nat.add_le_add h1 h2
      _ = (2 * C₁ + 280 * C₂) * N ^ 2 := by ring
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast hb

end IntegerMultBounds.MathlibTM2
