module

public import IntegerMultBounds.MathlibTM2.DFT.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The transform in time `O(N (log N) ^ (1 - κ))`

* `M.tH m = max_{m' ≤ m} ⌈M.time m' / (m' + 1)⌉`: monotone (`tH_mono`) and a majorant
  `M.time m ≤ (m + 1) M.tH m` (`time_le_tH`).
* `dftTimeOf H N = 100000 (N + 1) (H (16 N + 16) + 1)` bounds `dftBound H n w + 2` for
  `N = (n + 2) (w + 1)` (`dftBound_le`), so the main procedure computes the transform within
  `dftTimeOf M.tH` (`computesWithin`).
* `tH_le`: `M.tH m ≤ K + c (log m) ^ (1 - κ) + 1` from `M.time =O n (log n) ^ (1 - κ)`, and
  `dftTime_isBigO`: `dftTimeOf M.tH =O N (log N) ^ (1 - κ)` for `κ ≤ 1`.
* `dftInTime`: a host multiplier with exponent `κ ≤ 1` gives `DFTInTime κ`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  Asymptotics Filter

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The time function of the transform, from a per-symbol majorant `H` of the multiplier. -/
def dftTimeOf (H : ℕ → ℕ) (N : ℕ) : ℕ := 100000 * (N + 1) * (H (16 * N + 16) + 1)

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ)

/-! ### The per-symbol majorant -/

/-- `max_{m' ≤ m} ⌈M.time m' / (m' + 1)⌉`. -/
def tH (m : ℕ) : ℕ := (Finset.range (m + 1)).sup fun m' => (M.time m' + m') / (m' + 1)

theorem tH_mono : Monotone M.tH := fun _ _ hab =>
  Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hab))

theorem time_le_tH (m : ℕ) : M.time m ≤ (m + 1) * M.tH m := by
  have h1 : (M.time m + m) / (m + 1) ≤ M.tH m :=
    Finset.le_sup (f := fun m' => (M.time m' + m') / (m' + 1)) (Finset.mem_range.2 (by omega))
  have h2 : M.time m ≤ (m + 1) * ((M.time m + m) / (m + 1)) := by
    have := Nat.div_add_mod (M.time m + m) (m + 1)
    have := Nat.mod_lt (M.time m + m) (show 0 < m + 1 by omega)
    omega
  exact h2.trans (Nat.mul_le_mul_left _ h1)

end HostMultiplier

/-! ### The step bound -/

theorem dftBound_le {H : ℕ → ℕ} (hH : Monotone H) (n w : ℕ) :
    HostMultiplier.dftBound H n w + 2 ≤ dftTimeOf H ((n + 2) * (w + 1)) := by
  have b1 : H (4 * (2 * w) + 4) ≤ H (16 * ((n + 2) * (w + 1)) + 16) := hH (by nlinarith)
  have b2 : H (3 * (2 * (2 * w)) + 3) ≤ H (16 * ((n + 2) * (w + 1)) + 16) := hH (by nlinarith)
  have b3 : H (4 * (2 * (2 * w)) + 3) ≤ H (16 * ((n + 2) * (w + 1)) + 16) := hH (by nlinarith)
  have b4 : H (3 * w * (3 * n + 1)) ≤ H (16 * ((n + 2) * (w + 1)) + 16) := hH (by nlinarith)
  simp only [HostMultiplier.dftBound, HostMultiplier.pipeBound, HostMultiplier.chirpCost,
    HostMultiplier.inputCost, HostMultiplier.unpackCost, dftTimeOf]
  generalize H (16 * ((n + 2) * (w + 1)) + 16) = h at b1 b2 b3 b4 ⊢
  generalize H (4 * (2 * w) + 4) = x1 at b1 ⊢
  generalize H (3 * (2 * (2 * w)) + 3) = x2 at b2 ⊢
  generalize H (4 * (2 * (2 * w)) + 3) = x3 at b3 ⊢
  generalize H (3 * w * (3 * n + 1)) = x4 at b4 ⊢
  have p1 := Nat.mul_le_mul_right w b1
  have p2 := Nat.mul_le_mul_right (n * w) b2
  have p2' := Nat.mul_le_mul_right n b2
  have p3 := Nat.mul_le_mul_right (n * w) b3
  have p3' := Nat.mul_le_mul_right n b3
  have p4 := Nat.mul_le_mul_right (n * w) b4
  have p4' := Nat.mul_le_mul_right w b4
  nlinarith [p1, p2, p2', p3, p3', p4, p4', b1, b2, b3, b4, Nat.zero_le (n * w * h),
    Nat.zero_le (n * h), Nat.zero_le (w * h), Nat.zero_le (n * w), Nat.zero_le h]

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ)

instance instFintypeU : Fintype M.U := M.fintypeU

instance instFintypeP : Fintype M.P := M.fintypeP

/-! ### Computing the transform -/

/-- The initial local state of the transform. -/
def dftσ₀ : HS (M.T + 50) M.Q M.A (M.U × Unit) :=
  { flag := false, sym := none, st := M.v₀.st, scan := fun _ => 0, nxt := none,
    user := (M.v₀.user, ()) }

theorem computesWithin :
    ComputesWithin (M.tab 50 Unit (M.dftMain Unit M.dftσ₀)) none M.dftσ₀ DFTInstance.encode
      encodeNatList DFTInstance.transform (dftTimeOf M.tH) := by
  intro x
  obtain ⟨m, hm, e⟩ := M.dftMain_exec Unit M.tH M.tH_mono M.time_le_tH M.dftσ₀ x
  refine ⟨m, ?_, e⟩
  have hlen : x.encode.length = (x.n + 2) * (Nat.size x.p + 1) := by
    rw [DFTInstance.encode, length_encodeFixedList]
    simp
  rw [hlen]
  exact (Nat.add_le_add_right hm 2).trans (dftBound_le M.tH_mono _ _)

/-! ### The time bound -/

theorem tH_le (hκ : κ ≤ 1) : ∃ K c : ℝ, 0 ≤ K ∧ 0 ≤ c ∧ ∀ m : ℕ, 1 ≤ m →
    (M.tH m : ℝ) ≤ K + c * Real.log m ^ (1 - κ) + 1 := by
  obtain ⟨c, hc, hb⟩ := M.isBigO.exists_pos
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hb.bound
  set K : ℕ := (Finset.range (max m₀ 1)).sup fun m' => (M.time m' + m') / (m' + 1) with hKdef
  refine ⟨K, c, by positivity, hc.le, fun m hm => ?_⟩
  obtain ⟨m', hm', heq⟩ := Finset.exists_mem_eq_sup (Finset.range (m + 1))
    (Finset.nonempty_range_iff.2 (by omega)) (fun m' => (M.time m' + m') / (m' + 1))
  rw [tH, heq]
  rw [Finset.mem_range] at hm'
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog0 : 0 ≤ Real.log m ^ (1 - κ) := Real.rpow_nonneg (Real.log_nonneg hm1) _
  have hK0 : (0 : ℝ) ≤ K := by positivity
  by_cases hsmall : m' < max m₀ 1
  · have h1 : (M.time m' + m') / (m' + 1) ≤ K :=
      Finset.le_sup (f := fun m' => (M.time m' + m') / (m' + 1)) (Finset.mem_range.2 hsmall)
    have h2 : (((M.time m' + m') / (m' + 1) : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
    nlinarith [mul_nonneg hc.le hlog0]
  · replace hsmall := not_lt.1 hsmall
    have hm'1 : 1 ≤ m' := le_trans (le_max_right _ _) hsmall
    have hm'0 : m₀ ≤ m' := le_trans (le_max_left _ _) hsmall
    have hm'1r : (1 : ℝ) ≤ m' := by exact_mod_cast hm'1
    have hl : 0 ≤ Real.log m' ^ (1 - κ) := Real.rpow_nonneg (Real.log_nonneg hm'1r) _
    have hb' := hm₀ m' hm'0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at hb'
    have hdiv : (((M.time m' + m') / (m' + 1) : ℕ) : ℝ) ≤ ((M.time m' : ℝ) + m') / (m' + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := M.time m' + m') (n := m' + 1)
      push_cast at this
      exact this
    have hpos : (0 : ℝ) < m' + 1 := by positivity
    have h1 : ((M.time m' : ℝ) + m') / (m' + 1) ≤ c * Real.log m' ^ (1 - κ) + 1 := by
      rw [div_le_iff₀ hpos]
      nlinarith [hb', mul_nonneg hc.le hl]
    have h2 : Real.log m' ^ (1 - κ) ≤ Real.log m ^ (1 - κ) :=
      Real.rpow_le_rpow (Real.log_nonneg hm'1r)
        (Real.log_le_log (by positivity) (by exact_mod_cast (show m' ≤ m by omega))) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

theorem dftTime_isBigO (hκ : κ ≤ 1) :
    (fun N => (dftTimeOf M.tH N : ℝ)) =O[atTop] fun N : ℕ => (N : ℝ) * Real.log N ^ (1 - κ) := by
  obtain ⟨K, c, hK, hc, hH⟩ := M.tH_le hκ
  refine IsBigO.of_bound (200000 * (K + 2 + c * 2 ^ (1 - κ))) ?_
  filter_upwards [eventually_ge_atTop (max 17 ⌈Real.exp 1⌉₊)] with N hN
  have hN1 : (17 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hNe : Real.exp 1 ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hlogN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hNe
  replace hN : 17 ≤ N := le_trans (le_max_left _ _) hN
  have hL1 : 1 ≤ Real.log N ^ (1 - κ) := Real.one_le_rpow hlogN (by linarith)
  have hHN := hH (16 * N + 16) (by omega)
  have h16 : (1 : ℝ) ≤ ((16 * N + 16 : ℕ) : ℝ) := by push_cast; linarith
  have hlog16 : Real.log ((16 * N + 16 : ℕ) : ℝ) ≤ 2 * Real.log N := by
    rw [two_mul, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) (by push_cast; nlinarith)
  have hpow : Real.log ((16 * N + 16 : ℕ) : ℝ) ^ (1 - κ) ≤
      2 ^ (1 - κ) * Real.log N ^ (1 - κ) := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (Real.log_nonneg h16) (by linarith) (by linarith)
  have h2pos : (0 : ℝ) ≤ 2 ^ (1 - κ) := by positivity
  have hL0 : (0 : ℝ) ≤ Real.log N ^ (1 - κ) := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  simp only [dftTimeOf]
  push_cast
  have hH' : (M.tH (16 * N + 16) : ℝ) + 1 ≤ (K + 2 + c * 2 ^ (1 - κ)) * Real.log N ^ (1 - κ) := by
    have e1 : c * Real.log ((16 * N + 16 : ℕ) : ℝ) ^ (1 - κ) ≤
        c * (2 ^ (1 - κ) * Real.log N ^ (1 - κ)) := mul_le_mul_of_nonneg_left hpow hc
    push_cast at hHN e1
    nlinarith [mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ K + 2 by linarith)]
  calc (100000 : ℝ) * (N + 1) * (M.tH (16 * N + 16) + 1)
      ≤ 100000 * (2 * N) * ((K + 2 + c * 2 ^ (1 - κ)) * Real.log N ^ (1 - κ)) := by
        gcongr
        · linarith
    _ = 200000 * (K + 2 + c * 2 ^ (1 - κ)) * (N * Real.log N ^ (1 - κ)) := by ring

include M in
/-- A host multiplier with exponent `κ ≤ 1` gives the transform in time
`O(N (log N) ^ (1 - κ))`. -/
theorem dftInTime (hκ : κ ≤ 1) : DFTInTime κ :=
  dftInTime_of_computes (M.tab 50 Unit (M.dftMain Unit M.dftσ₀)) none M.dftσ₀ (dftTimeOf M.tH)
    M.computesWithin (M.dftTime_isBigO hκ)

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
