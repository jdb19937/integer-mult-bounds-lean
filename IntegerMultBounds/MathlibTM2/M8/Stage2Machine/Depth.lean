module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The depth of the reversed family

Every child of a frame of `n ≥ m` atoms has at most `(m - 1) n / m` atoms, so its logarithm is at
least `1 / m` smaller, and the depth of the recursion below `n` atoms is at most `2 m log n + 1`
(`depthF_le`). For the stage-2 family, with `n` at most a width `e`, the depth is at most a
constant times `clog b e` for any base `b ≥ 2` (`depth_le_clog`): the rows of a view whose count
`roleCount^(c clog b e)` divides split over the family's depth.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Depth

open RevMachine

theorem depthF_zero (m : ℕ) (hm : 0 < m) (Rk : List ℕ) : ∀ k, RevNode.depthF m Rk k 0 = 0
  | 0 => rfl
  | k+1 => by simp only [RevNode.depthF]; rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

theorem foldr_max_le_real {l : List ℕ} {B : ℝ} (h : ∀ a ∈ l, (a : ℝ) ≤ B) (hB : 0 ≤ B) :
    ((l.foldr max 0 : ℕ) : ℝ) ≤ B := by
  induction l with
  | nil => simpa using hB
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.cast_max]
    exact max_le (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **The depth with fuel** is at most `2 m log n + 1`. -/
theorem depthF_le {m : ℕ} (hm : 2 ≤ m) {Rk : List ℕ} (hRk : ∀ r ∈ Rk, r < m) :
    ∀ k n, 1 ≤ n → (RevNode.depthF m Rk k n : ℝ) ≤ 2 * m * Real.log n + 1
  | 0, n, hn => by
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    simp only [RevNode.depthF, Nat.cast_zero]
    positivity
  | k+1, n, hn => by
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    simp only [RevNode.depthF]
    split_ifs with hmn
    · push_cast
      have hmax : (((Rk.map fun r => RevNode.depthF m Rk k (r * (n / m))).foldr max 0 : ℕ) : ℝ) ≤
          2 * m * Real.log n := by
        refine foldr_max_le_real ?_ (by positivity)
        intro a ha
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
        have hcle : r * (n / m) ≤ (m - 1) * (n / m) := Nat.mul_le_mul_right _ (by have := hRk r hr; omega)
        set c := r * (n / m)
        clear_value c
        rcases Nat.eq_zero_or_pos c with hc | hc
        · rw [hc, depthF_zero m (by omega)]
          simp only [Nat.cast_zero]
          positivity
        · have ih := depthF_le hm hRk k c hc
          have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
          have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          have hcR : (0 : ℝ) < c := by exact_mod_cast hc
          -- `c ≤ (m - 1) n / m`
          have hcn : (c : ℝ) * m ≤ (m - 1) * n := by
            have h1 : c ≤ (m - 1) * (n / m) := hcle
            have h2 : m * (n / m) ≤ n := Nat.mul_div_le n m
            have h3 : (m - 1) * (n / m) * m ≤ (m - 1) * n := by
              rw [Nat.mul_assoc, Nat.mul_comm (n / m) m]; exact Nat.mul_le_mul_left _ h2
            have h4 : c * m ≤ (m - 1) * n := (Nat.mul_le_mul_right m h1).trans h3
            have h5 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega)]; simp
            have h6 : ((c * m : ℕ) : ℝ) ≤ (((m - 1) * n : ℕ) : ℝ) := by exact_mod_cast h4
            rw [Nat.cast_mul, Nat.cast_mul, h5] at h6
            exact h6
          -- `log c ≤ log n - 1 / m`
          have hq : Real.log (c / n) ≤ c / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
          have hdiv : (c : ℝ) / n - 1 ≤ -1 / m := by
            rw [div_sub_one hnR.ne', div_le_div_iff₀ hnR hmR]
            nlinarith
          have hlc : Real.log c ≤ Real.log n - 1 / m := by
            have := Real.log_div hcR.ne' hnR.ne'
            have h1 : Real.log c - Real.log n ≤ -1 / m := this ▸ hq.trans hdiv
            have h2 : -1 / (m : ℝ) = -(1 / m) := by ring
            linarith
          have : 2 * m * Real.log c + 1 ≤ 2 * m * Real.log n := by
            have h2 : 2 * (m : ℝ) * (1 / m) = 2 := by field_simp
            nlinarith
          linarith
      linarith
    · simp only [Nat.cast_zero]
      positivity

/-- The depth of the stage-2 family at a width `e` of base-`b` length `clog b e`. -/
theorem depth_le_clog {b : ℕ} (hb : 2 ≤ b) {e n : ℕ} (hn : n ≤ e) :
    RevNode.depth rev97m.width (RevHalf.Rk rev97m) n ≤ (1058 * b + 1) * Nat.clog b e := by
  have hRk : ∀ r ∈ RevHalf.Rk rev97m, r < rev97m.width := by
    have h : RevHalf.Rk rev97m = M8.ranks97 := Schedule.ranks_schedule97
    rw [h]; exact fun r hr => M8.ranks97_lt hr
  have hm : rev97m.width = 529 := rfl
  rcases Nat.lt_or_ge n 529 with hsmall | hbig
  · have : RevNode.depth rev97m.width (RevHalf.Rk rev97m) n = 0 := by
      unfold RevNode.depth
      cases n with
      | zero => rfl
      | succ n => simp only [RevNode.depthF]; rw [ite_eq_right_iff.mpr (fun h => absurd h (by rw [hm]; omega))]
    rw [this]; exact Nat.zero_le _
  · have he : 2 ≤ e := by omega
    have hk : 1 ≤ Nat.clog b e := Nat.one_le_iff_ne_zero.mpr (by
      intro h; have := Nat.le_pow_clog (by omega : 1 < b) e; rw [h, pow_zero] at this; omega)
    have h := depthF_le (m := rev97m.width) (by rw [hm]; norm_num) hRk n n (by omega)
    rw [hm] at h
    -- `log n ≤ log e ≤ clog b e · log b ≤ clog b e · b`
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hle : Real.log n ≤ Nat.clog b e * b := by
      have h1 : Real.log n ≤ Real.log e := Real.log_le_log (by linarith) (by exact_mod_cast hn)
      have h2 : (e : ℝ) ≤ (b : ℝ) ^ Nat.clog b e := by exact_mod_cast Nat.le_pow_clog (by omega) e
      have h3 : Real.log e ≤ Nat.clog b e * Real.log b := by
        rw [← Real.log_pow]; exact Real.log_le_log (by exact_mod_cast (show 0 < e by omega)) h2
      have h4 : Real.log b ≤ b := (Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < b by omega))).trans
        (by linarith)
      have hk0 : (0 : ℝ) ≤ Nat.clog b e := Nat.cast_nonneg _
      nlinarith
    have hkR : (1 : ℝ) ≤ Nat.clog b e := by exact_mod_cast hk
    have : (RevNode.depth rev97m.width (RevHalf.Rk rev97m) n : ℝ) ≤ ((1058 * b + 1) * Nat.clog b e : ℕ) := by
      unfold RevNode.depth
      rw [hm]
      push_cast
      norm_num at h
      have h7 := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 1058)
      nlinarith
    exact_mod_cast this

end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Depth
