module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIndex
public import IntegerMultBounds.MathlibTM2.Layer.CompactCount
public import IntegerMultBounds.Compact.RepairBounds
public import Mathlib.Data.Nat.Log

/-!
# Exceptional indices in the actual selective routing layout

Only target and borrowed fields enter the guard predicate. Its count therefore
allows every spectator value, with no source initialization or source-order
assumption. The original window-count proof needs no width assumption on x.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ)

def selectiveFields : Fields 5 := ⟨0, 2, 3, 1, 4⟩

theorem selectiveGoodIdx (i : ℕ) :
    GoodIdx p (selectiveLen p X) selectiveFields i ↔ Good p (selectiveView p X i) := Iff.rfl

open Classical in
/-- The count applies to the same physical predicate as the executed endpoint. -/
theorem selectiveBad_card_le (R : ℕ) (hGK : p.G + 1 < p.K) :
    ((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card ≤
      p.n * (2 * (R * 2 ^ (fieldsLen (selectiveLen p X) - p.G)) +
        R * 2 ^ (fieldsLen (selectiveLen p X) - (p.K - 1 - p.G))) := by
  exact card_bad_le_of_lengths (p := p) (F := selectiveFields)
    (len := selectiveLen p X) rfl rfl rfl hGK
    (fun f _ => fieldOff_add_le_total (selectiveLen p X) f)

open Classical in
/-- Fractional form of the physical count, including arbitrary complete spectators. -/
theorem selectiveBad_fraction_le (R : ℕ) (hGK : p.G + 1 < p.K) :
    (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card : ℝ) ≤
      (2 * (p.n : ℝ) / (2 : ℝ) ^ p.G +
        (p.n : ℝ) / (2 : ℝ) ^ (p.K - 1 - p.G)) *
        (R * 2 ^ fieldsLen (selectiveLen p X) : ℕ) := by
  have hc := selectiveBad_card_le p X R hGK
  by_cases hn : p.n = 0
  · have hz : ((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
        fun i => ¬ Good p (selectiveView p X i)).card = 0 := by simpa [hn] using hc
    simp [hn, hz]
  have hn' : 1 ≤ p.n := by omega
  have hg : p.G ≤ fieldsLen (selectiveLen p X) := by
    have h := fieldOff_add_le_total (selectiveLen p X) 0
    have hmul := Nat.mul_le_mul_right p.G hn'
    change 1 * p.G ≤ p.n * p.G at hmul
    change fieldOff (selectiveLen p X) 0 + p.n * p.G ≤ _ at h
    omega
  have hk : p.K - 1 - p.G ≤ fieldsLen (selectiveLen p X) := by
    have h := fieldOff_add_le_total (selectiveLen p X) 1
    have hmul := Nat.mul_le_mul_right p.K hn'
    change fieldOff (selectiveLen p X) 1 + (p.ρ + p.n * p.K + p.m) ≤ _ at h
    omega
  have hpow (w : ℕ) (hw : w ≤ fieldsLen (selectiveLen p X)) :
      (R : ℝ) * 2 ^ (fieldsLen (selectiveLen p X) - w) =
        (R : ℝ) * 2 ^ fieldsLen (selectiveLen p X) / (2 : ℝ) ^ w := by
    apply (eq_div_iff (by positivity)).2
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hw]
  have hc' : (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card : ℝ) ≤
      (p.n : ℝ) * (2 * ((R : ℝ) * 2 ^ (fieldsLen (selectiveLen p X) - p.G)) +
        (R : ℝ) * 2 ^ (fieldsLen (selectiveLen p X) - (p.K - 1 - p.G))) := by
    exact_mod_cast hc
  rw [hpow p.G hg, hpow (p.K - 1 - p.G) hk] at hc'
  push_cast
  convert hc' using 1; ring

open Classical in
/-- The repair density follows from two explicit dyadic radix bounds. -/
theorem selectiveBad_repair_density (R : ℕ) (hGK : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)) :
    (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card : ℝ) ≤
      5 / (128 * scale ^ 3) * (R * 2 ^ fieldsLen (selectiveLen p X) : ℕ) := by
  have hd := IntegerMultBounds.Compact.repair_density_bound scale p.n
    ((2 : ℝ) ^ p.G) ((2 : ℝ) ^ (p.K - 1 - p.G)) hscale (by positivity) hn hradix hgap
  have hsmall : (p.n : ℝ) / (2 : ℝ) ^ (p.K - 1 - p.G) ≤
      8 * p.n / (2 : ℝ) ^ (p.K - 1 - p.G) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) p.n]
  exact (selectiveBad_fraction_le p X R hGK).trans
    (mul_le_mul_of_nonneg_right (le_trans (by linarith) hd) (by positivity))

/-- A logarithmic guard choice with ample room for both exceptional windows. -/
def routingParameters (ρ n m g : ℕ) : Par := ⟨8 * g + 17, ρ, n, 4 * g + 6, m⟩

theorem routingParameters_guards (ρ n m g : ℕ) :
    0 < (routingParameters ρ n m g).G ∧
      0 < (routingParameters ρ n m g).K ∧
      (routingParameters ρ n m g).G + 1 < (routingParameters ρ n m g).K := by
  simp only [routingParameters]
  omega

theorem routingParameters_radices (ρ n m g : ℕ) (scale : ℝ)
    (hscale : 0 ≤ scale) (hs : scale ≤ (2 : ℝ) ^ g) :
    64 * scale ^ 4 ≤ (2 : ℝ) ^ (routingParameters ρ n m g).G ∧
      1024 * scale ^ 4 ≤ (2 : ℝ) ^ ((routingParameters ρ n m g).K - 1 -
        (routingParameters ρ n m g).G) := by
  have hp : scale ^ 4 ≤ ((2 : ℝ) ^ g) ^ 4 := by gcongr
  have he : 8 * g + 17 - 1 - (4 * g + 6) = 4 * g + 10 := by omega
  simp only [routingParameters, he]
  constructor
  · calc
      64 * scale ^ 4 ≤ 64 * ((2 : ℝ) ^ g) ^ 4 := by gcongr
      _ = (2 : ℝ) ^ (4 * g + 6) := by rw [pow_add, Nat.mul_comm 4 g, pow_mul]; norm_num; ring
  · calc
      1024 * scale ^ 4 ≤ 1024 * ((2 : ℝ) ^ g) ^ 4 := by gcongr
      _ = (2 : ℝ) ^ (4 * g + 10) := by rw [pow_add, Nat.mul_comm 4 g, pow_mul]; norm_num; ring

open Classical in
/-- Concrete guard widths, rather than an assumed radix/density inequality. -/
theorem routingParameters_density (ρ n m g X R : ℕ) (scale : ℝ)
    (hscale : 0 < scale) (hn : (n : ℝ) ≤ scale) (hs : scale ≤ (2 : ℝ) ^ g) :
    let p := routingParameters ρ n m g
    (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card : ℝ) ≤
      5 / (128 * scale ^ 3) * (R * 2 ^ fieldsLen (selectiveLen p X) : ℕ) := by
  have hr := routingParameters_radices ρ n m g scale hscale.le hs
  exact selectiveBad_repair_density _ X R (routingParameters_guards ρ n m g).2.2
    scale hscale hn hr.1 hr.2

open Classical in
/-- The ceiling binary logarithm gives a uniform finite guard choice. -/
theorem routingParameters_clog_density (ρ n m X R scale : ℕ)
    (hscale : 0 < scale) (hn : n ≤ scale) :
    let p := routingParameters ρ n m (Nat.clog 2 scale)
    (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card : ℝ) ≤
      5 / (128 * (scale : ℝ) ^ 3) * (R * 2 ^ fieldsLen (selectiveLen p X) : ℕ) := by
  apply routingParameters_density ρ n m (Nat.clog 2 scale) X R scale
  · exact_mod_cast hscale
  · exact_mod_cast hn
  · exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) scale

end IntegerMultBounds.MathlibTM2.Routing
