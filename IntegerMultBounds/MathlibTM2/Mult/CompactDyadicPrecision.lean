module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! Natural arithmetic room bounds for a candidate dyadic dimension.
These lemmas do not change the executable size generator or assert a machine-time bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactDyadicPrecision
open IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- The usual size-volume comparison leaves a sixth power of dimension in the axis width. -/
theorem sixth_le_two_axis {d b ℓ : ℕ} (hd : 1≤d) (hpow : d^7≤b)
    (haxis : b≤2*d*ℓ) : d^6≤2*ℓ := by
  have h : d*d^6≤d*(2*ℓ) := by
    calc
      d*d^6=d^7 := by ring
      _ ≤ b := hpow
      _ ≤ 2*d*ℓ := haxis
      _ = d*(2*ℓ) := by ring
  exact Nat.le_of_mul_le_mul_left h hd

/-- Even at dimension two, the sixth-power axis room pays the complete modulus exponent. -/
theorem modulus_exponent_room {d b ℓ : ℕ} (hd : 2≤d) (hpow : d^7≤b)
    (haxis : b≤2*d*ℓ) : 4+2*d+4*d^2≤ℓ-1 := by
  have h6 := sixth_le_two_axis (by omega : 1≤d) hpow haxis
  have h4 : d^2*16≤d^6 := by
    have h16 : 16≤d^4 := by
      calc
        16=2^4 := by norm_num
        _ ≤ d^4 := Nat.pow_le_pow_left hd 4
    calc
      d^2*16≤d^2*d^4 := Nat.mul_le_mul_left _ h16
      _ = d^6 := by ring
  have hsmall : 10+4*d≤8*d^2 := by nlinarith
  omega

/-- An odd-product bound of the existing parameter algorithm fits the available modulus room. -/
theorem modulus_room {d b ℓ N : ℕ} (hd : 2≤d) (hpow : d^7≤b)
    (haxis : b≤2*d*ℓ) (hNpos : 1≤N) (hN : N≤(4*d)^(2*d)) :
    8*d^2*N+4*d≤2^(ℓ-1) := by
  have hN' : N≤2^(2*d*(2*d)) := by
    calc
      N≤(4*d)^(2*d) := hN
      _ ≤ (2^(2*d))^(2*d) := Nat.pow_le_pow_left (le_two_pow_two_mul hd) _
      _ = 2^(2*d*(2*d)) := by rw [←pow_mul]
  have hd2 : d^2≤2^(2*d) := by
    calc
      d^2≤(2^d)^2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = 2^(2*d) := by rw [←pow_mul,mul_comm]
  have hdN : d≤d^2*N := by
    calc
      d≤d^2 := Nat.le_self_pow (by decide) d
      _ ≤ d^2*N := Nat.le_mul_of_pos_right _ hNpos
  have hprod := Nat.mul_le_mul hd2 hN'
  calc
    8*d^2*N+4*d≤16*(d^2*N) := by nlinarith only [hdN]
    _ ≤ 16*(2^(2*d)*2^(2*d*(2*d))) := Nat.mul_le_mul_left _ hprod
    _ = 2^(4+2*d+4*d^2) := by rw [pow_add,pow_add]; norm_num; ring
    _ ≤ 2^(ℓ-1) := Nat.pow_le_pow_right (by decide) (modulus_exponent_room hd hpow haxis)

/-- The numerical guard coefficient already fits a seventh power for dimension at least sixty-four. -/
theorem guard_coefficient_le {d b : ℕ} (hd : 64≤d) (hpow : d^7≤b) :
    49152*d^4≤b := by
  have hc : 49152≤d^3 := by
    calc
      49152≤64^3 := by norm_num
      _ ≤ d^3 := Nat.pow_le_pow_left hd 3
  calc
    49152*d^4≤d^3*d^4 := Nat.mul_le_mul_right _ hc
    _ = d^7 := by ring
    _ ≤ b := hpow

/-- The existing fourth-power Gaussian width estimate still implies the exact recovery guard. -/
theorem four_gamma_le {d b α : ℕ} (hd : 64≤d) (hpow : d^7≤b)
    (hα : α^4≤192*d^2*b) : 4*(d*(2*α^2+2))≤b := by
  have hc := guard_coefficient_le hd hpow
  have hs : (16*d*α^2)^2≤b^2 := by
    calc
      (16*d*α^2)^2=256*d^2*α^4 := by ring
      _ ≤ 256*d^2*(192*d^2*b) := Nat.mul_le_mul_left _ hα
      _ = 49152*d^4*b := by ring
      _ ≤ b*b := Nat.mul_le_mul_right _ hc
      _ = b^2 := by ring
  have ha : 16*d*α^2≤b := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hs
  have hd4 : d^4≤b := (Nat.pow_le_pow_right (by omega : 0<d) (by decide : 4≤7)).trans hpow
  have hdsmall : 16*d≤b := by
    calc
      16*d≤d*d := Nat.mul_le_mul_right _ (by omega : 16≤d)
      _ = d^2 := by ring
      _ ≤ d^4 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ b := hd4
  nlinarith only [ha,hdsmall]

end IntegerMultBounds.MathlibTM2.Mult.CompactDyadicPrecision
