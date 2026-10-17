module

import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigDivisor
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.Machine.CompactGlobalRowPadding
public import IntegerMultBounds.MathlibTM2.Layer.LayerZ
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-! A fixed polynomial bounds the actual original-depth row divisor. All
constants are named expressions; finite wire cardinalities are not normalized. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer Filter
noncomputable section

/-- Fixed polynomial exponent determined only by the finite wire system. -/
def compactCallerDivisorExponent : ℕ := Nat.clog m NW

/-- Fixed dyadic coefficient exponent. -/
def compactCallerDivisorCoeffExponent : ℕ :=
  Nat.clog 2 (m+1)*compactCallerDivisorExponent

private lemma divisorPolynomial {W base J p e c cb : ℕ}
    (hW : W≤base^e) (hc : base+1≤2^cb) (he : cb*e=c)
    (hdepth : base^J≤(base+1)*(p+1)) :
    W^J≤2^c*(p+1)^e := by
  calc
    W^J ≤ (base^e)^J := Nat.pow_le_pow_left hW J
    _ = (base^J)^e := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ ≤ ((base+1)*(p+1))^e := Nat.pow_le_pow_left hdepth _
    _ = (base+1)^e*(p+1)^e := mul_pow _ _ _
    _ ≤ (2^cb)^e*(p+1)^e := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc _)
    _ = _ := by rw [←pow_mul,he]

/-- The row divisor is polynomial in any upper bound for original depth. -/
theorem compactCaller_divisor_polynomial (W d p : ℕ) (hd : 0<d) (hp : d≤p) :
    W^CompactGlobalRowPadding.depth m d≤
      2^(Nat.clog 2 (m+1)*Nat.clog m W)*(p+1)^Nat.clog m W := by
  have hdepth : m^CompactGlobalRowPadding.depth m d≤(m+1)*(p+1) := by
    rw [←compactTopConfigDepth d hd]
    have h := mrO_pow_synJ_le (d-1)
    have hmul := Nat.mul_le_mul_left m ((Nat.sub_le d 1).trans hp)
    nlinarith
  with_reducible exact (@divisorPolynomial W m (CompactGlobalRowPadding.depth m d) p
    (Nat.clog m W) (Nat.clog 2 (m+1)*Nat.clog m W) (Nat.clog 2 (m+1))
    (Nat.le_pow_clog one_lt_m W) (Nat.le_pow_clog (by decide) (m+1)) rfl hdepth)

/-- Runtime precision bounds original depth and therefore the actual row divisor. -/
theorem compactCaller_runtime_divisor_polynomial (M : ℕ) (hM : 2≤M) :
    NW^CompactGlobalRowPadding.depth m (Mult.Sizes.d M)≤
      2^(Nat.clog 2 (m+1)*Nat.clog m NW)*(Mult.Sizes.p M+1)^Nat.clog m NW := by
  have hd := Mult.Sizes.one_le_d hM
  have hdp : Mult.Sizes.d M≤Mult.Sizes.p M := by
    have h := Mult.Sizes.d_le_b M
    unfold Mult.Sizes.p
    omega
  with_reducible exact (compactCaller_divisor_polynomial NW (Mult.Sizes.d M) (Mult.Sizes.p M) (by omega) hdp)

end
end IntegerMultBounds.MathlibTM2.Cost
