module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! Fixed polynomial setup work is absorbed by the actual coefficient count.
The coefficients are powers of two and all statements use runtime sizes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter
noncomputable section

theorem compactRuntime_eventually_polynomial (c e : ℕ) : ∀ᶠ N : ℕ in atTop,
    2^c*(Mult.Sizes.p N+1)^e≤Mult.Sizes.r N := by
  filter_upwards [Mult.Sizes.eventually_pow_p_le_r (e+1),
    tendsto_atTop.1 Mult.Sizes.tendsto_b (2^(c+e)+1)] with N hpow hb
  have hbpow : 2^(c+e)≤Mult.Sizes.b N := (Nat.le_succ _).trans hb
  have hbpos : 1≤Mult.Sizes.b N := (Nat.succ_le_succ (Nat.zero_le _)).trans hb
  have hbase : Mult.Sizes.b N≤Mult.Sizes.p N := Nat.le_mul_of_pos_left _ (by decide : 0<6)
  have hp : 1≤Mult.Sizes.p N := hbpos.trans hbase
  have hcoeff : 2^c*2^e≤Mult.Sizes.p N := by
    rw [←pow_add]
    exact hbpow.trans hbase
  calc
    2^c*(Mult.Sizes.p N+1)^e≤2^c*(2*Mult.Sizes.p N)^e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) e)
    _ = (2^c*2^e)*Mult.Sizes.p N^e := by rw [mul_pow]; ring
    _ ≤ Mult.Sizes.p N*Mult.Sizes.p N^e := Nat.mul_le_mul_right _ hcoeff
    _ = Mult.Sizes.p N^(e+1) := by rw [pow_succ]; ring
    _ ≤ Mult.Sizes.r N := hpow

/-- A common polynomial scalar budget can be raised to any fixed power and
still be paid by the actual coefficient count. -/
theorem compactRuntime_eventually_scalar_power (a c e t : ℕ) : ∀ᶠ N : ℕ in atTop,
    ∀ B : ℕ, B≤2^c*(Mult.Sizes.p N+1)^e →
      2^a*(B+1)^t≤Mult.Sizes.r N := by
  filter_upwards [compactRuntime_eventually_polynomial (a+(c+1)*t) (e*t)] with N hn
  intro B hB
  have hpow : 1≤(Mult.Sizes.p N+1)^e := Nat.one_le_pow _ _ (by omega)
  have hb : B+1≤2^(c+1)*(Mult.Sizes.p N+1)^e := by
    rw [pow_succ]
    have hpos : 1≤2^c := Nat.one_le_pow _ _ (by decide)
    nlinarith
  calc
    2^a*(B+1)^t≤2^a*(2^(c+1)*(Mult.Sizes.p N+1)^e)^t :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb t)
    _ = 2^(a+(c+1)*t)*(Mult.Sizes.p N+1)^(e*t) := by
      rw [mul_pow,←pow_mul,←pow_mul,pow_add]
      ring
    _ ≤ Mult.Sizes.r N := hn

/-- Absorbing a fixed polynomial setup charge costs at most one dyadic step
in the stream-volume coefficient, with no change to its asymptotic exponent. -/
theorem compactRuntime_eventually_setup_volume (C c e t s : ℕ) : ∀ᶠ N : ℕ in atTop,
    ∀ B V : ℕ, B≤2^c*(Mult.Sizes.p N+1)^e → Mult.Sizes.r N≤V →
      C*B^t+2^s*V≤2^(s+1)*V := by
  filter_upwards [compactRuntime_eventually_scalar_power (Nat.clog 2 C) c e t] with N hn
  intro B V hB hV
  have hc : C≤2^Nat.clog 2 C := Nat.le_pow_clog (by decide) C
  have hsetup : C*B^t≤V :=
    (Nat.mul_le_mul hc (Nat.pow_le_pow_left (Nat.le_succ B) t)).trans ((hn B hB).trans hV)
  have hs : 1≤2^s := Nat.one_le_pow _ _ (by decide)
  calc
    C*B^t+2^s*V≤V+2^s*V := Nat.add_le_add_right hsetup _
    _ ≤ (2^s+2^s)*V := by nlinarith
    _ = 2^(s+1)*V := by rw [pow_succ]; ring

end
end IntegerMultBounds.MathlibTM2.Cost
