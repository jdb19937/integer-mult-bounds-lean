module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveDensity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin

/-!
# Space for three routing reservoirs

Wider segment spacing leaves enough unused coordinates for three reservoirs,
each large enough for all three borrowed fields. The existing R2 density proof
continues to apply because increasing the gap can only improve its bound.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def routingReservoirWidth (n G : ℕ) : ℕ := (n / (64 * G) + 1) * G

theorem routingReservoir_budget (n G : ℕ) (hlarge : 64 * G ≤ n) :
    32 * routingReservoirWidth n G ≤ n := by
  have hd := Nat.div_mul_le_self n (64 * G)
  unfold routingReservoirWidth
  nlinarith

theorem routingReservoir_fit (n G : ℕ) (hlarge : 64 * G ≤ n) :
    9 * routingReservoirWidth n G ≤ n := by
  have h := routingReservoir_budget n G hlarge
  omega

/-- Concrete disjoint consecutive reservoirs; unused coordinates stay outside. -/
def routingReservoir (n H : ℕ) (hfit : 9 * H ≤ n) (k : Fin 3) : Finset (Fin n) :=
  Finset.univ.map {
    toFun := fun r : Fin (3 * H) => ⟨k.val * (3 * H) + r.val, by
      have hk := Nat.mul_le_mul_right (3 * H) (show k.val + 1 ≤ 3 by omega)
      have hr := r.isLt
      nlinarith⟩
    inj' := by
      intro r s he
      apply Fin.ext
      have hv := congrArg Fin.val he
      change k.val * (3 * H) + r.val = k.val * (3 * H) + s.val at hv
      exact Nat.add_left_cancel hv }

theorem routingReservoir_card (n H : ℕ) (hfit : 9 * H ≤ n) (k : Fin 3) :
    (routingReservoir n H hfit k).card = 3 * H := by simp [routingReservoir]

theorem routingReservoir_disjoint (n H : ℕ) (hfit : 9 * H ≤ n) :
    Pairwise (fun i j => Disjoint (routingReservoir n H hfit i) (routingReservoir n H hfit j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hy
  have he := congrArg Fin.val (ha.trans hb.symm)
  change i.val * (3 * H) + a.val = j.val * (3 * H) + b.val at he
  have hlt := a.isLt
  have hlt' := b.isLt
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

/-- Router spacing reserves room for borrowed fields while retaining R2 guards. -/
def routerParameters (ρ digits m g : ℕ) : Par := ⟨64 * (4 * g + 6), ρ, digits, 4 * g + 6, m⟩

theorem routerParameters_guards (ρ digits m g : ℕ) :
    0 < (routerParameters ρ digits m g).G ∧ 0 < (routerParameters ρ digits m g).K ∧
      (routerParameters ρ digits m g).G + 1 < (routerParameters ρ digits m g).K := by
  simp only [routerParameters]
  omega

theorem routerParameters_radices (ρ digits m g : ℕ) (scale : ℝ)
    (hscale : 0 ≤ scale) (hs : scale ≤ (2 : ℝ) ^ g) :
    64 * scale ^ 4 ≤ (2 : ℝ) ^ (routerParameters ρ digits m g).G ∧
      1024 * scale ^ 4 ≤ (2 : ℝ) ^ ((routerParameters ρ digits m g).K - 1 -
        (routerParameters ρ digits m g).G) := by
  have h := routingParameters_radices ρ digits m g scale hscale hs
  refine ⟨h.1, h.2.trans ?_⟩
  apply pow_le_pow_right₀ (by norm_num)
  change 8 * g + 17 - 1 - (4 * g + 6) ≤ 64 * (4 * g + 6) - 1 - (4 * g + 6)
  omega

end IntegerMultBounds.MathlibTM2.Routing
