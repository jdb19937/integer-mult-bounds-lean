module

public import IntegerMultBounds.MathlibTM2.Routing.SlotSources

/-!
# Compile preserved target-field coordinates to R2 source descriptors

Every coordinate of the complete target field has a low, segment or high source
constructor. Only selected low segment bits are forbidden. This compiler uses no
ordering assumption on the requested sources.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (hK : 0 < p.K) {X : ℕ}

def sourceOfY (q : Fin p.wy) : SlotSource p X :=
  if hlo : q.val < p.ρ then .low ⟨q.val, hlo⟩
  else if hmid : q.val < p.ρ + p.n * p.K then
    .digit ⟨(q.val - p.ρ) / p.K, by
      apply (Nat.div_lt_iff_lt_mul hK).mpr
      omega⟩ ⟨(q.val - p.ρ) % p.K, Nat.mod_lt _ hK⟩
  else .high ⟨q.val - (p.ρ + p.n * p.K), by
    have hq := q.isLt
    unfold Par.wy at hq
    omega⟩

theorem sourceOfY_physical (q : Fin p.wy) (y x : ℕ) :
    (sourceOfY p hK q : SlotSource p X).physical y x = y.testBit q.val := by
  unfold sourceOfY
  split_ifs with hlo hmid
  · rfl
  · simp only [SlotSource.physical]
    congr 1
    have he := Nat.mod_add_div (q.val - p.ρ) p.K
    have hs : q.val - p.ρ + p.ρ = q.val := by omega
    nlinarith
  · simp only [SlotSource.physical]
    congr 1
    omega

/-- Excluding the active target coordinates is exactly the source requirement. -/
theorem sourceOfY_allowed (active : Fin p.n → Bool) (q : Fin p.wy)
    (hq : ∀ c, active c = true → q.val ≠ p.ρ + c.val * p.K) :
    (sourceOfY p hK q : SlotSource p X).Allowed active := by
  unfold sourceOfY
  split_ifs with hlo hmid
  · trivial
  · change active ⟨(q.val - p.ρ) / p.K, _⟩ = true →
      0 < (q.val - p.ρ) % p.K
    intro ha
    have hn := hq ⟨(q.val - p.ρ) / p.K, _⟩ ha
    change q.val ≠ p.ρ + ((q.val - p.ρ) / p.K) * p.K at hn
    have he := Nat.mod_add_div (q.val - p.ρ) p.K
    have hs : q.val - p.ρ + p.ρ = q.val := by omega
    by_contra h
    have hz : (q.val - p.ρ) % p.K = 0 := by omega
    apply hn
    nlinarith
  · trivial

end IntegerMultBounds.MathlibTM2.Routing
