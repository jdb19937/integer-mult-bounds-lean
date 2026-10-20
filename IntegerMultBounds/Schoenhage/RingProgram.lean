module

public import IntegerMultBounds.Schoenhage.RingSpec

/-! The step bound of the packed ring product `ringProd`, `O(N log N log log N)` in the packed
size `N = W r` (`ringCost_le`). The compiled 91-tape program and its contract `ringProgram_spec`
are retired with the multitape backend (restore from 3ce5bd58). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- The step bound in the packed size alone. -/
theorem ringCost_le {Wd r w s N : ℕ} (_hr : 1 ≤ r) (hWd : w + 1 ≤ Wd) (hws : w + s ≤ Wd + 1) (hN : N = Wd * r) :
    ringCost Wd r w s N ≤
      4 * costC cA cB cC0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1) + 11000 * N + 250000 := by
  have hc := cost_le cA cB cC0 N
  have h1 : r * (Wd + w + s + 10) ≤ 3 * N + 10 * N := by
    have : r * (Wd + w + s + 10) ≤ r * (3 * Wd) + r * 10 := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left r (by omega)
    have hW : 1 ≤ Wd := by omega
    have e : r * (3 * Wd) = 3 * N := by rw [hN]; ring
    have f : r * 10 ≤ 10 * N := by rw [hN]; nlinarith
    omega
  unfold ringCost
  have e : 400 * r * (Wd + w + s + 10) = 400 * (r * (Wd + w + s + 10)) := by ring
  rw [e]
  nlinarith

end IntegerMultBounds.Schoenhage
