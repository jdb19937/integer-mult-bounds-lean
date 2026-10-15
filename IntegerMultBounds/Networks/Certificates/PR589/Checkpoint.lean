module

public import IntegerMultBounds.Networks.Certificates.PR589.Scalar

/-! Shallow row-ID snapshots separate the cheap off-target consistency check
from exact XOR checks on registers actually changed by a scalar chunk. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589

def snapshot (bank : ℕ → BitVec 661) (refs : ℕ → ℕ) (i : ℕ) : BitVec 661 :=
  if i < 661 then bank (refs i) else 0

def offTargetCheck (targets : List ℕ) (before after : ℕ → ℕ) : Bool :=
  (List.range 661).all (fun i => targets.contains i || before i == after i)

theorem snapshot_off_target (bank : ℕ → BitVec 661) (targets : List ℕ)
    (before after : ℕ → ℕ) (hc : offTargetCheck targets before after = true)
    (i : ℕ) (hi : i ∉ targets) :
    snapshot bank before i = snapshot bank after i := by
  by_cases hb : i < 661
  · have hh := (List.all_eq_true.mp hc) i (List.mem_range.mpr hb)
    have he : before i = after i := by simpa [List.contains_eq_mem, hi] using hh
    simp only [snapshot, if_pos hb, he]
  · simp [snapshot, hb]

/-- Target rows and off-target row IDs together certify the entire scalar chunk. -/
theorem checkpoint (bank : ℕ → BitVec 661) (before after : ℕ → ℕ)
    (gs : List RawGate)
    (hc : offTargetCheck (gs.map RawGate.target) before after = true)
    (hrows : ∀ i ∈ gs.map RawGate.target,
      replay gs (snapshot bank before) i = snapshot bank after i) :
    replay gs (snapshot bank before) = snapshot bank after := by
  funext i
  by_cases hi : i ∈ gs.map RawGate.target
  · exact hrows i hi
  · rw [replay_preserves gs _ i (by
      intro g hg he
      exact hi (List.mem_map.mpr ⟨g, hg, he⟩))]
    exact snapshot_off_target bank _ before after hc i hi

end IntegerMultBounds.Networks.Certificates.PR589
