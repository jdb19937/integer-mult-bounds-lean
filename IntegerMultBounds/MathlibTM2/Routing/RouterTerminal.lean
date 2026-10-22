module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySchedule
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry

/-!
# Terminal routing in the shared borrowed-field geometry

The common digit count leaves a suffix of `routerTail` target-field coordinates.
Filter the requested targets into that suffix and use the elementary rank
schedule. Its exact shear contract holds on every record and all outer rows;
its number of calls is less than 131G at the chosen spacing. Uniform loading of
successive elementary configurations is still required for machine composition.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable (n K G : ℕ)

def routerTerminalTargets (targets : Finset (Fin (routerTargetWidth n K G))) :
    Finset (Fin (routerTargetWidth n K G)) :=
  targets.filter fun i => routerDigits n K G * K ≤ i.val

theorem routerTerminalTargets_card (targets : Finset (Fin (routerTargetWidth n K G)))
    (hn : K ≤ n) : (routerTerminalTargets n K G targets).card ≤ routerTail n K G := by
  have hw := routerTargetWidth_eq n K G hn
  have ht := routerTail_eq n K G hn
  have h := Finset.card_le_card_of_injOn (s := routerTerminalTargets n K G targets)
    (t := Finset.range (routerTail n K G)) (fun i => i.val - routerDigits n K G * K) ?_ ?_
  · simpa using h
  · intro i hi
    have ht' := (Finset.mem_filter.mp hi).2
    have hi' := i.isLt
    change i.val - routerDigits n K G * K ∈ Finset.range (routerTail n K G)
    rw [Finset.mem_range]
    omega
  · intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    change i.val - routerDigits n K G * K = j.val - routerDigits n K G * K at he
    apply Fin.ext
    omega

theorem routerTerminalTargets_spacing
    (targets : Finset (Fin (routerTargetWidth n (64 * G) G)))
    (hG : 0 < G) (hn : 64 * G ≤ n) :
    (routerTerminalTargets n (64 * G) G targets).card < 131 * G :=
  lt_of_le_of_lt (routerTerminalTargets_card n (64 * G) G targets hn)
    (routerTail_spacing n G hG hn)

/-- The concrete elementary rank schedule has the exact terminal shear effect. -/
theorem routerTerminal_shear (R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ i ∈ targets, source i ∉ targets)
    (i : Fin (R * 2 ^ routerTargetWidth n K G)) :
    (fun q => (elementaryRankSchedule R source (routerTerminalTargets n K G targets).toList i).val.testBit q.val) =
      shear (routerTerminalTargets n K G targets) source (fun q => i.val.testBit q.val) := by
  apply elementaryRankSchedule_shear
  intro i hi hj
  exact hsource i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1

/-- Terminal elementary routing leaves the entire outer row index unchanged. -/
theorem routerTerminal_row (R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (i : Fin (R * 2 ^ routerTargetWidth n K G)) :
    (elementaryRankSchedule R source (routerTerminalTargets n K G targets).toList i).val /
        2 ^ routerTargetWidth n K G = i.val / 2 ^ routerTargetWidth n K G :=
  elementaryRankSchedule_row R source _ i

end IntegerMultBounds.MathlibTM2.Routing
