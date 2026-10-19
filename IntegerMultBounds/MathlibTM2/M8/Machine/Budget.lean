module

public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.Depth

/-!
# The recursive budget

Charged coefficients and a natural-valued budget for the recursive machine, as
`Shared50RecursiveBudget` and `Shared50RecursiveBudgetAssembly` give them for Shared50. Each
child receives the logical parent volume divided by the role count; parked ancestor storage never
enters the recursive argument. The node coefficient covers the split, the merge, the pieces, the
temporaries' fill and clear, and every controller edge and return (`node_bound`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.Budget
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open RecursiveChildCallSetup (fields words)
open NodeExecution (entryCoefficient exitCoefficient scheduleCoefficient)

def base (k : ℕ) := RecursiveDigitRoleBank.coefficient+134+k

def node (k : ℕ) := entryCoefficient+exitCoefficient+scheduleCoefficient k+137+k

/-- The target budget includes all actual nonrecursive work and one same-volume
recursive budget for each literal call. Correctness is proved separately. -/
def budget (k : ℕ) : ℕ → ℕ → ℕ
  | 0, V => base k*V
  | depth+1, V => node k*V+(Net.net).rankSum*budget k depth (V/roleCount)

omit [Net] in
/-- Bound occupied-header cleanup and parent-frame restoration using only the
word lengths charged to the current logical child volume. -/
theorem return_cost_bound (V : ℕ) (hV : 0 < V) (old current : Fin 6 → List Bool)
    (ho : ∀ i, (old i).length ≤ 2*V) (hc : ∀ i, (current i).length ≤ 2*V) :
    RecursiveChildCallReturn.cost old current ≤ 127*V := by
  have hpop := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words old)
    (2*V) (by
      intro op hop
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact ho z)
  have hclear := BinaryDescriptorCleanupList.cost_le (BinaryDescriptorFrameRestore.slots fields) (words current)
    (2*V) (by
      intro z hz
      obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hc i)
  have hlen : (BinaryDescriptorFrameRestore.slots fields).length = 6 := by
    simp [BinaryDescriptorFrameRestore.slots,fields]
  rw [hlen] at hclear
  unfold RecursiveChildCallReturn.cost
  omega

omit [Net] in
/-- All fixed joins and return costs are paid from positive logical volume. -/
theorem assembly {E X T V R S C H k : ℕ} (hV : 0 < V) (hR : R ≤ V)
    (hH : H ≤ 127*V) :
    (E+X)*V+T*R+S*C+H+k+10 ≤ (E+X+T+137+k)*V+S*C := by
  have hT := Nat.mul_le_mul_left T hR
  have hk := Nat.mul_le_mul_left (k+10) hV
  nlinarith

/-- The bound of the guard-to-return node trace meets the same natural budget
used by the recursive child induction. -/
theorem node_bound (k depth V R H : ℕ) (hV : 0 < V) (hR : R ≤ V)
    (hH : H ≤ 127*V) :
    (entryCoefficient+exitCoefficient)*V+scheduleCoefficient k*R+
      (Net.net).rankSum*budget k depth (V/roleCount)+H+k+10 ≤ budget k (depth+1) V := by
  rw [budget.eq_2]
  exact assembly hV hR hH

end
end IntegerMultBounds.MathlibTM2.M8.Machine.Budget
