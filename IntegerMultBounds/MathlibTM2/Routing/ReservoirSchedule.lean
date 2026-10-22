module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPartition
public import IntegerMultBounds.MathlibTM2.Routing.MatchingShears

/-!
# Three reservoir-safe matching classes, each realized by three shears

This is the logical schedule to compile into residue-separated R2 calls. It is
not yet a physical placement, descriptor generator or priced tape execution.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable (banks : Fin 3 → Finset ι) (mate : ι → ι) (hinv : Function.Involutive mate)

def reservoirPass (k : Fin 3) (x : ι → Bool) : ι → Bool :=
  matchingShears (matchingClass banks mate k) (matchingLeft (matchingClass banks mate k)) x

include hinv in
theorem reservoirPass_eq (k : Fin 3) (x : ι → Bool) :
    reservoirPass banks mate k x = fun i => x (matchingClass banks mate k i) :=
  matchingShears_involution (matchingClass banks mate k) (matchingClass_involutive banks mate hinv k) x

def reservoirSchedule (x : ι → Bool) : ι → Bool :=
  reservoirPass banks mate 0 (reservoirPass banks mate 1 (reservoirPass banks mate 2 x))

include hinv in
/-- Nine directional shears realize the original coordinate matching. -/
theorem reservoirSchedule_eq (x : ι → Bool) :
    reservoirSchedule banks mate x = fun i => x (mate i) := by
  simp only [reservoirSchedule, reservoirPass_eq banks mate hinv]
  funext i
  exact congrArg x (matchingClass_comp banks mate hinv i)

include hinv in
/-- Both directional target sets of each class avoid its borrowed reservoir. -/
theorem reservoirPass_targets_avoid
    (separate : Pairwise (fun i j => Disjoint (banks i) (banks j))) (k : Fin 3) :
    Disjoint (matchingLeft (matchingClass banks mate k)) (banks k) ∧
      Disjoint ((matchingLeft (matchingClass banks mate k)).image (matchingClass banks mate k)) (banks k) := by
  have hi := matchingClass_involutive banks mate hinv k
  have hl : Disjoint (matchingLeft (matchingClass banks mate k)) (banks k) := by
    apply Finset.disjoint_left.mpr
    intro i hm hb
    have hlt : i < matchingClass banks mate k i := (Finset.mem_filter.mp hm).2
    rw [matchingClass_fixes banks mate separate k i hb] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hl, Finset.disjoint_left.mpr ?_⟩
  intro i hm hb
  have hm' := (matchingRight_mem (matchingClass banks mate k) hi
    (matchingLeft (matchingClass banks mate k)) i).mp hm
  rw [matchingClass_fixes banks mate separate k i hb] at hm'
  exact Finset.disjoint_left.mp hl hm' hb

end IntegerMultBounds.MathlibTM2.Routing
