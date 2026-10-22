module

public import IntegerMultBounds.MathlibTM2.M8.Local.PendingWeightsB

/-! Summing the actual serving slots gives the node's backward weight. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open Classical

/-- Observation weights at rest-use slots are the weights of consecutive fresh slots. -/
theorem serveRest_observations {α : Type*} (n p : Nat) (us : List Use) (st : State)
    (hnd : us.Nodup) (w : Nat → α) :
    us.map (fun u => w ((State.serveRest n p st us).pend u)) =
      (List.range' st.next us.length).map w := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    rw [FrameFlow.serveRest_pend_index n p us st hnd i hi]
    simp

/-- The first served use keeps the pivot, and all others observe successive fresh slots. -/
theorem serve_observations {α : Type*} (n p : Nat) (u : Use) (us : List Use) (st : State)
    (hnd : (u :: us).Nodup) (w : Nat → α) :
    (u :: us).map (fun v => w ((State.serve n p st (u :: us)).pend v)) =
      w p :: (List.range' st.next us.length).map w := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map] at hi
    cases i with
    | zero =>
      simpa using congrArg w (FrameFlow.serve_pend_index n p (u :: us) st hnd 0 hi)
    | succ i =>
      have hs := FrameFlow.serve_pend_index n p (u :: us) st hnd (i + 1) hi
      simpa using congrArg w hs

/-- Agreement with use weights turns the pivot and fresh-slot sum into the node sum. -/
theorem served_observation_sum (n p : Nat) (u : Use) (us : List Use) (st : State)
    (hnd : (u :: us).Nodup) (w : Reg →₀ ZMod 2) (c : Use → ZMod 2)
    (hc : ∀ v ∈ u :: us, w (.aux ((State.serve n p st (u :: us)).pend v)) = c v) :
    w (.aux p) + ((List.range' st.next us.length).map fun f => w (.aux f)).sum =
      ((u :: us).map c).sum := by
  have hm := serve_observations n p u us st hnd (fun s => w (.aux s))
  have he : (u :: us).map (fun v => w (.aux ((State.serve n p st (u :: us)).pend v))) =
      (u :: us).map c := List.map_congr_left hc
  rw [he] at hm
  exact (congrArg List.sum hm).symm

/-- After pulling back the copies, the pivot weight is exactly the sum of free-use weights. -/
theorem served_pivot_weight (D : Dag) (n p : Nat) (hn : D.v ≤ n)
    (u : Use) (us : List Use) (st : State) (hnd : (u :: us).Nodup) (hp : p < st.next)
    (w : Reg →₀ ZMod 2) (c : Use → ZMod 2)
    (hc : ∀ v ∈ u :: us, w (.aux ((State.serve n p st (u :: us)).pend v)) = c v) :
    (pullOps ((copies p (List.range' st.next us.length) n).map D.vop) w) (.aux p) =
      ((u :: us).map c).sum := by
  rw [pullOps_internal_copies D p n hn]
  · simpa using served_observation_sum n p u us st hnd w c hc
  · intro h
    obtain ⟨i, _, hi⟩ := List.mem_range'.mp h
    simp only [Nat.one_mul] at hi
    omega

/-- Pulling back the addition preserves its pivot weight and adds it to the other operand. -/
theorem addition_operand_weights (p q n : Nat) (hpq : p ≠ q) (w : Reg →₀ ZMod 2) :
    (pullOp (.add p q n) w) (.aux p) = w (.aux p) ∧
      (pullOp (.add p q n) w) (.aux q) = w (.aux q) + w (.aux p) := by
  simp [pullOp, pullAdd, hpq]

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
