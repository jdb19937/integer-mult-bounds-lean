module

public import IntegerMultBounds.MathlibTM2.M8.Global.Auto

/-! Close distinct side roles through their terminal frames and whole-projector exits. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {ι : Type} [DecidableEq ι] {d : Nat}

/-- Reach the terminal frame, then exit to the complementary entrance gauge. -/
def closeGauges (A C : ι → Mat d) : (ι → Mat d) → List ι → List (FStep ι d)
  | _, [] => []
  | fr, i :: ws => move i (fr i) (A i) ++ .exit i (A i) (C i) ::
      closeGauges A C (Function.update fr i (1 - C i)) ws

/-- Every required terminal alignment and exit is an actual valid framed step. -/
theorem closeGauges_valid (A C : ι → Mat d) :
    ∀ (ws : List ι) (fr : ι → Mat d) (z : ι → Prop), ws.Nodup →
    (∀ i ∈ ws, IsFrame (A i)) →
    (∀ i ∈ ws, ∀ fr z, fr i = A i → (FStep.exit i (A i) (C i)).Ok fr z) →
    (∀ i ∈ ws, Cmp (fr i) (A i)) → Valid (closeGauges A C fr ws) fr z
  | [], _, _, _, _, _, _ => trivial
  | i :: ws, fr, z, hn, hA, he, hc => by
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hn
    obtain ⟨hm, hf, hz⟩ := move_valid (i := i) fr z rfl
      (hA i (List.mem_cons_self)) (hc i (List.mem_cons_self))
    have ht : Function.update (Function.update fr i (A i)) i (1 - C i) =
        Function.update fr i (1 - C i) := by
      funext j
      by_cases h : j = i <;> simp [h]
    have ih := closeGauges_valid A C ws (Function.update fr i (1 - C i)) z hn
      (fun j hj => hA j (List.mem_cons_of_mem _ hj))
      (fun j hj => he j (List.mem_cons_of_mem _ hj)) (fun j hj => by
        have hne : j ≠ i := fun h => hnot (h ▸ hj)
        rw [Function.update_of_ne hne]
        exact hc j (List.mem_cons_of_mem _ hj))
    rw [closeGauges, valid_append, hf, hz]
    refine ⟨hm, he i (List.mem_cons_self) _ _ (Function.update_self _ _ _), ?_⟩
    change Valid (closeGauges A C (Function.update fr i (1 - C i)) ws)
      (Function.update (Function.update fr i (A i)) i (1 - C i)) z
    rw [ht]
    exact ih

/-- A closed side role ends at the complement of its entrance; spectators retain their frame. -/
theorem finalFrames_closeGauges (A C : ι → Mat d) :
    ∀ (ws : List ι) (fr : ι → Mat d), finalFrames (closeGauges A C fr ws) fr =
      fun i => if i ∈ ws then 1 - C i else fr i
  | [], fr => by funext i; simp [closeGauges, finalFrames]
  | i :: ws, fr => by
    have hm : finalFrames (move i (fr i) (A i)) fr = Function.update fr i (A i) := by
      unfold move
      split_ifs with h h
      · rw [← h, Function.update_eq_self]; rfl
      · rfl
      · rfl
    rw [closeGauges, finalFrames_append, hm]
    change finalFrames (closeGauges A C (Function.update fr i (1 - C i)) ws)
      (Function.update (Function.update fr i (A i)) i (1 - C i)) = _
    have ht : Function.update (Function.update fr i (A i)) i (1 - C i) =
        Function.update fr i (1 - C i) := by
      funext j
      by_cases h : j = i <;> simp [h]
    rw [ht, finalFrames_closeGauges A C ws]
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h, List.mem_cons]

/-- Gauge closure changes addresses only; it preserves every logical stream. -/
theorem logicRun_closeGauges {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (A C : ι → Mat d) : ∀ (ws : List ι) (fr : ι → Mat d) (x : ι → E),
      logicRun (closeGauges A C fr ws) x = x
  | [], _, _ => rfl
  | i :: ws, fr, x => by
    rw [closeGauges, logicRun_append, logicRun_move]
    exact logicRun_closeGauges A C ws _ x

end
end IntegerMultBounds.MathlibTM2.M8.Global
