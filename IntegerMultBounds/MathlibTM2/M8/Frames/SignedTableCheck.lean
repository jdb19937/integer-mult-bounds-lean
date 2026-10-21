module

public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedCheck

/-! Valid signed labels in balanced lookup tables. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.Signed

def tableCheck (size : Nat) : Local.Tree Frame → Bool
  | .leaf frame => frame.validCheck size
  | .node l r => tableCheck size l && tableCheck size r

theorem tableCheck_get (size : Nat) : ∀ (table : Local.Tree Frame) (width i : Nat),
    tableCheck size table = true → (table.get width i).validCheck size = true
  | .leaf _, _, _, h => h
  | .node l r, width, i, h => by
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    rw [Local.Tree.get_node]
    split_ifs
    · exact tableCheck_get size l _ _ hl
    · exact tableCheck_get size r _ _ hr

end IntegerMultBounds.MathlibTM2.M8.Frames.Signed
