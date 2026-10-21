module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootCheck
public import IntegerMultBounds.MathlibTM2.M8.Local.TreeFacts

/-! Small checks for a shared bank of computed root-complement frames.
Each basis is checked once. A chain checks only its indices and inclusion of
successive bases in the preceding frame's certified generators. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.RootBank

structure Record where
  basis : List Nat
  generators : List Nat
  scale : Int
  inverse : List (List Int)
  deriving Inhabited

/-- Validate the untrusted scaled inverse once per bank entry. -/
@[irreducible] def Record.matrixCheck (entry : Record) : Bool :=
  entry.basis.all RootCheck.validCode && (entry.scale != 0) &&
    RootCheck.mulRows entry.scale (RootCheck.cols entry.basis.length entry.inverse) 0
      (RootCheck.gramOf RootCheck.g9 entry.basis)

/-- Exact residual checks, split into small declarations by the generator. -/
@[irreducible] def Record.generatorCheck (entry : Record) (generators : List Nat) : Bool :=
  generators.all fun g => RootCheck.validCode g &&
    (entry.basis.contains g || RootCheck.memOk entry.scale entry.inverse
      (RootCheck.gramOf RootCheck.dotE entry.basis) entry.basis g)

def Record.check (entry : Record) : Bool :=
  entry.matrixCheck && entry.generatorCheck entry.generators

theorem Record.generatorCheck_flatten (entry : Record) (chunks : List (List Nat)) :
    entry.generatorCheck chunks.flatten = (chunks.map entry.generatorCheck).all id := by
  simp only [Record.generatorCheck, List.all_flatten, List.all_map,
    Function.comp_def, id_eq]

/-- Reassemble small residual checks without rechecking the matrix certificate. -/
theorem Record.check_of_chunks (entry : Record) (chunks : List (List Nat))
    (hgens : entry.generators = chunks.flatten) (hm : entry.matrixCheck = true)
    (hc : (chunks.map entry.generatorCheck).all id = true) : entry.check = true := by
  rw [Record.check, hgens, entry.generatorCheck_flatten, hm, hc]
  rfl

/-- Validate every entry of a balanced lookup tree. -/
def bankCheck : Local.Tree Record → Bool
  | .leaf entry => entry.check
  | .node l r => bankCheck l && bankCheck r

/-- The same certified entry can be used at every occurrence of its frame. -/
theorem bankCheck_get : ∀ (bank : Local.Tree Record) (width i : Nat),
    bankCheck bank = true → (bank.get width i).check = true
  | .leaf entry, _, _, h => h
  | .node l r, width, i, h => by
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    rw [Local.Tree.get_node]
    split_ifs
    · exact bankCheck_get l _ _ hl
    · exact bankCheck_get r _ _ hr

/-- The next complement contains this one when its basis is spanned by the
current record's generators. The matrix calculation is already certified. -/
def Record.nestedCheck (a b : Record) : Bool :=
  b.basis.all fun k => a.generators.contains k

/-- Check a chain without repeating the bank's basis checks. -/
def chainCheck (bank : Nat → Record) (size : Nat) : List Nat → Bool
  | [] => true
  | i :: ids => Nat.blt i size &&
      match ids with
      | [] => true
      | j :: _ => (bank i).nestedCheck (bank j) && chainCheck bank size ids

/-- Check all computed sections of a collection of wire chains. -/
def chainsCheck (bank : Nat → Record) (size : Nat) (chains : List (List Nat)) : Bool :=
  chains.all (chainCheck bank size)

theorem chainsCheck_flatten (bank : Nat → Record) (size : Nat) (chunks : List (List (List Nat))) :
    chainsCheck bank size chunks.flatten =
      (chunks.map (chainsCheck bank size)).all id := by
  simp only [chainsCheck, List.all_flatten, List.all_map, Function.comp_def, id_eq]

end IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
