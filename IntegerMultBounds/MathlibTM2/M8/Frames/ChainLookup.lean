module

public import IntegerMultBounds.MathlibTM2.M8.Local.TreeFacts
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedCheck

/-! Reuse checked frame chains by lookup and structural subsequence checks.
No span inclusion or orthogonality calculation is repeated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup
open Local

def every {α : Type} (f : α → Bool) : Tree α → Bool
  | .leaf a => f a
  | .node l r => every f l && every f r

theorem every_get {α : Type} (f : α → Bool) (t : Tree α)
    (h : every f t = true) (w i : Nat) : f (t.get w i) = true := by
  induction t generalizing w i with
  | leaf a => exact h
  | node l r ihl ihr =>
    simp only [every, Bool.and_eq_true] at h
    rw [Tree.get_node]
    split_ifs
    · exact ihl h.1 _ _
    · exact ihr h.2 _ _

theorem all_getD {α : Type} (f : α → Bool) (xs : List α) (h : xs.all f = true)
    (d : α) (hd : f d = true) (i : Nat) : f (xs[i]?.getD d) = true := by
  cases he : xs[i]? with
  | none => exact hd
  | some a => exact List.all_eq_true.mp h a (List.mem_of_getElem? he)

/-- Greedy subsequence matching, structurally recursive on the checked chain. -/
def sublistCheck : List Signed.Frame → List Signed.Frame → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys =>
    if a = b then sublistCheck xs ys else sublistCheck (a :: xs) ys

theorem sublistCheck_sound : ∀ (xs ys : List Signed.Frame), sublistCheck xs ys = true → xs.Sublist ys
  | [], ys, _ => List.nil_sublist ys
  | _ :: _, [], h => by cases h
  | a :: xs, b :: ys, h => by
    unfold sublistCheck at h
    split at h
    · next he =>
      subst b
      exact List.Sublist.cons_cons a (sublistCheck_sound xs ys h)
    · exact List.Sublist.cons b (sublistCheck_sound (a :: xs) ys h)

def edgeCheck (a b : Signed.Frame) (chain : List Signed.Frame) : Bool :=
  decide (a = b) || sublistCheck [a, b] chain

/-- A path may repeat frames; every strict move reuses an ordered pair of a known chain. -/
def pathCheck (size : Nat) (chain : List Signed.Frame) : List Signed.Frame → Bool
  | [] => true
  | a :: xs => a.validCheck size && match xs with
    | [] => true
    | b :: _ => edgeCheck a b chain && pathCheck size chain xs

end IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup
