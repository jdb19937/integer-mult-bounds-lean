module

public import IntegerMultBounds.Networks.PairedCircuit
import IntegerMultBounds.Networks.DAGCompact
import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DAGAllocatorBudget
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Data.Finset.Union

/-! Simulation of a construction by the same construction over a small atom
alphabet. Each abstract atom stands for a real support; when every abstract
support's image is already stored in the real DAG, every abstract interning
hit is also a real hit. The real run therefore allocates no more nodes than
the abstract one, and a small abstract run can be counted by evaluation. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DAGSimulation

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι] (f : α → Finset ι)

/-- The real support represented by an abstract support. -/
def image (s : Finset α) : Finset ι := s.biUnion f

/-- Every abstract support has its image stored in the real DAG. -/
def Covers (abs : List (Node α)) (real : List (Node ι)) : Prop :=
  ∀ s ∈ abs.map Node.support, image f s ∈ real.map Node.support

/-- Related references: both valid, both zero or both present, and the real
support is the image of the abstract one. -/
def RefRel (abs : List (Node α)) (real : List (Node ι)) (a b : Ref) : Prop :=
  RefValid abs a ∧ RefValid real b ∧ a.isSome = b.isSome ∧
    refSupport real b = image f (refSupport abs a)

/-- One simulated step: coverage, extension and the allocation comparison. -/
structure Step (abs : List (Node α)) (real : List (Node ι))
    (abs' : List (Node α)) (real' : List (Node ι)) : Prop where
  covers : Covers f abs' real'
  abs_extends : Extends abs abs'
  real_extends : Extends real real'
  count : additionCount real' + additionCount abs ≤ additionCount real + additionCount abs'

omit [DecidableEq α] in
theorem refRel_extends {abs abs' : List (Node α)} {real real' : List (Node ι)}
    (ha : Extends abs abs') (hr : Extends real real') {a b : Ref}
    (h : RefRel f abs real a b) : RefRel f abs' real' a b :=
  ⟨refValid_extends ha h.1, refValid_extends hr h.2.1, h.2.2.1, by
    rw [refSupport_extends hr h.2.1, refSupport_extends ha h.1]; exact h.2.2.2⟩

omit [DecidableEq α] in
theorem Step.refl (abs : List (Node α)) (real : List (Node ι)) (hc : Covers f abs real) :
    Step f abs real abs real := ⟨hc, extends_refl _, extends_refl _, le_refl _⟩

omit [DecidableEq α] in
theorem Step.trans {abs abs' abs'' : List (Node α)} {real real' real'' : List (Node ι)}
    (h₁ : Step f abs real abs' real') (h₂ : Step f abs' real' abs'' real'') :
    Step f abs real abs'' real'' :=
  ⟨h₂.covers, extends_trans h₁.abs_extends h₂.abs_extends,
    extends_trans h₁.real_extends h₂.real_extends, by have := h₁.count; have := h₂.count; omega⟩

theorem image_union (s t : Finset α) : image f (s ∪ t) = image f s ∪ image f t :=
  Finset.union_biUnion

omit [DecidableEq α] in
private theorem intern_mem (nodes : List (Node ι)) (node : Node ι) :
    node.support ∈ (intern nodes node).1.map Node.support :=
  List.mem_of_getElem? (intern_support nodes node)

omit [DecidableEq α] in
private theorem intern_of_mem (nodes : List (Node ι)) (node : Node ι)
    (h : node.support ∈ nodes.map Node.support) : (intern nodes node).1 = nodes := by
  unfold intern
  split
  · rfl
  · rename_i hn
    exact False.elim ((DisjointUnique.findSupport_none_iff _ _).mp hn h)

omit [DecidableEq α] in
private theorem intern_bound (nodes : List (Node ι)) (node : Node ι) :
    (intern nodes node).2 < (intern nodes node).1.length := by
  have h := DAGReplay.lookup_bound (intern_support nodes node)
  exact h

/-- Zero elision and interning commute with the simulation. -/
theorem smartAdd_sim (abs : List (Node α)) (real : List (Node ι)) (l r : Ref) (l' r' : Ref)
    (hc : Covers f abs real) (hl : RefRel f abs real l l') (hr : RefRel f abs real r r') :
    Step f abs real (smartAdd abs l r).1 (smartAdd real l' r').1 ∧
      RefRel f (smartAdd abs l r).1 (smartAdd real l' r').1 (smartAdd abs l r).2 (smartAdd real l' r').2 := by
  cases l with
  | none =>
    have hl' : l' = none := by cases l' <;> simp_all [RefRel]
    subst hl'
    exact ⟨Step.refl f abs real hc, hr⟩
  | some i =>
    cases r with
    | none =>
      have hr' : r' = none := by cases r' <;> simp_all [RefRel]
      subst hr'
      cases l' with
      | none => simp [RefRel] at hl
      | some i' => exact ⟨Step.refl f abs real hc, hl⟩
    | some j =>
      cases l' with
      | none => simp [RefRel] at hl
      | some i' =>
        cases r' with
        | none => simp [RefRel] at hr
        | some j' =>
          let na : Node α := ⟨.add i j, refSupport abs (some i) ∪ refSupport abs (some j)⟩
          let nr : Node ι := ⟨.add i' j', refSupport real (some i') ∪ refSupport real (some j')⟩
          have himage : nr.support = image f na.support := by
            change refSupport real (some i') ∪ refSupport real (some j') =
              image f (refSupport abs (some i) ∪ refSupport abs (some j))
            rw [image_union, hl.2.2.2, hr.2.2.2]
          have ha := intern_support abs na
          have hb := intern_support real nr
          have hcov : Covers f (intern abs na).1 (intern real nr).1 := by
            intro s hs
            by_cases hold : s ∈ abs.map Node.support
            · exact List.Sublist.subset (by
                obtain ⟨tail, htail⟩ := DAGReplay.intern_extends real nr
                rw [htail, List.map_append]
                exact List.sublist_append_left _ _) (hc s hold)
            · have hs' : s = na.support := by
                unfold intern at hs
                split at hs
                · exact False.elim (hold hs)
                · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                    List.mem_singleton] at hs
                  exact hs.resolve_left hold
              rw [hs', ← himage]
              exact intern_mem real nr
          have hcount : additionCount (intern real nr).1 + additionCount abs ≤
              additionCount real + additionCount (intern abs na).1 := by
            by_cases hm : na.support ∈ abs.map Node.support
            · rw [intern_of_mem abs na hm, intern_of_mem real nr (by rw [himage]; exact hc _ hm)]
            · have hn : findSupport na.support (abs.map Node.support) = none :=
                (DisjointUnique.findSupport_none_iff _ _).mpr hm
              have habs : (intern abs na).1 = abs ++ [na] := by simp [intern, hn]
              have hle := DAGCompact.intern_additionCount_le real nr
              rw [habs]
              simp only [additionCount, List.countP_append, List.countP_singleton] at hle ⊢
              simp only [na, nr] at hle ⊢
              simp at hle ⊢
              omega
          refine ⟨⟨hcov, DAGReplay.intern_extends abs na, DAGReplay.intern_extends real nr, hcount⟩,
            ⟨intern_bound abs na, intern_bound real nr, rfl, ?_⟩⟩
          change refSupport (intern real nr).1 (some (intern real nr).2) =
            image f (refSupport (intern abs na).1 (some (intern abs na).2))
          simp only [refSupport, ha, hb, Option.getD_some]
          exact himage

/-- Balanced totals of pointwise related operand lists are simulated. -/
theorem total_sim (abs : List (Node α)) (real : List (Node ι)) (refs refs' : List Ref)
    (hc : Covers f abs real) (h : List.Forall₂ (RefRel f abs real) refs refs') :
    Step f abs real (DisjointBalanced.total abs refs).1 (DisjointBalanced.total real refs').1 ∧
      RefRel f (DisjointBalanced.total abs refs).1 (DisjointBalanced.total real refs').1
        (DisjointBalanced.total abs refs).2 (DisjointBalanced.total real refs').2 := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction
      generalizing abs real refs' with
  | h refs ih =>
    match refs, refs', h with
    | [], [], _ =>
      simp only [DisjointBalanced.total]
      exact ⟨Step.refl f abs real hc, trivial, trivial, rfl, by simp [refSupport, image]⟩
    | [x], [x'], h =>
      simp only [DisjointBalanced.total]
      exact ⟨Step.refl f abs real hc, (List.forall₂_cons.mp h).1⟩
    | x :: y :: rs, x' :: y' :: rs', h =>
      let values := x :: y :: rs
      let values' := x' :: y' :: rs'
      have hlen : values.length = values'.length := h.length_eq
      have hleft := List.forall₂_take (values.length / 2) h
      have hright := List.forall₂_drop (values.length / 2) h
      rw [hlen] at hleft hright
      have hl : (values.take (values'.length / 2)).length < values.length := by
        simp only [List.length_take, values, values', List.length_cons] at hlen ⊢; omega
      have hr : (values.drop (values'.length / 2)).length < values.length := by
        simp only [List.length_drop, values, values', List.length_cons] at hlen ⊢; omega
      obtain ⟨sl, rl⟩ := ih _ hl abs real _ hc hleft
      have hright' := hright.imp (fun a b hab => refRel_extends f sl.abs_extends sl.real_extends hab)
      obtain ⟨sr, rr⟩ := ih _ hr _ _ _ sl.covers hright'
      have rl' := refRel_extends f sr.abs_extends sr.real_extends rl
      obtain ⟨sa, ra⟩ := smartAdd_sim f _ _ _ _ _ _ sr.covers rl' rr
      rw [DisjointBalanced.total, DisjointBalanced.total]
      have hl2 : values.length / 2 = values'.length / 2 := by rw [hlen]
      simp only [values, values'] at hl2 ⊢
      rw [hl2]
      exact ⟨Step.trans f (Step.trans f sl sr) sa, ra⟩

omit [DecidableEq α] in
/-- A state-threading loop is simulated when each body is, for all extensions
of its starting DAGs. The output relation must persist under extensions. -/
theorem mapBuild_sim {X Y Z : Type*} (fa : List (Node α) → X → List (Node α) × Y)
    (fr : List (Node ι) → X → List (Node ι) × Z)
    (out : List (Node α) → List (Node ι) → Y → Z → Prop)
    (hout : ∀ abs abs' real real' y z, Extends abs abs' → Extends real real' →
      out abs real y z → out abs' real' y z)
    (abs0 : List (Node α)) (real0 : List (Node ι)) (xs : List X)
    (hbody : ∀ x ∈ xs, ∀ abs real, Extends abs0 abs → Extends real0 real → Covers f abs real →
      Step f abs real (fa abs x).1 (fr real x).1 ∧ out (fa abs x).1 (fr real x).1 (fa abs x).2 (fr real x).2)
    (abs : List (Node α)) (real : List (Node ι)) (ha : Extends abs0 abs) (hr : Extends real0 real)
    (hc : Covers f abs real) :
    Step f abs real (mapBuild fa abs xs).1 (mapBuild fr real xs).1 ∧
      List.Forall₂ (out (mapBuild fa abs xs).1 (mapBuild fr real xs).1)
        (mapBuild fa abs xs).2 (mapBuild fr real xs).2 := by
  induction xs generalizing abs real with
  | nil => exact ⟨Step.refl f abs real hc, List.Forall₂.nil⟩
  | cons x xs ih =>
    obtain ⟨s1, o1⟩ := hbody x (by simp) abs real ha hr hc
    obtain ⟨s2, o2⟩ := ih (fun y hy => hbody y (by simp [hy])) _ _
      (extends_trans ha s1.abs_extends) (extends_trans hr s1.real_extends) s1.covers
    refine ⟨Step.trans f s1 s2, List.Forall₂.cons (hout _ _ _ _ _ _ s2.abs_extends s2.real_extends o1) o2⟩

end IntegerMultBounds.Networks.DAGSimulation
