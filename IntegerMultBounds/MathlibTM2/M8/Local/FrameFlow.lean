module

public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule

/-! Frame flow with one label per operation, allowing copies of the same node
at different frames. A kept slot ends at the last actual copy's label. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow

variable {α : Type}

def touch (label : Op → α) (cur : Nat → Option α) (op : Op) : Nat → Option α :=
  fun s => if s ∈ op.slots then some (label op) else cur s

def last (label : Op → α) (ops : List Op) : Nat → Option α :=
  ops.foldl (touch label) fun _ => none

def framesOf (label : Op → α) (s : Nat) (ops : List Op) : List α :=
  (ops.filter fun op => s ∈ op.slots).map label

def Mono (R : α → α → Prop) (label : Op → α) : List Op → (Nat → Option α) → Prop
  | [], _ => True
  | op :: ops, cur =>
      (∀ s ∈ op.slots, ∀ a, cur s = some a → R a (label op)) ∧
        Mono R label ops (touch label cur op)

theorem mono_append (R : α → α → Prop) (label : Op → α) :
    ∀ (a b : List Op) (cur : Nat → Option α),
      Mono R label (a ++ b) cur ↔
        Mono R label a cur ∧ Mono R label b (a.foldl (touch label) cur)
  | [], _, _ => by simp [Mono]
  | op :: ops, b, cur => by
    simp only [List.cons_append, Mono, List.foldl_cons, mono_append R label ops b]
    tauto

theorem mono_chain (R : α → α → Prop) (label : Op → α) :
    ∀ (ops : List Op) (cur : Nat → Option α), Mono R label ops cur →
      ∀ s, List.IsChain R ((cur s).toList ++ framesOf label s ops)
  | [], cur, _, s => by cases cur s <;> simp [framesOf]
  | op :: ops, cur, h, s => by
    have ih := mono_chain R label ops (touch label cur op) h.2 s
    by_cases hs : s ∈ op.slots
    · have ht : touch label cur op s = some (label op) := by simp [touch, hs]
      rw [ht] at ih
      simp only [framesOf, List.filter_cons, hs, decide_true, ite_true, List.map_cons] at ih ⊢
      cases hc : cur s with
      | none => simpa using ih
      | some a =>
        simp only [Option.toList_some, List.singleton_append] at ih ⊢
        exact List.isChain_cons_cons.mpr ⟨h.1 s hs a hc, ih⟩
    · have ht : touch label cur op s = cur s := by simp [touch, hs]
      rw [ht] at ih
      simpa [framesOf, hs] using ih

theorem foldl_last (label : Op → α) {s : Nat} :
    ∀ (ops : List Op) (cur : Nat → Option α),
      (ops.foldl (touch label) cur) s = ((framesOf label s ops).getLast?).or (cur s)
  | [], cur => by simp [framesOf]
  | op :: ops, cur => by
    rw [List.foldl_cons, foldl_last label ops (touch label cur op)]
    by_cases hs : s ∈ op.slots
    · simp only [framesOf, List.filter_cons, hs, decide_true, ite_true, List.map_cons, touch]
      cases h : (List.map label (List.filter (fun op => decide (s ∈ op.slots)) ops)).getLast? <;>
        simp [List.getLast?_cons, h]
    · simp [framesOf, hs, touch]

theorem last_append_single (label : Op → α) (ops : List Op) (op : Op) (s : Nat) :
    last label (ops ++ [op]) s = if s ∈ op.slots then some (label op) else last label ops s := by
  simp only [last, List.foldl_append, List.foldl_cons, List.foldl_nil, touch]

theorem copies_pivot (label : Op → α) (piv node : Nat) (fs : List Nat) :
    framesOf label piv (copies piv fs node) = fs.map fun f => label (.copy piv f node) := by
  simp only [framesOf, copies, List.filter_map]
  have h : fs.filter (fun f => decide (piv ∈ (Op.copy piv f node).slots)) = fs := by
    apply List.filter_eq_self.mpr
    intro f _
    simp [Op.slots]
  simp only [Function.comp_def]
  rw [h, List.map_map]
  rfl

theorem foldl_copies_pivot (label : Op → α) (piv node : Nat) (fs : List Nat)
    (cur : Nat → Option α) :
    ((copies piv fs node).foldl (touch label) cur) piv =
      ((fs.map fun f => label (.copy piv f node)).getLast?).or (cur piv) := by
  rw [foldl_last, copies_pivot]

theorem foldl_copies_other (label : Op → α) (piv node s : Nat) (hsp : s ≠ piv) :
    ∀ (fs : List Nat) (cur : Nat → Option α),
      ((copies piv fs node).foldl (touch label) cur) s =
        if s ∈ fs then some (label (.copy piv s node)) else cur s
  | [], cur => by simp [copies]
  | f :: fs, cur => by
    change ((copies piv fs node).foldl (touch label) (touch label cur (.copy piv f node))) s = _
    rw [foldl_copies_other label piv node s hsp fs]
    by_cases hs : s ∈ fs
    · simp [hs]
    · by_cases hsf : s = f
      · subst f; simp [hs, touch, Op.slots]
      · simp [hs, hsf, hsp, touch, Op.slots]

/-- Copies can advance through different frames. Fresh targets do not impose
an earlier operation label, while the pivot follows the supplied frame chain. -/
theorem mono_copies (R : α → α → Prop) (label : Op → α) (piv node : Nat) :
    ∀ (fs : List Nat) (cur : Nat → Option α),
      List.IsChain R ((cur piv).toList ++ fs.map fun f => label (.copy piv f node)) →
      (∀ f ∈ fs, cur f = none) → fs.Nodup → piv ∉ fs → Mono R label (copies piv fs node) cur
  | [], _, _, _, _, _ => trivial
  | f :: fs, cur, hchain, hfresh, hnd, hpf => by
    rw [List.nodup_cons] at hnd
    have hpiv : touch label cur (.copy piv f node) piv = some (label (.copy piv f node)) := by
      simp [touch, Op.slots]
    have hstep : ∀ a, cur piv = some a → R a (label (.copy piv f node)) := by
      intro a ha
      rw [ha] at hchain
      exact (List.isChain_cons_cons.mp hchain).1
    have htail : List.IsChain R
        (label (.copy piv f node) :: fs.map fun g => label (.copy piv g node)) := by
      cases ha : cur piv with
      | none => simpa [ha] using hchain
      | some a =>
        rw [ha] at hchain
        exact (List.isChain_cons_cons.mp hchain).2
    refine ⟨fun s hs a ha => ?_, ?_⟩
    · simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hstep a ha
      · rw [hfresh s (by simp)] at ha
        cases ha
    · apply mono_copies R label piv node fs
      · simpa only [hpiv, Option.toList_some, List.singleton_append] using htail
      · intro g hg
        have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
        have hgp : g ≠ piv := fun h => hpf (by rw [← h]; exact List.mem_cons_of_mem _ hg)
        simpa [touch, Op.slots, hgf, hgp] using hfresh g (List.mem_cons_of_mem _ hg)
      · exact hnd.2
      · exact fun h => hpf (List.mem_cons_of_mem _ h)


end IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
