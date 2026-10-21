module

public import IntegerMultBounds.MathlibTM2.M8.Local.SlotCount
public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule
import Mathlib.Tactic.Abel

/-!
# The moves along the compiled slots, node by node

Each slot of the compiled operations passes through the nodes of the operations touching it
(`nodesOf`). For a cost `c p n` of a move from the slot's previous node `p` (`none` for a fresh
slot) to node `n`, with no cost for staying (`c (some n) n = 0`), the total over the slots
(`slotSum`) is a sum over the nodes (`slotSum_compile`): a leaf fills a fresh slot, an addition
moves the slots of its two arguments from their sources (`Dag.srcNode`), and every further free
use fills a fresh slot by a copy (`ev`).

At the end every slot was last touched either at the node of a root it serves or at an addition
that is no donor, whose second slot it was (`lastSum_compile`): every slot is either the read
slot of one root or the abandoned second slot of one such addition.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Classical

variable {M : Type*} [AddCommMonoid M]

/-- The cost of the moves along a list of nodes, after node `p`. -/
def chainC (c : Option ℕ → ℕ → M) : Option ℕ → List ℕ → M
  | _, [] => 0
  | p, n :: l => c p n + chainC c (some n) l

theorem chainC_append (c : Option ℕ → ℕ → M) :
    ∀ (p : Option ℕ) (a b : List ℕ), chainC c p (a ++ b) = chainC c p a + chainC c (a.getLast?.or p) b
  | p, [], b => by simp [chainC]
  | p, n :: a, b => by
    rw [List.cons_append, chainC, chainC, chainC_append c (some n) a b, add_assoc]
    congr 2
    cases a <;> simp [List.getLast?_cons]

/-- The cost of a list of operations, slot by slot, after the last nodes `cur`. -/
def opsC (c : Option ℕ → ℕ → M) : List Op → (ℕ → Option ℕ) → M
  | [], _ => 0
  | op :: rest, cur => (op.slots.map fun s => c (cur s) op.node).sum + opsC c rest (touchOp cur op)

theorem opsC_append (c : Option ℕ → ℕ → M) :
    ∀ (a b : List Op) (cur : ℕ → Option ℕ), opsC c (a ++ b) cur = opsC c a cur + opsC c b (a.foldl touchOp cur)
  | [], b, cur => by simp [opsC]
  | op :: a, b, cur => by
    rw [List.cons_append, opsC, opsC, opsC_append c a b, add_assoc, List.foldl_cons]

theorem Op.slots_nodup {op : Op} (h : op.Distinct) : op.slots.Nodup := by
  cases op <;> simp_all [Op.slots, Op.Distinct]

theorem Op.slots_lt {op : Op} {B : ℕ} (h : op.SlotsLt B) : ∀ s ∈ op.slots, s < B := by
  cases op <;> simp_all [Op.slots, Op.SlotsLt]

/-- **Slot sums as operation sums.** -/
theorem sum_chainC (c : Option ℕ → ℕ → M) (B : ℕ) :
    ∀ (ops : List Op) (cur : ℕ → Option ℕ), (∀ op ∈ ops, op.Distinct ∧ op.SlotsLt B) →
      ∑ s ∈ Finset.range B, chainC c (cur s) (nodesOf s ops) = opsC c ops cur
  | [], cur, _ => by simp [nodesOf, chainC, opsC]
  | op :: rest, cur, h => by
    have ih := sum_chainC c B rest (touchOp cur op) (fun o ho => h o (by simp [ho]))
    have hnd := Op.slots_nodup (h op (by simp)).1
    have hlt := Op.slots_lt (h op (by simp)).2
    have hsplit : ∀ s, chainC c (cur s) (nodesOf s (op :: rest)) =
        (if s ∈ op.slots then c (cur s) op.node else 0) +
          chainC c (touchOp cur op s) (nodesOf s rest) := by
      intro s
      by_cases hs : s ∈ op.slots
      · simp [nodesOf, hs, chainC, touchOp]
      · simp [nodesOf, hs, touchOp]
    rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib, ih, opsC]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← List.sum_toFinset _ hnd]
    apply Finset.sum_congr _ fun _ _ => rfl
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h' => ⟨hlt s h', h'⟩⟩

theorem opsC_copies (c : Option ℕ → ℕ → M) (hc : ∀ n, c (some n) n = 0) (piv node : ℕ) :
    ∀ (fs : List ℕ) (cur : ℕ → Option ℕ), cur piv = some node → (∀ f ∈ fs, cur f = none) →
      fs.Nodup → piv ∉ fs → opsC c (copies piv fs node) cur = fs.length • c none node
  | [], _, _, _, _, _ => by simp [copies, opsC]
  | f :: fs, cur, hpiv, hfresh, hnd, hpf => by
    rw [List.nodup_cons] at hnd
    have hfp : f ≠ piv := fun h => hpf (by simp [h])
    have ih := opsC_copies c hc piv node fs (touchOp cur (.copy piv f node))
      (by simp [touchOp, Op.slots, Op.node])
      (fun g hg => by
        have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
        have hgp : g ≠ piv := fun h => hpf (by rw [← h]; exact List.mem_cons_of_mem _ hg)
        simp only [touchOp, Op.slots, List.mem_cons, List.not_mem_nil, hgf, hgp,
          or_self, ite_false]
        exact hfresh g (List.mem_cons_of_mem _ hg))
      hnd.2 (fun h => hpf (List.mem_cons_of_mem _ h))
    have he : copies piv (f :: fs) node = .copy piv f node :: copies piv fs node := rfl
    rw [he, opsC, ih]
    simp only [Op.slots, Op.node, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, hpiv, hc, zero_add, hfresh f (by simp), List.length_cons, succ_nsmul]
    rw [add_comm]

namespace Dag
variable (D : Dag)

/-- The cost of node `k`'s operations. -/
noncomputable def ev (c : Option ℕ → ℕ → M) (k : ℕ) : M :=
  (if k < D.v then c none k
    else c (some (D.srcNode (.gate k false))) k + c (some (D.srcNode (.gate k true))) k) +
    ((D.freeUses k).length - 1) • c none k

/-- The total cost along the slots. -/
def slotSum (c : Option ℕ → ℕ → M) (st : State) : M :=
  ∑ s ∈ Finset.range st.next, chainC c none (nodesOf s st.ops)

private theorem trivial_order : D.FrameOrder fun _ _ => True := ⟨fun _ => trivial,
  fun _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem compileTo_succ (k : ℕ) : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
  simp only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem nodesOf_eq_nil {ops : List Op} {B s : ℕ} (h : ∀ op ∈ ops, op.SlotsLt B) (hs : B ≤ s) :
    nodesOf s ops = [] := by
  simp only [nodesOf, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  intro op hop hmem
  have := Op.slots_lt (h op hop) s hmem
  omega

/-- The new operations of one step cost `ev`. -/
theorem opsC_step (hv : D.Valid) (c : Option ℕ → ℕ → M) (hc : ∀ n, c (some n) n = 0) {k : ℕ}
    (hk : k < D.N) {st : State} (hi : D.Inv (fun _ => 0) k st) (hf : D.FInv (fun _ _ => True) k st)
    {new : List Op} (hnew : (D.step st k).ops = st.ops ++ new) :
    opsC c new (lastNode st.ops) = D.ev c k := by
  have hfree := (D.freeUses k).length
  unfold step at hnew
  split_ifs at hnew with hleaf
  · -- a leaf: a fresh slot, then the copies
    rw [(State.serve_ops _ _ _ _).1] at hnew
    simp only [List.append_assoc, List.append_cancel_left_eq] at hnew
    subst hnew
    rw [opsC_append, opsC_copies c hc st.next k]
    · simp only [ev, ite_eq_left_iff.mpr (fun h => absurd hleaf h), opsC, Op.slots, Op.node, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, hf.fresh st.next le_rfl, List.length_range']
    · simp [touchOp, Op.slots, Op.node]
    · intro f hf'
      rw [List.mem_range'_1] at hf'
      simp only [List.foldl_cons, List.foldl_nil, touchOp, Op.slots, List.mem_singleton]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      exact hf.fresh f (by omega)
    · exact List.nodup_range'
    · intro h; rw [List.mem_range'_1] at h; omega
  · have hvk : D.v ≤ k := Nat.le_of_not_lt hleaf
    have hpa := D.pending_arg hv hvk hk false
    have hpb := D.pending_arg hv hvk hk true
    set sa := st.pend (.gate k false)
    set sb := st.pend (.gate k true)
    have hla : lastNode st.ops sa = some (D.srcNode (.gate k false)) := hf.last _ hpa
    have hlb : lastNode st.ops sb = some (D.srcNode (.gate k true)) := hf.last _ hpb
    have hab : sa ≠ sb := fun h => by have := hi.inj _ _ hpa hpb h; cases this
    have hsa := hi.slot_lt _ hpa
    have hsb := hi.slot_lt _ hpb
    -- the copies after the addition at slots `piv`, `oth`
    have hadd : ∀ piv oth, ({piv, oth} : Finset ℕ) = {sa, sb} → piv ≠ oth →
        opsC c ([.add piv oth k] ++
          copies piv (List.range' st.next ((D.freeUses k).length - 1)) k) (lastNode st.ops) =
        D.ev c k := by
      intro piv oth he hpo
      have hp : piv < st.next ∧ oth < st.next := by
        have h1 : piv ∈ ({sa, sb} : Finset ℕ) := he ▸ by simp
        have h2 : oth ∈ ({sa, sb} : Finset ℕ) := he ▸ by simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
        omega
      rw [opsC_append, opsC_copies c hc piv k]
      · have hsum : c (lastNode st.ops piv) k + c (lastNode st.ops oth) k =
            c (some (D.srcNode (.gate k false))) k + c (some (D.srcNode (.gate k true))) k := by
          have h1 : piv ∈ ({sa, sb} : Finset ℕ) := he ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl
          · have h2 : oth = sb := by
              have : oth ∈ ({sa, sb} : Finset ℕ) := he ▸ by simp
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h
              · exact absurd h.symm hpo
              · exact h
            rw [h2, hla, hlb]
          · have h2 : oth = sa := by
              have : oth ∈ ({sa, sb} : Finset ℕ) := he ▸ by simp
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h
              · exact h
              · exact absurd h.symm hpo
            rw [h2, hla, hlb, add_comm]
        simp only [opsC, Op.slots, Op.node, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, ev, ite_eq_right_iff.mpr (fun h => absurd h hleaf),
          List.length_range']
        rw [hsum]
      · simp [touchOp, Op.slots, Op.node]
      · intro f hf'
        rw [List.mem_range'_1] at hf'
        simp only [List.foldl_cons, List.foldl_nil, touchOp, Op.slots, List.mem_cons,
          List.not_mem_nil, or_false]
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
        exact hf.fresh f (by omega)
      · exact List.nodup_range'
      · intro h; rw [List.mem_range'_1] at h; omega
    cases hl : D.link k with
    | none =>
      simp only [hl] at hnew
      rw [(State.serve_ops _ _ _ _).1] at hnew
      simp only [List.append_assoc, List.append_cancel_left_eq] at hnew
      rw [← hnew]
      exact hadd sa sb rfl hab
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      simp only [hl] at hnew
      rw [(State.serve_ops _ _ _ _).1] at hnew
      simp only [State.assign, List.append_assoc, List.append_cancel_left_eq] at hnew
      rw [← hnew]
      cases o
      · exact hadd sb sa (Finset.pair_comm _ _) (Ne.symm hab)
      · exact hadd sa sb rfl hab

/-- **The slot moves, node by node.** -/
theorem slotSum_compileTo (hv : D.Valid) (c : Option ℕ → ℕ → M) (hc : ∀ n, c (some n) n = 0) :
    ∀ k, k ≤ D.N → slotSum c (D.compileTo k) = ∑ t ∈ Finset.range k, D.ev c t := by
  intro k
  induction k with
  | zero => intro _; simp [slotSum, compileTo, start]
  | succ k ih =>
    intro hk
    have hk' : k < D.N := by omega
    set st := D.compileTo k
    have hi := D.inv_compileTo hv (fun _ => 0) k (by omega)
    have hf := D.finv_compileTo hv (D.trivial_order) k (by omega)
    have hi' := D.inv_compileTo hv (fun _ => 0) (k + 1) hk
    obtain ⟨new, hnew, -⟩ := D.step_ops st k
    rw [Finset.sum_range_succ, ← ih (by omega), compileTo_succ]
    have hle : st.next ≤ (D.step st k).next := by
      rw [D.step_next hv st hk']; omega
    have hok : ∀ op ∈ (D.step st k).ops, op.Distinct ∧ op.SlotsLt (D.step st k).next := by
      rw [← compileTo_succ]; exact hi'.ops_ok
    unfold slotSum
    -- the slots up to the new count; the old ones end where they were last touched
    have hsplit : ∀ s, chainC c none (nodesOf s (D.step st k).ops) =
        chainC c none (nodesOf s st.ops) + chainC c (lastNode st.ops s) (nodesOf s new) := by
      intro s
      have hl := nodesOf_getLast (s := s) st.ops (fun _ => none)
      simp only [Option.or_none] at hl
      rw [hnew, show nodesOf s (st.ops ++ new) = nodesOf s st.ops ++ nodesOf s new by
        simp [nodesOf, List.filter_append], chainC_append, Option.or_none]
      rw [← hl]
      rfl
    rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib]
    have hold : ∑ s ∈ Finset.range (D.step st k).next, chainC c none (nodesOf s st.ops) =
        ∑ s ∈ Finset.range st.next, chainC c none (nodesOf s st.ops) := by
      refine (Finset.sum_subset (Finset.range_subset_range.mpr hle) fun s hs hns => ?_).symm
      rw [Finset.mem_range, not_lt] at hns
      rw [nodesOf_eq_nil (fun op h => (hi.ops_ok op h).2) hns]
      rfl
    rw [hold]
    congr 1
    rw [sum_chainC c _ new _ (fun op h => hok op (by rw [hnew]; exact List.mem_append_right _ h))]
    exact D.opsC_step hv c hc hk' hi hf hnew

theorem slotSum_compile (hv : D.Valid) (c : Option ℕ → ℕ → M) (hc : ∀ n, c (some n) n = 0) :
    slotSum c D.compile = ∑ t ∈ Finset.range D.N, D.ev c t :=
  D.slotSum_compileTo hv c hc D.N le_rfl

/-- The free uses, weighted by their nodes. -/
theorem sum_freeUses_smul (hv : D.Valid) (X : ℕ → M) :
    ∑ n ∈ Finset.range D.N, (D.freeUses n).length • X n =
      ∑ u ∈ D.allUses.filter (fun u => D.linkedB u = false), X (D.useNode u) := by
  have hlen : ∀ y, (D.freeUses y).length =
      ((D.allUses.filter fun u => D.linkedB u = false).filter fun u => D.useNode u = y).card := by
    intro y
    rw [← List.toFinset_card_of_nodup (D.freeUses_nodup y), D.freeUses_toFinset hv,
      Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro u _
    exact and_comm
  rw [← Finset.sum_fiberwise_of_maps_to (g := D.useNode) (t := Finset.range D.N)
    (fun u hu => Finset.mem_range.mpr (D.useNode_lt hv (Finset.mem_filter.mp hu).1))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hlen y, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.mp hu).2]

/-- **The slot moves by uses.** Each addition moves its argument slots from their sources less
one fresh fill, and every free use fills one fresh slot. -/
theorem slotSum_uses {G : Type*} [AddCommGroup G] (hv : D.Valid) (c : Option ℕ → ℕ → G)
    (hc : ∀ n, c (some n) n = 0) :
    slotSum c D.compile =
      ∑ k ∈ Finset.range D.N, (if D.v ≤ k then c (some (D.srcNode (.gate k false))) k +
          c (some (D.srcNode (.gate k true))) k - c none k else 0) +
        ∑ u ∈ D.allUses.filter (fun u => D.linkedB u = false), c none (D.useNode u) := by
  rw [D.slotSum_compile hv c hc, ← D.sum_freeUses_smul hv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hpos := D.freeUses_length_pos hv (Finset.mem_range.mp hk)
  have hsm : ((D.freeUses k).length - 1) • c none k = (D.freeUses k).length • c none k - c none k := by
    conv_rhs => rw [show (D.freeUses k).length = ((D.freeUses k).length - 1) + 1 by omega]
    rw [succ_nsmul, add_sub_cancel_right]
  rw [ev, hsm]
  by_cases hl : k < D.v
  · rw [ite_eq_left_iff.mpr (fun h => absurd hl h),
      ite_eq_right_iff.mpr (fun h => absurd h (Nat.not_le_of_lt hl))]
    abel
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hl), ite_eq_left_iff.mpr (fun h => absurd (Nat.le_of_not_lt hl) h)]
    abel

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
