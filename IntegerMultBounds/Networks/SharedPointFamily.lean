module

public import IntegerMultBounds.Networks.PairedIndexedPruning
public import IntegerMultBounds.Networks.SharedPointLift
public import IntegerMultBounds.Networks.SharedPointMatching
public import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DAGAdditionIds
public import IntegerMultBounds.Networks.SharedPointLocalFamily

/-! The actual fifty-copy family of local addition supports, for the literal
recursive local constructor pruned to the ancestors of its outputs. No
generated local DAG or support bank is imported. -/

@[expose] public section

namespace IntegerMultBounds.Networks.SharedPointFamily

open DisjointCircuit SharedPointMatching

export DAGAdditionIds (isAddition isAddition_iff additionIds mem_additionIds
  additionIds_bound additionIds_card)

/-- The local circuit replayed at every common point. -/
def localCircuit : PairedLocalCircuit := PairedIndexedPruning.implementation

/-- Each common point gets one copy of every local addition. -/
def domain : Finset (CopyNode 50) := SharedPointLocalFamily.domain localCircuit

/-- The actual source support at a local node; absent indices are empty. -/
def localSupport (i : ℕ) : Finset (Fin 1176) := localCircuit.support i

def support (node : CopyNode 50) : Finset (NeighborCounts.Triple 50) :=
  SharedPointLocalFamily.support localCircuit node

@[simp] theorem mem_domain (node : CopyNode 50) :
    node ∈ domain ↔ node.2 ∈ additionIds localCircuit.nodes :=
  SharedPointLocalFamily.mem_domain localCircuit node

theorem mem_domain_iff (node : CopyNode 50) : node ∈ domain ↔
    ∃ localNode, localCircuit.nodes[node.2]? = some localNode ∧
      ∃ l r, localNode.kind = .add l r := by
  rw [mem_domain, mem_additionIds]

theorem localSupport_get (i : ℕ) (hi : i < localCircuit.nodes.length) :
    localSupport i = localCircuit.nodes[i].support :=
  localCircuit.support_get i hi

theorem support_eq (node : CopyNode 50) : support node = SharedPointLift.lift49 node.1 (localSupport node.2) :=
  rfl

theorem support_nontrivial (node : CopyNode 50) (hn : node ∈ domain) : 2 ≤ (support node).card :=
  SharedPointLocalFamily.support_nontrivial localCircuit node hn

theorem support_common (node : CopyNode 50) (hn : node ∈ domain)
    (T : NeighborCounts.Triple 50) (hT : T ∈ support node) : node.1 ∈ T.val :=
  SharedPointLocalFamily.support_common localCircuit node hn T hT

theorem support_unique (a : CopyNode 50) (ha : a ∈ domain) (b : CopyNode 50) (hb : b ∈ domain)
    (hc : a.1 = b.1) (he : support a = support b) : a = b :=
  SharedPointLocalFamily.support_unique localCircuit a ha b hb hc he

/-- The main sharing argument consumes the implementation-independent family. -/
def family : Family 50 := SharedPointLocalFamily.family localCircuit

/-- The unmerged fifty-copy family has at most fifty times 9,813 additions. -/
theorem domain_card : domain.card ≤ 50 * 9813 := by
  rw [domain, SharedPointLocalFamily.domain_card]
  exact Nat.mul_le_mul_left 50 PairedIndexedPruning.additions_le

end IntegerMultBounds.Networks.SharedPointFamily
