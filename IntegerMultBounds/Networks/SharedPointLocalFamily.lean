module

public import IntegerMultBounds.Networks.PairedLocalCircuit
public import IntegerMultBounds.Networks.SharedPointMatching

/-! The shared-point support family of any proved local pair-exclusion
constructor. The main matching argument depends on this contract, not on
certificate rows or a particular input-mask representation. -/

@[expose] public section

namespace IntegerMultBounds.Networks.SharedPointLocalFamily

open DisjointCircuit SharedPointMatching DAGAdditionIds

/-- One copy of each actual local addition for every common point. -/
def domain (source : PairedLocalCircuit) : Finset (CopyNode 50) :=
  Finset.univ ×ˢ additionIds source.nodes

def support (source : PairedLocalCircuit) (node : CopyNode 50) : Finset (NeighborCounts.Triple 50) :=
  SharedPointLift.lift49 node.1 (source.support node.2)

@[simp] theorem mem_domain (source : PairedLocalCircuit) (node : CopyNode 50) :
    node ∈ domain source ↔ node.2 ∈ additionIds source.nodes := by simp [domain]

theorem support_nontrivial (source : PairedLocalCircuit) (node : CopyNode 50)
    (hn : node ∈ domain source) : 2 ≤ (support source node).card := by
  rw [support, SharedPointLift.lift49_card]
  exact source.support_card_two node.2 ((mem_domain source node).mp hn)

theorem support_common (source : PairedLocalCircuit) (node : CopyNode 50)
    (_hn : node ∈ domain source) (T : NeighborCounts.Triple 50) (hT : T ∈ support source node) :
    node.1 ∈ T.val := SharedPointLift.common_mem _ _ node.1 _ T hT

theorem support_unique (source : PairedLocalCircuit) (a : CopyNode 50) (ha : a ∈ domain source)
    (b : CopyNode 50) (hb : b ∈ domain source) (hc : a.1 = b.1)
    (he : support source a = support source b) : a = b := by
  have hi := additionIds_bound source.nodes a.2 ((mem_domain source a).mp ha)
  have hj := additionIds_bound source.nodes b.2 ((mem_domain source b).mp hb)
  have hs : source.support a.2 = source.support b.2 := by
    apply SharedPointLift.lift49_injective b.1
    simpa only [support, hc] using he
  rw [source.support_get a.2 hi, source.support_get b.2 hj] at hs
  have hs' : (source.nodes.map Node.support)[a.2]'(by simpa using hi) =
      (source.nodes.map Node.support)[b.2]'(by simpa using hj) := by simpa using hs
  exact Prod.ext hc (source.supports_nodup.getElem_inj.mp hs')

/-- The family consumed by duplicate matching and global allocation bounds. -/
def family (source : PairedLocalCircuit) : Family 50 :=
  ⟨domain source, support source, support_nontrivial source,
    support_common source, support_unique source⟩

/-- Exact semantic endpoint summaries establish a genuine duplicate without
any signature-row or mask-bank acceptance premise. -/
theorem witness_of_endpoints (source : PairedLocalCircuit) (a b : CopyNode 50)
    (ha : a ∈ domain source) (hb : b ∈ domain source) (hab : a.1 < b.1)
    (hn : (source.endpointCore a.2).Nonempty)
    (hcore : insert a.1 ((source.endpointCore a.2).image a.1.succAbove) =
      insert b.1 ((source.endpointCore b.2).image b.1.succAbove))
    (hunion : insert a.1 ((source.endpointUnion a.2).image a.1.succAbove) =
      insert b.1 ((source.endpointUnion b.2).image b.1.succAbove)) :
    IsWitness (family source) (a,b) := by
  refine ⟨ha, hb, hab, ?_⟩
  have hca := source.support_card_two a.2 ((mem_domain source a).mp ha)
  have hcb := source.support_card_two b.2 ((mem_domain source b).mp hb)
  apply SharedPointLift.equal_of_signatures _ _ a.1 b.1 (source.support a.2) (source.support b.2)
    (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
    (source.endpointCore a.2) (source.endpointUnion a.2)
    (source.endpointCore b.2) (source.endpointUnion b.2) rfl rfl rfl rfl hcore hunion
    (SharedPointLift.lifted_core_card a.1 _ hn)

end IntegerMultBounds.Networks.SharedPointLocalFamily
