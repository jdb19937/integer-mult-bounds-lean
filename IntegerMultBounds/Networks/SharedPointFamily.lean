module

public import IntegerMultBounds.Networks.Paired49Certificate
public import IntegerMultBounds.Networks.SharedPointLift
public import IntegerMultBounds.Networks.SharedPointMatching
public import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DAGAdditionIds
public import IntegerMultBounds.Networks.SharedPointLocalFamily

/-! The actual fifty-copy family of certified local addition supports.
Its size is derived from the checked arithmetic count, without reducing a
large semantic finite set or assuming any duplicate-witness facts. -/

@[expose] public section

namespace IntegerMultBounds.Networks.SharedPointFamily

open DisjointCircuit SharedPointMatching

export DAGAdditionIds (isAddition isAddition_iff additionIds mem_additionIds
  additionIds_bound additionIds_card)

attribute [local irreducible] Paired49Certificate.nodes Certificates.Paired49.entries Certificates.Paired49.bank

/-- Each common point gets one copy of every certified local addition. -/
def domain : Finset (CopyNode 50) :=
  Finset.univ ×ˢ additionIds Paired49Certificate.nodes

/-- The actual source support at a local node; absent indices are empty. -/
def localSupport (i : ℕ) : Finset (Fin 1176) :=
  (Paired49Certificate.nodes[i]?.map Node.support).getD ∅

def support (node : CopyNode 50) : Finset (NeighborCounts.Triple 50) :=
  SharedPointLift.lift49 node.1 (localSupport node.2)

@[simp] theorem mem_domain (node : CopyNode 50) : node ∈ domain ↔ node.2 ∈ additionIds Paired49Certificate.nodes := by
  simp [domain]

theorem mem_domain_iff (node : CopyNode 50) : node ∈ domain ↔
    ∃ localNode, Paired49Certificate.nodes[node.2]? = some localNode ∧
      ∃ l r, localNode.kind = .add l r := by
  rw [mem_domain, mem_additionIds]

/-- Entry-level membership interface for the compact kind classifier. -/
theorem mem_domain_entries (node : CopyNode 50) : node ∈ domain ↔
    ∃ entry, Certificates.Paired49.entries[node.2]? = some entry ∧
      ∃ l r, entry.kind = .add l r := by
  rw [mem_domain_iff]
  simp only [Paired49Certificate.nodes, List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨localNode, ⟨entry, he, hn⟩, l, r, hk⟩
    subst localNode
    exact ⟨entry, he, l, r, hk⟩
  · rintro ⟨entry, he, l, r, hk⟩
    exact ⟨entry.toNode, ⟨entry, he, rfl⟩, l, r, hk⟩

theorem domain_bounds (node : CopyNode 50) (hn : node ∈ domain) : node.2 < 10989 := by
  have hh := additionIds_bound Paired49Certificate.nodes node.2 (mem_domain node |>.mp hn)
  rwa [Paired49Certificate.node_count] at hh

theorem localSupport_get (i : ℕ) (hi : i < Paired49Certificate.nodes.length) :
    localSupport i = Paired49Certificate.nodes[i].support := by
  simp [localSupport, List.getElem?_eq_getElem hi]

/-- The actual local support is the decoded checked static-bank mask. -/
theorem localSupport_bank (i : ℕ) (hi : i < 10989) :
    localSupport i = MaskDAG.decode ((Certificates.Paired49.bank.lookup i).getD 0) := by
  have hb := (MaskDAG.checkChunk_sound Certificates.Paired49.bank.lookup [] Certificates.Paired49.entries
    (by intro j hj; simp at hj) Certificates.Paired49.entries_checked).2 i
    (by simpa only [List.length_append, List.length_nil, zero_add, List.length_map,
      Certificates.Paired49.entries_length] using hi)
  simp only [List.nil_append, List.getElem?_map] at hb
  have he : (Paired49Certificate.nodes[i]?.map Node.support) =
      (Certificates.Paired49.bank.lookup i).map MaskDAG.decode := by
    rw [hb]
    simp only [Paired49Certificate.nodes, List.getElem?_map, Option.map_map,
      Function.comp_def, MaskDAG.Entry.toNode]
  rw [localSupport, he]
  cases Certificates.Paired49.bank.lookup i <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
  ext v
  simp [MaskDAG.decode]

theorem support_bank (node : CopyNode 50) (hi : node.2 < 10989) :
    support node = SharedPointLift.lift49 node.1
      (MaskDAG.decode ((Certificates.Paired49.bank.lookup node.2).getD 0)) := by
  rw [support, localSupport_bank node.2 hi]

theorem support_nontrivial (node : CopyNode 50) (hn : node ∈ domain) : 2 ≤ (support node).card :=
  SharedPointLocalFamily.support_nontrivial Paired49Certificate.implementation node hn

theorem support_common (node : CopyNode 50) (hn : node ∈ domain)
    (T : NeighborCounts.Triple 50) (hT : T ∈ support node) : node.1 ∈ T.val :=
  SharedPointLocalFamily.support_common Paired49Certificate.implementation node hn T hT

theorem support_unique (a : CopyNode 50) (ha : a ∈ domain) (b : CopyNode 50) (hb : b ∈ domain)
    (hc : a.1 = b.1) (he : support a = support b) : a = b :=
  SharedPointLocalFamily.support_unique Paired49Certificate.implementation a ha b hb hc he

/-- The main sharing argument consumes the implementation-independent family. -/
def family : Family 50 := SharedPointLocalFamily.family Paired49Certificate.implementation

/-- The unmerged fifty-copy family has exactly fifty times9813 additions. -/
theorem domain_card : domain.card = 50 * 9813 := by
  rw [domain, Finset.card_product, additionIds_card, Paired49Certificate.additions]
  simp

theorem family_domain_card : family.domain.card = 50 * 9813 := domain_card

end IntegerMultBounds.Networks.SharedPointFamily
