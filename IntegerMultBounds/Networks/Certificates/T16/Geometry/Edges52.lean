module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1664 : Fin frame440.rank → ℕ := ![2,4,8]
theorem edge1664_span : frame440.space ≤ frame443.space :=
  frame440.inclusion frame443 witness1664 (by decide)
def edge1664 : CertifiedEdge catalog where
  old := 440
  next := 443
  rank := 1
  good := by
    constructor
    · exact edge1664_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1665 : Fin frame440.rank → ℕ := ![6,72,112]
theorem edge1665_span : frame440.space ≤ frame449.space :=
  frame440.inclusion frame449 witness1665 (by decide)
def edge1665 : CertifiedEdge catalog where
  old := 440
  next := 449
  rank := 4
  good := by
    constructor
    · exact edge1665_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1666 : Fin frame441.rank → ℕ := ![1,18,20,40]
theorem edge1666_span : frame441.space ≤ frame446.space :=
  frame441.inclusion frame446 witness1666 (by decide)
def edge1666 : CertifiedEdge catalog where
  old := 441
  next := 446
  rank := 2
  good := by
    constructor
    · exact edge1666_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1667 : Fin frame441.rank → ℕ := ![1,2,4,56]
theorem edge1667_span : frame441.space ≤ frame450.space :=
  frame441.inclusion frame450 witness1667 (by decide)
def edge1667 : CertifiedEdge catalog where
  old := 441
  next := 450
  rank := 3
  good := by
    constructor
    · exact edge1667_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1668 : Fin frame442.rank → ℕ := ![3,36,40,16]
theorem edge1668_span : frame442.space ≤ frame445.space :=
  frame442.inclusion frame445 witness1668 (by decide)
def edge1668 : CertifiedEdge catalog where
  old := 442
  next := 445
  rank := 2
  good := by
    constructor
    · exact edge1668_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1669 : Fin frame442.rank → ℕ := ![7,72,80,32]
theorem edge1669_span : frame442.space ≤ frame452.space :=
  frame442.inclusion frame452 witness1669 (by decide)
def edge1669 : CertifiedEdge catalog where
  old := 442
  next := 452
  rank := 3
  good := by
    constructor
    · exact edge1669_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1670 : Fin frame443.rank → ℕ := ![1,2,36,56]
theorem edge1670_span : frame443.space ≤ frame444.space :=
  frame443.inclusion frame444 witness1670 (by decide)
def edge1670 : CertifiedEdge catalog where
  old := 443
  next := 444
  rank := 2
  good := by
    constructor
    · exact edge1670_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1671 : Fin frame443.rank → ℕ := ![21,22,8,96]
theorem edge1671_span : frame443.space ≤ frame447.space :=
  frame443.inclusion frame447 witness1671 (by decide)
def edge1671 : CertifiedEdge catalog where
  old := 443
  next := 447
  rank := 3
  good := by
    constructor
    · exact edge1671_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1672 : Fin frame444.rank → ℕ := ![9,10,4,16,32,64]
theorem edge1672_span : frame444.space ≤ frame448.space :=
  frame444.inclusion frame448 witness1672 (by decide)
def edge1672 : CertifiedEdge catalog where
  old := 444
  next := 448
  rank := 1
  good := by
    constructor
    · exact edge1672_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1673 : Fin frame444.rank → ℕ := ![5,6,8,16,32,64]
theorem edge1673_span : frame444.space ≤ frame452.space :=
  frame444.inclusion frame452 witness1673 (by decide)
def edge1673 : CertifiedEdge catalog where
  old := 444
  next := 452
  rank := 1
  good := by
    constructor
    · exact edge1673_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1674 : Fin frame445.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1674_span : frame445.space ≤ frame449.space :=
  frame445.inclusion frame449 witness1674 (by decide)
def edge1674 : CertifiedEdge catalog where
  old := 445
  next := 449
  rank := 1
  good := by
    constructor
    · exact edge1674_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1675 : Fin frame445.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1675_span : frame445.space ≤ frame450.space :=
  frame445.inclusion frame450 witness1675 (by decide)
def edge1675 : CertifiedEdge catalog where
  old := 445
  next := 450
  rank := 1
  good := by
    constructor
    · exact edge1675_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1676 : Fin frame446.rank → ℕ := ![1,2,4,40,16,64]
theorem edge1676_span : frame446.space ≤ frame447.space :=
  frame446.inclusion frame447 witness1676 (by decide)
def edge1676 : CertifiedEdge catalog where
  old := 446
  next := 447
  rank := 1
  good := by
    constructor
    · exact edge1676_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1677 : Fin frame446.rank → ℕ := ![1,2,4,40,16,64]
theorem edge1677_span : frame446.space ≤ frame451.space :=
  frame446.inclusion frame451 witness1677 (by decide)
def edge1677 : CertifiedEdge catalog where
  old := 446
  next := 451
  rank := 1
  good := by
    constructor
    · exact edge1677_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1678 : Fin frame447.rank → ℕ := ![1,2,4,392,16,288,448]
theorem edge1678_span : frame447.space ≤ frame1.space :=
  frame447.inclusion frame1 witness1678 (by decide)
def edge1678 : CertifiedEdge catalog where
  old := 447
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1678_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1679 : Fin frame447.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1679_span : frame447.space ≤ frame775.space :=
  frame447.inclusion frame775 witness1679 (by decide)
def edge1679 : CertifiedEdge catalog where
  old := 447
  next := 775
  rank := 1
  good := by
    constructor
    · exact edge1679_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1680 : Fin frame447.rank → ℕ := ![1,2,4,136,16,32,192]
theorem edge1680_span : frame447.space ≤ frame778.space :=
  frame447.inclusion frame778 witness1680 (by decide)
def edge1680 : CertifiedEdge catalog where
  old := 447
  next := 778
  rank := 1
  good := by
    constructor
    · exact edge1680_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1681 : Fin frame448.rank → ℕ := ![5,6,264,16,288,320,128]
theorem edge1681_span : frame448.space ≤ frame1.space :=
  frame448.inclusion frame1 witness1681 (by decide)
def edge1681 : CertifiedEdge catalog where
  old := 448
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1681_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1682 : Fin frame448.rank → ℕ := ![5,6,8,16,32,64,128]
theorem edge1682_span : frame448.space ≤ frame783.space :=
  frame448.inclusion frame783 witness1682 (by decide)
def edge1682 : CertifiedEdge catalog where
  old := 448
  next := 783
  rank := 1
  good := by
    constructor
    · exact edge1682_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1683 : Fin frame448.rank → ℕ := ![1,2,132,8,144,160,64]
theorem edge1683_span : frame448.space ≤ frame786.space :=
  frame448.inclusion frame786 witness1683 (by decide)
def edge1683 : CertifiedEdge catalog where
  old := 448
  next := 786
  rank := 1
  good := by
    constructor
    · exact edge1683_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1684 : Fin frame449.rank → ℕ := ![17,2,20,264,288,320,128]
theorem edge1684_span : frame449.space ≤ frame1.space :=
  frame449.inclusion frame1 witness1684 (by decide)
def edge1684 : CertifiedEdge catalog where
  old := 449
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1684_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1685 : Fin frame449.rank → ℕ := ![17,2,20,8,32,64,128]
theorem edge1685_span : frame449.space ≤ frame799.space :=
  frame449.inclusion frame799 witness1685 (by decide)
def edge1685 : CertifiedEdge catalog where
  old := 449
  next := 799
  rank := 1
  good := by
    constructor
    · exact edge1685_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1686 : Fin frame449.rank → ℕ := ![1,2,4,136,144,160,64]
theorem edge1686_span : frame449.space ≤ frame802.space :=
  frame449.inclusion frame802 witness1686 (by decide)
def edge1686 : CertifiedEdge catalog where
  old := 449
  next := 802
  rank := 1
  good := by
    constructor
    · exact edge1686_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1687 : Fin frame450.rank → ℕ := ![1,18,20,264,288,320,128]
theorem edge1687_span : frame450.space ≤ frame1.space :=
  frame450.inclusion frame1 witness1687 (by decide)
def edge1687 : CertifiedEdge catalog where
  old := 450
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1687_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1688 : Fin frame450.rank → ℕ := ![1,18,20,8,32,64,128]
theorem edge1688_span : frame450.space ≤ frame791.space :=
  frame450.inclusion frame791 witness1688 (by decide)
def edge1688 : CertifiedEdge catalog where
  old := 450
  next := 791
  rank := 1
  good := by
    constructor
    · exact edge1688_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1689 : Fin frame450.rank → ℕ := ![1,2,4,136,144,160,64]
theorem edge1689_span : frame450.space ≤ frame794.space :=
  frame450.inclusion frame794 witness1689 (by decide)
def edge1689 : CertifiedEdge catalog where
  old := 450
  next := 794
  rank := 1
  good := by
    constructor
    · exact edge1689_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1690 : Fin frame451.rank → ℕ := ![1,2,4,264,16,416,448]
theorem edge1690_span : frame451.space ≤ frame1.space :=
  frame451.inclusion frame1 witness1690 (by decide)
def edge1690 : CertifiedEdge catalog where
  old := 451
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1690_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1691 : Fin frame451.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1691_span : frame451.space ≤ frame815.space :=
  frame451.inclusion frame815 witness1691 (by decide)
def edge1691 : CertifiedEdge catalog where
  old := 451
  next := 815
  rank := 1
  good := by
    constructor
    · exact edge1691_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1692 : Fin frame451.rank → ℕ := ![1,2,4,8,16,160,192]
theorem edge1692_span : frame451.space ≤ frame818.space :=
  frame451.inclusion frame818 witness1692 (by decide)
def edge1692 : CertifiedEdge catalog where
  old := 451
  next := 818
  rank := 1
  good := by
    constructor
    · exact edge1692_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1693 : Fin frame452.rank → ℕ := ![17,18,4,264,288,320,128]
theorem edge1693_span : frame452.space ≤ frame1.space :=
  frame452.inclusion frame1 witness1693 (by decide)
def edge1693 : CertifiedEdge catalog where
  old := 452
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1693_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1694 : Fin frame452.rank → ℕ := ![17,18,4,8,32,64,128]
theorem edge1694_span : frame452.space ≤ frame807.space :=
  frame452.inclusion frame807 witness1694 (by decide)
def edge1694 : CertifiedEdge catalog where
  old := 452
  next := 807
  rank := 1
  good := by
    constructor
    · exact edge1694_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1695 : Fin frame452.rank → ℕ := ![1,2,4,136,144,160,64]
theorem edge1695_span : frame452.space ≤ frame810.space :=
  frame452.inclusion frame810 witness1695 (by decide)
def edge1695 : CertifiedEdge catalog where
  old := 452
  next := 810
  rank := 1
  good := by
    constructor
    · exact edge1695_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
