module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1632 : Fin frame434.rank → ℕ := ![17,18,4,8,32]
theorem edge1632_span : frame434.space ≤ frame650.space :=
  frame434.inclusion frame650 witness1632 (by decide)
def edge1632 : CertifiedEdge catalog where
  old := 434
  next := 650
  rank := 1
  good := by
    constructor
    · exact edge1632_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1633 : Fin frame434.rank → ℕ := ![1,2,20,24,32]
theorem edge1633_span : frame434.space ≤ frame651.space :=
  frame434.inclusion frame651 witness1633 (by decide)
def edge1633 : CertifiedEdge catalog where
  old := 434
  next := 651
  rank := 1
  good := by
    constructor
    · exact edge1633_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1634 : Fin frame434.rank → ℕ := ![17,18,4,8,32]
theorem edge1634_span : frame434.space ≤ frame652.space :=
  frame434.inclusion frame652 witness1634 (by decide)
def edge1634 : CertifiedEdge catalog where
  old := 434
  next := 652
  rank := 1
  good := by
    constructor
    · exact edge1634_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1635 : Fin frame434.rank → ℕ := ![1,2,20,24,32]
theorem edge1635_span : frame434.space ≤ frame653.space :=
  frame434.inclusion frame653 witness1635 (by decide)
def edge1635 : CertifiedEdge catalog where
  old := 434
  next := 653
  rank := 1
  good := by
    constructor
    · exact edge1635_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1636 : Fin frame435.rank → ℕ := ![5,6,8,16]
theorem edge1636_span : frame435.space ≤ frame630.space :=
  frame435.inclusion frame630 witness1636 (by decide)
def edge1636 : CertifiedEdge catalog where
  old := 435
  next := 630
  rank := 1
  good := by
    constructor
    · exact edge1636_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1637 : Fin frame435.rank → ℕ := ![1,2,20,24]
theorem edge1637_span : frame435.space ≤ frame631.space :=
  frame435.inclusion frame631 witness1637 (by decide)
def edge1637 : CertifiedEdge catalog where
  old := 435
  next := 631
  rank := 1
  good := by
    constructor
    · exact edge1637_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1638 : Fin frame435.rank → ℕ := ![1,2,20,8]
theorem edge1638_span : frame435.space ≤ frame632.space :=
  frame435.inclusion frame632 witness1638 (by decide)
def edge1638 : CertifiedEdge catalog where
  old := 435
  next := 632
  rank := 1
  good := by
    constructor
    · exact edge1638_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1639 : Fin frame435.rank → ℕ := ![5,6,8,16]
theorem edge1639_span : frame435.space ≤ frame633.space :=
  frame435.inclusion frame633 witness1639 (by decide)
def edge1639 : CertifiedEdge catalog where
  old := 435
  next := 633
  rank := 1
  good := by
    constructor
    · exact edge1639_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1640 : Fin frame435.rank → ℕ := ![5,6,8,16]
theorem edge1640_span : frame435.space ≤ frame634.space :=
  frame435.inclusion frame634 witness1640 (by decide)
def edge1640 : CertifiedEdge catalog where
  old := 435
  next := 634
  rank := 1
  good := by
    constructor
    · exact edge1640_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1641 : Fin frame435.rank → ℕ := ![1,2,20,24]
theorem edge1641_span : frame435.space ≤ frame635.space :=
  frame435.inclusion frame635 witness1641 (by decide)
def edge1641 : CertifiedEdge catalog where
  old := 435
  next := 635
  rank := 1
  good := by
    constructor
    · exact edge1641_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1642 : Fin frame435.rank → ℕ := ![1,2,20,24]
theorem edge1642_span : frame435.space ≤ frame636.space :=
  frame435.inclusion frame636 witness1642 (by decide)
def edge1642 : CertifiedEdge catalog where
  old := 435
  next := 636
  rank := 1
  good := by
    constructor
    · exact edge1642_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1643 : Fin frame435.rank → ℕ := ![5,6,8,16]
theorem edge1643_span : frame435.space ≤ frame637.space :=
  frame435.inclusion frame637 witness1643 (by decide)
def edge1643 : CertifiedEdge catalog where
  old := 435
  next := 637
  rank := 1
  good := by
    constructor
    · exact edge1643_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1644 : Fin frame436.rank → ℕ := ![1,2,20,24,32]
theorem edge1644_span : frame436.space ≤ frame686.space :=
  frame436.inclusion frame686 witness1644 (by decide)
def edge1644 : CertifiedEdge catalog where
  old := 436
  next := 686
  rank := 1
  good := by
    constructor
    · exact edge1644_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1645 : Fin frame436.rank → ℕ := ![9,10,4,16,32]
theorem edge1645_span : frame436.space ≤ frame687.space :=
  frame436.inclusion frame687 witness1645 (by decide)
def edge1645 : CertifiedEdge catalog where
  old := 436
  next := 687
  rank := 1
  good := by
    constructor
    · exact edge1645_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1646 : Fin frame436.rank → ℕ := ![9,10,4,16,32]
theorem edge1646_span : frame436.space ≤ frame688.space :=
  frame436.inclusion frame688 witness1646 (by decide)
def edge1646 : CertifiedEdge catalog where
  old := 436
  next := 688
  rank := 1
  good := by
    constructor
    · exact edge1646_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1647 : Fin frame436.rank → ℕ := ![1,2,20,24,32]
theorem edge1647_span : frame436.space ≤ frame689.space :=
  frame436.inclusion frame689 witness1647 (by decide)
def edge1647 : CertifiedEdge catalog where
  old := 436
  next := 689
  rank := 1
  good := by
    constructor
    · exact edge1647_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1648 : Fin frame436.rank → ℕ := ![1,2,36,8,48]
theorem edge1648_span : frame436.space ≤ frame690.space :=
  frame436.inclusion frame690 witness1648 (by decide)
def edge1648 : CertifiedEdge catalog where
  old := 436
  next := 690
  rank := 1
  good := by
    constructor
    · exact edge1648_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1649 : Fin frame436.rank → ℕ := ![9,10,4,16,32]
theorem edge1649_span : frame436.space ≤ frame691.space :=
  frame436.inclusion frame691 witness1649 (by decide)
def edge1649 : CertifiedEdge catalog where
  old := 436
  next := 691
  rank := 1
  good := by
    constructor
    · exact edge1649_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1650 : Fin frame436.rank → ℕ := ![9,10,4,16,32]
theorem edge1650_span : frame436.space ≤ frame692.space :=
  frame436.inclusion frame692 witness1650 (by decide)
def edge1650 : CertifiedEdge catalog where
  old := 436
  next := 692
  rank := 1
  good := by
    constructor
    · exact edge1650_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1651 : Fin frame436.rank → ℕ := ![1,2,36,8,48]
theorem edge1651_span : frame436.space ≤ frame693.space :=
  frame436.inclusion frame693 witness1651 (by decide)
def edge1651 : CertifiedEdge catalog where
  old := 436
  next := 693
  rank := 1
  good := by
    constructor
    · exact edge1651_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1652 : Fin frame437.rank → ℕ := ![1,2,36,8,48]
theorem edge1652_span : frame437.space ≤ frame654.space :=
  frame437.inclusion frame654 witness1652 (by decide)
def edge1652 : CertifiedEdge catalog where
  old := 437
  next := 654
  rank := 1
  good := by
    constructor
    · exact edge1652_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1653 : Fin frame437.rank → ℕ := ![33,34,4,8,16]
theorem edge1653_span : frame437.space ≤ frame655.space :=
  frame437.inclusion frame655 witness1653 (by decide)
def edge1653 : CertifiedEdge catalog where
  old := 437
  next := 655
  rank := 1
  good := by
    constructor
    · exact edge1653_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1654 : Fin frame437.rank → ℕ := ![1,2,36,40,48]
theorem edge1654_span : frame437.space ≤ frame656.space :=
  frame437.inclusion frame656 witness1654 (by decide)
def edge1654 : CertifiedEdge catalog where
  old := 437
  next := 656
  rank := 1
  good := by
    constructor
    · exact edge1654_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1655 : Fin frame437.rank → ℕ := ![1,2,36,40,48]
theorem edge1655_span : frame437.space ≤ frame657.space :=
  frame437.inclusion frame657 witness1655 (by decide)
def edge1655 : CertifiedEdge catalog where
  old := 437
  next := 657
  rank := 1
  good := by
    constructor
    · exact edge1655_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1656 : Fin frame437.rank → ℕ := ![1,2,36,40,48]
theorem edge1656_span : frame437.space ≤ frame658.space :=
  frame437.inclusion frame658 witness1656 (by decide)
def edge1656 : CertifiedEdge catalog where
  old := 437
  next := 658
  rank := 1
  good := by
    constructor
    · exact edge1656_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1657 : Fin frame437.rank → ℕ := ![1,2,36,40,48]
theorem edge1657_span : frame437.space ≤ frame659.space :=
  frame437.inclusion frame659 witness1657 (by decide)
def edge1657 : CertifiedEdge catalog where
  old := 437
  next := 659
  rank := 1
  good := by
    constructor
    · exact edge1657_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1658 : Fin frame437.rank → ℕ := ![33,34,4,8,16]
theorem edge1658_span : frame437.space ≤ frame660.space :=
  frame437.inclusion frame660 witness1658 (by decide)
def edge1658 : CertifiedEdge catalog where
  old := 437
  next := 660
  rank := 1
  good := by
    constructor
    · exact edge1658_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1659 : Fin frame437.rank → ℕ := ![1,2,36,40,16]
theorem edge1659_span : frame437.space ≤ frame661.space :=
  frame437.inclusion frame661 witness1659 (by decide)
def edge1659 : CertifiedEdge catalog where
  old := 437
  next := 661
  rank := 1
  good := by
    constructor
    · exact edge1659_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1660 : Fin frame438.rank → ℕ := ![1,10,4]
theorem edge1660_span : frame438.space ≤ frame442.space :=
  frame438.inclusion frame442 witness1660 (by decide)
def edge1660 : CertifiedEdge catalog where
  old := 438
  next := 442
  rank := 1
  good := by
    constructor
    · exact edge1660_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1661 : Fin frame438.rank → ℕ := ![7,72,32]
theorem edge1661_span : frame438.space ≤ frame451.space :=
  frame438.inclusion frame451 witness1661 (by decide)
def edge1661 : CertifiedEdge catalog where
  old := 438
  next := 451
  rank := 4
  good := by
    constructor
    · exact edge1661_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1662 : Fin frame439.rank → ℕ := ![5,6,8]
theorem edge1662_span : frame439.space ≤ frame441.space :=
  frame439.inclusion frame441 witness1662 (by decide)
def edge1662 : CertifiedEdge catalog where
  old := 439
  next := 441
  rank := 1
  good := by
    constructor
    · exact edge1662_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1663 : Fin frame439.rank → ℕ := ![9,2,52]
theorem edge1663_span : frame439.space ≤ frame448.space :=
  frame439.inclusion frame448 witness1663 (by decide)
def edge1663 : CertifiedEdge catalog where
  old := 439
  next := 448
  rank := 4
  good := by
    constructor
    · exact edge1663_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
