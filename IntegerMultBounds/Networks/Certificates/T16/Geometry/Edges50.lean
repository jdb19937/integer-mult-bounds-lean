module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1600 : Fin frame430.rank → ℕ := ![11,4,16,32]
theorem edge1600_span : frame430.space ≤ frame682.space :=
  frame430.inclusion frame682 witness1600 (by decide)
def edge1600 : CertifiedEdge catalog where
  old := 430
  next := 682
  rank := 2
  good := by
    constructor
    · exact edge1600_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1601 : Fin frame430.rank → ℕ := ![11,4,16,32]
theorem edge1601_span : frame430.space ≤ frame683.space :=
  frame430.inclusion frame683 witness1601 (by decide)
def edge1601 : CertifiedEdge catalog where
  old := 430
  next := 683
  rank := 2
  good := by
    constructor
    · exact edge1601_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1602 : Fin frame430.rank → ℕ := ![37,2,40,16]
theorem edge1602_span : frame430.space ≤ frame684.space :=
  frame430.inclusion frame684 witness1602 (by decide)
def edge1602 : CertifiedEdge catalog where
  old := 430
  next := 684
  rank := 2
  good := by
    constructor
    · exact edge1602_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1603 : Fin frame430.rank → ℕ := ![37,2,8,48]
theorem edge1603_span : frame430.space ≤ frame685.space :=
  frame430.inclusion frame685 witness1603 (by decide)
def edge1603 : CertifiedEdge catalog where
  old := 430
  next := 685
  rank := 2
  good := by
    constructor
    · exact edge1603_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1604 : Fin frame431.rank → ℕ := ![1,2,36,8,48]
theorem edge1604_span : frame431.space ≤ frame670.space :=
  frame431.inclusion frame670 witness1604 (by decide)
def edge1604 : CertifiedEdge catalog where
  old := 431
  next := 670
  rank := 1
  good := by
    constructor
    · exact edge1604_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1605 : Fin frame431.rank → ℕ := ![1,2,4,40,48]
theorem edge1605_span : frame431.space ≤ frame671.space :=
  frame431.inclusion frame671 witness1605 (by decide)
def edge1605 : CertifiedEdge catalog where
  old := 431
  next := 671
  rank := 1
  good := by
    constructor
    · exact edge1605_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1606 : Fin frame431.rank → ℕ := ![1,2,36,40,48]
theorem edge1606_span : frame431.space ≤ frame672.space :=
  frame431.inclusion frame672 witness1606 (by decide)
def edge1606 : CertifiedEdge catalog where
  old := 431
  next := 672
  rank := 1
  good := by
    constructor
    · exact edge1606_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1607 : Fin frame431.rank → ℕ := ![1,2,36,40,48]
theorem edge1607_span : frame431.space ≤ frame673.space :=
  frame431.inclusion frame673 witness1607 (by decide)
def edge1607 : CertifiedEdge catalog where
  old := 431
  next := 673
  rank := 1
  good := by
    constructor
    · exact edge1607_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1608 : Fin frame431.rank → ℕ := ![1,2,36,40,48]
theorem edge1608_span : frame431.space ≤ frame674.space :=
  frame431.inclusion frame674 witness1608 (by decide)
def edge1608 : CertifiedEdge catalog where
  old := 431
  next := 674
  rank := 1
  good := by
    constructor
    · exact edge1608_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1609 : Fin frame431.rank → ℕ := ![1,2,36,40,48]
theorem edge1609_span : frame431.space ≤ frame675.space :=
  frame431.inclusion frame675 witness1609 (by decide)
def edge1609 : CertifiedEdge catalog where
  old := 431
  next := 675
  rank := 1
  good := by
    constructor
    · exact edge1609_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1610 : Fin frame431.rank → ℕ := ![1,2,4,40,48]
theorem edge1610_span : frame431.space ≤ frame676.space :=
  frame431.inclusion frame676 witness1610 (by decide)
def edge1610 : CertifiedEdge catalog where
  old := 431
  next := 676
  rank := 1
  good := by
    constructor
    · exact edge1610_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1611 : Fin frame431.rank → ℕ := ![1,2,36,8,48]
theorem edge1611_span : frame431.space ≤ frame677.space :=
  frame431.inclusion frame677 witness1611 (by decide)
def edge1611 : CertifiedEdge catalog where
  old := 431
  next := 677
  rank := 1
  good := by
    constructor
    · exact edge1611_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1612 : Fin frame432.rank → ℕ := ![3,4,8,16,32]
theorem edge1612_span : frame432.space ≤ frame662.space :=
  frame432.inclusion frame662 witness1612 (by decide)
def edge1612 : CertifiedEdge catalog where
  old := 432
  next := 662
  rank := 1
  good := by
    constructor
    · exact edge1612_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1613 : Fin frame432.rank → ℕ := ![3,4,8,16,32]
theorem edge1613_span : frame432.space ≤ frame663.space :=
  frame432.inclusion frame663 witness1613 (by decide)
def edge1613 : CertifiedEdge catalog where
  old := 432
  next := 663
  rank := 1
  good := by
    constructor
    · exact edge1613_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1614 : Fin frame432.rank → ℕ := ![33,2,4,40,16]
theorem edge1614_span : frame432.space ≤ frame664.space :=
  frame432.inclusion frame664 witness1614 (by decide)
def edge1614 : CertifiedEdge catalog where
  old := 432
  next := 664
  rank := 1
  good := by
    constructor
    · exact edge1614_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1615 : Fin frame432.rank → ℕ := ![33,34,4,8,16]
theorem edge1615_span : frame432.space ≤ frame665.space :=
  frame432.inclusion frame665 witness1615 (by decide)
def edge1615 : CertifiedEdge catalog where
  old := 432
  next := 665
  rank := 1
  good := by
    constructor
    · exact edge1615_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1616 : Fin frame432.rank → ℕ := ![3,4,8,16,32]
theorem edge1616_span : frame432.space ≤ frame666.space :=
  frame432.inclusion frame666 witness1616 (by decide)
def edge1616 : CertifiedEdge catalog where
  old := 432
  next := 666
  rank := 1
  good := by
    constructor
    · exact edge1616_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1617 : Fin frame432.rank → ℕ := ![3,4,8,16,32]
theorem edge1617_span : frame432.space ≤ frame667.space :=
  frame432.inclusion frame667 witness1617 (by decide)
def edge1617 : CertifiedEdge catalog where
  old := 432
  next := 667
  rank := 1
  good := by
    constructor
    · exact edge1617_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1618 : Fin frame432.rank → ℕ := ![33,2,36,8,16]
theorem edge1618_span : frame432.space ≤ frame668.space :=
  frame432.inclusion frame668 witness1618 (by decide)
def edge1618 : CertifiedEdge catalog where
  old := 432
  next := 668
  rank := 1
  good := by
    constructor
    · exact edge1618_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1619 : Fin frame432.rank → ℕ := ![33,34,4,8,16]
theorem edge1619_span : frame432.space ≤ frame669.space :=
  frame432.inclusion frame669 witness1619 (by decide)
def edge1619 : CertifiedEdge catalog where
  old := 432
  next := 669
  rank := 1
  good := by
    constructor
    · exact edge1619_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1620 : Fin frame433.rank → ℕ := ![9,10,4,16,32]
theorem edge1620_span : frame433.space ≤ frame638.space :=
  frame433.inclusion frame638 witness1620 (by decide)
def edge1620 : CertifiedEdge catalog where
  old := 433
  next := 638
  rank := 1
  good := by
    constructor
    · exact edge1620_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1621 : Fin frame433.rank → ℕ := ![33,2,4,40,16]
theorem edge1621_span : frame433.space ≤ frame639.space :=
  frame433.inclusion frame639 witness1621 (by decide)
def edge1621 : CertifiedEdge catalog where
  old := 433
  next := 639
  rank := 1
  good := by
    constructor
    · exact edge1621_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1622 : Fin frame433.rank → ℕ := ![3,4,8,16,32]
theorem edge1622_span : frame433.space ≤ frame640.space :=
  frame433.inclusion frame640 witness1622 (by decide)
def edge1622 : CertifiedEdge catalog where
  old := 433
  next := 640
  rank := 1
  good := by
    constructor
    · exact edge1622_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1623 : Fin frame433.rank → ℕ := ![3,4,8,16,32]
theorem edge1623_span : frame433.space ≤ frame641.space :=
  frame433.inclusion frame641 witness1623 (by decide)
def edge1623 : CertifiedEdge catalog where
  old := 433
  next := 641
  rank := 1
  good := by
    constructor
    · exact edge1623_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1624 : Fin frame433.rank → ℕ := ![9,10,4,16,32]
theorem edge1624_span : frame433.space ≤ frame642.space :=
  frame433.inclusion frame642 witness1624 (by decide)
def edge1624 : CertifiedEdge catalog where
  old := 433
  next := 642
  rank := 1
  good := by
    constructor
    · exact edge1624_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1625 : Fin frame433.rank → ℕ := ![9,2,12,16,32]
theorem edge1625_span : frame433.space ≤ frame643.space :=
  frame433.inclusion frame643 witness1625 (by decide)
def edge1625 : CertifiedEdge catalog where
  old := 433
  next := 643
  rank := 1
  good := by
    constructor
    · exact edge1625_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1626 : Fin frame433.rank → ℕ := ![3,4,8,16,32]
theorem edge1626_span : frame433.space ≤ frame644.space :=
  frame433.inclusion frame644 witness1626 (by decide)
def edge1626 : CertifiedEdge catalog where
  old := 433
  next := 644
  rank := 1
  good := by
    constructor
    · exact edge1626_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1627 : Fin frame433.rank → ℕ := ![3,4,8,16,32]
theorem edge1627_span : frame433.space ≤ frame645.space :=
  frame433.inclusion frame645 witness1627 (by decide)
def edge1627 : CertifiedEdge catalog where
  old := 433
  next := 645
  rank := 1
  good := by
    constructor
    · exact edge1627_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1628 : Fin frame434.rank → ℕ := ![17,18,4,8,32]
theorem edge1628_span : frame434.space ≤ frame646.space :=
  frame434.inclusion frame646 witness1628 (by decide)
def edge1628 : CertifiedEdge catalog where
  old := 434
  next := 646
  rank := 1
  good := by
    constructor
    · exact edge1628_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1629 : Fin frame434.rank → ℕ := ![1,2,36,40,48]
theorem edge1629_span : frame434.space ≤ frame647.space :=
  frame434.inclusion frame647 witness1629 (by decide)
def edge1629 : CertifiedEdge catalog where
  old := 434
  next := 647
  rank := 1
  good := by
    constructor
    · exact edge1629_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1630 : Fin frame434.rank → ℕ := ![17,18,4,8,32]
theorem edge1630_span : frame434.space ≤ frame648.space :=
  frame434.inclusion frame648 witness1630 (by decide)
def edge1630 : CertifiedEdge catalog where
  old := 434
  next := 648
  rank := 1
  good := by
    constructor
    · exact edge1630_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1631 : Fin frame434.rank → ℕ := ![1,2,36,8,48]
theorem edge1631_span : frame434.space ≤ frame649.space :=
  frame434.inclusion frame649 witness1631 (by decide)
def edge1631 : CertifiedEdge catalog where
  old := 434
  next := 649
  rank := 1
  good := by
    constructor
    · exact edge1631_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
