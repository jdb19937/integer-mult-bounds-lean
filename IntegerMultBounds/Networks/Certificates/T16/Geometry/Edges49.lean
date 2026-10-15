module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1568 : Fin frame426.rank → ℕ := ![3,4,8,16]
theorem edge1568_span : frame426.space ≤ frame738.space :=
  frame426.inclusion frame738 witness1568 (by decide)
def edge1568 : CertifiedEdge catalog where
  old := 426
  next := 738
  rank := 1
  good := by
    constructor
    · exact edge1568_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1569 : Fin frame426.rank → ℕ := ![3,4,8,16]
theorem edge1569_span : frame426.space ≤ frame739.space :=
  frame426.inclusion frame739 witness1569 (by decide)
def edge1569 : CertifiedEdge catalog where
  old := 426
  next := 739
  rank := 1
  good := by
    constructor
    · exact edge1569_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1570 : Fin frame426.rank → ℕ := ![3,4,8,16]
theorem edge1570_span : frame426.space ≤ frame740.space :=
  frame426.inclusion frame740 witness1570 (by decide)
def edge1570 : CertifiedEdge catalog where
  old := 426
  next := 740
  rank := 1
  good := by
    constructor
    · exact edge1570_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1571 : Fin frame426.rank → ℕ := ![3,4,8,16]
theorem edge1571_span : frame426.space ≤ frame741.space :=
  frame426.inclusion frame741 witness1571 (by decide)
def edge1571 : CertifiedEdge catalog where
  old := 426
  next := 741
  rank := 1
  good := by
    constructor
    · exact edge1571_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1572 : Fin frame427.rank → ℕ := ![33,34,20,8]
theorem edge1572_span : frame427.space ≤ frame726.space :=
  frame427.inclusion frame726 witness1572 (by decide)
def edge1572 : CertifiedEdge catalog where
  old := 427
  next := 726
  rank := 2
  good := by
    constructor
    · exact edge1572_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1573 : Fin frame427.rank → ℕ := ![1,2,52,40]
theorem edge1573_span : frame427.space ≤ frame727.space :=
  frame427.inclusion frame727 witness1573 (by decide)
def edge1573 : CertifiedEdge catalog where
  old := 427
  next := 727
  rank := 2
  good := by
    constructor
    · exact edge1573_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1574 : Fin frame427.rank → ℕ := ![1,2,20,40]
theorem edge1574_span : frame427.space ≤ frame728.space :=
  frame427.inclusion frame728 witness1574 (by decide)
def edge1574 : CertifiedEdge catalog where
  old := 427
  next := 728
  rank := 2
  good := by
    constructor
    · exact edge1574_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1575 : Fin frame427.rank → ℕ := ![1,2,20,40]
theorem edge1575_span : frame427.space ≤ frame729.space :=
  frame427.inclusion frame729 witness1575 (by decide)
def edge1575 : CertifiedEdge catalog where
  old := 427
  next := 729
  rank := 2
  good := by
    constructor
    · exact edge1575_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1576 : Fin frame427.rank → ℕ := ![1,2,20,40]
theorem edge1576_span : frame427.space ≤ frame730.space :=
  frame427.inclusion frame730 witness1576 (by decide)
def edge1576 : CertifiedEdge catalog where
  old := 427
  next := 730
  rank := 2
  good := by
    constructor
    · exact edge1576_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1577 : Fin frame427.rank → ℕ := ![1,2,20,40]
theorem edge1577_span : frame427.space ≤ frame731.space :=
  frame427.inclusion frame731 witness1577 (by decide)
def edge1577 : CertifiedEdge catalog where
  old := 427
  next := 731
  rank := 2
  good := by
    constructor
    · exact edge1577_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1578 : Fin frame427.rank → ℕ := ![1,2,52,40]
theorem edge1578_span : frame427.space ≤ frame732.space :=
  frame427.inclusion frame732 witness1578 (by decide)
def edge1578 : CertifiedEdge catalog where
  old := 427
  next := 732
  rank := 2
  good := by
    constructor
    · exact edge1578_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1579 : Fin frame427.rank → ℕ := ![1,2,52,40]
theorem edge1579_span : frame427.space ≤ frame733.space :=
  frame427.inclusion frame733 witness1579 (by decide)
def edge1579 : CertifiedEdge catalog where
  old := 427
  next := 733
  rank := 2
  good := by
    constructor
    · exact edge1579_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1580 : Fin frame428.rank → ℕ := ![1,2,52,24]
theorem edge1580_span : frame428.space ≤ frame702.space :=
  frame428.inclusion frame702 witness1580 (by decide)
def edge1580 : CertifiedEdge catalog where
  old := 428
  next := 702
  rank := 2
  good := by
    constructor
    · exact edge1580_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1581 : Fin frame428.rank → ℕ := ![17,18,36,8]
theorem edge1581_span : frame428.space ≤ frame703.space :=
  frame428.inclusion frame703 witness1581 (by decide)
def edge1581 : CertifiedEdge catalog where
  old := 428
  next := 703
  rank := 2
  good := by
    constructor
    · exact edge1581_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1582 : Fin frame428.rank → ℕ := ![17,18,36,8]
theorem edge1582_span : frame428.space ≤ frame704.space :=
  frame428.inclusion frame704 witness1582 (by decide)
def edge1582 : CertifiedEdge catalog where
  old := 428
  next := 704
  rank := 2
  good := by
    constructor
    · exact edge1582_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1583 : Fin frame428.rank → ℕ := ![1,2,52,24]
theorem edge1583_span : frame428.space ≤ frame705.space :=
  frame428.inclusion frame705 witness1583 (by decide)
def edge1583 : CertifiedEdge catalog where
  old := 428
  next := 705
  rank := 2
  good := by
    constructor
    · exact edge1583_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1584 : Fin frame428.rank → ℕ := ![1,2,52,24]
theorem edge1584_span : frame428.space ≤ frame706.space :=
  frame428.inclusion frame706 witness1584 (by decide)
def edge1584 : CertifiedEdge catalog where
  old := 428
  next := 706
  rank := 2
  good := by
    constructor
    · exact edge1584_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1585 : Fin frame428.rank → ℕ := ![1,2,52,40]
theorem edge1585_span : frame428.space ≤ frame707.space :=
  frame428.inclusion frame707 witness1585 (by decide)
def edge1585 : CertifiedEdge catalog where
  old := 428
  next := 707
  rank := 2
  good := by
    constructor
    · exact edge1585_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1586 : Fin frame428.rank → ℕ := ![1,2,20,40]
theorem edge1586_span : frame428.space ≤ frame708.space :=
  frame428.inclusion frame708 witness1586 (by decide)
def edge1586 : CertifiedEdge catalog where
  old := 428
  next := 708
  rank := 2
  good := by
    constructor
    · exact edge1586_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1587 : Fin frame428.rank → ℕ := ![1,2,52,24]
theorem edge1587_span : frame428.space ≤ frame709.space :=
  frame428.inclusion frame709 witness1587 (by decide)
def edge1587 : CertifiedEdge catalog where
  old := 428
  next := 709
  rank := 2
  good := by
    constructor
    · exact edge1587_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1588 : Fin frame429.rank → ℕ := ![35,4,8,16]
theorem edge1588_span : frame429.space ≤ frame694.space :=
  frame429.inclusion frame694 witness1588 (by decide)
def edge1588 : CertifiedEdge catalog where
  old := 429
  next := 694
  rank := 2
  good := by
    constructor
    · exact edge1588_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1589 : Fin frame429.rank → ℕ := ![35,4,8,16]
theorem edge1589_span : frame429.space ≤ frame695.space :=
  frame429.inclusion frame695 witness1589 (by decide)
def edge1589 : CertifiedEdge catalog where
  old := 429
  next := 695
  rank := 2
  good := by
    constructor
    · exact edge1589_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1590 : Fin frame429.rank → ℕ := ![41,2,12,16]
theorem edge1590_span : frame429.space ≤ frame696.space :=
  frame429.inclusion frame696 witness1590 (by decide)
def edge1590 : CertifiedEdge catalog where
  old := 429
  next := 696
  rank := 2
  good := by
    constructor
    · exact edge1590_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1591 : Fin frame429.rank → ℕ := ![37,6,8,16]
theorem edge1591_span : frame429.space ≤ frame697.space :=
  frame429.inclusion frame697 witness1591 (by decide)
def edge1591 : CertifiedEdge catalog where
  old := 429
  next := 697
  rank := 2
  good := by
    constructor
    · exact edge1591_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1592 : Fin frame429.rank → ℕ := ![35,4,8,16]
theorem edge1592_span : frame429.space ≤ frame698.space :=
  frame429.inclusion frame698 witness1592 (by decide)
def edge1592 : CertifiedEdge catalog where
  old := 429
  next := 698
  rank := 2
  good := by
    constructor
    · exact edge1592_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1593 : Fin frame429.rank → ℕ := ![35,4,8,16]
theorem edge1593_span : frame429.space ≤ frame699.space :=
  frame429.inclusion frame699 witness1593 (by decide)
def edge1593 : CertifiedEdge catalog where
  old := 429
  next := 699
  rank := 2
  good := by
    constructor
    · exact edge1593_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1594 : Fin frame429.rank → ℕ := ![49,2,4,24]
theorem edge1594_span : frame429.space ≤ frame700.space :=
  frame429.inclusion frame700 witness1594 (by decide)
def edge1594 : CertifiedEdge catalog where
  old := 429
  next := 700
  rank := 2
  good := by
    constructor
    · exact edge1594_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1595 : Fin frame429.rank → ℕ := ![37,6,8,16]
theorem edge1595_span : frame429.space ≤ frame701.space :=
  frame429.inclusion frame701 witness1595 (by decide)
def edge1595 : CertifiedEdge catalog where
  old := 429
  next := 701
  rank := 2
  good := by
    constructor
    · exact edge1595_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1596 : Fin frame430.rank → ℕ := ![11,4,16,32]
theorem edge1596_span : frame430.space ≤ frame678.space :=
  frame430.inclusion frame678 witness1596 (by decide)
def edge1596 : CertifiedEdge catalog where
  old := 430
  next := 678
  rank := 2
  good := by
    constructor
    · exact edge1596_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1597 : Fin frame430.rank → ℕ := ![11,4,16,32]
theorem edge1597_span : frame430.space ≤ frame679.space :=
  frame430.inclusion frame679 witness1597 (by decide)
def edge1597 : CertifiedEdge catalog where
  old := 430
  next := 679
  rank := 2
  good := by
    constructor
    · exact edge1597_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1598 : Fin frame430.rank → ℕ := ![37,2,40,16]
theorem edge1598_span : frame430.space ≤ frame680.space :=
  frame430.inclusion frame680 witness1598 (by decide)
def edge1598 : CertifiedEdge catalog where
  old := 430
  next := 680
  rank := 2
  good := by
    constructor
    · exact edge1598_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1599 : Fin frame430.rank → ℕ := ![37,2,8,48]
theorem edge1599_span : frame430.space ≤ frame681.space :=
  frame430.inclusion frame681 witness1599 (by decide)
def edge1599 : CertifiedEdge catalog where
  old := 430
  next := 681
  rank := 2
  good := by
    constructor
    · exact edge1599_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
