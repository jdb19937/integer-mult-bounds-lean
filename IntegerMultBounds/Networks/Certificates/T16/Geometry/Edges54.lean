module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1728 : Fin frame466.rank → ℕ := ![1,2,68,72,16,32,128]
theorem edge1728_span : frame466.space ≤ frame970.space :=
  frame466.inclusion frame970 witness1728 (by decide)
def edge1728 : CertifiedEdge catalog where
  old := 466
  next := 970
  rank := 1
  good := by
    constructor
    · exact edge1728_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1729 : Fin frame467.rank → ℕ := ![1,2,12]
theorem edge1729_span : frame467.space ≤ frame471.space :=
  frame467.inclusion frame471 witness1729 (by decide)
def edge1729 : CertifiedEdge catalog where
  old := 467
  next := 471
  rank := 1
  good := by
    constructor
    · exact edge1729_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1730 : Fin frame467.rank → ℕ := ![1,22,40]
theorem edge1730_span : frame467.space ≤ frame478.space :=
  frame467.inclusion frame478 witness1730 (by decide)
def edge1730 : CertifiedEdge catalog where
  old := 467
  next := 478
  rank := 4
  good := by
    constructor
    · exact edge1730_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1731 : Fin frame468.rank → ℕ := ![2,4,8]
theorem edge1731_span : frame468.space ≤ frame470.space :=
  frame468.inclusion frame470 witness1731 (by decide)
def edge1731 : CertifiedEdge catalog where
  old := 468
  next := 470
  rank := 1
  good := by
    constructor
    · exact edge1731_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1732 : Fin frame468.rank → ℕ := ![82,20,40]
theorem edge1732_span : frame468.space ≤ frame476.space :=
  frame468.inclusion frame476 witness1732 (by decide)
def edge1732 : CertifiedEdge catalog where
  old := 468
  next := 476
  rank := 4
  good := by
    constructor
    · exact edge1732_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1733 : Fin frame469.rank → ℕ := ![1,8,16]
theorem edge1733_span : frame469.space ≤ frame472.space :=
  frame469.inclusion frame472 witness1733 (by decide)
def edge1733 : CertifiedEdge catalog where
  old := 469
  next := 472
  rank := 2
  good := by
    constructor
    · exact edge1733_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1734 : Fin frame469.rank → ℕ := ![33,40,64]
theorem edge1734_span : frame469.space ≤ frame477.space :=
  frame469.inclusion frame477 witness1734 (by decide)
def edge1734 : CertifiedEdge catalog where
  old := 469
  next := 477
  rank := 4
  good := by
    constructor
    · exact edge1734_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1735 : Fin frame470.rank → ℕ := ![1,82,20,40]
theorem edge1735_span : frame470.space ≤ frame464.space :=
  frame470.inclusion frame464 witness1735 (by decide)
def edge1735 : CertifiedEdge catalog where
  old := 470
  next := 464
  rank := 3
  good := by
    constructor
    · exact edge1735_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1736 : Fin frame470.rank → ℕ := ![1,34,4,24]
theorem edge1736_span : frame470.space ≤ frame475.space :=
  frame470.inclusion frame475 witness1736 (by decide)
def edge1736 : CertifiedEdge catalog where
  old := 470
  next := 475
  rank := 2
  good := by
    constructor
    · exact edge1736_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1737 : Fin frame471.rank → ℕ := ![1,22,8,32]
theorem edge1737_span : frame471.space ≤ frame474.space :=
  frame471.inclusion frame474 witness1737 (by decide)
def edge1737 : CertifiedEdge catalog where
  old := 471
  next := 474
  rank := 2
  good := by
    constructor
    · exact edge1737_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1738 : Fin frame471.rank → ℕ := ![65,22,72,32]
theorem edge1738_span : frame471.space ≤ frame479.space :=
  frame471.inclusion frame479 witness1738 (by decide)
def edge1738 : CertifiedEdge catalog where
  old := 471
  next := 479
  rank := 3
  good := by
    constructor
    · exact edge1738_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1739 : Fin frame472.rank → ℕ := ![17,2,68,24,32]
theorem edge1739_span : frame472.space ≤ frame450.space :=
  frame472.inclusion frame450 witness1739 (by decide)
def edge1739 : CertifiedEdge catalog where
  old := 472
  next := 450
  rank := 2
  good := by
    constructor
    · exact edge1739_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1740 : Fin frame472.rank → ℕ := ![1,18,20,8,32]
theorem edge1740_span : frame472.space ≤ frame473.space :=
  frame472.inclusion frame473 witness1740 (by decide)
def edge1740 : CertifiedEdge catalog where
  old := 472
  next := 473
  rank := 1
  good := by
    constructor
    · exact edge1740_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1741 : Fin frame473.rank → ℕ := ![1,66,4,8,80,32]
theorem edge1741_span : frame473.space ≤ frame476.space :=
  frame473.inclusion frame476 witness1741 (by decide)
def edge1741 : CertifiedEdge catalog where
  old := 473
  next := 476
  rank := 1
  good := by
    constructor
    · exact edge1741_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1742 : Fin frame473.rank → ℕ := ![33,2,4,40,16,64]
theorem edge1742_span : frame473.space ≤ frame479.space :=
  frame473.inclusion frame479 witness1742 (by decide)
def edge1742 : CertifiedEdge catalog where
  old := 473
  next := 479
  rank := 1
  good := by
    constructor
    · exact edge1742_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1743 : Fin frame474.rank → ℕ := ![1,66,68,8,16,32]
theorem edge1743_span : frame474.space ≤ frame464.space :=
  frame474.inclusion frame464 witness1743 (by decide)
def edge1743 : CertifiedEdge catalog where
  old := 474
  next := 464
  rank := 1
  good := by
    constructor
    · exact edge1743_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1744 : Fin frame474.rank → ℕ := ![65,2,4,72,16,32]
theorem edge1744_span : frame474.space ≤ frame477.space :=
  frame474.inclusion frame477 witness1744 (by decide)
def edge1744 : CertifiedEdge catalog where
  old := 474
  next := 477
  rank := 1
  good := by
    constructor
    · exact edge1744_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1745 : Fin frame475.rank → ℕ := ![33,2,4,8,48,64]
theorem edge1745_span : frame475.space ≤ frame450.space :=
  frame475.inclusion frame450 witness1745 (by decide)
def edge1745 : CertifiedEdge catalog where
  old := 475
  next := 450
  rank := 1
  good := by
    constructor
    · exact edge1745_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1746 : Fin frame475.rank → ℕ := ![1,18,20,8,32,64]
theorem edge1746_span : frame475.space ≤ frame478.space :=
  frame475.inclusion frame478 witness1746 (by decide)
def edge1746 : CertifiedEdge catalog where
  old := 475
  next := 478
  rank := 1
  good := by
    constructor
    · exact edge1746_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1747 : Fin frame476.rank → ℕ := ![289,2,4,40,16,320,128]
theorem edge1747_span : frame476.space ≤ frame1.space :=
  frame476.inclusion frame1 witness1747 (by decide)
def edge1747 : CertifiedEdge catalog where
  old := 476
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1747_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1748 : Fin frame476.rank → ℕ := ![33,2,4,40,16,64,128]
theorem edge1748_span : frame476.space ≤ frame800.space :=
  frame476.inclusion frame800 witness1748 (by decide)
def edge1748 : CertifiedEdge catalog where
  old := 476
  next := 800
  rank := 1
  good := by
    constructor
    · exact edge1748_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1749 : Fin frame476.rank → ℕ := ![129,2,4,8,16,160,64]
theorem edge1749_span : frame476.space ≤ frame803.space :=
  frame476.inclusion frame803 witness1749 (by decide)
def edge1749 : CertifiedEdge catalog where
  old := 476
  next := 803
  rank := 1
  good := by
    constructor
    · exact edge1749_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1750 : Fin frame477.rank → ℕ := ![1,130,132,264,16,288,320]
theorem edge1750_span : frame477.space ≤ frame1.space :=
  frame477.inclusion frame1 witness1750 (by decide)
def edge1750 : CertifiedEdge catalog where
  old := 477
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1750_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1751 : Fin frame477.rank → ℕ := ![1,130,132,8,16,32,64]
theorem edge1751_span : frame477.space ≤ frame960.space :=
  frame477.inclusion frame960 witness1751 (by decide)
def edge1751 : CertifiedEdge catalog where
  old := 477
  next := 960
  rank := 1
  good := by
    constructor
    · exact edge1751_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1752 : Fin frame477.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1752_span : frame477.space ≤ frame963.space :=
  frame477.inclusion frame963 witness1752 (by decide)
def edge1752 : CertifiedEdge catalog where
  old := 477
  next := 963
  rank := 1
  good := by
    constructor
    · exact edge1752_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1753 : Fin frame478.rank → ℕ := ![321,2,4,264,16,96,128]
theorem edge1753_span : frame478.space ≤ frame1.space :=
  frame478.inclusion frame1 witness1753 (by decide)
def edge1753 : CertifiedEdge catalog where
  old := 478
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1753_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1754 : Fin frame478.rank → ℕ := ![129,2,4,136,16,32,64]
theorem edge1754_span : frame478.space ≤ frame991.space :=
  frame478.inclusion frame991 witness1754 (by decide)
def edge1754 : CertifiedEdge catalog where
  old := 478
  next := 991
  rank := 1
  good := by
    constructor
    · exact edge1754_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1755 : Fin frame478.rank → ℕ := ![65,2,4,8,16,96,128]
theorem edge1755_span : frame478.space ≤ frame994.space :=
  frame478.inclusion frame994 witness1755 (by decide)
def edge1755 : CertifiedEdge catalog where
  old := 478
  next := 994
  rank := 1
  good := by
    constructor
    · exact edge1755_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1756 : Fin frame479.rank → ℕ := ![1,130,4,264,144,288,320]
theorem edge1756_span : frame479.space ≤ frame1.space :=
  frame479.inclusion frame1 witness1756 (by decide)
def edge1756 : CertifiedEdge catalog where
  old := 479
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1756_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1757 : Fin frame479.rank → ℕ := ![1,130,4,8,144,32,64]
theorem edge1757_span : frame479.space ≤ frame983.space :=
  frame479.inclusion frame983 witness1757 (by decide)
def edge1757 : CertifiedEdge catalog where
  old := 479
  next := 983
  rank := 1
  good := by
    constructor
    · exact edge1757_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1758 : Fin frame479.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1758_span : frame479.space ≤ frame986.space :=
  frame479.inclusion frame986 witness1758 (by decide)
def edge1758 : CertifiedEdge catalog where
  old := 479
  next := 986
  rank := 1
  good := by
    constructor
    · exact edge1758_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1759 : Fin frame480.rank → ℕ := ![3,4,8]
theorem edge1759_span : frame480.space ≤ frame484.space :=
  frame480.inclusion frame484 witness1759 (by decide)
def edge1759 : CertifiedEdge catalog where
  old := 480
  next := 484
  rank := 1
  good := by
    constructor
    · exact edge1759_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
