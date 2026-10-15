module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1536 : Fin frame423.rank → ℕ := ![2]
theorem edge1536_span : frame423.space ≤ frame336.space :=
  frame423.inclusion frame336 witness1536 (by decide)
def edge1536 : CertifiedEdge catalog where
  old := 423
  next := 336
  rank := 1
  good := by
    constructor
    · exact edge1536_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1537 : Fin frame423.rank → ℕ := ![2]
theorem edge1537_span : frame423.space ≤ frame347.space :=
  frame423.inclusion frame347 witness1537 (by decide)
def edge1537 : CertifiedEdge catalog where
  old := 423
  next := 347
  rank := 1
  good := by
    constructor
    · exact edge1537_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1538 : Fin frame423.rank → ℕ := ![2]
theorem edge1538_span : frame423.space ≤ frame365.space :=
  frame423.inclusion frame365 witness1538 (by decide)
def edge1538 : CertifiedEdge catalog where
  old := 423
  next := 365
  rank := 1
  good := by
    constructor
    · exact edge1538_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1539 : Fin frame423.rank → ℕ := ![1]
theorem edge1539_span : frame423.space ≤ frame376.space :=
  frame423.inclusion frame376 witness1539 (by decide)
def edge1539 : CertifiedEdge catalog where
  old := 423
  next := 376
  rank := 1
  good := by
    constructor
    · exact edge1539_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1540 : Fin frame423.rank → ℕ := ![2]
theorem edge1540_span : frame423.space ≤ frame394.space :=
  frame423.inclusion frame394 witness1540 (by decide)
def edge1540 : CertifiedEdge catalog where
  old := 423
  next := 394
  rank := 1
  good := by
    constructor
    · exact edge1540_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1541 : Fin frame423.rank → ℕ := ![2]
theorem edge1541_span : frame423.space ≤ frame405.space :=
  frame423.inclusion frame405 witness1541 (by decide)
def edge1541 : CertifiedEdge catalog where
  old := 423
  next := 405
  rank := 1
  good := by
    constructor
    · exact edge1541_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1542 : Fin frame423.rank → ℕ := ![12]
theorem edge1542_span : frame423.space ≤ frame425.space :=
  frame423.inclusion frame425 witness1542 (by decide)
def edge1542 : CertifiedEdge catalog where
  old := 423
  next := 425
  rank := 3
  good := by
    constructor
    · exact edge1542_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1543 : Fin frame423.rank → ℕ := ![10]
theorem edge1543_span : frame423.space ≤ frame426.space :=
  frame423.inclusion frame426 witness1543 (by decide)
def edge1543 : CertifiedEdge catalog where
  old := 423
  next := 426
  rank := 3
  good := by
    constructor
    · exact edge1543_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1544 : Fin frame423.rank → ℕ := ![8]
theorem edge1544_span : frame423.space ≤ frame427.space :=
  frame423.inclusion frame427 witness1544 (by decide)
def edge1544 : CertifiedEdge catalog where
  old := 423
  next := 427
  rank := 3
  good := by
    constructor
    · exact edge1544_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1545 : Fin frame423.rank → ℕ := ![12]
theorem edge1545_span : frame423.space ≤ frame433.space :=
  frame423.inclusion frame433 witness1545 (by decide)
def edge1545 : CertifiedEdge catalog where
  old := 423
  next := 433
  rank := 4
  good := by
    constructor
    · exact edge1545_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1546 : Fin frame423.rank → ℕ := ![24]
theorem edge1546_span : frame423.space ≤ frame434.space :=
  frame423.inclusion frame434 witness1546 (by decide)
def edge1546 : CertifiedEdge catalog where
  old := 423
  next := 434
  rank := 4
  good := by
    constructor
    · exact edge1546_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1547 : Fin frame423.rank → ℕ := ![4]
theorem edge1547_span : frame423.space ≤ frame435.space :=
  frame423.inclusion frame435 witness1547 (by decide)
def edge1547 : CertifiedEdge catalog where
  old := 423
  next := 435
  rank := 3
  good := by
    constructor
    · exact edge1547_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1548 : Fin frame424.rank → ℕ := ![19,4,8,32]
theorem edge1548_span : frame424.space ≤ frame710.space :=
  frame424.inclusion frame710 witness1548 (by decide)
def edge1548 : CertifiedEdge catalog where
  old := 424
  next := 710
  rank := 2
  good := by
    constructor
    · exact edge1548_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1549 : Fin frame424.rank → ℕ := ![19,4,8,32]
theorem edge1549_span : frame424.space ≤ frame711.space :=
  frame424.inclusion frame711 witness1549 (by decide)
def edge1549 : CertifiedEdge catalog where
  old := 424
  next := 711
  rank := 2
  good := by
    constructor
    · exact edge1549_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1550 : Fin frame424.rank → ℕ := ![25,2,12,32]
theorem edge1550_span : frame424.space ≤ frame712.space :=
  frame424.inclusion frame712 witness1550 (by decide)
def edge1550 : CertifiedEdge catalog where
  old := 424
  next := 712
  rank := 2
  good := by
    constructor
    · exact edge1550_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1551 : Fin frame424.rank → ℕ := ![25,10,4,32]
theorem edge1551_span : frame424.space ≤ frame713.space :=
  frame424.inclusion frame713 witness1551 (by decide)
def edge1551 : CertifiedEdge catalog where
  old := 424
  next := 713
  rank := 2
  good := by
    constructor
    · exact edge1551_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1552 : Fin frame424.rank → ℕ := ![19,4,8,32]
theorem edge1552_span : frame424.space ≤ frame714.space :=
  frame424.inclusion frame714 witness1552 (by decide)
def edge1552 : CertifiedEdge catalog where
  old := 424
  next := 714
  rank := 2
  good := by
    constructor
    · exact edge1552_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1553 : Fin frame424.rank → ℕ := ![19,4,8,32]
theorem edge1553_span : frame424.space ≤ frame715.space :=
  frame424.inclusion frame715 witness1553 (by decide)
def edge1553 : CertifiedEdge catalog where
  old := 424
  next := 715
  rank := 2
  good := by
    constructor
    · exact edge1553_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1554 : Fin frame424.rank → ℕ := ![25,2,12,32]
theorem edge1554_span : frame424.space ≤ frame716.space :=
  frame424.inclusion frame716 witness1554 (by decide)
def edge1554 : CertifiedEdge catalog where
  old := 424
  next := 716
  rank := 2
  good := by
    constructor
    · exact edge1554_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1555 : Fin frame424.rank → ℕ := ![41,2,4,48]
theorem edge1555_span : frame424.space ≤ frame717.space :=
  frame424.inclusion frame717 witness1555 (by decide)
def edge1555 : CertifiedEdge catalog where
  old := 424
  next := 717
  rank := 2
  good := by
    constructor
    · exact edge1555_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1556 : Fin frame425.rank → ℕ := ![41,34,4,16]
theorem edge1556_span : frame425.space ≤ frame718.space :=
  frame425.inclusion frame718 witness1556 (by decide)
def edge1556 : CertifiedEdge catalog where
  old := 425
  next := 718
  rank := 2
  good := by
    constructor
    · exact edge1556_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1557 : Fin frame425.rank → ℕ := ![41,2,36,16]
theorem edge1557_span : frame425.space ≤ frame719.space :=
  frame425.inclusion frame719 witness1557 (by decide)
def edge1557 : CertifiedEdge catalog where
  old := 425
  next := 719
  rank := 2
  good := by
    constructor
    · exact edge1557_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1558 : Fin frame425.rank → ℕ := ![19,4,8,32]
theorem edge1558_span : frame425.space ≤ frame720.space :=
  frame425.inclusion frame720 witness1558 (by decide)
def edge1558 : CertifiedEdge catalog where
  old := 425
  next := 720
  rank := 2
  good := by
    constructor
    · exact edge1558_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1559 : Fin frame425.rank → ℕ := ![19,4,8,32]
theorem edge1559_span : frame425.space ≤ frame721.space :=
  frame425.inclusion frame721 witness1559 (by decide)
def edge1559 : CertifiedEdge catalog where
  old := 425
  next := 721
  rank := 2
  good := by
    constructor
    · exact edge1559_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1560 : Fin frame425.rank → ℕ := ![41,2,4,48]
theorem edge1560_span : frame425.space ≤ frame722.space :=
  frame425.inclusion frame722 witness1560 (by decide)
def edge1560 : CertifiedEdge catalog where
  old := 425
  next := 722
  rank := 2
  good := by
    constructor
    · exact edge1560_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1561 : Fin frame425.rank → ℕ := ![41,2,36,16]
theorem edge1561_span : frame425.space ≤ frame723.space :=
  frame425.inclusion frame723 witness1561 (by decide)
def edge1561 : CertifiedEdge catalog where
  old := 425
  next := 723
  rank := 2
  good := by
    constructor
    · exact edge1561_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1562 : Fin frame425.rank → ℕ := ![19,4,8,32]
theorem edge1562_span : frame425.space ≤ frame724.space :=
  frame425.inclusion frame724 witness1562 (by decide)
def edge1562 : CertifiedEdge catalog where
  old := 425
  next := 724
  rank := 2
  good := by
    constructor
    · exact edge1562_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1563 : Fin frame425.rank → ℕ := ![19,4,8,32]
theorem edge1563_span : frame425.space ≤ frame725.space :=
  frame425.inclusion frame725 witness1563 (by decide)
def edge1563 : CertifiedEdge catalog where
  old := 425
  next := 725
  rank := 2
  good := by
    constructor
    · exact edge1563_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1564 : Fin frame426.rank → ℕ := ![3,4,8,16]
theorem edge1564_span : frame426.space ≤ frame734.space :=
  frame426.inclusion frame734 witness1564 (by decide)
def edge1564 : CertifiedEdge catalog where
  old := 426
  next := 734
  rank := 1
  good := by
    constructor
    · exact edge1564_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1565 : Fin frame426.rank → ℕ := ![17,2,4,24]
theorem edge1565_span : frame426.space ≤ frame735.space :=
  frame426.inclusion frame735 witness1565 (by decide)
def edge1565 : CertifiedEdge catalog where
  old := 426
  next := 735
  rank := 1
  good := by
    constructor
    · exact edge1565_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1566 : Fin frame426.rank → ℕ := ![3,4,8,16]
theorem edge1566_span : frame426.space ≤ frame736.space :=
  frame426.inclusion frame736 witness1566 (by decide)
def edge1566 : CertifiedEdge catalog where
  old := 426
  next := 736
  rank := 1
  good := by
    constructor
    · exact edge1566_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1567 : Fin frame426.rank → ℕ := ![17,18,4,8]
theorem edge1567_span : frame426.space ≤ frame737.space :=
  frame426.inclusion frame737 witness1567 (by decide)
def edge1567 : CertifiedEdge catalog where
  old := 426
  next := 737
  rank := 1
  good := by
    constructor
    · exact edge1567_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
