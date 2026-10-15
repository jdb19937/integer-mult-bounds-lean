module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness544 : Fin frame82.rank → ℕ := ![2,4]
theorem edge544_span : frame82.space ≤ frame87.space :=
  frame82.inclusion frame87 witness544 (by decide)
def edge544 : CertifiedEdge catalog where
  old := 82
  next := 87
  rank := 1
  good := by
    constructor
    · exact edge544_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness545 : Fin frame82.rank → ℕ := ![2,4]
theorem edge545_span : frame82.space ≤ frame94.space :=
  frame82.inclusion frame94 witness545 (by decide)
def edge545 : CertifiedEdge catalog where
  old := 82
  next := 94
  rank := 1
  good := by
    constructor
    · exact edge545_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness546 : Fin frame83.rank → ℕ := ![5,6]
theorem edge546_span : frame83.space ≤ frame89.space :=
  frame83.inclusion frame89 witness546 (by decide)
def edge546 : CertifiedEdge catalog where
  old := 83
  next := 89
  rank := 1
  good := by
    constructor
    · exact edge546_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness547 : Fin frame83.rank → ℕ := ![5,2]
theorem edge547_span : frame83.space ≤ frame91.space :=
  frame83.inclusion frame91 witness547 (by decide)
def edge547 : CertifiedEdge catalog where
  old := 83
  next := 91
  rank := 1
  good := by
    constructor
    · exact edge547_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness548 : Fin frame84.rank → ℕ := ![5,6]
theorem edge548_span : frame84.space ≤ frame87.space :=
  frame84.inclusion frame87 witness548 (by decide)
def edge548 : CertifiedEdge catalog where
  old := 84
  next := 87
  rank := 1
  good := by
    constructor
    · exact edge548_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness549 : Fin frame84.rank → ℕ := ![5,2]
theorem edge549_span : frame84.space ≤ frame93.space :=
  frame84.inclusion frame93 witness549 (by decide)
def edge549 : CertifiedEdge catalog where
  old := 84
  next := 93
  rank := 1
  good := by
    constructor
    · exact edge549_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness550 : Fin frame85.rank → ℕ := ![2,4]
theorem edge550_span : frame85.space ≤ frame480.space :=
  frame85.inclusion frame480 witness550 (by decide)
def edge550 : CertifiedEdge catalog where
  old := 85
  next := 480
  rank := 1
  good := by
    constructor
    · exact edge550_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness551 : Fin frame85.rank → ℕ := ![4,8]
theorem edge551_span : frame85.space ≤ frame483.space :=
  frame85.inclusion frame483 witness551 (by decide)
def edge551 : CertifiedEdge catalog where
  old := 85
  next := 483
  rank := 2
  good := by
    constructor
    · exact edge551_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness552 : Fin frame85.rank → ℕ := ![2,4]
theorem edge552_span : frame85.space ≤ frame506.space :=
  frame85.inclusion frame506 witness552 (by decide)
def edge552 : CertifiedEdge catalog where
  old := 85
  next := 506
  rank := 1
  good := by
    constructor
    · exact edge552_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness553 : Fin frame85.rank → ℕ := ![2,4]
theorem edge553_span : frame85.space ≤ frame508.space :=
  frame85.inclusion frame508 witness553 (by decide)
def edge553 : CertifiedEdge catalog where
  old := 85
  next := 508
  rank := 2
  good := by
    constructor
    · exact edge553_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness554 : Fin frame86.rank → ℕ := ![5,6]
theorem edge554_span : frame86.space ≤ frame492.space :=
  frame86.inclusion frame492 witness554 (by decide)
def edge554 : CertifiedEdge catalog where
  old := 86
  next := 492
  rank := 1
  good := by
    constructor
    · exact edge554_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness555 : Fin frame86.rank → ℕ := ![55,40]
theorem edge555_span : frame86.space ≤ frame498.space :=
  frame86.inclusion frame498 witness555 (by decide)
def edge555 : CertifiedEdge catalog where
  old := 86
  next := 498
  rank := 4
  good := by
    constructor
    · exact edge555_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness556 : Fin frame86.rank → ℕ := ![3,4]
theorem edge556_span : frame86.space ≤ frame505.space :=
  frame86.inclusion frame505 witness556 (by decide)
def edge556 : CertifiedEdge catalog where
  old := 86
  next := 505
  rank := 1
  good := by
    constructor
    · exact edge556_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness557 : Fin frame86.rank → ℕ := ![43,20]
theorem edge557_span : frame86.space ≤ frame511.space :=
  frame86.inclusion frame511 witness557 (by decide)
def edge557 : CertifiedEdge catalog where
  old := 86
  next := 511
  rank := 4
  good := by
    constructor
    · exact edge557_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness558 : Fin frame87.rank → ℕ := ![5,2,8]
theorem edge558_span : frame87.space ≤ frame95.space :=
  frame87.inclusion frame95 witness558 (by decide)
def edge558 : CertifiedEdge catalog where
  old := 87
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge558_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness559 : Fin frame87.rank → ℕ := ![27,4,32]
theorem edge559_span : frame87.space ≤ frame656.space :=
  frame87.inclusion frame656 witness559 (by decide)
def edge559 : CertifiedEdge catalog where
  old := 87
  next := 656
  rank := 3
  good := by
    constructor
    · exact edge559_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness560 : Fin frame87.rank → ℕ := ![13,34,48]
theorem edge560_span : frame87.space ≤ frame680.space :=
  frame87.inclusion frame680 witness560 (by decide)
def edge560 : CertifiedEdge catalog where
  old := 87
  next := 680
  rank := 3
  good := by
    constructor
    · exact edge560_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness561 : Fin frame88.rank → ℕ := ![1,10,4]
theorem edge561_span : frame88.space ≤ frame95.space :=
  frame88.inclusion frame95 witness561 (by decide)
def edge561 : CertifiedEdge catalog where
  old := 88
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge561_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness562 : Fin frame88.rank → ℕ := ![19,36,8]
theorem edge562_span : frame88.space ≤ frame657.space :=
  frame88.inclusion frame657 witness562 (by decide)
def edge562 : CertifiedEdge catalog where
  old := 88
  next := 657
  rank := 3
  good := by
    constructor
    · exact edge562_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness563 : Fin frame88.rank → ℕ := ![9,50,36]
theorem edge563_span : frame88.space ≤ frame681.space :=
  frame88.inclusion frame681 witness563 (by decide)
def edge563 : CertifiedEdge catalog where
  old := 88
  next := 681
  rank := 3
  good := by
    constructor
    · exact edge563_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness564 : Fin frame89.rank → ℕ := ![9,2,4]
theorem edge564_span : frame89.space ≤ frame95.space :=
  frame89.inclusion frame95 witness564 (by decide)
def edge564 : CertifiedEdge catalog where
  old := 89
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge564_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness565 : Fin frame89.rank → ℕ := ![25,34,36]
theorem edge565_span : frame89.space ≤ frame664.space :=
  frame89.inclusion frame664 witness565 (by decide)
def edge565 : CertifiedEdge catalog where
  old := 89
  next := 664
  rank := 3
  good := by
    constructor
    · exact edge565_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness566 : Fin frame89.rank → ℕ := ![51,4,8]
theorem edge566_span : frame89.space ≤ frame672.space :=
  frame89.inclusion frame672 witness566 (by decide)
def edge566 : CertifiedEdge catalog where
  old := 89
  next := 672
  rank := 3
  good := by
    constructor
    · exact edge566_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness567 : Fin frame90.rank → ℕ := ![1,6,8]
theorem edge567_span : frame90.space ≤ frame95.space :=
  frame90.inclusion frame95 witness567 (by decide)
def edge567 : CertifiedEdge catalog where
  old := 90
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge567_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness568 : Fin frame90.rank → ℕ := ![9,38,48]
theorem edge568_span : frame90.space ≤ frame665.space :=
  frame90.inclusion frame665 witness568 (by decide)
def edge568 : CertifiedEdge catalog where
  old := 90
  next := 665
  rank := 3
  good := by
    constructor
    · exact edge568_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness569 : Fin frame90.rank → ℕ := ![19,12,32]
theorem edge569_span : frame90.space ≤ frame673.space :=
  frame90.inclusion frame673 witness569 (by decide)
def edge569 : CertifiedEdge catalog where
  old := 90
  next := 673
  rank := 3
  good := by
    constructor
    · exact edge569_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness570 : Fin frame91.rank → ℕ := ![5,6,8]
theorem edge570_span : frame91.space ≤ frame95.space :=
  frame91.inclusion frame95 witness570 (by decide)
def edge570 : CertifiedEdge catalog where
  old := 91
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge570_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness571 : Fin frame91.rank → ℕ := ![37,18,24]
theorem edge571_span : frame91.space ≤ frame696.space :=
  frame91.inclusion frame696 witness571 (by decide)
def edge571 : CertifiedEdge catalog where
  old := 91
  next := 696
  rank := 3
  good := by
    constructor
    · exact edge571_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness572 : Fin frame91.rank → ℕ := ![11,44,48]
theorem edge572_span : frame91.space ≤ frame704.space :=
  frame91.inclusion frame704 witness572 (by decide)
def edge572 : CertifiedEdge catalog where
  old := 91
  next := 704
  rank := 3
  good := by
    constructor
    · exact edge572_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness573 : Fin frame92.rank → ℕ := ![1,2,4]
theorem edge573_span : frame92.space ≤ frame95.space :=
  frame92.inclusion frame95 witness573 (by decide)
def edge573 : CertifiedEdge catalog where
  old := 92
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge573_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness574 : Fin frame92.rank → ℕ := ![9,50,36]
theorem edge574_span : frame92.space ≤ frame697.space :=
  frame92.inclusion frame697 witness574 (by decide)
def edge574 : CertifiedEdge catalog where
  old := 92
  next := 697
  rank := 3
  good := by
    constructor
    · exact edge574_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness575 : Fin frame92.rank → ℕ := ![19,36,8]
theorem edge575_span : frame92.space ≤ frame705.space :=
  frame92.inclusion frame705 witness575 (by decide)
def edge575 : CertifiedEdge catalog where
  old := 92
  next := 705
  rank := 3
  good := by
    constructor
    · exact edge575_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
