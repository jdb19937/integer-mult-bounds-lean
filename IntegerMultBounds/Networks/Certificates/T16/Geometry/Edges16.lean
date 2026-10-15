module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness512 : Fin frame70.rank → ℕ := ![1]
theorem edge512_span : frame70.space ≤ frame83.space :=
  frame70.inclusion frame83 witness512 (by decide)
def edge512 : CertifiedEdge catalog where
  old := 70
  next := 83
  rank := 1
  good := by
    constructor
    · exact edge512_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness513 : Fin frame70.rank → ℕ := ![1]
theorem edge513_span : frame70.space ≤ frame84.space :=
  frame70.inclusion frame84 witness513 (by decide)
def edge513 : CertifiedEdge catalog where
  old := 70
  next := 84
  rank := 1
  good := by
    constructor
    · exact edge513_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness514 : Fin frame71.rank → ℕ := ![3]
theorem edge514_span : frame71.space ≤ frame79.space :=
  frame71.inclusion frame79 witness514 (by decide)
def edge514 : CertifiedEdge catalog where
  old := 71
  next := 79
  rank := 1
  good := by
    constructor
    · exact edge514_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness515 : Fin frame71.rank → ℕ := ![3]
theorem edge515_span : frame71.space ≤ frame81.space :=
  frame71.inclusion frame81 witness515 (by decide)
def edge515 : CertifiedEdge catalog where
  old := 71
  next := 81
  rank := 1
  good := by
    constructor
    · exact edge515_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness516 : Fin frame71.rank → ℕ := ![3]
theorem edge516_span : frame71.space ≤ frame85.space :=
  frame71.inclusion frame85 witness516 (by decide)
def edge516 : CertifiedEdge catalog where
  old := 71
  next := 85
  rank := 1
  good := by
    constructor
    · exact edge516_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness517 : Fin frame72.rank → ℕ := ![3]
theorem edge517_span : frame72.space ≤ frame76.space :=
  frame72.inclusion frame76 witness517 (by decide)
def edge517 : CertifiedEdge catalog where
  old := 72
  next := 76
  rank := 1
  good := by
    constructor
    · exact edge517_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness518 : Fin frame72.rank → ℕ := ![3]
theorem edge518_span : frame72.space ≤ frame83.space :=
  frame72.inclusion frame83 witness518 (by decide)
def edge518 : CertifiedEdge catalog where
  old := 72
  next := 83
  rank := 1
  good := by
    constructor
    · exact edge518_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness519 : Fin frame72.rank → ℕ := ![1]
theorem edge519_span : frame72.space ≤ frame86.space :=
  frame72.inclusion frame86 witness519 (by decide)
def edge519 : CertifiedEdge catalog where
  old := 72
  next := 86
  rank := 1
  good := by
    constructor
    · exact edge519_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness520 : Fin frame73.rank → ℕ := ![3]
theorem edge520_span : frame73.space ≤ frame77.space :=
  frame73.inclusion frame77 witness520 (by decide)
def edge520 : CertifiedEdge catalog where
  old := 73
  next := 77
  rank := 1
  good := by
    constructor
    · exact edge520_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness521 : Fin frame73.rank → ℕ := ![3]
theorem edge521_span : frame73.space ≤ frame84.space :=
  frame73.inclusion frame84 witness521 (by decide)
def edge521 : CertifiedEdge catalog where
  old := 73
  next := 84
  rank := 1
  good := by
    constructor
    · exact edge521_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness522 : Fin frame73.rank → ℕ := ![3]
theorem edge522_span : frame73.space ≤ frame86.space :=
  frame73.inclusion frame86 witness522 (by decide)
def edge522 : CertifiedEdge catalog where
  old := 73
  next := 86
  rank := 1
  good := by
    constructor
    · exact edge522_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness523 : Fin frame74.rank → ℕ := ![1]
theorem edge523_span : frame74.space ≤ frame80.space :=
  frame74.inclusion frame80 witness523 (by decide)
def edge523 : CertifiedEdge catalog where
  old := 74
  next := 80
  rank := 1
  good := by
    constructor
    · exact edge523_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness524 : Fin frame74.rank → ℕ := ![1]
theorem edge524_span : frame74.space ≤ frame82.space :=
  frame74.inclusion frame82 witness524 (by decide)
def edge524 : CertifiedEdge catalog where
  old := 74
  next := 82
  rank := 1
  good := by
    constructor
    · exact edge524_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness525 : Fin frame74.rank → ℕ := ![1]
theorem edge525_span : frame74.space ≤ frame85.space :=
  frame74.inclusion frame85 witness525 (by decide)
def edge525 : CertifiedEdge catalog where
  old := 74
  next := 85
  rank := 1
  good := by
    constructor
    · exact edge525_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness526 : Fin frame75.rank → ℕ := ![3,4]
theorem edge526_span : frame75.space ≤ frame439.space :=
  frame75.inclusion frame439 witness526 (by decide)
def edge526 : CertifiedEdge catalog where
  old := 75
  next := 439
  rank := 1
  good := by
    constructor
    · exact edge526_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness527 : Fin frame75.rank → ℕ := ![1,28]
theorem edge527_span : frame75.space ≤ frame445.space :=
  frame75.inclusion frame445 witness527 (by decide)
def edge527 : CertifiedEdge catalog where
  old := 75
  next := 445
  rank := 4
  good := by
    constructor
    · exact edge527_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness528 : Fin frame75.rank → ℕ := ![1,4]
theorem edge528_span : frame75.space ≤ frame480.space :=
  frame75.inclusion frame480 witness528 (by decide)
def edge528 : CertifiedEdge catalog where
  old := 75
  next := 480
  rank := 1
  good := by
    constructor
    · exact edge528_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness529 : Fin frame75.rank → ℕ := ![19,40]
theorem edge529_span : frame75.space ≤ frame486.space :=
  frame75.inclusion frame486 witness529 (by decide)
def edge529 : CertifiedEdge catalog where
  old := 75
  next := 486
  rank := 4
  good := by
    constructor
    · exact edge529_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness530 : Fin frame76.rank → ℕ := ![1,2]
theorem edge530_span : frame76.space ≤ frame88.space :=
  frame76.inclusion frame88 witness530 (by decide)
def edge530 : CertifiedEdge catalog where
  old := 76
  next := 88
  rank := 1
  good := by
    constructor
    · exact edge530_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness531 : Fin frame76.rank → ℕ := ![1,6]
theorem edge531_span : frame76.space ≤ frame94.space :=
  frame76.inclusion frame94 witness531 (by decide)
def edge531 : CertifiedEdge catalog where
  old := 76
  next := 94
  rank := 1
  good := by
    constructor
    · exact edge531_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness532 : Fin frame77.rank → ℕ := ![1,2]
theorem edge532_span : frame77.space ≤ frame90.space :=
  frame77.inclusion frame90 witness532 (by decide)
def edge532 : CertifiedEdge catalog where
  old := 77
  next := 90
  rank := 1
  good := by
    constructor
    · exact edge532_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness533 : Fin frame77.rank → ℕ := ![1,6]
theorem edge533_span : frame77.space ≤ frame92.space :=
  frame77.inclusion frame92 witness533 (by decide)
def edge533 : CertifiedEdge catalog where
  old := 77
  next := 92
  rank := 1
  good := by
    constructor
    · exact edge533_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness534 : Fin frame78.rank → ℕ := ![2,4]
theorem edge534_span : frame78.space ≤ frame440.space :=
  frame78.inclusion frame440 witness534 (by decide)
def edge534 : CertifiedEdge catalog where
  old := 78
  next := 440
  rank := 1
  good := by
    constructor
    · exact edge534_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness535 : Fin frame78.rank → ℕ := ![2,12]
theorem edge535_span : frame78.space ≤ frame442.space :=
  frame78.inclusion frame442 witness535 (by decide)
def edge535 : CertifiedEdge catalog where
  old := 78
  next := 442
  rank := 2
  good := by
    constructor
    · exact edge535_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness536 : Fin frame78.rank → ℕ := ![2,4]
theorem edge536_span : frame78.space ≤ frame492.space :=
  frame78.inclusion frame492 witness536 (by decide)
def edge536 : CertifiedEdge catalog where
  old := 78
  next := 492
  rank := 1
  good := by
    constructor
    · exact edge536_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness537 : Fin frame78.rank → ℕ := ![8,16]
theorem edge537_span : frame78.space ≤ frame495.space :=
  frame78.inclusion frame495 witness537 (by decide)
def edge537 : CertifiedEdge catalog where
  old := 78
  next := 495
  rank := 3
  good := by
    constructor
    · exact edge537_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness538 : Fin frame79.rank → ℕ := ![2,4]
theorem edge538_span : frame79.space ≤ frame88.space :=
  frame79.inclusion frame88 witness538 (by decide)
def edge538 : CertifiedEdge catalog where
  old := 79
  next := 88
  rank := 1
  good := by
    constructor
    · exact edge538_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness539 : Fin frame79.rank → ℕ := ![2,4]
theorem edge539_span : frame79.space ≤ frame93.space :=
  frame79.inclusion frame93 witness539 (by decide)
def edge539 : CertifiedEdge catalog where
  old := 79
  next := 93
  rank := 1
  good := by
    constructor
    · exact edge539_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness540 : Fin frame80.rank → ℕ := ![2,4]
theorem edge540_span : frame80.space ≤ frame89.space :=
  frame80.inclusion frame89 witness540 (by decide)
def edge540 : CertifiedEdge catalog where
  old := 80
  next := 89
  rank := 1
  good := by
    constructor
    · exact edge540_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness541 : Fin frame80.rank → ℕ := ![2,4]
theorem edge541_span : frame80.space ≤ frame92.space :=
  frame80.inclusion frame92 witness541 (by decide)
def edge541 : CertifiedEdge catalog where
  old := 80
  next := 92
  rank := 1
  good := by
    constructor
    · exact edge541_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness542 : Fin frame81.rank → ℕ := ![2,4]
theorem edge542_span : frame81.space ≤ frame90.space :=
  frame81.inclusion frame90 witness542 (by decide)
def edge542 : CertifiedEdge catalog where
  old := 81
  next := 90
  rank := 1
  good := by
    constructor
    · exact edge542_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness543 : Fin frame81.rank → ℕ := ![2,4]
theorem edge543_span : frame81.space ≤ frame91.space :=
  frame81.inclusion frame91 witness543 (by decide)
def edge543 : CertifiedEdge catalog where
  old := 81
  next := 91
  rank := 1
  good := by
    constructor
    · exact edge543_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
