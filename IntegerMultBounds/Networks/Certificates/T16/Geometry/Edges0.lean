module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness0 : Fin frame0.rank → ℕ := ![]
theorem edge0_span : frame0.space ≤ frame2.space :=
  frame0.inclusion frame2 witness0 (by decide)
def edge0 : CertifiedEdge catalog where
  old := 0
  next := 2
  rank := 1
  good := by
    constructor
    · exact edge0_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1 : Fin frame0.rank → ℕ := ![]
theorem edge1_span : frame0.space ≤ frame3.space :=
  frame0.inclusion frame3 witness1 (by decide)
def edge1 : CertifiedEdge catalog where
  old := 0
  next := 3
  rank := 1
  good := by
    constructor
    · exact edge1_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2 : Fin frame0.rank → ℕ := ![]
theorem edge2_span : frame0.space ≤ frame4.space :=
  frame0.inclusion frame4 witness2 (by decide)
def edge2 : CertifiedEdge catalog where
  old := 0
  next := 4
  rank := 1
  good := by
    constructor
    · exact edge2_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness3 : Fin frame0.rank → ℕ := ![]
theorem edge3_span : frame0.space ≤ frame5.space :=
  frame0.inclusion frame5 witness3 (by decide)
def edge3 : CertifiedEdge catalog where
  old := 0
  next := 5
  rank := 1
  good := by
    constructor
    · exact edge3_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness4 : Fin frame0.rank → ℕ := ![]
theorem edge4_span : frame0.space ≤ frame6.space :=
  frame0.inclusion frame6 witness4 (by decide)
def edge4 : CertifiedEdge catalog where
  old := 0
  next := 6
  rank := 1
  good := by
    constructor
    · exact edge4_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness5 : Fin frame0.rank → ℕ := ![]
theorem edge5_span : frame0.space ≤ frame7.space :=
  frame0.inclusion frame7 witness5 (by decide)
def edge5 : CertifiedEdge catalog where
  old := 0
  next := 7
  rank := 1
  good := by
    constructor
    · exact edge5_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness6 : Fin frame0.rank → ℕ := ![]
theorem edge6_span : frame0.space ≤ frame8.space :=
  frame0.inclusion frame8 witness6 (by decide)
def edge6 : CertifiedEdge catalog where
  old := 0
  next := 8
  rank := 1
  good := by
    constructor
    · exact edge6_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness7 : Fin frame0.rank → ℕ := ![]
theorem edge7_span : frame0.space ≤ frame9.space :=
  frame0.inclusion frame9 witness7 (by decide)
def edge7 : CertifiedEdge catalog where
  old := 0
  next := 9
  rank := 1
  good := by
    constructor
    · exact edge7_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness8 : Fin frame0.rank → ℕ := ![]
theorem edge8_span : frame0.space ≤ frame10.space :=
  frame0.inclusion frame10 witness8 (by decide)
def edge8 : CertifiedEdge catalog where
  old := 0
  next := 10
  rank := 1
  good := by
    constructor
    · exact edge8_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness9 : Fin frame0.rank → ℕ := ![]
theorem edge9_span : frame0.space ≤ frame11.space :=
  frame0.inclusion frame11 witness9 (by decide)
def edge9 : CertifiedEdge catalog where
  old := 0
  next := 11
  rank := 1
  good := by
    constructor
    · exact edge9_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness10 : Fin frame0.rank → ℕ := ![]
theorem edge10_span : frame0.space ≤ frame12.space :=
  frame0.inclusion frame12 witness10 (by decide)
def edge10 : CertifiedEdge catalog where
  old := 0
  next := 12
  rank := 1
  good := by
    constructor
    · exact edge10_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness11 : Fin frame0.rank → ℕ := ![]
theorem edge11_span : frame0.space ≤ frame13.space :=
  frame0.inclusion frame13 witness11 (by decide)
def edge11 : CertifiedEdge catalog where
  old := 0
  next := 13
  rank := 1
  good := by
    constructor
    · exact edge11_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness12 : Fin frame0.rank → ℕ := ![]
theorem edge12_span : frame0.space ≤ frame14.space :=
  frame0.inclusion frame14 witness12 (by decide)
def edge12 : CertifiedEdge catalog where
  old := 0
  next := 14
  rank := 1
  good := by
    constructor
    · exact edge12_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness13 : Fin frame0.rank → ℕ := ![]
theorem edge13_span : frame0.space ≤ frame15.space :=
  frame0.inclusion frame15 witness13 (by decide)
def edge13 : CertifiedEdge catalog where
  old := 0
  next := 15
  rank := 1
  good := by
    constructor
    · exact edge13_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness14 : Fin frame0.rank → ℕ := ![]
theorem edge14_span : frame0.space ≤ frame16.space :=
  frame0.inclusion frame16 witness14 (by decide)
def edge14 : CertifiedEdge catalog where
  old := 0
  next := 16
  rank := 1
  good := by
    constructor
    · exact edge14_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness15 : Fin frame0.rank → ℕ := ![]
theorem edge15_span : frame0.space ≤ frame20.space :=
  frame0.inclusion frame20 witness15 (by decide)
def edge15 : CertifiedEdge catalog where
  old := 0
  next := 20
  rank := 2
  good := by
    constructor
    · exact edge15_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness16 : Fin frame0.rank → ℕ := ![]
theorem edge16_span : frame0.space ≤ frame27.space :=
  frame0.inclusion frame27 witness16 (by decide)
def edge16 : CertifiedEdge catalog where
  old := 0
  next := 27
  rank := 2
  good := by
    constructor
    · exact edge16_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness17 : Fin frame0.rank → ℕ := ![]
theorem edge17_span : frame0.space ≤ frame38.space :=
  frame0.inclusion frame38 witness17 (by decide)
def edge17 : CertifiedEdge catalog where
  old := 0
  next := 38
  rank := 1
  good := by
    constructor
    · exact edge17_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness18 : Fin frame0.rank → ℕ := ![]
theorem edge18_span : frame0.space ≤ frame39.space :=
  frame0.inclusion frame39 witness18 (by decide)
def edge18 : CertifiedEdge catalog where
  old := 0
  next := 39
  rank := 1
  good := by
    constructor
    · exact edge18_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness19 : Fin frame0.rank → ℕ := ![]
theorem edge19_span : frame0.space ≤ frame40.space :=
  frame0.inclusion frame40 witness19 (by decide)
def edge19 : CertifiedEdge catalog where
  old := 0
  next := 40
  rank := 1
  good := by
    constructor
    · exact edge19_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness20 : Fin frame0.rank → ℕ := ![]
theorem edge20_span : frame0.space ≤ frame41.space :=
  frame0.inclusion frame41 witness20 (by decide)
def edge20 : CertifiedEdge catalog where
  old := 0
  next := 41
  rank := 1
  good := by
    constructor
    · exact edge20_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness21 : Fin frame0.rank → ℕ := ![]
theorem edge21_span : frame0.space ≤ frame42.space :=
  frame0.inclusion frame42 witness21 (by decide)
def edge21 : CertifiedEdge catalog where
  old := 0
  next := 42
  rank := 1
  good := by
    constructor
    · exact edge21_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness22 : Fin frame0.rank → ℕ := ![]
theorem edge22_span : frame0.space ≤ frame43.space :=
  frame0.inclusion frame43 witness22 (by decide)
def edge22 : CertifiedEdge catalog where
  old := 0
  next := 43
  rank := 1
  good := by
    constructor
    · exact edge22_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness23 : Fin frame0.rank → ℕ := ![]
theorem edge23_span : frame0.space ≤ frame44.space :=
  frame0.inclusion frame44 witness23 (by decide)
def edge23 : CertifiedEdge catalog where
  old := 0
  next := 44
  rank := 1
  good := by
    constructor
    · exact edge23_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness24 : Fin frame0.rank → ℕ := ![]
theorem edge24_span : frame0.space ≤ frame45.space :=
  frame0.inclusion frame45 witness24 (by decide)
def edge24 : CertifiedEdge catalog where
  old := 0
  next := 45
  rank := 1
  good := by
    constructor
    · exact edge24_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness25 : Fin frame0.rank → ℕ := ![]
theorem edge25_span : frame0.space ≤ frame49.space :=
  frame0.inclusion frame49 witness25 (by decide)
def edge25 : CertifiedEdge catalog where
  old := 0
  next := 49
  rank := 2
  good := by
    constructor
    · exact edge25_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness26 : Fin frame0.rank → ℕ := ![]
theorem edge26_span : frame0.space ≤ frame56.space :=
  frame0.inclusion frame56 witness26 (by decide)
def edge26 : CertifiedEdge catalog where
  old := 0
  next := 56
  rank := 2
  good := by
    constructor
    · exact edge26_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness27 : Fin frame0.rank → ℕ := ![]
theorem edge27_span : frame0.space ≤ frame67.space :=
  frame0.inclusion frame67 witness27 (by decide)
def edge27 : CertifiedEdge catalog where
  old := 0
  next := 67
  rank := 1
  good := by
    constructor
    · exact edge27_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness28 : Fin frame0.rank → ℕ := ![]
theorem edge28_span : frame0.space ≤ frame68.space :=
  frame0.inclusion frame68 witness28 (by decide)
def edge28 : CertifiedEdge catalog where
  old := 0
  next := 68
  rank := 1
  good := by
    constructor
    · exact edge28_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness29 : Fin frame0.rank → ℕ := ![]
theorem edge29_span : frame0.space ≤ frame69.space :=
  frame0.inclusion frame69 witness29 (by decide)
def edge29 : CertifiedEdge catalog where
  old := 0
  next := 69
  rank := 1
  good := by
    constructor
    · exact edge29_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness30 : Fin frame0.rank → ℕ := ![]
theorem edge30_span : frame0.space ≤ frame70.space :=
  frame0.inclusion frame70 witness30 (by decide)
def edge30 : CertifiedEdge catalog where
  old := 0
  next := 70
  rank := 1
  good := by
    constructor
    · exact edge30_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness31 : Fin frame0.rank → ℕ := ![]
theorem edge31_span : frame0.space ≤ frame71.space :=
  frame0.inclusion frame71 witness31 (by decide)
def edge31 : CertifiedEdge catalog where
  old := 0
  next := 71
  rank := 1
  good := by
    constructor
    · exact edge31_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
