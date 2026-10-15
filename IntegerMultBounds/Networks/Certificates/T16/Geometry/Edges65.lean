module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2080 : Fin frame620.rank → ℕ := ![1,2,8,16]
theorem edge2080_span : frame620.space ≤ frame739.space :=
  frame620.inclusion frame739 witness2080 (by decide)
def edge2080 : CertifiedEdge catalog where
  old := 620
  next := 739
  rank := 1
  good := by
    constructor
    · exact edge2080_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2081 : Fin frame620.rank → ℕ := ![69,34,8,48]
theorem edge2081_span : frame620.space ≤ frame764.space :=
  frame620.inclusion frame764 witness2081 (by decide)
def edge2081 : CertifiedEdge catalog where
  old := 620
  next := 764
  rank := 3
  good := by
    constructor
    · exact edge2081_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2082 : Fin frame621.rank → ℕ := ![1,34,4,8,48,64]
theorem edge2082_span : frame621.space ≤ frame756.space :=
  frame621.inclusion frame756 witness2082 (by decide)
def edge2082 : CertifiedEdge catalog where
  old := 621
  next := 756
  rank := 1
  good := by
    constructor
    · exact edge2082_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2083 : Fin frame621.rank → ℕ := ![1,34,4,8,48,64]
theorem edge2083_span : frame621.space ≤ frame762.space :=
  frame621.inclusion frame762 witness2083 (by decide)
def edge2083 : CertifiedEdge catalog where
  old := 621
  next := 762
  rank := 1
  good := by
    constructor
    · exact edge2083_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2084 : Fin frame622.rank → ℕ := ![17,18,4,8]
theorem edge2084_span : frame622.space ≤ frame636.space :=
  frame622.inclusion frame636 witness2084 (by decide)
def edge2084 : CertifiedEdge catalog where
  old := 622
  next := 636
  rank := 1
  good := by
    constructor
    · exact edge2084_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2085 : Fin frame622.rank → ℕ := ![5,6,40,112]
theorem edge2085_span : frame622.space ≤ frame767.space :=
  frame622.inclusion frame767 witness2085 (by decide)
def edge2085 : CertifiedEdge catalog where
  old := 622
  next := 767
  rank := 3
  good := by
    constructor
    · exact edge2085_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2086 : Fin frame623.rank → ℕ := ![1,2,20,24]
theorem edge2086_span : frame623.space ≤ frame637.space :=
  frame623.inclusion frame637 witness2086 (by decide)
def edge2086 : CertifiedEdge catalog where
  old := 623
  next := 637
  rank := 1
  good := by
    constructor
    · exact edge2086_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2087 : Fin frame623.rank → ℕ := ![65,66,52,72]
theorem edge2087_span : frame623.space ≤ frame769.space :=
  frame623.inclusion frame769 witness2087 (by decide)
def edge2087 : CertifiedEdge catalog where
  old := 623
  next := 769
  rank := 3
  good := by
    constructor
    · exact edge2087_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2088 : Fin frame624.rank → ℕ := ![1,10,12,16]
theorem edge2088_span : frame624.space ≤ frame734.space :=
  frame624.inclusion frame734 witness2088 (by decide)
def edge2088 : CertifiedEdge catalog where
  old := 624
  next := 734
  rank := 1
  good := by
    constructor
    · exact edge2088_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2089 : Fin frame624.rank → ℕ := ![35,4,72,48]
theorem edge2089_span : frame624.space ≤ frame769.space :=
  frame624.inclusion frame769 witness2089 (by decide)
def edge2089 : CertifiedEdge catalog where
  old := 624
  next := 769
  rank := 3
  good := by
    constructor
    · exact edge2089_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2090 : Fin frame625.rank → ℕ := ![1,18,20,24]
theorem edge2090_span : frame625.space ≤ frame735.space :=
  frame625.inclusion frame735 witness2090 (by decide)
def edge2090 : CertifiedEdge catalog where
  old := 625
  next := 735
  rank := 1
  good := by
    constructor
    · exact edge2090_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2091 : Fin frame625.rank → ℕ := ![7,72,80,96]
theorem edge2091_span : frame625.space ≤ frame768.space :=
  frame625.inclusion frame768 witness2091 (by decide)
def edge2091 : CertifiedEdge catalog where
  old := 625
  next := 768
  rank := 3
  good := by
    constructor
    · exact edge2091_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2092 : Fin frame626.rank → ℕ := ![17,2,4,8]
theorem edge2092_span : frame626.space ≤ frame636.space :=
  frame626.inclusion frame636 witness2092 (by decide)
def edge2092 : CertifiedEdge catalog where
  old := 626
  next := 636
  rank := 1
  good := by
    constructor
    · exact edge2092_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2093 : Fin frame626.rank → ℕ := ![5,6,40,112]
theorem edge2093_span : frame626.space ≤ frame771.space :=
  frame626.inclusion frame771 witness2093 (by decide)
def edge2093 : CertifiedEdge catalog where
  old := 626
  next := 771
  rank := 3
  good := by
    constructor
    · exact edge2093_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2094 : Fin frame627.rank → ℕ := ![17,2,4,24]
theorem edge2094_span : frame627.space ≤ frame637.space :=
  frame627.inclusion frame637 witness2094 (by decide)
def edge2094 : CertifiedEdge catalog where
  old := 627
  next := 637
  rank := 1
  good := by
    constructor
    · exact edge2094_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2095 : Fin frame627.rank → ℕ := ![49,66,68,72]
theorem edge2095_span : frame627.space ≤ frame773.space :=
  frame627.inclusion frame773 witness2095 (by decide)
def edge2095 : CertifiedEdge catalog where
  old := 627
  next := 773
  rank := 3
  good := by
    constructor
    · exact edge2095_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2096 : Fin frame628.rank → ℕ := ![9,2,12,16]
theorem edge2096_span : frame628.space ≤ frame740.space :=
  frame628.inclusion frame740 witness2096 (by decide)
def edge2096 : CertifiedEdge catalog where
  old := 628
  next := 740
  rank := 1
  good := by
    constructor
    · exact edge2096_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2097 : Fin frame628.rank → ℕ := ![1,38,72,48]
theorem edge2097_span : frame628.space ≤ frame773.space :=
  frame628.inclusion frame773 witness2097 (by decide)
def edge2097 : CertifiedEdge catalog where
  old := 628
  next := 773
  rank := 3
  good := by
    constructor
    · exact edge2097_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2098 : Fin frame629.rank → ℕ := ![1,10,12,16]
theorem edge2098_span : frame629.space ≤ frame741.space :=
  frame629.inclusion frame741 witness2098 (by decide)
def edge2098 : CertifiedEdge catalog where
  old := 629
  next := 741
  rank := 1
  good := by
    constructor
    · exact edge2098_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2099 : Fin frame629.rank → ℕ := ![37,2,72,48]
theorem edge2099_span : frame629.space ≤ frame772.space :=
  frame629.inclusion frame772 witness2099 (by decide)
def edge2099 : CertifiedEdge catalog where
  old := 629
  next := 772
  rank := 3
  good := by
    constructor
    · exact edge2099_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2100 : Fin frame630.rank → ℕ := ![33,34,36,40,48]
theorem edge2100_span : frame630.space ≤ frame774.space :=
  frame630.inclusion frame774 witness2100 (by decide)
def edge2100 : CertifiedEdge catalog where
  old := 630
  next := 774
  rank := 1
  good := by
    constructor
    · exact edge2100_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2101 : Fin frame630.rank → ℕ := ![33,34,36,40,48]
theorem edge2101_span : frame630.space ≤ frame782.space :=
  frame630.inclusion frame782 witness2101 (by decide)
def edge2101 : CertifiedEdge catalog where
  old := 630
  next := 782
  rank := 1
  good := by
    constructor
    · exact edge2101_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2102 : Fin frame630.rank → ℕ := ![225,226,228,104,240]
theorem edge2102_span : frame630.space ≤ frame998.space :=
  frame630.inclusion frame998 witness2102 (by decide)
def edge2102 : CertifiedEdge catalog where
  old := 630
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2102_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2103 : Fin frame631.rank → ℕ := ![5,6,8,16,32]
theorem edge2103_span : frame631.space ≤ frame777.space :=
  frame631.inclusion frame777 witness2103 (by decide)
def edge2103 : CertifiedEdge catalog where
  old := 631
  next := 777
  rank := 1
  good := by
    constructor
    · exact edge2103_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2104 : Fin frame631.rank → ℕ := ![1,2,20,24,32]
theorem edge2104_span : frame631.space ≤ frame785.space :=
  frame631.inclusion frame785 witness2104 (by decide)
def edge2104 : CertifiedEdge catalog where
  old := 631
  next := 785
  rank := 1
  good := by
    constructor
    · exact edge2104_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2105 : Fin frame631.rank → ℕ := ![5,6,40,176,64]
theorem edge2105_span : frame631.space ≤ frame998.space :=
  frame631.inclusion frame998 witness2105 (by decide)
def edge2105 : CertifiedEdge catalog where
  old := 631
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2105_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2106 : Fin frame632.rank → ℕ := ![5,6,8,16,32]
theorem edge2106_span : frame632.space ≤ frame780.space :=
  frame632.inclusion frame780 witness2106 (by decide)
def edge2106 : CertifiedEdge catalog where
  old := 632
  next := 780
  rank := 1
  good := by
    constructor
    · exact edge2106_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2107 : Fin frame632.rank → ℕ := ![1,2,20,24,32]
theorem edge2107_span : frame632.space ≤ frame788.space :=
  frame632.inclusion frame788 witness2107 (by decide)
def edge2107 : CertifiedEdge catalog where
  old := 632
  next := 788
  rank := 1
  good := by
    constructor
    · exact edge2107_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2108 : Fin frame632.rank → ℕ := ![5,6,104,112,128]
theorem edge2108_span : frame632.space ≤ frame999.space :=
  frame632.inclusion frame999 witness2108 (by decide)
def edge2108 : CertifiedEdge catalog where
  old := 632
  next := 999
  rank := 3
  good := by
    constructor
    · exact edge2108_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2109 : Fin frame633.rank → ℕ := ![33,34,36,40,48]
theorem edge2109_span : frame633.space ≤ frame781.space :=
  frame633.inclusion frame781 witness2109 (by decide)
def edge2109 : CertifiedEdge catalog where
  old := 633
  next := 781
  rank := 1
  good := by
    constructor
    · exact edge2109_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2110 : Fin frame633.rank → ℕ := ![33,34,36,40,48]
theorem edge2110_span : frame633.space ≤ frame789.space :=
  frame633.inclusion frame789 witness2110 (by decide)
def edge2110 : CertifiedEdge catalog where
  old := 633
  next := 789
  rank := 1
  good := by
    constructor
    · exact edge2110_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2111 : Fin frame633.rank → ℕ := ![33,34,36,232,112]
theorem edge2111_span : frame633.space ≤ frame999.space :=
  frame633.inclusion frame999 witness2111 (by decide)
def edge2111 : CertifiedEdge catalog where
  old := 633
  next := 999
  rank := 3
  good := by
    constructor
    · exact edge2111_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
