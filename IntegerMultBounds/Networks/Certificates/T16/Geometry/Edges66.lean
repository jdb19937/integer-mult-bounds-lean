module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2112 : Fin frame634.rank → ℕ := ![1,2,4,40,16]
theorem edge2112_span : frame634.space ≤ frame780.space :=
  frame634.inclusion frame780 witness2112 (by decide)
def edge2112 : CertifiedEdge catalog where
  old := 634
  next := 780
  rank := 1
  good := by
    constructor
    · exact edge2112_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2113 : Fin frame634.rank → ℕ := ![1,2,4,40,48]
theorem edge2113_span : frame634.space ≤ frame789.space :=
  frame634.inclusion frame789 witness2113 (by decide)
def edge2113 : CertifiedEdge catalog where
  old := 634
  next := 789
  rank := 1
  good := by
    constructor
    · exact edge2113_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2114 : Fin frame634.rank → ℕ := ![65,66,68,232,112]
theorem edge2114_span : frame634.space ≤ frame999.space :=
  frame634.inclusion frame999 witness2114 (by decide)
def edge2114 : CertifiedEdge catalog where
  old := 634
  next := 999
  rank := 3
  good := by
    constructor
    · exact edge2114_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2115 : Fin frame635.rank → ℕ := ![5,6,8,16,32]
theorem edge2115_span : frame635.space ≤ frame781.space :=
  frame635.inclusion frame781 witness2115 (by decide)
def edge2115 : CertifiedEdge catalog where
  old := 635
  next := 781
  rank := 1
  good := by
    constructor
    · exact edge2115_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2116 : Fin frame635.rank → ℕ := ![1,2,4,40,48]
theorem edge2116_span : frame635.space ≤ frame788.space :=
  frame635.inclusion frame788 witness2116 (by decide)
def edge2116 : CertifiedEdge catalog where
  old := 635
  next := 788
  rank := 1
  good := by
    constructor
    · exact edge2116_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2117 : Fin frame635.rank → ℕ := ![5,6,8,144,224]
theorem edge2117_span : frame635.space ≤ frame999.space :=
  frame635.inclusion frame999 witness2117 (by decide)
def edge2117 : CertifiedEdge catalog where
  old := 635
  next := 999
  rank := 3
  good := by
    constructor
    · exact edge2117_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2118 : Fin frame636.rank → ℕ := ![5,6,8,16,32]
theorem edge2118_span : frame636.space ≤ frame774.space :=
  frame636.inclusion frame774 witness2118 (by decide)
def edge2118 : CertifiedEdge catalog where
  old := 636
  next := 774
  rank := 1
  good := by
    constructor
    · exact edge2118_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2119 : Fin frame636.rank → ℕ := ![1,2,36,40,16]
theorem edge2119_span : frame636.space ≤ frame785.space :=
  frame636.inclusion frame785 witness2119 (by decide)
def edge2119 : CertifiedEdge catalog where
  old := 636
  next := 785
  rank := 1
  good := by
    constructor
    · exact edge2119_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2120 : Fin frame636.rank → ℕ := ![5,6,72,208,32]
theorem edge2120_span : frame636.space ≤ frame998.space :=
  frame636.inclusion frame998 witness2120 (by decide)
def edge2120 : CertifiedEdge catalog where
  old := 636
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2120_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2121 : Fin frame637.rank → ℕ := ![1,2,4,40,48]
theorem edge2121_span : frame637.space ≤ frame777.space :=
  frame637.inclusion frame777 witness2121 (by decide)
def edge2121 : CertifiedEdge catalog where
  old := 637
  next := 777
  rank := 1
  good := by
    constructor
    · exact edge2121_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2122 : Fin frame637.rank → ℕ := ![1,2,4,40,48]
theorem edge2122_span : frame637.space ≤ frame782.space :=
  frame637.inclusion frame782 witness2122 (by decide)
def edge2122 : CertifiedEdge catalog where
  old := 637
  next := 782
  rank := 1
  good := by
    constructor
    · exact edge2122_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2123 : Fin frame637.rank → ℕ := ![129,130,132,104,240]
theorem edge2123_span : frame637.space ≤ frame998.space :=
  frame637.inclusion frame998 witness2123 (by decide)
def edge2123 : CertifiedEdge catalog where
  old := 637
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2123_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2124 : Fin frame638.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2124_span : frame638.space ≤ frame790.space :=
  frame638.inclusion frame790 witness2124 (by decide)
def edge2124 : CertifiedEdge catalog where
  old := 638
  next := 790
  rank := 1
  good := by
    constructor
    · exact edge2124_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2125 : Fin frame638.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2125_span : frame638.space ≤ frame798.space :=
  frame638.inclusion frame798 witness2125 (by decide)
def edge2125 : CertifiedEdge catalog where
  old := 638
  next := 798
  rank := 1
  good := by
    constructor
    · exact edge2125_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2126 : Fin frame638.rank → ℕ := ![131,4,8,16,160,64]
theorem edge2126_span : frame638.space ≤ frame1003.space :=
  frame638.inclusion frame1003 witness2126 (by decide)
def edge2126 : CertifiedEdge catalog where
  old := 638
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2126_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2127 : Fin frame639.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2127_span : frame639.space ≤ frame793.space :=
  frame639.inclusion frame793 witness2127 (by decide)
def edge2127 : CertifiedEdge catalog where
  old := 639
  next := 793
  rank := 1
  good := by
    constructor
    · exact edge2127_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2128 : Fin frame639.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2128_span : frame639.space ≤ frame801.space :=
  frame639.inclusion frame801 witness2128 (by decide)
def edge2128 : CertifiedEdge catalog where
  old := 639
  next := 801
  rank := 1
  good := by
    constructor
    · exact edge2128_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2129 : Fin frame639.rank → ℕ := ![19,20,8,32,64,128]
theorem edge2129_span : frame639.space ≤ frame1003.space :=
  frame639.inclusion frame1003 witness2129 (by decide)
def edge2129 : CertifiedEdge catalog where
  old := 639
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2129_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2130 : Fin frame640.rank → ℕ := ![17,2,20,8,32,64]
theorem edge2130_span : frame640.space ≤ frame796.space :=
  frame640.inclusion frame796 witness2130 (by decide)
def edge2130 : CertifiedEdge catalog where
  old := 640
  next := 796
  rank := 1
  good := by
    constructor
    · exact edge2130_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2131 : Fin frame640.rank → ℕ := ![1,18,4,24,32,64]
theorem edge2131_span : frame640.space ≤ frame804.space :=
  frame640.inclusion frame804 witness2131 (by decide)
def edge2131 : CertifiedEdge catalog where
  old := 640
  next := 804
  rank := 1
  good := by
    constructor
    · exact edge2131_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2132 : Fin frame640.rank → ℕ := ![17,34,20,40,64,128]
theorem edge2132_span : frame640.space ≤ frame1002.space :=
  frame640.inclusion frame1002 witness2132 (by decide)
def edge2132 : CertifiedEdge catalog where
  old := 640
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2132_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2133 : Fin frame641.rank → ℕ := ![17,2,4,24,32,64]
theorem edge2133_span : frame641.space ≤ frame797.space :=
  frame641.inclusion frame797 witness2133 (by decide)
def edge2133 : CertifiedEdge catalog where
  old := 641
  next := 797
  rank := 1
  good := by
    constructor
    · exact edge2133_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2134 : Fin frame641.rank → ℕ := ![1,18,20,8,32,64]
theorem edge2134_span : frame641.space ≤ frame805.space :=
  frame641.inclusion frame805 witness2134 (by decide)
def edge2134 : CertifiedEdge catalog where
  old := 641
  next := 805
  rank := 1
  good := by
    constructor
    · exact edge2134_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2135 : Fin frame641.rank → ℕ := ![33,18,20,40,64,128]
theorem edge2135_span : frame641.space ≤ frame1002.space :=
  frame641.inclusion frame1002 witness2135 (by decide)
def edge2135 : CertifiedEdge catalog where
  old := 641
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2135_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2136 : Fin frame642.rank → ℕ := ![35,260,40,272,320,128]
theorem edge2136_span : frame642.space ≤ frame1.space :=
  frame642.inclusion frame1 witness2136 (by decide)
def edge2136 : CertifiedEdge catalog where
  old := 642
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2136_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2137 : Fin frame642.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2137_span : frame642.space ≤ frame796.space :=
  frame642.inclusion frame796 witness2137 (by decide)
def edge2137 : CertifiedEdge catalog where
  old := 642
  next := 796
  rank := 1
  good := by
    constructor
    · exact edge2137_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2138 : Fin frame642.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2138_span : frame642.space ≤ frame805.space :=
  frame642.inclusion frame805 witness2138 (by decide)
def edge2138 : CertifiedEdge catalog where
  old := 642
  next := 805
  rank := 1
  good := by
    constructor
    · exact edge2138_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2139 : Fin frame643.rank → ℕ := ![275,20,8,32,320,128]
theorem edge2139_span : frame643.space ≤ frame1.space :=
  frame643.inclusion frame1 witness2139 (by decide)
def edge2139 : CertifiedEdge catalog where
  old := 643
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2139_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2140 : Fin frame643.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2140_span : frame643.space ≤ frame797.space :=
  frame643.inclusion frame797 witness2140 (by decide)
def edge2140 : CertifiedEdge catalog where
  old := 643
  next := 797
  rank := 1
  good := by
    constructor
    · exact edge2140_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2141 : Fin frame643.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2141_span : frame643.space ≤ frame804.space :=
  frame643.inclusion frame804 witness2141 (by decide)
def edge2141 : CertifiedEdge catalog where
  old := 643
  next := 804
  rank := 1
  good := by
    constructor
    · exact edge2141_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2142 : Fin frame644.rank → ℕ := ![49,258,20,40,320,128]
theorem edge2142_span : frame644.space ≤ frame1.space :=
  frame644.inclusion frame1 witness2142 (by decide)
def edge2142 : CertifiedEdge catalog where
  old := 644
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2142_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2143 : Fin frame644.rank → ℕ := ![17,2,20,8,32,64]
theorem edge2143_span : frame644.space ≤ frame790.space :=
  frame644.inclusion frame790 witness2143 (by decide)
def edge2143 : CertifiedEdge catalog where
  old := 644
  next := 790
  rank := 1
  good := by
    constructor
    · exact edge2143_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
