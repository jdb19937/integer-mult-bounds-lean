module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2048 : Fin frame604.rank → ℕ := ![17,18,20,24]
theorem edge2048_span : frame604.space ≤ frame737.space :=
  frame604.inclusion frame737 witness2048 (by decide)
def edge2048 : CertifiedEdge catalog where
  old := 604
  next := 737
  rank := 1
  good := by
    constructor
    · exact edge2048_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2049 : Fin frame604.rank → ℕ := ![71,8,16,96]
theorem edge2049_span : frame604.space ≤ frame752.space :=
  frame604.inclusion frame752 witness2049 (by decide)
def edge2049 : CertifiedEdge catalog where
  old := 604
  next := 752
  rank := 3
  good := by
    constructor
    · exact edge2049_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2050 : Fin frame605.rank → ℕ := ![17,2,4,8]
theorem edge2050_span : frame605.space ≤ frame632.space :=
  frame605.inclusion frame632 witness2050 (by decide)
def edge2050 : CertifiedEdge catalog where
  old := 605
  next := 632
  rank := 1
  good := by
    constructor
    · exact edge2050_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2051 : Fin frame605.rank → ℕ := ![5,6,104,112]
theorem edge2051_span : frame605.space ≤ frame755.space :=
  frame605.inclusion frame755 witness2051 (by decide)
def edge2051 : CertifiedEdge catalog where
  old := 605
  next := 755
  rank := 3
  good := by
    constructor
    · exact edge2051_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2052 : Fin frame606.rank → ℕ := ![9,2,4,16]
theorem edge2052_span : frame606.space ≤ frame633.space :=
  frame606.inclusion frame633 witness2052 (by decide)
def edge2052 : CertifiedEdge catalog where
  old := 606
  next := 633
  rank := 1
  good := by
    constructor
    · exact edge2052_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2053 : Fin frame606.rank → ℕ := ![73,34,36,48]
theorem edge2053_span : frame606.space ≤ frame757.space :=
  frame606.inclusion frame757 witness2053 (by decide)
def edge2053 : CertifiedEdge catalog where
  old := 606
  next := 757
  rank := 3
  good := by
    constructor
    · exact edge2053_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2054 : Fin frame607.rank → ℕ := ![1,2,4,24]
theorem edge2054_span : frame607.space ≤ frame738.space :=
  frame607.inclusion frame738 witness2054 (by decide)
def edge2054 : CertifiedEdge catalog where
  old := 607
  next := 738
  rank := 1
  good := by
    constructor
    · exact edge2054_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2055 : Fin frame607.rank → ℕ := ![1,70,72,48]
theorem edge2055_span : frame607.space ≤ frame757.space :=
  frame607.inclusion frame757 witness2055 (by decide)
def edge2055 : CertifiedEdge catalog where
  old := 607
  next := 757
  rank := 3
  good := by
    constructor
    · exact edge2055_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2056 : Fin frame608.rank → ℕ := ![1,10,12,16,32,64]
theorem edge2056_span : frame608.space ≤ frame755.space :=
  frame608.inclusion frame755 witness2056 (by decide)
def edge2056 : CertifiedEdge catalog where
  old := 608
  next := 755
  rank := 1
  good := by
    constructor
    · exact edge2056_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2057 : Fin frame608.rank → ℕ := ![1,66,68,8,16,32]
theorem edge2057_span : frame608.space ≤ frame765.space :=
  frame608.inclusion frame765 witness2057 (by decide)
def edge2057 : CertifiedEdge catalog where
  old := 608
  next := 765
  rank := 1
  good := by
    constructor
    · exact edge2057_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2058 : Fin frame609.rank → ℕ := ![1,2,4,24]
theorem edge2058_span : frame609.space ≤ frame739.space :=
  frame609.inclusion frame739 witness2058 (by decide)
def edge2058 : CertifiedEdge catalog where
  old := 609
  next := 739
  rank := 1
  good := by
    constructor
    · exact edge2058_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2059 : Fin frame609.rank → ℕ := ![69,2,72,48]
theorem edge2059_span : frame609.space ≤ frame756.space :=
  frame609.inclusion frame756 witness2059 (by decide)
def edge2059 : CertifiedEdge catalog where
  old := 609
  next := 756
  rank := 3
  good := by
    constructor
    · exact edge2059_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2060 : Fin frame610.rank → ℕ := ![9,2,12,16,32,64]
theorem edge2060_span : frame610.space ≤ frame754.space :=
  frame610.inclusion frame754 witness2060 (by decide)
def edge2060 : CertifiedEdge catalog where
  old := 610
  next := 754
  rank := 1
  good := by
    constructor
    · exact edge2060_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2061 : Fin frame610.rank → ℕ := ![65,2,68,8,16,32]
theorem edge2061_span : frame610.space ≤ frame764.space :=
  frame610.inclusion frame764 witness2061 (by decide)
def edge2061 : CertifiedEdge catalog where
  old := 610
  next := 764
  rank := 1
  good := by
    constructor
    · exact edge2061_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2062 : Fin frame611.rank → ℕ := ![1,2,12,16]
theorem edge2062_span : frame611.space ≤ frame634.space :=
  frame611.inclusion frame634 witness2062 (by decide)
def edge2062 : CertifiedEdge catalog where
  old := 611
  next := 634
  rank := 1
  good := by
    constructor
    · exact edge2062_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2063 : Fin frame611.rank → ℕ := ![33,34,76,48]
theorem edge2063_span : frame611.space ≤ frame759.space :=
  frame611.inclusion frame759 witness2063 (by decide)
def edge2063 : CertifiedEdge catalog where
  old := 611
  next := 759
  rank := 3
  good := by
    constructor
    · exact edge2063_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2064 : Fin frame612.rank → ℕ := ![5,6,8,16]
theorem edge2064_span : frame612.space ≤ frame635.space :=
  frame612.inclusion frame635 witness2064 (by decide)
def edge2064 : CertifiedEdge catalog where
  old := 612
  next := 635
  rank := 1
  good := by
    constructor
    · exact edge2064_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2065 : Fin frame612.rank → ℕ := ![5,6,72,112]
theorem edge2065_span : frame612.space ≤ frame761.space :=
  frame612.inclusion frame761 witness2065 (by decide)
def edge2065 : CertifiedEdge catalog where
  old := 612
  next := 761
  rank := 3
  good := by
    constructor
    · exact edge2065_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2066 : Fin frame613.rank → ℕ := ![1,2,8,16]
theorem edge2066_span : frame613.space ≤ frame736.space :=
  frame613.inclusion frame736 witness2066 (by decide)
def edge2066 : CertifiedEdge catalog where
  old := 613
  next := 736
  rank := 1
  good := by
    constructor
    · exact edge2066_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2067 : Fin frame613.rank → ℕ := ![67,36,8,48]
theorem edge2067_span : frame613.space ≤ frame761.space :=
  frame613.inclusion frame761 witness2067 (by decide)
def edge2067 : CertifiedEdge catalog where
  old := 613
  next := 761
  rank := 3
  good := by
    constructor
    · exact edge2067_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2068 : Fin frame614.rank → ℕ := ![1,2,36,8,48,64]
theorem edge2068_span : frame614.space ≤ frame753.space :=
  frame614.inclusion frame753 witness2068 (by decide)
def edge2068 : CertifiedEdge catalog where
  old := 614
  next := 753
  rank := 1
  good := by
    constructor
    · exact edge2068_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2069 : Fin frame614.rank → ℕ := ![1,2,36,8,48,64]
theorem edge2069_span : frame614.space ≤ frame759.space :=
  frame614.inclusion frame759 witness2069 (by decide)
def edge2069 : CertifiedEdge catalog where
  old := 614
  next := 759
  rank := 1
  good := by
    constructor
    · exact edge2069_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2070 : Fin frame615.rank → ℕ := ![17,2,4,8]
theorem edge2070_span : frame615.space ≤ frame737.space :=
  frame615.inclusion frame737 witness2070 (by decide)
def edge2070 : CertifiedEdge catalog where
  old := 615
  next := 737
  rank := 1
  good := by
    constructor
    · exact edge2070_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2071 : Fin frame615.rank → ℕ := ![71,8,16,96]
theorem edge2071_span : frame615.space ≤ frame760.space :=
  frame615.inclusion frame760 witness2071 (by decide)
def edge2071 : CertifiedEdge catalog where
  old := 615
  next := 760
  rank := 3
  good := by
    constructor
    · exact edge2071_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2072 : Fin frame616.rank → ℕ := ![9,2,4,16]
theorem edge2072_span : frame616.space ≤ frame634.space :=
  frame616.inclusion frame634 witness2072 (by decide)
def edge2072 : CertifiedEdge catalog where
  old := 616
  next := 634
  rank := 1
  good := by
    constructor
    · exact edge2072_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2073 : Fin frame616.rank → ℕ := ![73,34,36,48]
theorem edge2073_span : frame616.space ≤ frame763.space :=
  frame616.inclusion frame763 witness2073 (by decide)
def edge2073 : CertifiedEdge catalog where
  old := 616
  next := 763
  rank := 3
  good := by
    constructor
    · exact edge2073_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2074 : Fin frame617.rank → ℕ := ![5,2,8,16]
theorem edge2074_span : frame617.space ≤ frame635.space :=
  frame617.inclusion frame635 witness2074 (by decide)
def edge2074 : CertifiedEdge catalog where
  old := 617
  next := 635
  rank := 1
  good := by
    constructor
    · exact edge2074_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2075 : Fin frame617.rank → ℕ := ![5,6,72,112]
theorem edge2075_span : frame617.space ≤ frame765.space :=
  frame617.inclusion frame765 witness2075 (by decide)
def edge2075 : CertifiedEdge catalog where
  old := 617
  next := 765
  rank := 3
  good := by
    constructor
    · exact edge2075_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2076 : Fin frame618.rank → ℕ := ![1,2,8,16]
theorem edge2076_span : frame618.space ≤ frame738.space :=
  frame618.inclusion frame738 witness2076 (by decide)
def edge2076 : CertifiedEdge catalog where
  old := 618
  next := 738
  rank := 1
  good := by
    constructor
    · exact edge2076_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2077 : Fin frame618.rank → ℕ := ![33,70,8,48]
theorem edge2077_span : frame618.space ≤ frame765.space :=
  frame618.inclusion frame765 witness2077 (by decide)
def edge2077 : CertifiedEdge catalog where
  old := 618
  next := 765
  rank := 3
  good := by
    constructor
    · exact edge2077_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2078 : Fin frame619.rank → ℕ := ![33,2,4,8,48,64]
theorem edge2078_span : frame619.space ≤ frame757.space :=
  frame619.inclusion frame757 witness2078 (by decide)
def edge2078 : CertifiedEdge catalog where
  old := 619
  next := 757
  rank := 1
  good := by
    constructor
    · exact edge2078_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2079 : Fin frame619.rank → ℕ := ![33,2,4,8,48,64]
theorem edge2079_span : frame619.space ≤ frame763.space :=
  frame619.inclusion frame763 witness2079 (by decide)
def edge2079 : CertifiedEdge catalog where
  old := 619
  next := 763
  rank := 1
  good := by
    constructor
    · exact edge2079_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
