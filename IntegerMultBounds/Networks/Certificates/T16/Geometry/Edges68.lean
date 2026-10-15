module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2176 : Fin frame655.rank → ℕ := ![65,66,68,72,16,96]
theorem edge2176_span : frame655.space ≤ frame833.space :=
  frame655.inclusion frame833 witness2176 (by decide)
def edge2176 : CertifiedEdge catalog where
  old := 655
  next := 833
  rank := 1
  good := by
    constructor
    · exact edge2176_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2177 : Fin frame655.rank → ℕ := ![65,66,196,72,144,96]
theorem edge2177_span : frame655.space ≤ frame1003.space :=
  frame655.inclusion frame1003 witness2177 (by decide)
def edge2177 : CertifiedEdge catalog where
  old := 655
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2177_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2178 : Fin frame656.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2178_span : frame656.space ≤ frame828.space :=
  frame656.inclusion frame828 witness2178 (by decide)
def edge2178 : CertifiedEdge catalog where
  old := 656
  next := 828
  rank := 1
  good := by
    constructor
    · exact edge2178_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2179 : Fin frame656.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2179_span : frame656.space ≤ frame836.space :=
  frame656.inclusion frame836 witness2179 (by decide)
def edge2179 : CertifiedEdge catalog where
  old := 656
  next := 836
  rank := 1
  good := by
    constructor
    · exact edge2179_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2180 : Fin frame656.rank → ℕ := ![65,66,68,72,208,224]
theorem edge2180_span : frame656.space ≤ frame1000.space :=
  frame656.inclusion frame1000 witness2180 (by decide)
def edge2180 : CertifiedEdge catalog where
  old := 656
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2180_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2181 : Fin frame657.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2181_span : frame657.space ≤ frame829.space :=
  frame657.inclusion frame829 witness2181 (by decide)
def edge2181 : CertifiedEdge catalog where
  old := 657
  next := 829
  rank := 1
  good := by
    constructor
    · exact edge2181_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2182 : Fin frame657.rank → ℕ := ![1,2,68,72,16,32]
theorem edge2182_span : frame657.space ≤ frame837.space :=
  frame657.inclusion frame837 witness2182 (by decide)
def edge2182 : CertifiedEdge catalog where
  old := 657
  next := 837
  rank := 1
  good := by
    constructor
    · exact edge2182_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2183 : Fin frame657.rank → ℕ := ![65,66,132,136,16,32]
theorem edge2183_span : frame657.space ≤ frame1000.space :=
  frame657.inclusion frame1000 witness2183 (by decide)
def edge2183 : CertifiedEdge catalog where
  old := 657
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2183_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2184 : Fin frame658.rank → ℕ := ![65,66,260,8,400,160]
theorem edge2184_span : frame658.space ≤ frame1.space :=
  frame658.inclusion frame1 witness2184 (by decide)
def edge2184 : CertifiedEdge catalog where
  old := 658
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2184_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2185 : Fin frame658.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2185_span : frame658.space ≤ frame828.space :=
  frame658.inclusion frame828 witness2185 (by decide)
def edge2185 : CertifiedEdge catalog where
  old := 658
  next := 828
  rank := 1
  good := by
    constructor
    · exact edge2185_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2186 : Fin frame658.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2186_span : frame658.space ≤ frame837.space :=
  frame658.inclusion frame837 witness2186 (by decide)
def edge2186 : CertifiedEdge catalog where
  old := 658
  next := 837
  rank := 1
  good := by
    constructor
    · exact edge2186_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2187 : Fin frame659.rank → ℕ := ![65,66,196,456,80,352]
theorem edge2187_span : frame659.space ≤ frame1.space :=
  frame659.inclusion frame1 witness2187 (by decide)
def edge2187 : CertifiedEdge catalog where
  old := 659
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2187_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2188 : Fin frame659.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2188_span : frame659.space ≤ frame829.space :=
  frame659.inclusion frame829 witness2188 (by decide)
def edge2188 : CertifiedEdge catalog where
  old := 659
  next := 829
  rank := 1
  good := by
    constructor
    · exact edge2188_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2189 : Fin frame659.rank → ℕ := ![1,2,68,72,16,32]
theorem edge2189_span : frame659.space ≤ frame836.space :=
  frame659.inclusion frame836 witness2189 (by decide)
def edge2189 : CertifiedEdge catalog where
  old := 659
  next := 836
  rank := 1
  good := by
    constructor
    · exact edge2189_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2190 : Fin frame660.rank → ℕ := ![257,258,420,168,304,320]
theorem edge2190_span : frame660.space ≤ frame1.space :=
  frame660.inclusion frame1 witness2190 (by decide)
def edge2190 : CertifiedEdge catalog where
  old := 660
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2190_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2191 : Fin frame660.rank → ℕ := ![65,66,68,8,80,96]
theorem edge2191_span : frame660.space ≤ frame822.space :=
  frame660.inclusion frame822 witness2191 (by decide)
def edge2191 : CertifiedEdge catalog where
  old := 660
  next := 822
  rank := 1
  good := by
    constructor
    · exact edge2191_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2192 : Fin frame660.rank → ℕ := ![1,2,68,72,16,32]
theorem edge2192_span : frame660.space ≤ frame833.space :=
  frame660.inclusion frame833 witness2192 (by decide)
def edge2192 : CertifiedEdge catalog where
  old := 660
  next := 833
  rank := 1
  good := by
    constructor
    · exact edge2192_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2193 : Fin frame661.rank → ℕ := ![65,66,292,40,304,128]
theorem edge2193_span : frame661.space ≤ frame1.space :=
  frame661.inclusion frame1 witness2193 (by decide)
def edge2193 : CertifiedEdge catalog where
  old := 661
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2193_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2194 : Fin frame661.rank → ℕ := ![33,34,4,8,16,64]
theorem edge2194_span : frame661.space ≤ frame825.space :=
  frame661.inclusion frame825 witness2194 (by decide)
def edge2194 : CertifiedEdge catalog where
  old := 661
  next := 825
  rank := 1
  good := by
    constructor
    · exact edge2194_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2195 : Fin frame661.rank → ℕ := ![1,2,68,8,80,32]
theorem edge2195_span : frame661.space ≤ frame830.space :=
  frame661.inclusion frame830 witness2195 (by decide)
def edge2195 : CertifiedEdge catalog where
  old := 661
  next := 830
  rank := 1
  good := by
    constructor
    · exact edge2195_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2196 : Fin frame662.rank → ℕ := ![1,66,4,72,16,32]
theorem edge2196_span : frame662.space ≤ frame838.space :=
  frame662.inclusion frame838 witness2196 (by decide)
def edge2196 : CertifiedEdge catalog where
  old := 662
  next := 838
  rank := 1
  good := by
    constructor
    · exact edge2196_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2197 : Fin frame662.rank → ℕ := ![65,2,68,8,16,32]
theorem edge2197_span : frame662.space ≤ frame846.space :=
  frame662.inclusion frame846 witness2197 (by decide)
def edge2197 : CertifiedEdge catalog where
  old := 662
  next := 846
  rank := 1
  good := by
    constructor
    · exact edge2197_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2198 : Fin frame662.rank → ℕ := ![65,130,68,136,16,32]
theorem edge2198_span : frame662.space ≤ frame1002.space :=
  frame662.inclusion frame1002 witness2198 (by decide)
def edge2198 : CertifiedEdge catalog where
  old := 662
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2198_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2199 : Fin frame663.rank → ℕ := ![1,66,68,8,16,32]
theorem edge2199_span : frame663.space ≤ frame841.space :=
  frame663.inclusion frame841 witness2199 (by decide)
def edge2199 : CertifiedEdge catalog where
  old := 663
  next := 841
  rank := 1
  good := by
    constructor
    · exact edge2199_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2200 : Fin frame663.rank → ℕ := ![65,2,4,72,16,32]
theorem edge2200_span : frame663.space ≤ frame849.space :=
  frame663.inclusion frame849 witness2200 (by decide)
def edge2200 : CertifiedEdge catalog where
  old := 663
  next := 849
  rank := 1
  good := by
    constructor
    · exact edge2200_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2201 : Fin frame663.rank → ℕ := ![129,66,68,136,16,32]
theorem edge2201_span : frame663.space ≤ frame1002.space :=
  frame663.inclusion frame1002 witness2201 (by decide)
def edge2201 : CertifiedEdge catalog where
  old := 663
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2201_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2202 : Fin frame664.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2202_span : frame664.space ≤ frame844.space :=
  frame664.inclusion frame844 witness2202 (by decide)
def edge2202 : CertifiedEdge catalog where
  old := 664
  next := 844
  rank := 1
  good := by
    constructor
    · exact edge2202_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2203 : Fin frame664.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2203_span : frame664.space ≤ frame852.space :=
  frame664.inclusion frame852 witness2203 (by decide)
def edge2203 : CertifiedEdge catalog where
  old := 664
  next := 852
  rank := 1
  good := by
    constructor
    · exact edge2203_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2204 : Fin frame664.rank → ℕ := ![67,68,8,16,32,128]
theorem edge2204_span : frame664.space ≤ frame1001.space :=
  frame664.inclusion frame1001 witness2204 (by decide)
def edge2204 : CertifiedEdge catalog where
  old := 664
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2204_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2205 : Fin frame665.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2205_span : frame665.space ≤ frame845.space :=
  frame665.inclusion frame845 witness2205 (by decide)
def edge2205 : CertifiedEdge catalog where
  old := 665
  next := 845
  rank := 1
  good := by
    constructor
    · exact edge2205_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2206 : Fin frame665.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2206_span : frame665.space ≤ frame853.space :=
  frame665.inclusion frame853 witness2206 (by decide)
def edge2206 : CertifiedEdge catalog where
  old := 665
  next := 853
  rank := 1
  good := by
    constructor
    · exact edge2206_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2207 : Fin frame665.rank → ℕ := ![131,4,8,144,32,64]
theorem edge2207_span : frame665.space ≤ frame1001.space :=
  frame665.inclusion frame1001 witness2207 (by decide)
def edge2207 : CertifiedEdge catalog where
  old := 665
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2207_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
