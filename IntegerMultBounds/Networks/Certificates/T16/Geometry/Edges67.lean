module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2144 : Fin frame644.rank → ℕ := ![1,66,4,8,80,32]
theorem edge2144_span : frame644.space ≤ frame801.space :=
  frame644.inclusion frame801 witness2144 (by decide)
def edge2144 : CertifiedEdge catalog where
  old := 644
  next := 801
  rank := 1
  good := by
    constructor
    · exact edge2144_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2145 : Fin frame645.rank → ℕ := ![257,50,20,40,320,128]
theorem edge2145_span : frame645.space ≤ frame1.space :=
  frame645.inclusion frame1 witness2145 (by decide)
def edge2145 : CertifiedEdge catalog where
  old := 645
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2145_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2146 : Fin frame645.rank → ℕ := ![65,2,4,8,80,32]
theorem edge2146_span : frame645.space ≤ frame793.space :=
  frame645.inclusion frame793 witness2146 (by decide)
def edge2146 : CertifiedEdge catalog where
  old := 645
  next := 793
  rank := 1
  good := by
    constructor
    · exact edge2146_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2147 : Fin frame645.rank → ℕ := ![1,18,20,8,32,64]
theorem edge2147_span : frame645.space ≤ frame798.space :=
  frame645.inclusion frame798 witness2147 (by decide)
def edge2147 : CertifiedEdge catalog where
  old := 645
  next := 798
  rank := 1
  good := by
    constructor
    · exact edge2147_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2148 : Fin frame646.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2148_span : frame646.space ≤ frame806.space :=
  frame646.inclusion frame806 witness2148 (by decide)
def edge2148 : CertifiedEdge catalog where
  old := 646
  next := 806
  rank := 1
  good := by
    constructor
    · exact edge2148_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2149 : Fin frame646.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2149_span : frame646.space ≤ frame814.space :=
  frame646.inclusion frame814 witness2149 (by decide)
def edge2149 : CertifiedEdge catalog where
  old := 646
  next := 814
  rank := 1
  good := by
    constructor
    · exact edge2149_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2150 : Fin frame646.rank → ℕ := ![161,162,164,168,176,192]
theorem edge2150_span : frame646.space ≤ frame1000.space :=
  frame646.inclusion frame1000 witness2150 (by decide)
def edge2150 : CertifiedEdge catalog where
  old := 646
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2150_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2151 : Fin frame647.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2151_span : frame647.space ≤ frame809.space :=
  frame647.inclusion frame809 witness2151 (by decide)
def edge2151 : CertifiedEdge catalog where
  old := 647
  next := 809
  rank := 1
  good := by
    constructor
    · exact edge2151_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2152 : Fin frame647.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2152_span : frame647.space ≤ frame817.space :=
  frame647.inclusion frame817 witness2152 (by decide)
def edge2152 : CertifiedEdge catalog where
  old := 647
  next := 817
  rank := 1
  good := by
    constructor
    · exact edge2152_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2153 : Fin frame647.rank → ℕ := ![17,18,36,40,64,128]
theorem edge2153_span : frame647.space ≤ frame1000.space :=
  frame647.inclusion frame1000 witness2153 (by decide)
def edge2153 : CertifiedEdge catalog where
  old := 647
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2153_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2154 : Fin frame648.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2154_span : frame648.space ≤ frame812.space :=
  frame648.inclusion frame812 witness2154 (by decide)
def edge2154 : CertifiedEdge catalog where
  old := 648
  next := 812
  rank := 1
  good := by
    constructor
    · exact edge2154_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2155 : Fin frame648.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2155_span : frame648.space ≤ frame820.space :=
  frame648.inclusion frame820 witness2155 (by decide)
def edge2155 : CertifiedEdge catalog where
  old := 648
  next := 820
  rank := 1
  good := by
    constructor
    · exact edge2155_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2156 : Fin frame648.rank → ℕ := ![33,34,164,40,48,192]
theorem edge2156_span : frame648.space ≤ frame1001.space :=
  frame648.inclusion frame1001 witness2156 (by decide)
def edge2156 : CertifiedEdge catalog where
  old := 648
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2156_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2157 : Fin frame649.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2157_span : frame649.space ≤ frame813.space :=
  frame649.inclusion frame813 witness2157 (by decide)
def edge2157 : CertifiedEdge catalog where
  old := 649
  next := 813
  rank := 1
  good := by
    constructor
    · exact edge2157_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2158 : Fin frame649.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2158_span : frame649.space ≤ frame821.space :=
  frame649.inclusion frame821 witness2158 (by decide)
def edge2158 : CertifiedEdge catalog where
  old := 649
  next := 821
  rank := 1
  good := by
    constructor
    · exact edge2158_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2159 : Fin frame649.rank → ℕ := ![17,18,36,40,64,128]
theorem edge2159_span : frame649.space ≤ frame1001.space :=
  frame649.inclusion frame1001 witness2159 (by decide)
def edge2159 : CertifiedEdge catalog where
  old := 649
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2159_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2160 : Fin frame650.rank → ℕ := ![257,258,420,168,272,448]
theorem edge2160_span : frame650.space ≤ frame1.space :=
  frame650.inclusion frame1 witness2160 (by decide)
def edge2160 : CertifiedEdge catalog where
  old := 650
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2160_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2161 : Fin frame650.rank → ℕ := ![1,2,36,40,16,64]
theorem edge2161_span : frame650.space ≤ frame812.space :=
  frame650.inclusion frame812 witness2161 (by decide)
def edge2161 : CertifiedEdge catalog where
  old := 650
  next := 812
  rank := 1
  good := by
    constructor
    · exact edge2161_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2162 : Fin frame650.rank → ℕ := ![65,66,68,8,80,96]
theorem edge2162_span : frame650.space ≤ frame821.space :=
  frame650.inclusion frame821 witness2162 (by decide)
def edge2162 : CertifiedEdge catalog where
  old := 650
  next := 821
  rank := 1
  good := by
    constructor
    · exact edge2162_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2163 : Fin frame651.rank → ℕ := ![17,18,388,136,32,448]
theorem edge2163_span : frame651.space ≤ frame1.space :=
  frame651.inclusion frame1 witness2163 (by decide)
def edge2163 : CertifiedEdge catalog where
  old := 651
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2163_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2164 : Fin frame651.rank → ℕ := ![1,2,68,8,16,96]
theorem edge2164_span : frame651.space ≤ frame813.space :=
  frame651.inclusion frame813 witness2164 (by decide)
def edge2164 : CertifiedEdge catalog where
  old := 651
  next := 813
  rank := 1
  good := by
    constructor
    · exact edge2164_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2165 : Fin frame651.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2165_span : frame651.space ≤ frame820.space :=
  frame651.inclusion frame820 witness2165 (by decide)
def edge2165 : CertifiedEdge catalog where
  old := 651
  next := 820
  rank := 1
  good := by
    constructor
    · exact edge2165_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2166 : Fin frame652.rank → ℕ := ![385,386,420,168,400,448]
theorem edge2166_span : frame652.space ≤ frame1.space :=
  frame652.inclusion frame1 witness2166 (by decide)
def edge2166 : CertifiedEdge catalog where
  old := 652
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2166_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2167 : Fin frame652.rank → ℕ := ![1,2,36,40,16,64]
theorem edge2167_span : frame652.space ≤ frame806.space :=
  frame652.inclusion frame806 witness2167 (by decide)
def edge2167 : CertifiedEdge catalog where
  old := 652
  next := 806
  rank := 1
  good := by
    constructor
    · exact edge2167_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2168 : Fin frame652.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2168_span : frame652.space ≤ frame817.space :=
  frame652.inclusion frame817 witness2168 (by decide)
def edge2168 : CertifiedEdge catalog where
  old := 652
  next := 817
  rank := 1
  good := by
    constructor
    · exact edge2168_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2169 : Fin frame653.rank → ℕ := ![17,18,260,8,160,448]
theorem edge2169_span : frame653.space ≤ frame1.space :=
  frame653.inclusion frame1 witness2169 (by decide)
def edge2169 : CertifiedEdge catalog where
  old := 653
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2169_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2170 : Fin frame653.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2170_span : frame653.space ≤ frame809.space :=
  frame653.inclusion frame809 witness2170 (by decide)
def edge2170 : CertifiedEdge catalog where
  old := 653
  next := 809
  rank := 1
  good := by
    constructor
    · exact edge2170_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2171 : Fin frame653.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2171_span : frame653.space ≤ frame814.space :=
  frame653.inclusion frame814 witness2171 (by decide)
def edge2171 : CertifiedEdge catalog where
  old := 653
  next := 814
  rank := 1
  good := by
    constructor
    · exact edge2171_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2172 : Fin frame654.rank → ℕ := ![33,34,4,8,16,64]
theorem edge2172_span : frame654.space ≤ frame822.space :=
  frame654.inclusion frame822 witness2172 (by decide)
def edge2172 : CertifiedEdge catalog where
  old := 654
  next := 822
  rank := 1
  good := by
    constructor
    · exact edge2172_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2173 : Fin frame654.rank → ℕ := ![1,2,36,40,16,64]
theorem edge2173_span : frame654.space ≤ frame830.space :=
  frame654.inclusion frame830 witness2173 (by decide)
def edge2173 : CertifiedEdge catalog where
  old := 654
  next := 830
  rank := 1
  good := by
    constructor
    · exact edge2173_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2174 : Fin frame654.rank → ℕ := ![33,34,68,72,16,128]
theorem edge2174_span : frame654.space ≤ frame1003.space :=
  frame654.inclusion frame1003 witness2174 (by decide)
def edge2174 : CertifiedEdge catalog where
  old := 654
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2174_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2175 : Fin frame655.rank → ℕ := ![65,66,68,72,16,96]
theorem edge2175_span : frame655.space ≤ frame825.space :=
  frame655.inclusion frame825 witness2175 (by decide)
def edge2175 : CertifiedEdge catalog where
  old := 655
  next := 825
  rank := 1
  good := by
    constructor
    · exact edge2175_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
