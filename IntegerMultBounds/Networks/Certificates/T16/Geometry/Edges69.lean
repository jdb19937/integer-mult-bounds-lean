module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2208 : Fin frame666.rank → ℕ := ![193,258,68,136,272,32]
theorem edge2208_span : frame666.space ≤ frame1.space :=
  frame666.inclusion frame1 witness2208 (by decide)
def edge2208 : CertifiedEdge catalog where
  old := 666
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2208_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2209 : Fin frame666.rank → ℕ := ![1,66,4,8,80,32]
theorem edge2209_span : frame666.space ≤ frame844.space :=
  frame666.inclusion frame844 witness2209 (by decide)
def edge2209 : CertifiedEdge catalog where
  old := 666
  next := 844
  rank := 1
  good := by
    constructor
    · exact edge2209_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2210 : Fin frame666.rank → ℕ := ![65,2,68,8,16,32]
theorem edge2210_span : frame666.space ≤ frame853.space :=
  frame666.inclusion frame853 witness2210 (by decide)
def edge2210 : CertifiedEdge catalog where
  old := 666
  next := 853
  rank := 1
  good := by
    constructor
    · exact edge2210_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2211 : Fin frame667.rank → ℕ := ![257,194,68,136,272,32]
theorem edge2211_span : frame667.space ≤ frame1.space :=
  frame667.inclusion frame1 witness2211 (by decide)
def edge2211 : CertifiedEdge catalog where
  old := 667
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2211_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2212 : Fin frame667.rank → ℕ := ![1,66,68,8,16,32]
theorem edge2212_span : frame667.space ≤ frame845.space :=
  frame667.inclusion frame845 witness2212 (by decide)
def edge2212 : CertifiedEdge catalog where
  old := 667
  next := 845
  rank := 1
  good := by
    constructor
    · exact edge2212_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2213 : Fin frame667.rank → ℕ := ![65,2,4,8,80,32]
theorem edge2213_span : frame667.space ≤ frame852.space :=
  frame667.inclusion frame852 witness2213 (by decide)
def edge2213 : CertifiedEdge catalog where
  old := 667
  next := 852
  rank := 1
  good := by
    constructor
    · exact edge2213_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2214 : Fin frame668.rank → ℕ := ![323,68,8,272,32,128]
theorem edge2214_span : frame668.space ≤ frame1.space :=
  frame668.inclusion frame1 witness2214 (by decide)
def edge2214 : CertifiedEdge catalog where
  old := 668
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2214_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2215 : Fin frame668.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2215_span : frame668.space ≤ frame838.space :=
  frame668.inclusion frame838 witness2215 (by decide)
def edge2215 : CertifiedEdge catalog where
  old := 668
  next := 838
  rank := 1
  good := by
    constructor
    · exact edge2215_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2216 : Fin frame668.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2216_span : frame668.space ≤ frame849.space :=
  frame668.inclusion frame849 witness2216 (by decide)
def edge2216 : CertifiedEdge catalog where
  old := 668
  next := 849
  rank := 1
  good := by
    constructor
    · exact edge2216_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2217 : Fin frame669.rank → ℕ := ![131,260,136,272,32,320]
theorem edge2217_span : frame669.space ≤ frame1.space :=
  frame669.inclusion frame1 witness2217 (by decide)
def edge2217 : CertifiedEdge catalog where
  old := 669
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2217_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2218 : Fin frame669.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2218_span : frame669.space ≤ frame841.space :=
  frame669.inclusion frame841 witness2218 (by decide)
def edge2218 : CertifiedEdge catalog where
  old := 669
  next := 841
  rank := 1
  good := by
    constructor
    · exact edge2218_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2219 : Fin frame669.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2219_span : frame669.space ≤ frame846.space :=
  frame669.inclusion frame846 witness2219 (by decide)
def edge2219 : CertifiedEdge catalog where
  old := 669
  next := 846
  rank := 1
  good := by
    constructor
    · exact edge2219_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2220 : Fin frame670.rank → ℕ := ![257,258,36,168,176,64]
theorem edge2220_span : frame670.space ≤ frame1.space :=
  frame670.inclusion frame1 witness2220 (by decide)
def edge2220 : CertifiedEdge catalog where
  old := 670
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2220_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2221 : Fin frame670.rank → ℕ := ![1,2,4,72,80,32]
theorem edge2221_span : frame670.space ≤ frame854.space :=
  frame670.inclusion frame854 witness2221 (by decide)
def edge2221 : CertifiedEdge catalog where
  old := 670
  next := 854
  rank := 1
  good := by
    constructor
    · exact edge2221_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2222 : Fin frame670.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2222_span : frame670.space ≤ frame862.space :=
  frame670.inclusion frame862 witness2222 (by decide)
def edge2222 : CertifiedEdge catalog where
  old := 670
  next := 862
  rank := 1
  good := by
    constructor
    · exact edge2222_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2223 : Fin frame671.rank → ℕ := ![257,258,100,296,368,384]
theorem edge2223_span : frame671.space ≤ frame1.space :=
  frame671.inclusion frame1 witness2223 (by decide)
def edge2223 : CertifiedEdge catalog where
  old := 671
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2223_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2224 : Fin frame671.rank → ℕ := ![1,2,36,8,48,64]
theorem edge2224_span : frame671.space ≤ frame857.space :=
  frame671.inclusion frame857 witness2224 (by decide)
def edge2224 : CertifiedEdge catalog where
  old := 671
  next := 857
  rank := 1
  good := by
    constructor
    · exact edge2224_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2225 : Fin frame671.rank → ℕ := ![65,66,4,72,80,96]
theorem edge2225_span : frame671.space ≤ frame865.space :=
  frame671.inclusion frame865 witness2225 (by decide)
def edge2225 : CertifiedEdge catalog where
  old := 671
  next := 865
  rank := 1
  good := by
    constructor
    · exact edge2225_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2226 : Fin frame672.rank → ℕ := ![257,258,324,392,464,288]
theorem edge2226_span : frame672.space ≤ frame1.space :=
  frame672.inclusion frame1 witness2226 (by decide)
def edge2226 : CertifiedEdge catalog where
  old := 672
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2226_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2227 : Fin frame672.rank → ℕ := ![1,2,68,8,80,32]
theorem edge2227_span : frame672.space ≤ frame860.space :=
  frame672.inclusion frame860 witness2227 (by decide)
def edge2227 : CertifiedEdge catalog where
  old := 672
  next := 860
  rank := 1
  good := by
    constructor
    · exact edge2227_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2228 : Fin frame672.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2228_span : frame672.space ≤ frame868.space :=
  frame672.inclusion frame868 witness2228 (by decide)
def edge2228 : CertifiedEdge catalog where
  old := 672
  next := 868
  rank := 1
  good := by
    constructor
    · exact edge2228_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2229 : Fin frame673.rank → ℕ := ![257,258,132,72,16,224]
theorem edge2229_span : frame673.space ≤ frame1.space :=
  frame673.inclusion frame1 witness2229 (by decide)
def edge2229 : CertifiedEdge catalog where
  old := 673
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2229_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2230 : Fin frame673.rank → ℕ := ![1,2,4,72,16,96]
theorem edge2230_span : frame673.space ≤ frame861.space :=
  frame673.inclusion frame861 witness2230 (by decide)
def edge2230 : CertifiedEdge catalog where
  old := 673
  next := 861
  rank := 1
  good := by
    constructor
    · exact edge2230_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2231 : Fin frame673.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2231_span : frame673.space ≤ frame869.space :=
  frame673.inclusion frame869 witness2231 (by decide)
def edge2231 : CertifiedEdge catalog where
  old := 673
  next := 869
  rank := 1
  good := by
    constructor
    · exact edge2231_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2232 : Fin frame674.rank → ℕ := ![1,2,4,72,16,96]
theorem edge2232_span : frame674.space ≤ frame860.space :=
  frame674.inclusion frame860 witness2232 (by decide)
def edge2232 : CertifiedEdge catalog where
  old := 674
  next := 860
  rank := 1
  good := by
    constructor
    · exact edge2232_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2233 : Fin frame674.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2233_span : frame674.space ≤ frame869.space :=
  frame674.inclusion frame869 witness2233 (by decide)
def edge2233 : CertifiedEdge catalog where
  old := 674
  next := 869
  rank := 1
  good := by
    constructor
    · exact edge2233_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2234 : Fin frame674.rank → ℕ := ![129,130,132,200,144,224]
theorem edge2234_span : frame674.space ≤ frame1001.space :=
  frame674.inclusion frame1001 witness2234 (by decide)
def edge2234 : CertifiedEdge catalog where
  old := 674
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2234_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2235 : Fin frame675.rank → ℕ := ![1,2,68,8,80,32]
theorem edge2235_span : frame675.space ≤ frame861.space :=
  frame675.inclusion frame861 witness2235 (by decide)
def edge2235 : CertifiedEdge catalog where
  old := 675
  next := 861
  rank := 1
  good := by
    constructor
    · exact edge2235_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2236 : Fin frame675.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2236_span : frame675.space ≤ frame868.space :=
  frame675.inclusion frame868 witness2236 (by decide)
def edge2236 : CertifiedEdge catalog where
  old := 675
  next := 868
  rank := 1
  good := by
    constructor
    · exact edge2236_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2237 : Fin frame675.rank → ℕ := ![129,130,68,8,80,32]
theorem edge2237_span : frame675.space ≤ frame1001.space :=
  frame675.inclusion frame1001 witness2237 (by decide)
def edge2237 : CertifiedEdge catalog where
  old := 675
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2237_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2238 : Fin frame676.rank → ℕ := ![1,2,36,8,48,64]
theorem edge2238_span : frame676.space ≤ frame854.space :=
  frame676.inclusion frame854 witness2238 (by decide)
def edge2238 : CertifiedEdge catalog where
  old := 676
  next := 854
  rank := 1
  good := by
    constructor
    · exact edge2238_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2239 : Fin frame676.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2239_span : frame676.space ≤ frame865.space :=
  frame676.inclusion frame865 witness2239 (by decide)
def edge2239 : CertifiedEdge catalog where
  old := 676
  next := 865
  rank := 1
  good := by
    constructor
    · exact edge2239_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
