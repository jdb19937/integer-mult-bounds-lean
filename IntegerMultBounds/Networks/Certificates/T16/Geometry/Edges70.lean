module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2240 : Fin frame676.rank → ℕ := ![129,130,36,8,48,64]
theorem edge2240_span : frame676.space ≤ frame1003.space :=
  frame676.inclusion frame1003 witness2240 (by decide)
def edge2240 : CertifiedEdge catalog where
  old := 676
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2240_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2241 : Fin frame677.rank → ℕ := ![1,2,4,72,80,32]
theorem edge2241_span : frame677.space ≤ frame857.space :=
  frame677.inclusion frame857 witness2241 (by decide)
def edge2241 : CertifiedEdge catalog where
  old := 677
  next := 857
  rank := 1
  good := by
    constructor
    · exact edge2241_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2242 : Fin frame677.rank → ℕ := ![65,66,68,8,80,96]
theorem edge2242_span : frame677.space ≤ frame862.space :=
  frame677.inclusion frame862 witness2242 (by decide)
def edge2242 : CertifiedEdge catalog where
  old := 677
  next := 862
  rank := 1
  good := by
    constructor
    · exact edge2242_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2243 : Fin frame677.rank → ℕ := ![129,130,132,72,208,160]
theorem edge2243_span : frame677.space ≤ frame1003.space :=
  frame677.inclusion frame1003 witness2243 (by decide)
def edge2243 : CertifiedEdge catalog where
  old := 677
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2243_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2244 : Fin frame678.rank → ℕ := ![321,130,260,8,80,160]
theorem edge2244_span : frame678.space ≤ frame1.space :=
  frame678.inclusion frame1 witness2244 (by decide)
def edge2244 : CertifiedEdge catalog where
  old := 678
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2244_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2245 : Fin frame678.rank → ℕ := ![65,2,4,8,80,32]
theorem edge2245_span : frame678.space ≤ frame870.space :=
  frame678.inclusion frame870 witness2245 (by decide)
def edge2245 : CertifiedEdge catalog where
  old := 678
  next := 870
  rank := 1
  good := by
    constructor
    · exact edge2245_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2246 : Fin frame678.rank → ℕ := ![1,66,4,8,16,96]
theorem edge2246_span : frame678.space ≤ frame878.space :=
  frame678.inclusion frame878 witness2246 (by decide)
def edge2246 : CertifiedEdge catalog where
  old := 678
  next := 878
  rank := 1
  good := by
    constructor
    · exact edge2246_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2247 : Fin frame679.rank → ℕ := ![129,322,260,8,80,160]
theorem edge2247_span : frame679.space ≤ frame1.space :=
  frame679.inclusion frame1 witness2247 (by decide)
def edge2247 : CertifiedEdge catalog where
  old := 679
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2247_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2248 : Fin frame679.rank → ℕ := ![65,2,4,8,16,96]
theorem edge2248_span : frame679.space ≤ frame873.space :=
  frame679.inclusion frame873 witness2248 (by decide)
def edge2248 : CertifiedEdge catalog where
  old := 679
  next := 873
  rank := 1
  good := by
    constructor
    · exact edge2248_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2249 : Fin frame679.rank → ℕ := ![1,66,4,8,80,32]
theorem edge2249_span : frame679.space ≤ frame881.space :=
  frame679.inclusion frame881 witness2249 (by decide)
def edge2249 : CertifiedEdge catalog where
  old := 679
  next := 881
  rank := 1
  good := by
    constructor
    · exact edge2249_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2250 : Fin frame680.rank → ℕ := ![387,260,8,16,160,64]
theorem edge2250_span : frame680.space ≤ frame1.space :=
  frame680.inclusion frame1 witness2250 (by decide)
def edge2250 : CertifiedEdge catalog where
  old := 680
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2250_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2251 : Fin frame680.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2251_span : frame680.space ≤ frame876.space :=
  frame680.inclusion frame876 witness2251 (by decide)
def edge2251 : CertifiedEdge catalog where
  old := 680
  next := 876
  rank := 1
  good := by
    constructor
    · exact edge2251_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2252 : Fin frame680.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2252_span : frame680.space ≤ frame884.space :=
  frame680.inclusion frame884 witness2252 (by decide)
def edge2252 : CertifiedEdge catalog where
  old := 680
  next := 884
  rank := 1
  good := by
    constructor
    · exact edge2252_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2253 : Fin frame681.rank → ℕ := ![67,260,8,80,288,384]
theorem edge2253_span : frame681.space ≤ frame1.space :=
  frame681.inclusion frame1 witness2253 (by decide)
def edge2253 : CertifiedEdge catalog where
  old := 681
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2253_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2254 : Fin frame681.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2254_span : frame681.space ≤ frame877.space :=
  frame681.inclusion frame877 witness2254 (by decide)
def edge2254 : CertifiedEdge catalog where
  old := 681
  next := 877
  rank := 1
  good := by
    constructor
    · exact edge2254_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2255 : Fin frame681.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2255_span : frame681.space ≤ frame885.space :=
  frame681.inclusion frame885 witness2255 (by decide)
def edge2255 : CertifiedEdge catalog where
  old := 681
  next := 885
  rank := 1
  good := by
    constructor
    · exact edge2255_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2256 : Fin frame682.rank → ℕ := ![65,2,4,8,80,32]
theorem edge2256_span : frame682.space ≤ frame876.space :=
  frame682.inclusion frame876 witness2256 (by decide)
def edge2256 : CertifiedEdge catalog where
  old := 682
  next := 876
  rank := 1
  good := by
    constructor
    · exact edge2256_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2257 : Fin frame682.rank → ℕ := ![1,66,4,8,16,96]
theorem edge2257_span : frame682.space ≤ frame885.space :=
  frame682.inclusion frame885 witness2257 (by decide)
def edge2257 : CertifiedEdge catalog where
  old := 682
  next := 885
  rank := 1
  good := by
    constructor
    · exact edge2257_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2258 : Fin frame682.rank → ℕ := ![65,130,4,8,80,160]
theorem edge2258_span : frame682.space ≤ frame1000.space :=
  frame682.inclusion frame1000 witness2258 (by decide)
def edge2258 : CertifiedEdge catalog where
  old := 682
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2258_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2259 : Fin frame683.rank → ℕ := ![65,2,4,8,16,96]
theorem edge2259_span : frame683.space ≤ frame877.space :=
  frame683.inclusion frame877 witness2259 (by decide)
def edge2259 : CertifiedEdge catalog where
  old := 683
  next := 877
  rank := 1
  good := by
    constructor
    · exact edge2259_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2260 : Fin frame683.rank → ℕ := ![1,66,4,8,80,32]
theorem edge2260_span : frame683.space ≤ frame884.space :=
  frame683.inclusion frame884 witness2260 (by decide)
def edge2260 : CertifiedEdge catalog where
  old := 683
  next := 884
  rank := 1
  good := by
    constructor
    · exact edge2260_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2261 : Fin frame683.rank → ℕ := ![129,66,4,8,80,160]
theorem edge2261_span : frame683.space ≤ frame1000.space :=
  frame683.inclusion frame1000 witness2261 (by decide)
def edge2261 : CertifiedEdge catalog where
  old := 683
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2261_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2262 : Fin frame684.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2262_span : frame684.space ≤ frame870.space :=
  frame684.inclusion frame870 witness2262 (by decide)
def edge2262 : CertifiedEdge catalog where
  old := 684
  next := 870
  rank := 1
  good := by
    constructor
    · exact edge2262_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2263 : Fin frame684.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2263_span : frame684.space ≤ frame881.space :=
  frame684.inclusion frame881 witness2263 (by decide)
def edge2263 : CertifiedEdge catalog where
  old := 684
  next := 881
  rank := 1
  good := by
    constructor
    · exact edge2263_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2264 : Fin frame684.rank → ℕ := ![131,4,8,16,160,64]
theorem edge2264_span : frame684.space ≤ frame1002.space :=
  frame684.inclusion frame1002 witness2264 (by decide)
def edge2264 : CertifiedEdge catalog where
  old := 684
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2264_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2265 : Fin frame685.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2265_span : frame685.space ≤ frame873.space :=
  frame685.inclusion frame873 witness2265 (by decide)
def edge2265 : CertifiedEdge catalog where
  old := 685
  next := 873
  rank := 1
  good := by
    constructor
    · exact edge2265_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2266 : Fin frame685.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2266_span : frame685.space ≤ frame878.space :=
  frame685.inclusion frame878 witness2266 (by decide)
def edge2266 : CertifiedEdge catalog where
  old := 685
  next := 878
  rank := 1
  good := by
    constructor
    · exact edge2266_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2267 : Fin frame685.rank → ℕ := ![67,4,8,80,32,128]
theorem edge2267_span : frame685.space ≤ frame1002.space :=
  frame685.inclusion frame1002 witness2267 (by decide)
def edge2267 : CertifiedEdge catalog where
  old := 685
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2267_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2268 : Fin frame686.rank → ℕ := ![9,10,388,272,32,448]
theorem edge2268_span : frame686.space ≤ frame1.space :=
  frame686.inclusion frame1 witness2268 (by decide)
def edge2268 : CertifiedEdge catalog where
  old := 686
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2268_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2269 : Fin frame686.rank → ℕ := ![9,10,4,16,32,64]
theorem edge2269_span : frame686.space ≤ frame886.space :=
  frame686.inclusion frame886 witness2269 (by decide)
def edge2269 : CertifiedEdge catalog where
  old := 686
  next := 886
  rank := 1
  good := by
    constructor
    · exact edge2269_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2270 : Fin frame686.rank → ℕ := ![1,2,68,8,16,96]
theorem edge2270_span : frame686.space ≤ frame894.space :=
  frame686.inclusion frame894 witness2270 (by decide)
def edge2270 : CertifiedEdge catalog where
  old := 686
  next := 894
  rank := 1
  good := by
    constructor
    · exact edge2270_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2271 : Fin frame687.rank → ℕ := ![129,130,420,136,304,448]
theorem edge2271_span : frame687.space ≤ frame1.space :=
  frame687.inclusion frame1 witness2271 (by decide)
def edge2271 : CertifiedEdge catalog where
  old := 687
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2271_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
