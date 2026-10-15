module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2272 : Fin frame687.rank → ℕ := ![65,66,68,72,16,96]
theorem edge2272_span : frame687.space ≤ frame889.space :=
  frame687.inclusion frame889 witness2272 (by decide)
def edge2272 : CertifiedEdge catalog where
  old := 687
  next := 889
  rank := 1
  good := by
    constructor
    · exact edge2272_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2273 : Fin frame687.rank → ℕ := ![1,2,36,8,48,64]
theorem edge2273_span : frame687.space ≤ frame897.space :=
  frame687.inclusion frame897 witness2273 (by decide)
def edge2273 : CertifiedEdge catalog where
  old := 687
  next := 897
  rank := 1
  good := by
    constructor
    · exact edge2273_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2274 : Fin frame688.rank → ℕ := ![385,386,420,392,304,448]
theorem edge2274_span : frame688.space ≤ frame1.space :=
  frame688.inclusion frame1 witness2274 (by decide)
def edge2274 : CertifiedEdge catalog where
  old := 688
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2274_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2275 : Fin frame688.rank → ℕ := ![65,66,68,72,16,96]
theorem edge2275_span : frame688.space ≤ frame892.space :=
  frame688.inclusion frame892 witness2275 (by decide)
def edge2275 : CertifiedEdge catalog where
  old := 688
  next := 892
  rank := 1
  good := by
    constructor
    · exact edge2275_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2276 : Fin frame688.rank → ℕ := ![1,2,36,8,48,64]
theorem edge2276_span : frame688.space ≤ frame900.space :=
  frame688.inclusion frame900 witness2276 (by decide)
def edge2276 : CertifiedEdge catalog where
  old := 688
  next := 900
  rank := 1
  good := by
    constructor
    · exact edge2276_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2277 : Fin frame689.rank → ℕ := ![9,10,132,16,288,448]
theorem edge2277_span : frame689.space ≤ frame1.space :=
  frame689.inclusion frame1 witness2277 (by decide)
def edge2277 : CertifiedEdge catalog where
  old := 689
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2277_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2278 : Fin frame689.rank → ℕ := ![9,10,4,16,32,64]
theorem edge2278_span : frame689.space ≤ frame893.space :=
  frame689.inclusion frame893 witness2278 (by decide)
def edge2278 : CertifiedEdge catalog where
  old := 689
  next := 893
  rank := 1
  good := by
    constructor
    · exact edge2278_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2279 : Fin frame689.rank → ℕ := ![1,2,68,8,16,96]
theorem edge2279_span : frame689.space ≤ frame901.space :=
  frame689.inclusion frame901 witness2279 (by decide)
def edge2279 : CertifiedEdge catalog where
  old := 689
  next := 901
  rank := 1
  good := by
    constructor
    · exact edge2279_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2280 : Fin frame690.rank → ℕ := ![9,10,36,304,64,384]
theorem edge2280_span : frame690.space ≤ frame1.space :=
  frame690.inclusion frame1 witness2280 (by decide)
def edge2280 : CertifiedEdge catalog where
  old := 690
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2280_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2281 : Fin frame690.rank → ℕ := ![9,10,4,16,32,64]
theorem edge2281_span : frame690.space ≤ frame892.space :=
  frame690.inclusion frame892 witness2281 (by decide)
def edge2281 : CertifiedEdge catalog where
  old := 690
  next := 892
  rank := 1
  good := by
    constructor
    · exact edge2281_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2282 : Fin frame690.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2282_span : frame690.space ≤ frame901.space :=
  frame690.inclusion frame901 witness2282 (by decide)
def edge2282 : CertifiedEdge catalog where
  old := 690
  next := 901
  rank := 1
  good := by
    constructor
    · exact edge2282_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2283 : Fin frame691.rank → ℕ := ![289,290,420,296,304,448]
theorem edge2283_span : frame691.space ≤ frame1.space :=
  frame691.inclusion frame1 witness2283 (by decide)
def edge2283 : CertifiedEdge catalog where
  old := 691
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2283_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2284 : Fin frame691.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2284_span : frame691.space ≤ frame893.space :=
  frame691.inclusion frame893 witness2284 (by decide)
def edge2284 : CertifiedEdge catalog where
  old := 691
  next := 893
  rank := 1
  good := by
    constructor
    · exact edge2284_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2285 : Fin frame691.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2285_span : frame691.space ≤ frame900.space :=
  frame691.inclusion frame900 witness2285 (by decide)
def edge2285 : CertifiedEdge catalog where
  old := 691
  next := 900
  rank := 1
  good := by
    constructor
    · exact edge2285_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2286 : Fin frame692.rank → ℕ := ![33,34,420,40,304,448]
theorem edge2286_span : frame692.space ≤ frame1.space :=
  frame692.inclusion frame1 witness2286 (by decide)
def edge2286 : CertifiedEdge catalog where
  old := 692
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2286_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2287 : Fin frame692.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2287_span : frame692.space ≤ frame886.space :=
  frame692.inclusion frame886 witness2287 (by decide)
def edge2287 : CertifiedEdge catalog where
  old := 692
  next := 886
  rank := 1
  good := by
    constructor
    · exact edge2287_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2288 : Fin frame692.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2288_span : frame692.space ≤ frame897.space :=
  frame692.inclusion frame897 witness2288 (by decide)
def edge2288 : CertifiedEdge catalog where
  old := 692
  next := 897
  rank := 1
  good := by
    constructor
    · exact edge2288_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2289 : Fin frame693.rank → ℕ := ![9,10,292,304,320,128]
theorem edge2289_span : frame693.space ≤ frame1.space :=
  frame693.inclusion frame1 witness2289 (by decide)
def edge2289 : CertifiedEdge catalog where
  old := 693
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2289_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2290 : Fin frame693.rank → ℕ := ![9,10,4,16,32,64]
theorem edge2290_span : frame693.space ≤ frame889.space :=
  frame693.inclusion frame889 witness2290 (by decide)
def edge2290 : CertifiedEdge catalog where
  old := 693
  next := 889
  rank := 1
  good := by
    constructor
    · exact edge2290_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2291 : Fin frame693.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2291_span : frame693.space ≤ frame894.space :=
  frame693.inclusion frame894 witness2291 (by decide)
def edge2291 : CertifiedEdge catalog where
  old := 693
  next := 894
  rank := 1
  good := by
    constructor
    · exact edge2291_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2292 : Fin frame694.rank → ℕ := ![41,130,12,48,192,256]
theorem edge2292_span : frame694.space ≤ frame1.space :=
  frame694.inclusion frame1 witness2292 (by decide)
def edge2292 : CertifiedEdge catalog where
  old := 694
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2292_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2293 : Fin frame694.rank → ℕ := ![1,34,4,8,48,64]
theorem edge2293_span : frame694.space ≤ frame902.space :=
  frame694.inclusion frame902 witness2293 (by decide)
def edge2293 : CertifiedEdge catalog where
  old := 694
  next := 902
  rank := 1
  good := by
    constructor
    · exact edge2293_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2294 : Fin frame694.rank → ℕ := ![9,2,12,16,32,64]
theorem edge2294_span : frame694.space ≤ frame910.space :=
  frame694.inclusion frame910 witness2294 (by decide)
def edge2294 : CertifiedEdge catalog where
  old := 694
  next := 910
  rank := 1
  good := by
    constructor
    · exact edge2294_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2295 : Fin frame695.rank → ℕ := ![129,42,12,48,192,256]
theorem edge2295_span : frame695.space ≤ frame1.space :=
  frame695.inclusion frame1 witness2295 (by decide)
def edge2295 : CertifiedEdge catalog where
  old := 695
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2295_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2296 : Fin frame695.rank → ℕ := ![1,10,12,16,32,64]
theorem edge2296_span : frame695.space ≤ frame905.space :=
  frame695.inclusion frame905 witness2296 (by decide)
def edge2296 : CertifiedEdge catalog where
  old := 695
  next := 905
  rank := 1
  good := by
    constructor
    · exact edge2296_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2297 : Fin frame695.rank → ℕ := ![33,2,4,8,48,64]
theorem edge2297_span : frame695.space ≤ frame913.space :=
  frame695.inclusion frame913 witness2297 (by decide)
def edge2297 : CertifiedEdge catalog where
  old := 695
  next := 913
  rank := 1
  good := by
    constructor
    · exact edge2297_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2298 : Fin frame696.rank → ℕ := ![139,12,16,32,192,256]
theorem edge2298_span : frame696.space ≤ frame1.space :=
  frame696.inclusion frame1 witness2298 (by decide)
def edge2298 : CertifiedEdge catalog where
  old := 696
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2298_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2299 : Fin frame696.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2299_span : frame696.space ≤ frame908.space :=
  frame696.inclusion frame908 witness2299 (by decide)
def edge2299 : CertifiedEdge catalog where
  old := 696
  next := 908
  rank := 1
  good := by
    constructor
    · exact edge2299_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2300 : Fin frame696.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2300_span : frame696.space ≤ frame916.space :=
  frame696.inclusion frame916 witness2300 (by decide)
def edge2300 : CertifiedEdge catalog where
  old := 696
  next := 916
  rank := 1
  good := by
    constructor
    · exact edge2300_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2301 : Fin frame697.rank → ℕ := ![35,132,136,48,192,256]
theorem edge2301_span : frame697.space ≤ frame1.space :=
  frame697.inclusion frame1 witness2301 (by decide)
def edge2301 : CertifiedEdge catalog where
  old := 697
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2301_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2302 : Fin frame697.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2302_span : frame697.space ≤ frame909.space :=
  frame697.inclusion frame909 witness2302 (by decide)
def edge2302 : CertifiedEdge catalog where
  old := 697
  next := 909
  rank := 1
  good := by
    constructor
    · exact edge2302_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2303 : Fin frame697.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2303_span : frame697.space ≤ frame917.space :=
  frame697.inclusion frame917 witness2303 (by decide)
def edge2303 : CertifiedEdge catalog where
  old := 697
  next := 917
  rank := 1
  good := by
    constructor
    · exact edge2303_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
