module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2304 : Fin frame698.rank → ℕ := ![137,34,12,48,192,256]
theorem edge2304_span : frame698.space ≤ frame1.space :=
  frame698.inclusion frame1 witness2304 (by decide)
def edge2304 : CertifiedEdge catalog where
  old := 698
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2304_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2305 : Fin frame698.rank → ℕ := ![1,18,4,24,32,64]
theorem edge2305_span : frame698.space ≤ frame908.space :=
  frame698.inclusion frame908 witness2305 (by decide)
def edge2305 : CertifiedEdge catalog where
  old := 698
  next := 908
  rank := 1
  good := by
    constructor
    · exact edge2305_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2306 : Fin frame698.rank → ℕ := ![9,2,12,16,32,64]
theorem edge2306_span : frame698.space ≤ frame917.space :=
  frame698.inclusion frame917 witness2306 (by decide)
def edge2306 : CertifiedEdge catalog where
  old := 698
  next := 917
  rank := 1
  good := by
    constructor
    · exact edge2306_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2307 : Fin frame699.rank → ℕ := ![33,138,12,48,192,256]
theorem edge2307_span : frame699.space ≤ frame1.space :=
  frame699.inclusion frame1 witness2307 (by decide)
def edge2307 : CertifiedEdge catalog where
  old := 699
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2307_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2308 : Fin frame699.rank → ℕ := ![1,10,12,16,32,64]
theorem edge2308_span : frame699.space ≤ frame909.space :=
  frame699.inclusion frame909 witness2308 (by decide)
def edge2308 : CertifiedEdge catalog where
  old := 699
  next := 909
  rank := 1
  good := by
    constructor
    · exact edge2308_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2309 : Fin frame699.rank → ℕ := ![17,2,4,24,32,64]
theorem edge2309_span : frame699.space ≤ frame916.space :=
  frame699.inclusion frame916 witness2309 (by decide)
def edge2309 : CertifiedEdge catalog where
  old := 699
  next := 916
  rank := 1
  good := by
    constructor
    · exact edge2309_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2310 : Fin frame700.rank → ℕ := ![43,12,48,64,128,256]
theorem edge2310_span : frame700.space ≤ frame1.space :=
  frame700.inclusion frame1 witness2310 (by decide)
def edge2310 : CertifiedEdge catalog where
  old := 700
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2310_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2311 : Fin frame700.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2311_span : frame700.space ≤ frame902.space :=
  frame700.inclusion frame902 witness2311 (by decide)
def edge2311 : CertifiedEdge catalog where
  old := 700
  next := 902
  rank := 1
  good := by
    constructor
    · exact edge2311_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2312 : Fin frame700.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2312_span : frame700.space ≤ frame913.space :=
  frame700.inclusion frame913 witness2312 (by decide)
def edge2312 : CertifiedEdge catalog where
  old := 700
  next := 913
  rank := 1
  good := by
    constructor
    · exact edge2312_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2313 : Fin frame701.rank → ℕ := ![131,36,40,48,192,256]
theorem edge2313_span : frame701.space ≤ frame1.space :=
  frame701.inclusion frame1 witness2313 (by decide)
def edge2313 : CertifiedEdge catalog where
  old := 701
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2313_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2314 : Fin frame701.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2314_span : frame701.space ≤ frame905.space :=
  frame701.inclusion frame905 witness2314 (by decide)
def edge2314 : CertifiedEdge catalog where
  old := 701
  next := 905
  rank := 1
  good := by
    constructor
    · exact edge2314_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2315 : Fin frame701.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2315_span : frame701.space ≤ frame910.space :=
  frame701.inclusion frame910 witness2315 (by decide)
def edge2315 : CertifiedEdge catalog where
  old := 701
  next := 910
  rank := 1
  good := by
    constructor
    · exact edge2315_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2316 : Fin frame702.rank → ℕ := ![33,34,260,8,400,448]
theorem edge2316_span : frame702.space ≤ frame1.space :=
  frame702.inclusion frame1 witness2316 (by decide)
def edge2316 : CertifiedEdge catalog where
  old := 702
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2316_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2317 : Fin frame702.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2317_span : frame702.space ≤ frame918.space :=
  frame702.inclusion frame918 witness2317 (by decide)
def edge2317 : CertifiedEdge catalog where
  old := 702
  next := 918
  rank := 1
  good := by
    constructor
    · exact edge2317_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2318 : Fin frame702.rank → ℕ := ![33,34,4,8,16,64]
theorem edge2318_span : frame702.space ≤ frame926.space :=
  frame702.inclusion frame926 witness2318 (by decide)
def edge2318 : CertifiedEdge catalog where
  old := 702
  next := 926
  rank := 1
  good := by
    constructor
    · exact edge2318_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2319 : Fin frame703.rank → ℕ := ![129,130,148,408,160,448]
theorem edge2319_span : frame703.space ≤ frame1.space :=
  frame703.inclusion frame1 witness2319 (by decide)
def edge2319 : CertifiedEdge catalog where
  old := 703
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2319_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2320 : Fin frame703.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2320_span : frame703.space ≤ frame921.space :=
  frame703.inclusion frame921 witness2320 (by decide)
def edge2320 : CertifiedEdge catalog where
  old := 703
  next := 921
  rank := 1
  good := by
    constructor
    · exact edge2320_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2321 : Fin frame703.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2321_span : frame703.space ≤ frame929.space :=
  frame703.inclusion frame929 witness2321 (by decide)
def edge2321 : CertifiedEdge catalog where
  old := 703
  next := 929
  rank := 1
  good := by
    constructor
    · exact edge2321_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2322 : Fin frame704.rank → ℕ := ![257,258,148,408,288,448]
theorem edge2322_span : frame704.space ≤ frame1.space :=
  frame704.inclusion frame1 witness2322 (by decide)
def edge2322 : CertifiedEdge catalog where
  old := 704
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2322_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2323 : Fin frame704.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2323_span : frame704.space ≤ frame924.space :=
  frame704.inclusion frame924 witness2323 (by decide)
def edge2323 : CertifiedEdge catalog where
  old := 704
  next := 924
  rank := 1
  good := by
    constructor
    · exact edge2323_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2324 : Fin frame704.rank → ℕ := ![65,66,4,72,80,96]
theorem edge2324_span : frame704.space ≤ frame932.space :=
  frame704.inclusion frame932 witness2324 (by decide)
def edge2324 : CertifiedEdge catalog where
  old := 704
  next := 932
  rank := 1
  good := by
    constructor
    · exact edge2324_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2325 : Fin frame705.rank → ℕ := ![33,34,132,392,16,448]
theorem edge2325_span : frame705.space ≤ frame1.space :=
  frame705.inclusion frame1 witness2325 (by decide)
def edge2325 : CertifiedEdge catalog where
  old := 705
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2325_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2326 : Fin frame705.rank → ℕ := ![1,2,4,72,16,96]
theorem edge2326_span : frame705.space ≤ frame925.space :=
  frame705.inclusion frame925 witness2326 (by decide)
def edge2326 : CertifiedEdge catalog where
  old := 705
  next := 925
  rank := 1
  good := by
    constructor
    · exact edge2326_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2327 : Fin frame705.rank → ℕ := ![33,34,4,8,16,64]
theorem edge2327_span : frame705.space ≤ frame933.space :=
  frame705.inclusion frame933 witness2327 (by decide)
def edge2327 : CertifiedEdge catalog where
  old := 705
  next := 933
  rank := 1
  good := by
    constructor
    · exact edge2327_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2328 : Fin frame706.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2328_span : frame706.space ≤ frame924.space :=
  frame706.inclusion frame924 witness2328 (by decide)
def edge2328 : CertifiedEdge catalog where
  old := 706
  next := 924
  rank := 1
  good := by
    constructor
    · exact edge2328_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2329 : Fin frame706.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2329_span : frame706.space ≤ frame933.space :=
  frame706.inclusion frame933 witness2329 (by decide)
def edge2329 : CertifiedEdge catalog where
  old := 706
  next := 933
  rank := 1
  good := by
    constructor
    · exact edge2329_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2330 : Fin frame706.rank → ℕ := ![33,34,36,168,48,192]
theorem edge2330_span : frame706.space ≤ frame1001.space :=
  frame706.inclusion frame1001 witness2330 (by decide)
def edge2330 : CertifiedEdge catalog where
  old := 706
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2330_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2331 : Fin frame707.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2331_span : frame707.space ≤ frame925.space :=
  frame707.inclusion frame925 witness2331 (by decide)
def edge2331 : CertifiedEdge catalog where
  old := 707
  next := 925
  rank := 1
  good := by
    constructor
    · exact edge2331_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2332 : Fin frame707.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2332_span : frame707.space ≤ frame932.space :=
  frame707.inclusion frame932 witness2332 (by decide)
def edge2332 : CertifiedEdge catalog where
  old := 707
  next := 932
  rank := 1
  good := by
    constructor
    · exact edge2332_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2333 : Fin frame707.rank → ℕ := ![33,34,20,24,64,128]
theorem edge2333_span : frame707.space ≤ frame1001.space :=
  frame707.inclusion frame1001 witness2333 (by decide)
def edge2333 : CertifiedEdge catalog where
  old := 707
  next := 1001
  rank := 2
  good := by
    constructor
    · exact edge2333_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2334 : Fin frame708.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2334_span : frame708.space ≤ frame918.space :=
  frame708.inclusion frame918 witness2334 (by decide)
def edge2334 : CertifiedEdge catalog where
  old := 708
  next := 918
  rank := 1
  good := by
    constructor
    · exact edge2334_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2335 : Fin frame708.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2335_span : frame708.space ≤ frame929.space :=
  frame708.inclusion frame929 witness2335 (by decide)
def edge2335 : CertifiedEdge catalog where
  old := 708
  next := 929
  rank := 1
  good := by
    constructor
    · exact edge2335_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
