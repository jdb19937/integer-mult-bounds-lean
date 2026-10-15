module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2432 : Fin frame740.rank → ℕ := ![129,70,8,144,96]
theorem edge2432_span : frame740.space ≤ frame998.space :=
  frame740.inclusion frame998 witness2432 (by decide)
def edge2432 : CertifiedEdge catalog where
  old := 740
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2432_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2433 : Fin frame741.rank → ℕ := ![33,2,4,8,48]
theorem edge2433_span : frame741.space ≤ frame985.space :=
  frame741.inclusion frame985 witness2433 (by decide)
def edge2433 : CertifiedEdge catalog where
  old := 741
  next := 985
  rank := 1
  good := by
    constructor
    · exact edge2433_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2434 : Fin frame741.rank → ℕ := ![5,2,8,16,32]
theorem edge2434_span : frame741.space ≤ frame990.space :=
  frame741.inclusion frame990 witness2434 (by decide)
def edge2434 : CertifiedEdge catalog where
  old := 741
  next := 990
  rank := 1
  good := by
    constructor
    · exact edge2434_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2435 : Fin frame741.rank → ℕ := ![69,130,8,144,96]
theorem edge2435_span : frame741.space ≤ frame998.space :=
  frame741.inclusion frame998 witness2435 (by decide)
def edge2435 : CertifiedEdge catalog where
  old := 741
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2435_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2436 : Fin frame742.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2436_span : frame742.space ≤ frame832.space :=
  frame742.inclusion frame832 witness2436 (by decide)
def edge2436 : CertifiedEdge catalog where
  old := 742
  next := 832
  rank := 1
  good := by
    constructor
    · exact edge2436_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2437 : Fin frame742.rank → ℕ := ![65,66,68,72,80,96,128]
theorem edge2437_span : frame742.space ≤ frame835.space :=
  frame742.inclusion frame835 witness2437 (by decide)
def edge2437 : CertifiedEdge catalog where
  old := 742
  next := 835
  rank := 1
  good := by
    constructor
    · exact edge2437_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2438 : Fin frame742.rank → ℕ := ![65,66,68,72,80,96,128]
theorem edge2438_span : frame742.space ≤ frame998.space :=
  frame742.inclusion frame998 witness2438 (by decide)
def edge2438 : CertifiedEdge catalog where
  old := 742
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2438_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2439 : Fin frame743.rank → ℕ := ![1,2,132,8,144,32,64]
theorem edge2439_span : frame743.space ≤ frame824.space :=
  frame743.inclusion frame824 witness2439 (by decide)
def edge2439 : CertifiedEdge catalog where
  old := 743
  next := 824
  rank := 1
  good := by
    constructor
    · exact edge2439_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2440 : Fin frame743.rank → ℕ := ![1,2,132,136,16,32,64]
theorem edge2440_span : frame743.space ≤ frame827.space :=
  frame743.inclusion frame827 witness2440 (by decide)
def edge2440 : CertifiedEdge catalog where
  old := 743
  next := 827
  rank := 1
  good := by
    constructor
    · exact edge2440_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2441 : Fin frame743.rank → ℕ := ![1,2,132,136,16,32,64]
theorem edge2441_span : frame743.space ≤ frame998.space :=
  frame743.inclusion frame998 witness2441 (by decide)
def edge2441 : CertifiedEdge catalog where
  old := 743
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2441_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2442 : Fin frame744.rank → ℕ := ![1,2,4,136,16,160,64]
theorem edge2442_span : frame744.space ≤ frame823.space :=
  frame744.inclusion frame823 witness2442 (by decide)
def edge2442 : CertifiedEdge catalog where
  old := 744
  next := 823
  rank := 1
  good := by
    constructor
    · exact edge2442_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2443 : Fin frame744.rank → ℕ := ![1,2,4,8,144,160,64]
theorem edge2443_span : frame744.space ≤ frame826.space :=
  frame744.inclusion frame826 witness2443 (by decide)
def edge2443 : CertifiedEdge catalog where
  old := 744
  next := 826
  rank := 1
  good := by
    constructor
    · exact edge2443_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2444 : Fin frame744.rank → ℕ := ![1,2,4,8,144,160,64]
theorem edge2444_span : frame744.space ≤ frame998.space :=
  frame744.inclusion frame998 witness2444 (by decide)
def edge2444 : CertifiedEdge catalog where
  old := 744
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2444_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2445 : Fin frame745.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2445_span : frame745.space ≤ frame831.space :=
  frame745.inclusion frame831 witness2445 (by decide)
def edge2445 : CertifiedEdge catalog where
  old := 745
  next := 831
  rank := 1
  good := by
    constructor
    · exact edge2445_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2446 : Fin frame745.rank → ℕ := ![65,66,4,8,16,32,128]
theorem edge2446_span : frame745.space ≤ frame834.space :=
  frame745.inclusion frame834 witness2446 (by decide)
def edge2446 : CertifiedEdge catalog where
  old := 745
  next := 834
  rank := 1
  good := by
    constructor
    · exact edge2446_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2447 : Fin frame745.rank → ℕ := ![65,66,4,8,16,32,128]
theorem edge2447_span : frame745.space ≤ frame998.space :=
  frame745.inclusion frame998 witness2447 (by decide)
def edge2447 : CertifiedEdge catalog where
  old := 745
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2447_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2448 : Fin frame746.rank → ℕ := ![1,386,4,136,272,32,64]
theorem edge2448_span : frame746.space ≤ frame1.space :=
  frame746.inclusion frame1 witness2448 (by decide)
def edge2448 : CertifiedEdge catalog where
  old := 746
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2448_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2449 : Fin frame746.rank → ℕ := ![1,130,4,8,144,32,64]
theorem edge2449_span : frame746.space ≤ frame848.space :=
  frame746.inclusion frame848 witness2449 (by decide)
def edge2449 : CertifiedEdge catalog where
  old := 746
  next := 848
  rank := 1
  good := by
    constructor
    · exact edge2449_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2450 : Fin frame746.rank → ℕ := ![1,130,4,136,16,32,64]
theorem edge2450_span : frame746.space ≤ frame851.space :=
  frame746.inclusion frame851 witness2450 (by decide)
def edge2450 : CertifiedEdge catalog where
  old := 746
  next := 851
  rank := 1
  good := by
    constructor
    · exact edge2450_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2451 : Fin frame746.rank → ℕ := ![1,130,4,136,16,32,64]
theorem edge2451_span : frame746.space ≤ frame998.space :=
  frame746.inclusion frame998 witness2451 (by decide)
def edge2451 : CertifiedEdge catalog where
  old := 746
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2451_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2452 : Fin frame747.rank → ℕ := ![129,2,4,136,16,32,64]
theorem edge2452_span : frame747.space ≤ frame840.space :=
  frame747.inclusion frame840 witness2452 (by decide)
def edge2452 : CertifiedEdge catalog where
  old := 747
  next := 840
  rank := 1
  good := by
    constructor
    · exact edge2452_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2453 : Fin frame747.rank → ℕ := ![129,2,4,8,144,32,64]
theorem edge2453_span : frame747.space ≤ frame843.space :=
  frame747.inclusion frame843 witness2453 (by decide)
def edge2453 : CertifiedEdge catalog where
  old := 747
  next := 843
  rank := 1
  good := by
    constructor
    · exact edge2453_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2454 : Fin frame747.rank → ℕ := ![129,2,4,136,16,32,64]
theorem edge2454_span : frame747.space ≤ frame998.space :=
  frame747.inclusion frame998 witness2454 (by decide)
def edge2454 : CertifiedEdge catalog where
  old := 747
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2454_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2455 : Fin frame748.rank → ℕ := ![65,2,68,264,272,32,384]
theorem edge2455_span : frame748.space ≤ frame1.space :=
  frame748.inclusion frame1 witness2455 (by decide)
def edge2455 : CertifiedEdge catalog where
  old := 748
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2455_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2456 : Fin frame748.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2456_span : frame748.space ≤ frame839.space :=
  frame748.inclusion frame839 witness2456 (by decide)
def edge2456 : CertifiedEdge catalog where
  old := 748
  next := 839
  rank := 1
  good := by
    constructor
    · exact edge2456_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2457 : Fin frame748.rank → ℕ := ![65,2,68,8,16,32,128]
theorem edge2457_span : frame748.space ≤ frame842.space :=
  frame748.inclusion frame842 witness2457 (by decide)
def edge2457 : CertifiedEdge catalog where
  old := 748
  next := 842
  rank := 1
  good := by
    constructor
    · exact edge2457_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2458 : Fin frame748.rank → ℕ := ![65,2,68,8,16,32,128]
theorem edge2458_span : frame748.space ≤ frame998.space :=
  frame748.inclusion frame998 witness2458 (by decide)
def edge2458 : CertifiedEdge catalog where
  old := 748
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2458_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2459 : Fin frame749.rank → ℕ := ![1,66,68,8,16,32,128]
theorem edge2459_span : frame749.space ≤ frame847.space :=
  frame749.inclusion frame847 witness2459 (by decide)
def edge2459 : CertifiedEdge catalog where
  old := 749
  next := 847
  rank := 1
  good := by
    constructor
    · exact edge2459_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2460 : Fin frame749.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2460_span : frame749.space ≤ frame850.space :=
  frame749.inclusion frame850 witness2460 (by decide)
def edge2460 : CertifiedEdge catalog where
  old := 749
  next := 850
  rank := 1
  good := by
    constructor
    · exact edge2460_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2461 : Fin frame749.rank → ℕ := ![1,66,68,8,16,32,128]
theorem edge2461_span : frame749.space ≤ frame998.space :=
  frame749.inclusion frame998 witness2461 (by decide)
def edge2461 : CertifiedEdge catalog where
  old := 749
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2461_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2462 : Fin frame750.rank → ℕ := ![1,2,4,72,16,96,128]
theorem edge2462_span : frame750.space ≤ frame864.space :=
  frame750.inclusion frame864 witness2462 (by decide)
def edge2462 : CertifiedEdge catalog where
  old := 750
  next := 864
  rank := 1
  good := by
    constructor
    · exact edge2462_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2463 : Fin frame750.rank → ℕ := ![1,2,4,72,80,32,128]
theorem edge2463_span : frame750.space ≤ frame867.space :=
  frame750.inclusion frame867 witness2463 (by decide)
def edge2463 : CertifiedEdge catalog where
  old := 750
  next := 867
  rank := 1
  good := by
    constructor
    · exact edge2463_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
