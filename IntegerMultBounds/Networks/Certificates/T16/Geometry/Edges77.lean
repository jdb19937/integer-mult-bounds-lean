module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2464 : Fin frame750.rank → ℕ := ![1,2,4,72,16,96,128]
theorem edge2464_span : frame750.space ≤ frame999.space :=
  frame750.inclusion frame999 witness2464 (by decide)
def edge2464 : CertifiedEdge catalog where
  old := 750
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2464_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2465 : Fin frame751.rank → ℕ := ![257,258,4,8,144,160,192]
theorem edge2465_span : frame751.space ≤ frame1.space :=
  frame751.inclusion frame1 witness2465 (by decide)
def edge2465 : CertifiedEdge catalog where
  old := 751
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2465_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2466 : Fin frame751.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2466_span : frame751.space ≤ frame856.space :=
  frame751.inclusion frame856 witness2466 (by decide)
def edge2466 : CertifiedEdge catalog where
  old := 751
  next := 856
  rank := 1
  good := by
    constructor
    · exact edge2466_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2467 : Fin frame751.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2467_span : frame751.space ≤ frame859.space :=
  frame751.inclusion frame859 witness2467 (by decide)
def edge2467 : CertifiedEdge catalog where
  old := 751
  next := 859
  rank := 1
  good := by
    constructor
    · exact edge2467_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2468 : Fin frame751.rank → ℕ := ![129,130,4,8,16,32,64]
theorem edge2468_span : frame751.space ≤ frame999.space :=
  frame751.inclusion frame999 witness2468 (by decide)
def edge2468 : CertifiedEdge catalog where
  old := 751
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2468_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2469 : Fin frame752.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2469_span : frame752.space ≤ frame855.space :=
  frame752.inclusion frame855 witness2469 (by decide)
def edge2469 : CertifiedEdge catalog where
  old := 752
  next := 855
  rank := 1
  good := by
    constructor
    · exact edge2469_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2470 : Fin frame752.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2470_span : frame752.space ≤ frame858.space :=
  frame752.inclusion frame858 witness2470 (by decide)
def edge2470 : CertifiedEdge catalog where
  old := 752
  next := 858
  rank := 1
  good := by
    constructor
    · exact edge2470_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2471 : Fin frame752.rank → ℕ := ![129,130,132,136,144,160,64]
theorem edge2471_span : frame752.space ≤ frame999.space :=
  frame752.inclusion frame999 witness2471 (by decide)
def edge2471 : CertifiedEdge catalog where
  old := 752
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2471_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2472 : Fin frame753.rank → ℕ := ![1,2,68,8,80,32,128]
theorem edge2472_span : frame753.space ≤ frame863.space :=
  frame753.inclusion frame863 witness2472 (by decide)
def edge2472 : CertifiedEdge catalog where
  old := 753
  next := 863
  rank := 1
  good := by
    constructor
    · exact edge2472_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2473 : Fin frame753.rank → ℕ := ![1,2,68,8,16,96,128]
theorem edge2473_span : frame753.space ≤ frame866.space :=
  frame753.inclusion frame866 witness2473 (by decide)
def edge2473 : CertifiedEdge catalog where
  old := 753
  next := 866
  rank := 1
  good := by
    constructor
    · exact edge2473_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2474 : Fin frame753.rank → ℕ := ![1,2,68,8,80,32,128]
theorem edge2474_span : frame753.space ≤ frame999.space :=
  frame753.inclusion frame999 witness2474 (by decide)
def edge2474 : CertifiedEdge catalog where
  old := 753
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2474_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2475 : Fin frame754.rank → ℕ := ![257,2,260,8,144,160,192]
theorem edge2475_span : frame754.space ≤ frame1.space :=
  frame754.inclusion frame1 witness2475 (by decide)
def edge2475 : CertifiedEdge catalog where
  old := 754
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2475_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2476 : Fin frame754.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2476_span : frame754.space ≤ frame880.space :=
  frame754.inclusion frame880 witness2476 (by decide)
def edge2476 : CertifiedEdge catalog where
  old := 754
  next := 880
  rank := 1
  good := by
    constructor
    · exact edge2476_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2477 : Fin frame754.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2477_span : frame754.space ≤ frame883.space :=
  frame754.inclusion frame883 witness2477 (by decide)
def edge2477 : CertifiedEdge catalog where
  old := 754
  next := 883
  rank := 1
  good := by
    constructor
    · exact edge2477_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2478 : Fin frame754.rank → ℕ := ![129,2,132,8,16,32,64]
theorem edge2478_span : frame754.space ≤ frame999.space :=
  frame754.inclusion frame999 witness2478 (by decide)
def edge2478 : CertifiedEdge catalog where
  old := 754
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2478_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2479 : Fin frame755.rank → ℕ := ![1,258,260,8,144,160,192]
theorem edge2479_span : frame755.space ≤ frame1.space :=
  frame755.inclusion frame1 witness2479 (by decide)
def edge2479 : CertifiedEdge catalog where
  old := 755
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2479_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2480 : Fin frame755.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2480_span : frame755.space ≤ frame872.space :=
  frame755.inclusion frame872 witness2480 (by decide)
def edge2480 : CertifiedEdge catalog where
  old := 755
  next := 872
  rank := 1
  good := by
    constructor
    · exact edge2480_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2481 : Fin frame755.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2481_span : frame755.space ≤ frame875.space :=
  frame755.inclusion frame875 witness2481 (by decide)
def edge2481 : CertifiedEdge catalog where
  old := 755
  next := 875
  rank := 1
  good := by
    constructor
    · exact edge2481_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2482 : Fin frame755.rank → ℕ := ![1,130,132,8,16,32,64]
theorem edge2482_span : frame755.space ≤ frame999.space :=
  frame755.inclusion frame999 witness2482 (by decide)
def edge2482 : CertifiedEdge catalog where
  old := 755
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2482_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2483 : Fin frame756.rank → ℕ := ![1,194,4,8,80,160,256]
theorem edge2483_span : frame756.space ≤ frame1.space :=
  frame756.inclusion frame1 witness2483 (by decide)
def edge2483 : CertifiedEdge catalog where
  old := 756
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2483_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2484 : Fin frame756.rank → ℕ := ![1,66,4,8,80,32,128]
theorem edge2484_span : frame756.space ≤ frame871.space :=
  frame756.inclusion frame871 witness2484 (by decide)
def edge2484 : CertifiedEdge catalog where
  old := 756
  next := 871
  rank := 1
  good := by
    constructor
    · exact edge2484_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2485 : Fin frame756.rank → ℕ := ![1,66,4,8,16,96,128]
theorem edge2485_span : frame756.space ≤ frame874.space :=
  frame756.inclusion frame874 witness2485 (by decide)
def edge2485 : CertifiedEdge catalog where
  old := 756
  next := 874
  rank := 1
  good := by
    constructor
    · exact edge2485_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2486 : Fin frame756.rank → ℕ := ![1,66,4,8,80,32,128]
theorem edge2486_span : frame756.space ≤ frame999.space :=
  frame756.inclusion frame999 witness2486 (by decide)
def edge2486 : CertifiedEdge catalog where
  old := 756
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2486_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2487 : Fin frame757.rank → ℕ := ![65,2,4,8,16,96,128]
theorem edge2487_span : frame757.space ≤ frame879.space :=
  frame757.inclusion frame879 witness2487 (by decide)
def edge2487 : CertifiedEdge catalog where
  old := 757
  next := 879
  rank := 1
  good := by
    constructor
    · exact edge2487_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2488 : Fin frame757.rank → ℕ := ![65,2,4,8,80,32,128]
theorem edge2488_span : frame757.space ≤ frame882.space :=
  frame757.inclusion frame882 witness2488 (by decide)
def edge2488 : CertifiedEdge catalog where
  old := 757
  next := 882
  rank := 1
  good := by
    constructor
    · exact edge2488_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2489 : Fin frame757.rank → ℕ := ![65,2,4,8,80,32,128]
theorem edge2489_span : frame757.space ≤ frame999.space :=
  frame757.inclusion frame999 witness2489 (by decide)
def edge2489 : CertifiedEdge catalog where
  old := 757
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2489_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2490 : Fin frame758.rank → ℕ := ![257,258,260,264,400,160,448]
theorem edge2490_span : frame758.space ≤ frame1.space :=
  frame758.inclusion frame1 witness2490 (by decide)
def edge2490 : CertifiedEdge catalog where
  old := 758
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2490_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2491 : Fin frame758.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2491_span : frame758.space ≤ frame896.space :=
  frame758.inclusion frame896 witness2491 (by decide)
def edge2491 : CertifiedEdge catalog where
  old := 758
  next := 896
  rank := 1
  good := by
    constructor
    · exact edge2491_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2492 : Fin frame758.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2492_span : frame758.space ≤ frame899.space :=
  frame758.inclusion frame899 witness2492 (by decide)
def edge2492 : CertifiedEdge catalog where
  old := 758
  next := 899
  rank := 1
  good := by
    constructor
    · exact edge2492_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2493 : Fin frame758.rank → ℕ := ![129,130,132,136,144,32,192]
theorem edge2493_span : frame758.space ≤ frame999.space :=
  frame758.inclusion frame999 witness2493 (by decide)
def edge2493 : CertifiedEdge catalog where
  old := 758
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2493_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2494 : Fin frame759.rank → ℕ := ![1,2,164,8,48,192,256]
theorem edge2494_span : frame759.space ≤ frame1.space :=
  frame759.inclusion frame1 witness2494 (by decide)
def edge2494 : CertifiedEdge catalog where
  old := 759
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2494_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2495 : Fin frame759.rank → ℕ := ![1,2,36,8,48,64,128]
theorem edge2495_span : frame759.space ≤ frame888.space :=
  frame759.inclusion frame888 witness2495 (by decide)
def edge2495 : CertifiedEdge catalog where
  old := 759
  next := 888
  rank := 1
  good := by
    constructor
    · exact edge2495_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
