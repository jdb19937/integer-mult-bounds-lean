module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2528 : Fin frame768.rank → ℕ := ![129,130,132,136,16,160,192]
theorem edge2528_span : frame768.space ≤ frame998.space :=
  frame768.inclusion frame998 witness2528 (by decide)
def edge2528 : CertifiedEdge catalog where
  old := 768
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2528_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2529 : Fin frame769.rank → ℕ := ![1,2,20,24,32,64,128]
theorem edge2529_span : frame769.space ≤ frame927.space :=
  frame769.inclusion frame927 witness2529 (by decide)
def edge2529 : CertifiedEdge catalog where
  old := 769
  next := 927
  rank := 1
  good := by
    constructor
    · exact edge2529_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2530 : Fin frame769.rank → ℕ := ![1,2,132,8,16,32,192]
theorem edge2530_span : frame769.space ≤ frame930.space :=
  frame769.inclusion frame930 witness2530 (by decide)
def edge2530 : CertifiedEdge catalog where
  old := 769
  next := 930
  rank := 1
  good := by
    constructor
    · exact edge2530_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2531 : Fin frame769.rank → ℕ := ![1,2,20,24,32,64,128]
theorem edge2531_span : frame769.space ≤ frame998.space :=
  frame769.inclusion frame998 witness2531 (by decide)
def edge2531 : CertifiedEdge catalog where
  old := 769
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2531_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2532 : Fin frame770.rank → ℕ := ![33,2,36,264,272,64,384]
theorem edge2532_span : frame770.space ≤ frame1.space :=
  frame770.inclusion frame1 witness2532 (by decide)
def edge2532 : CertifiedEdge catalog where
  old := 770
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2532_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2533 : Fin frame770.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2533_span : frame770.space ≤ frame944.space :=
  frame770.inclusion frame944 witness2533 (by decide)
def edge2533 : CertifiedEdge catalog where
  old := 770
  next := 944
  rank := 1
  good := by
    constructor
    · exact edge2533_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2534 : Fin frame770.rank → ℕ := ![33,2,36,8,16,64,128]
theorem edge2534_span : frame770.space ≤ frame947.space :=
  frame770.inclusion frame947 witness2534 (by decide)
def edge2534 : CertifiedEdge catalog where
  old := 770
  next := 947
  rank := 1
  good := by
    constructor
    · exact edge2534_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2535 : Fin frame771.rank → ℕ := ![1,34,36,264,272,64,384]
theorem edge2535_span : frame771.space ≤ frame1.space :=
  frame771.inclusion frame1 witness2535 (by decide)
def edge2535 : CertifiedEdge catalog where
  old := 771
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2535_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2536 : Fin frame771.rank → ℕ := ![1,34,36,8,16,64,128]
theorem edge2536_span : frame771.space ≤ frame936.space :=
  frame771.inclusion frame936 witness2536 (by decide)
def edge2536 : CertifiedEdge catalog where
  old := 771
  next := 936
  rank := 1
  good := by
    constructor
    · exact edge2536_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2537 : Fin frame771.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2537_span : frame771.space ≤ frame939.space :=
  frame771.inclusion frame939 witness2537 (by decide)
def edge2537 : CertifiedEdge catalog where
  old := 771
  next := 939
  rank := 1
  good := by
    constructor
    · exact edge2537_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2538 : Fin frame771.rank → ℕ := ![1,34,36,8,16,64,128]
theorem edge2538_span : frame771.space ≤ frame998.space :=
  frame771.inclusion frame998 witness2538 (by decide)
def edge2538 : CertifiedEdge catalog where
  old := 771
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2538_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2539 : Fin frame772.rank → ℕ := ![1,274,4,24,32,64,384]
theorem edge2539_span : frame772.space ≤ frame1.space :=
  frame772.inclusion frame1 witness2539 (by decide)
def edge2539 : CertifiedEdge catalog where
  old := 772
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2539_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2540 : Fin frame772.rank → ℕ := ![1,18,4,24,32,64,128]
theorem edge2540_span : frame772.space ≤ frame935.space :=
  frame772.inclusion frame935 witness2540 (by decide)
def edge2540 : CertifiedEdge catalog where
  old := 772
  next := 935
  rank := 1
  good := by
    constructor
    · exact edge2540_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2541 : Fin frame772.rank → ℕ := ![1,130,4,8,16,32,192]
theorem edge2541_span : frame772.space ≤ frame938.space :=
  frame772.inclusion frame938 witness2541 (by decide)
def edge2541 : CertifiedEdge catalog where
  old := 772
  next := 938
  rank := 1
  good := by
    constructor
    · exact edge2541_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2542 : Fin frame772.rank → ℕ := ![1,18,4,24,32,64,128]
theorem edge2542_span : frame772.space ≤ frame998.space :=
  frame772.inclusion frame998 witness2542 (by decide)
def edge2542 : CertifiedEdge catalog where
  old := 772
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2542_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2543 : Fin frame773.rank → ℕ := ![129,2,4,8,16,32,192]
theorem edge2543_span : frame773.space ≤ frame943.space :=
  frame773.inclusion frame943 witness2543 (by decide)
def edge2543 : CertifiedEdge catalog where
  old := 773
  next := 943
  rank := 1
  good := by
    constructor
    · exact edge2543_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2544 : Fin frame773.rank → ℕ := ![17,2,4,24,32,64,128]
theorem edge2544_span : frame773.space ≤ frame946.space :=
  frame773.inclusion frame946 witness2544 (by decide)
def edge2544 : CertifiedEdge catalog where
  old := 773
  next := 946
  rank := 1
  good := by
    constructor
    · exact edge2544_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2545 : Fin frame773.rank → ℕ := ![17,2,4,24,32,64,128]
theorem edge2545_span : frame773.space ≤ frame998.space :=
  frame773.inclusion frame998 witness2545 (by decide)
def edge2545 : CertifiedEdge catalog where
  old := 773
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2545_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2546 : Fin frame774.rank → ℕ := ![193,194,196,200,80,32]
theorem edge2546_span : frame774.space ≤ frame775.space :=
  frame774.inclusion frame775 witness2546 (by decide)
def edge2546 : CertifiedEdge catalog where
  old := 774
  next := 775
  rank := 2
  good := by
    constructor
    · exact edge2546_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2547 : Fin frame774.rank → ℕ := ![193,194,196,72,208,32]
theorem edge2547_span : frame774.space ≤ frame776.space :=
  frame774.inclusion frame776 witness2547 (by decide)
def edge2547 : CertifiedEdge catalog where
  old := 774
  next := 776
  rank := 2
  good := by
    constructor
    · exact edge2547_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2548 : Fin frame775.rank → ℕ := ![1,2,4,136,16,32,192,256]
theorem edge2548_span : frame775.space ≤ frame1.space :=
  frame775.inclusion frame1 witness2548 (by decide)
def edge2548 : CertifiedEdge catalog where
  old := 775
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2548_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2549 : Fin frame776.rank → ℕ := ![1,2,4,8,272,32,320,128]
theorem edge2549_span : frame776.space ≤ frame1.space :=
  frame776.inclusion frame1 witness2549 (by decide)
def edge2549 : CertifiedEdge catalog where
  old := 776
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2549_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2550 : Fin frame777.rank → ℕ := ![129,130,132,40,176,64]
theorem edge2550_span : frame777.space ≤ frame778.space :=
  frame777.inclusion frame778 witness2550 (by decide)
def edge2550 : CertifiedEdge catalog where
  old := 777
  next := 778
  rank := 2
  good := by
    constructor
    · exact edge2550_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2551 : Fin frame777.rank → ℕ := ![193,194,196,136,80,32]
theorem edge2551_span : frame777.space ≤ frame779.space :=
  frame777.inclusion frame779 witness2551 (by decide)
def edge2551 : CertifiedEdge catalog where
  old := 777
  next := 779
  rank := 2
  good := by
    constructor
    · exact edge2551_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2552 : Fin frame778.rank → ℕ := ![1,2,4,8,16,288,64,384]
theorem edge2552_span : frame778.space ≤ frame1.space :=
  frame778.inclusion frame1 witness2552 (by decide)
def edge2552 : CertifiedEdge catalog where
  old := 778
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2552_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2553 : Fin frame779.rank → ℕ := ![1,2,4,40,48,64,128,256]
theorem edge2553_span : frame779.space ≤ frame1.space :=
  frame779.inclusion frame1 witness2553 (by decide)
def edge2553 : CertifiedEdge catalog where
  old := 779
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2553_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2554 : Fin frame780.rank → ℕ := ![65,66,68,104,112,128]
theorem edge2554_span : frame780.space ≤ frame775.space :=
  frame780.inclusion frame775 witness2554 (by decide)
def edge2554 : CertifiedEdge catalog where
  old := 780
  next := 775
  rank := 2
  good := by
    constructor
    · exact edge2554_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2555 : Fin frame780.rank → ℕ := ![97,98,100,40,112,128]
theorem edge2555_span : frame780.space ≤ frame779.space :=
  frame780.inclusion frame779 witness2555 (by decide)
def edge2555 : CertifiedEdge catalog where
  old := 780
  next := 779
  rank := 2
  good := by
    constructor
    · exact edge2555_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2556 : Fin frame781.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2556_span : frame781.space ≤ frame776.space :=
  frame781.inclusion frame776 witness2556 (by decide)
def edge2556 : CertifiedEdge catalog where
  old := 781
  next := 776
  rank := 2
  good := by
    constructor
    · exact edge2556_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2557 : Fin frame781.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2557_span : frame781.space ≤ frame778.space :=
  frame781.inclusion frame778 witness2557 (by decide)
def edge2557 : CertifiedEdge catalog where
  old := 781
  next := 778
  rank := 2
  good := by
    constructor
    · exact edge2557_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2558 : Fin frame782.rank → ℕ := ![129,130,132,8,144,96]
theorem edge2558_span : frame782.space ≤ frame783.space :=
  frame782.inclusion frame783 witness2558 (by decide)
def edge2558 : CertifiedEdge catalog where
  old := 782
  next := 783
  rank := 2
  good := by
    constructor
    · exact edge2558_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2559 : Fin frame782.rank → ℕ := ![129,130,132,136,16,96]
theorem edge2559_span : frame782.space ≤ frame784.space :=
  frame782.inclusion frame784 witness2559 (by decide)
def edge2559 : CertifiedEdge catalog where
  old := 782
  next := 784
  rank := 2
  good := by
    constructor
    · exact edge2559_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
