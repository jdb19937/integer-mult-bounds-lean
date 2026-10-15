module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2592 : Fin frame805.rank → ℕ := ![33,2,4,40,16,64,128]
theorem edge2592_span : frame805.space ≤ frame799.space :=
  frame805.inclusion frame799 witness2592 (by decide)
def edge2592 : CertifiedEdge catalog where
  old := 805
  next := 799
  rank := 1
  good := by
    constructor
    · exact edge2592_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2593 : Fin frame805.rank → ℕ := ![1,2,132,8,144,160,64]
theorem edge2593_span : frame805.space ≤ frame803.space :=
  frame805.inclusion frame803 witness2593 (by decide)
def edge2593 : CertifiedEdge catalog where
  old := 805
  next := 803
  rank := 1
  good := by
    constructor
    · exact edge2593_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2594 : Fin frame806.rank → ℕ := ![129,130,132,136,144,32,192]
theorem edge2594_span : frame806.space ≤ frame807.space :=
  frame806.inclusion frame807 witness2594 (by decide)
def edge2594 : CertifiedEdge catalog where
  old := 806
  next := 807
  rank := 1
  good := by
    constructor
    · exact edge2594_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2595 : Fin frame806.rank → ℕ := ![129,130,4,136,144,160,192]
theorem edge2595_span : frame806.space ≤ frame808.space :=
  frame806.inclusion frame808 witness2595 (by decide)
def edge2595 : CertifiedEdge catalog where
  old := 806
  next := 808
  rank := 1
  good := by
    constructor
    · exact edge2595_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2596 : Fin frame807.rank → ℕ := ![257,258,4,264,272,288,320,128]
theorem edge2596_span : frame807.space ≤ frame1.space :=
  frame807.inclusion frame1 witness2596 (by decide)
def edge2596 : CertifiedEdge catalog where
  old := 807
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2596_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2597 : Fin frame808.rank → ℕ := ![129,130,132,136,144,32,192,256]
theorem edge2597_span : frame808.space ≤ frame1.space :=
  frame808.inclusion frame1 witness2597 (by decide)
def edge2597 : CertifiedEdge catalog where
  old := 808
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2597_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2598 : Fin frame809.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2598_span : frame809.space ≤ frame810.space :=
  frame809.inclusion frame810 witness2598 (by decide)
def edge2598 : CertifiedEdge catalog where
  old := 809
  next := 810
  rank := 1
  good := by
    constructor
    · exact edge2598_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2599 : Fin frame809.rank → ℕ := ![17,18,4,8,32,64,128]
theorem edge2599_span : frame809.space ≤ frame811.space :=
  frame809.inclusion frame811 witness2599 (by decide)
def edge2599 : CertifiedEdge catalog where
  old := 809
  next := 811
  rank := 1
  good := by
    constructor
    · exact edge2599_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2600 : Fin frame810.rank → ℕ := ![17,18,4,8,32,64,128,256]
theorem edge2600_span : frame810.space ≤ frame1.space :=
  frame810.inclusion frame1 witness2600 (by decide)
def edge2600 : CertifiedEdge catalog where
  old := 810
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2600_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2601 : Fin frame811.rank → ℕ := ![257,258,260,8,272,288,64,384]
theorem edge2601_span : frame811.space ≤ frame1.space :=
  frame811.inclusion frame1 witness2601 (by decide)
def edge2601 : CertifiedEdge catalog where
  old := 811
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2601_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2602 : Fin frame812.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2602_span : frame812.space ≤ frame807.space :=
  frame812.inclusion frame807 witness2602 (by decide)
def edge2602 : CertifiedEdge catalog where
  old := 812
  next := 807
  rank := 1
  good := by
    constructor
    · exact edge2602_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2603 : Fin frame812.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2603_span : frame812.space ≤ frame811.space :=
  frame812.inclusion frame811 witness2603 (by decide)
def edge2603 : CertifiedEdge catalog where
  old := 812
  next := 811
  rank := 1
  good := by
    constructor
    · exact edge2603_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2604 : Fin frame813.rank → ℕ := ![17,18,4,8,32,64,128]
theorem edge2604_span : frame813.space ≤ frame808.space :=
  frame813.inclusion frame808 witness2604 (by decide)
def edge2604 : CertifiedEdge catalog where
  old := 813
  next := 808
  rank := 1
  good := by
    constructor
    · exact edge2604_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2605 : Fin frame813.rank → ℕ := ![1,2,68,72,16,96,128]
theorem edge2605_span : frame813.space ≤ frame810.space :=
  frame813.inclusion frame810 witness2605 (by decide)
def edge2605 : CertifiedEdge catalog where
  old := 813
  next := 810
  rank := 1
  good := by
    constructor
    · exact edge2605_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2606 : Fin frame814.rank → ℕ := ![1,2,132,8,16,32,192]
theorem edge2606_span : frame814.space ≤ frame815.space :=
  frame814.inclusion frame815 witness2606 (by decide)
def edge2606 : CertifiedEdge catalog where
  old := 814
  next := 815
  rank := 1
  good := by
    constructor
    · exact edge2606_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2607 : Fin frame814.rank → ℕ := ![1,2,4,8,16,160,192]
theorem edge2607_span : frame814.space ≤ frame816.space :=
  frame814.inclusion frame816 witness2607 (by decide)
def edge2607 : CertifiedEdge catalog where
  old := 814
  next := 816
  rank := 1
  good := by
    constructor
    · exact edge2607_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2608 : Fin frame815.rank → ℕ := ![1,2,4,8,16,160,192,256]
theorem edge2608_span : frame815.space ≤ frame1.space :=
  frame815.inclusion frame1 witness2608 (by decide)
def edge2608 : CertifiedEdge catalog where
  old := 815
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2608_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2609 : Fin frame816.rank → ℕ := ![1,2,260,8,16,32,320,128]
theorem edge2609_span : frame816.space ≤ frame1.space :=
  frame816.inclusion frame1 witness2609 (by decide)
def edge2609 : CertifiedEdge catalog where
  old := 816
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2609_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2610 : Fin frame817.rank → ℕ := ![1,2,36,40,16,64,128]
theorem edge2610_span : frame817.space ≤ frame818.space :=
  frame817.inclusion frame818 witness2610 (by decide)
def edge2610 : CertifiedEdge catalog where
  old := 817
  next := 818
  rank := 1
  good := by
    constructor
    · exact edge2610_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2611 : Fin frame817.rank → ℕ := ![1,2,4,136,16,32,192]
theorem edge2611_span : frame817.space ≤ frame819.space :=
  frame817.inclusion frame819 witness2611 (by decide)
def edge2611 : CertifiedEdge catalog where
  old := 817
  next := 819
  rank := 1
  good := by
    constructor
    · exact edge2611_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2612 : Fin frame818.rank → ℕ := ![1,2,4,264,16,32,64,384]
theorem edge2612_span : frame818.space ≤ frame1.space :=
  frame818.inclusion frame1 witness2612 (by decide)
def edge2612 : CertifiedEdge catalog where
  old := 818
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2612_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2613 : Fin frame819.rank → ℕ := ![1,2,36,40,16,64,128,256]
theorem edge2613_span : frame819.space ≤ frame1.space :=
  frame819.inclusion frame1 witness2613 (by decide)
def edge2613 : CertifiedEdge catalog where
  old := 819
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2613_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2614 : Fin frame820.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2614_span : frame820.space ≤ frame816.space :=
  frame820.inclusion frame816 witness2614 (by decide)
def edge2614 : CertifiedEdge catalog where
  old := 820
  next := 816
  rank := 1
  good := by
    constructor
    · exact edge2614_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2615 : Fin frame820.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2615_span : frame820.space ≤ frame818.space :=
  frame820.inclusion frame818 witness2615 (by decide)
def edge2615 : CertifiedEdge catalog where
  old := 820
  next := 818
  rank := 1
  good := by
    constructor
    · exact edge2615_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2616 : Fin frame821.rank → ℕ := ![1,2,36,40,16,64,128]
theorem edge2616_span : frame821.space ≤ frame815.space :=
  frame821.inclusion frame815 witness2616 (by decide)
def edge2616 : CertifiedEdge catalog where
  old := 821
  next := 815
  rank := 1
  good := by
    constructor
    · exact edge2616_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2617 : Fin frame821.rank → ℕ := ![1,2,68,72,16,96,128]
theorem edge2617_span : frame821.space ≤ frame819.space :=
  frame821.inclusion frame819 witness2617 (by decide)
def edge2617 : CertifiedEdge catalog where
  old := 821
  next := 819
  rank := 1
  good := by
    constructor
    · exact edge2617_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2618 : Fin frame822.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2618_span : frame822.space ≤ frame823.space :=
  frame822.inclusion frame823 witness2618 (by decide)
def edge2618 : CertifiedEdge catalog where
  old := 822
  next := 823
  rank := 1
  good := by
    constructor
    · exact edge2618_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2619 : Fin frame822.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2619_span : frame822.space ≤ frame824.space :=
  frame822.inclusion frame824 witness2619 (by decide)
def edge2619 : CertifiedEdge catalog where
  old := 822
  next := 824
  rank := 1
  good := by
    constructor
    · exact edge2619_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2620 : Fin frame823.rank → ℕ := ![1,2,4,8,144,160,64,256]
theorem edge2620_span : frame823.space ≤ frame1.space :=
  frame823.inclusion frame1 witness2620 (by decide)
def edge2620 : CertifiedEdge catalog where
  old := 823
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2620_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2621 : Fin frame824.rank → ℕ := ![1,2,132,136,16,32,64,256]
theorem edge2621_span : frame824.space ≤ frame1.space :=
  frame824.inclusion frame1 witness2621 (by decide)
def edge2621 : CertifiedEdge catalog where
  old := 824
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2621_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2622 : Fin frame825.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2622_span : frame825.space ≤ frame826.space :=
  frame825.inclusion frame826 witness2622 (by decide)
def edge2622 : CertifiedEdge catalog where
  old := 825
  next := 826
  rank := 1
  good := by
    constructor
    · exact edge2622_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2623 : Fin frame825.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2623_span : frame825.space ≤ frame827.space :=
  frame825.inclusion frame827 witness2623 (by decide)
def edge2623 : CertifiedEdge catalog where
  old := 825
  next := 827
  rank := 1
  good := by
    constructor
    · exact edge2623_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
