module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2624 : Fin frame826.rank → ℕ := ![1,2,4,264,16,288,64,128]
theorem edge2624_span : frame826.space ≤ frame1.space :=
  frame826.inclusion frame1 witness2624 (by decide)
def edge2624 : CertifiedEdge catalog where
  old := 826
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2624_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2625 : Fin frame827.rank → ℕ := ![1,2,260,8,272,32,64,128]
theorem edge2625_span : frame827.space ≤ frame1.space :=
  frame827.inclusion frame1 witness2625 (by decide)
def edge2625 : CertifiedEdge catalog where
  old := 827
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2625_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2626 : Fin frame828.rank → ℕ := ![1,2,132,8,144,32,64]
theorem edge2626_span : frame828.space ≤ frame823.space :=
  frame828.inclusion frame823 witness2626 (by decide)
def edge2626 : CertifiedEdge catalog where
  old := 828
  next := 823
  rank := 1
  good := by
    constructor
    · exact edge2626_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2627 : Fin frame828.rank → ℕ := ![1,2,4,8,144,160,64]
theorem edge2627_span : frame828.space ≤ frame827.space :=
  frame828.inclusion frame827 witness2627 (by decide)
def edge2627 : CertifiedEdge catalog where
  old := 828
  next := 827
  rank := 1
  good := by
    constructor
    · exact edge2627_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2628 : Fin frame829.rank → ℕ := ![1,2,4,136,16,160,64]
theorem edge2628_span : frame829.space ≤ frame824.space :=
  frame829.inclusion frame824 witness2628 (by decide)
def edge2628 : CertifiedEdge catalog where
  old := 829
  next := 824
  rank := 1
  good := by
    constructor
    · exact edge2628_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2629 : Fin frame829.rank → ℕ := ![1,2,132,136,16,32,64]
theorem edge2629_span : frame829.space ≤ frame826.space :=
  frame829.inclusion frame826 witness2629 (by decide)
def edge2629 : CertifiedEdge catalog where
  old := 829
  next := 826
  rank := 1
  good := by
    constructor
    · exact edge2629_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2630 : Fin frame830.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2630_span : frame830.space ≤ frame831.space :=
  frame830.inclusion frame831 witness2630 (by decide)
def edge2630 : CertifiedEdge catalog where
  old := 830
  next := 831
  rank := 1
  good := by
    constructor
    · exact edge2630_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2631 : Fin frame830.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2631_span : frame830.space ≤ frame832.space :=
  frame830.inclusion frame832 witness2631 (by decide)
def edge2631 : CertifiedEdge catalog where
  old := 830
  next := 832
  rank := 1
  good := by
    constructor
    · exact edge2631_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2632 : Fin frame831.rank → ℕ := ![65,66,4,8,16,32,128,256]
theorem edge2632_span : frame831.space ≤ frame1.space :=
  frame831.inclusion frame1 witness2632 (by decide)
def edge2632 : CertifiedEdge catalog where
  old := 831
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2632_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2633 : Fin frame832.rank → ℕ := ![65,66,68,72,80,96,128,256]
theorem edge2633_span : frame832.space ≤ frame1.space :=
  frame832.inclusion frame1 witness2633 (by decide)
def edge2633 : CertifiedEdge catalog where
  old := 832
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2633_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2634 : Fin frame833.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2634_span : frame833.space ≤ frame834.space :=
  frame833.inclusion frame834 witness2634 (by decide)
def edge2634 : CertifiedEdge catalog where
  old := 833
  next := 834
  rank := 1
  good := by
    constructor
    · exact edge2634_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2635 : Fin frame833.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2635_span : frame833.space ≤ frame835.space :=
  frame833.inclusion frame835 witness2635 (by decide)
def edge2635 : CertifiedEdge catalog where
  old := 833
  next := 835
  rank := 1
  good := by
    constructor
    · exact edge2635_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2636 : Fin frame834.rank → ℕ := ![257,258,4,264,272,32,320,384]
theorem edge2636_span : frame834.space ≤ frame1.space :=
  frame834.inclusion frame1 witness2636 (by decide)
def edge2636 : CertifiedEdge catalog where
  old := 834
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2636_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2637 : Fin frame835.rank → ℕ := ![257,258,260,8,16,288,320,384]
theorem edge2637_span : frame835.space ≤ frame1.space :=
  frame835.inclusion frame1 witness2637 (by decide)
def edge2637 : CertifiedEdge catalog where
  old := 835
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2637_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2638 : Fin frame836.rank → ℕ := ![1,2,132,8,16,160,192]
theorem edge2638_span : frame836.space ≤ frame832.space :=
  frame836.inclusion frame832 witness2638 (by decide)
def edge2638 : CertifiedEdge catalog where
  old := 836
  next := 832
  rank := 1
  good := by
    constructor
    · exact edge2638_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2639 : Fin frame836.rank → ℕ := ![65,66,68,72,80,96,128]
theorem edge2639_span : frame836.space ≤ frame834.space :=
  frame836.inclusion frame834 witness2639 (by decide)
def edge2639 : CertifiedEdge catalog where
  old := 836
  next := 834
  rank := 1
  good := by
    constructor
    · exact edge2639_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2640 : Fin frame837.rank → ℕ := ![1,2,132,8,16,160,192]
theorem edge2640_span : frame837.space ≤ frame831.space :=
  frame837.inclusion frame831 witness2640 (by decide)
def edge2640 : CertifiedEdge catalog where
  old := 837
  next := 831
  rank := 1
  good := by
    constructor
    · exact edge2640_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2641 : Fin frame837.rank → ℕ := ![65,66,4,8,16,32,128]
theorem edge2641_span : frame837.space ≤ frame835.space :=
  frame837.inclusion frame835 witness2641 (by decide)
def edge2641 : CertifiedEdge catalog where
  old := 837
  next := 835
  rank := 1
  good := by
    constructor
    · exact edge2641_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2642 : Fin frame838.rank → ℕ := ![129,2,4,8,144,32,64]
theorem edge2642_span : frame838.space ≤ frame839.space :=
  frame838.inclusion frame839 witness2642 (by decide)
def edge2642 : CertifiedEdge catalog where
  old := 838
  next := 839
  rank := 1
  good := by
    constructor
    · exact edge2642_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2643 : Fin frame838.rank → ℕ := ![65,2,68,8,16,32,128]
theorem edge2643_span : frame838.space ≤ frame840.space :=
  frame838.inclusion frame840 witness2643 (by decide)
def edge2643 : CertifiedEdge catalog where
  old := 838
  next := 840
  rank := 1
  good := by
    constructor
    · exact edge2643_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2644 : Fin frame839.rank → ℕ := ![65,2,68,8,16,32,128,256]
theorem edge2644_span : frame839.space ≤ frame1.space :=
  frame839.inclusion frame1 witness2644 (by decide)
def edge2644 : CertifiedEdge catalog where
  old := 839
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2644_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2645 : Fin frame840.rank → ℕ := ![257,2,4,8,272,32,64,128]
theorem edge2645_span : frame840.space ≤ frame1.space :=
  frame840.inclusion frame1 witness2645 (by decide)
def edge2645 : CertifiedEdge catalog where
  old := 840
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2645_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2646 : Fin frame841.rank → ℕ := ![129,2,4,136,16,32,64]
theorem edge2646_span : frame841.space ≤ frame842.space :=
  frame841.inclusion frame842 witness2646 (by decide)
def edge2646 : CertifiedEdge catalog where
  old := 841
  next := 842
  rank := 1
  good := by
    constructor
    · exact edge2646_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2647 : Fin frame841.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2647_span : frame841.space ≤ frame843.space :=
  frame841.inclusion frame843 witness2647 (by decide)
def edge2647 : CertifiedEdge catalog where
  old := 841
  next := 843
  rank := 1
  good := by
    constructor
    · exact edge2647_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2648 : Fin frame842.rank → ℕ := ![257,2,260,264,272,32,320,384]
theorem edge2648_span : frame842.space ≤ frame1.space :=
  frame842.inclusion frame1 witness2648 (by decide)
def edge2648 : CertifiedEdge catalog where
  old := 842
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2648_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2649 : Fin frame843.rank → ℕ := ![129,2,4,136,16,32,64,256]
theorem edge2649_span : frame843.space ≤ frame1.space :=
  frame843.inclusion frame1 witness2649 (by decide)
def edge2649 : CertifiedEdge catalog where
  old := 843
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2649_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2650 : Fin frame844.rank → ℕ := ![65,2,4,72,16,32,128]
theorem edge2650_span : frame844.space ≤ frame839.space :=
  frame844.inclusion frame839 witness2650 (by decide)
def edge2650 : CertifiedEdge catalog where
  old := 844
  next := 839
  rank := 1
  good := by
    constructor
    · exact edge2650_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2651 : Fin frame844.rank → ℕ := ![65,2,68,8,16,32,128]
theorem edge2651_span : frame844.space ≤ frame843.space :=
  frame844.inclusion frame843 witness2651 (by decide)
def edge2651 : CertifiedEdge catalog where
  old := 844
  next := 843
  rank := 1
  good := by
    constructor
    · exact edge2651_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2652 : Fin frame845.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2652_span : frame845.space ≤ frame840.space :=
  frame845.inclusion frame840 witness2652 (by decide)
def edge2652 : CertifiedEdge catalog where
  old := 845
  next := 840
  rank := 1
  good := by
    constructor
    · exact edge2652_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2653 : Fin frame845.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2653_span : frame845.space ≤ frame842.space :=
  frame845.inclusion frame842 witness2653 (by decide)
def edge2653 : CertifiedEdge catalog where
  old := 845
  next := 842
  rank := 1
  good := by
    constructor
    · exact edge2653_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2654 : Fin frame846.rank → ℕ := ![1,130,4,136,16,32,64]
theorem edge2654_span : frame846.space ≤ frame847.space :=
  frame846.inclusion frame847 witness2654 (by decide)
def edge2654 : CertifiedEdge catalog where
  old := 846
  next := 847
  rank := 1
  good := by
    constructor
    · exact edge2654_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2655 : Fin frame846.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2655_span : frame846.space ≤ frame848.space :=
  frame846.inclusion frame848 witness2655 (by decide)
def edge2655 : CertifiedEdge catalog where
  old := 846
  next := 848
  rank := 1
  good := by
    constructor
    · exact edge2655_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
