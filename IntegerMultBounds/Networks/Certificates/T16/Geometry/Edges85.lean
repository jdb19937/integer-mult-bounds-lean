module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2720 : Fin frame890.rank → ℕ := ![1,2,4,8,16,288,320,128]
theorem edge2720_span : frame890.space ≤ frame1.space :=
  frame890.inclusion frame1 witness2720 (by decide)
def edge2720 : CertifiedEdge catalog where
  old := 890
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2720_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2721 : Fin frame891.rank → ℕ := ![1,2,36,8,48,64,128,256]
theorem edge2721_span : frame891.space ≤ frame1.space :=
  frame891.inclusion frame1 witness2721 (by decide)
def edge2721 : CertifiedEdge catalog where
  old := 891
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2721_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2722 : Fin frame892.rank → ℕ := ![1,2,36,8,48,64,128]
theorem edge2722_span : frame892.space ≤ frame887.space :=
  frame892.inclusion frame887 witness2722 (by decide)
def edge2722 : CertifiedEdge catalog where
  old := 892
  next := 887
  rank := 1
  good := by
    constructor
    · exact edge2722_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2723 : Fin frame892.rank → ℕ := ![1,2,4,8,144,32,192]
theorem edge2723_span : frame892.space ≤ frame891.space :=
  frame892.inclusion frame891 witness2723 (by decide)
def edge2723 : CertifiedEdge catalog where
  old := 892
  next := 891
  rank := 1
  good := by
    constructor
    · exact edge2723_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2724 : Fin frame893.rank → ℕ := ![1,2,4,8,16,160,192]
theorem edge2724_span : frame893.space ≤ frame888.space :=
  frame893.inclusion frame888 witness2724 (by decide)
def edge2724 : CertifiedEdge catalog where
  old := 893
  next := 888
  rank := 1
  good := by
    constructor
    · exact edge2724_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2725 : Fin frame893.rank → ℕ := ![1,2,132,8,16,32,192]
theorem edge2725_span : frame893.space ≤ frame890.space :=
  frame893.inclusion frame890 witness2725 (by decide)
def edge2725 : CertifiedEdge catalog where
  old := 893
  next := 890
  rank := 1
  good := by
    constructor
    · exact edge2725_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2726 : Fin frame894.rank → ℕ := ![1,2,132,136,16,160,64]
theorem edge2726_span : frame894.space ≤ frame895.space :=
  frame894.inclusion frame895 witness2726 (by decide)
def edge2726 : CertifiedEdge catalog where
  old := 894
  next := 895
  rank := 1
  good := by
    constructor
    · exact edge2726_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2727 : Fin frame894.rank → ℕ := ![9,10,4,16,32,64,128]
theorem edge2727_span : frame894.space ≤ frame896.space :=
  frame894.inclusion frame896 witness2727 (by decide)
def edge2727 : CertifiedEdge catalog where
  old := 894
  next := 896
  rank := 1
  good := by
    constructor
    · exact edge2727_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2728 : Fin frame895.rank → ℕ := ![9,10,4,16,32,64,128,256]
theorem edge2728_span : frame895.space ≤ frame1.space :=
  frame895.inclusion frame1 witness2728 (by decide)
def edge2728 : CertifiedEdge catalog where
  old := 895
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2728_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2729 : Fin frame896.rank → ℕ := ![257,258,260,264,272,32,320,128]
theorem edge2729_span : frame896.space ≤ frame1.space :=
  frame896.inclusion frame1 witness2729 (by decide)
def edge2729 : CertifiedEdge catalog where
  old := 896
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2729_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2730 : Fin frame897.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2730_span : frame897.space ≤ frame898.space :=
  frame897.inclusion frame898 witness2730 (by decide)
def edge2730 : CertifiedEdge catalog where
  old := 897
  next := 898
  rank := 1
  good := by
    constructor
    · exact edge2730_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2731 : Fin frame897.rank → ℕ := ![129,130,4,136,144,160,192]
theorem edge2731_span : frame897.space ≤ frame899.space :=
  frame897.inclusion frame899 witness2731 (by decide)
def edge2731 : CertifiedEdge catalog where
  old := 897
  next := 899
  rank := 1
  good := by
    constructor
    · exact edge2731_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2732 : Fin frame898.rank → ℕ := ![129,130,4,136,144,160,192,256]
theorem edge2732_span : frame898.space ≤ frame1.space :=
  frame898.inclusion frame1 witness2732 (by decide)
def edge2732 : CertifiedEdge catalog where
  old := 898
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2732_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2733 : Fin frame899.rank → ℕ := ![257,258,260,264,16,288,64,384]
theorem edge2733_span : frame899.space ≤ frame1.space :=
  frame899.inclusion frame1 witness2733 (by decide)
def edge2733 : CertifiedEdge catalog where
  old := 899
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2733_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2734 : Fin frame900.rank → ℕ := ![129,130,4,136,144,160,192]
theorem edge2734_span : frame900.space ≤ frame896.space :=
  frame900.inclusion frame896 witness2734 (by decide)
def edge2734 : CertifiedEdge catalog where
  old := 900
  next := 896
  rank := 1
  good := by
    constructor
    · exact edge2734_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2735 : Fin frame900.rank → ℕ := ![129,130,132,136,144,32,192]
theorem edge2735_span : frame900.space ≤ frame898.space :=
  frame900.inclusion frame898 witness2735 (by decide)
def edge2735 : CertifiedEdge catalog where
  old := 900
  next := 898
  rank := 1
  good := by
    constructor
    · exact edge2735_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2736 : Fin frame901.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2736_span : frame901.space ≤ frame895.space :=
  frame901.inclusion frame895 witness2736 (by decide)
def edge2736 : CertifiedEdge catalog where
  old := 901
  next := 895
  rank := 1
  good := by
    constructor
    · exact edge2736_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2737 : Fin frame901.rank → ℕ := ![9,10,4,16,32,64,128]
theorem edge2737_span : frame901.space ≤ frame899.space :=
  frame901.inclusion frame899 witness2737 (by decide)
def edge2737 : CertifiedEdge catalog where
  old := 901
  next := 899
  rank := 1
  good := by
    constructor
    · exact edge2737_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2738 : Fin frame902.rank → ℕ := ![17,2,4,24,32,64,128]
theorem edge2738_span : frame902.space ≤ frame903.space :=
  frame902.inclusion frame903 witness2738 (by decide)
def edge2738 : CertifiedEdge catalog where
  old := 902
  next := 903
  rank := 1
  good := by
    constructor
    · exact edge2738_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2739 : Fin frame902.rank → ℕ := ![9,2,12,16,32,64,128]
theorem edge2739_span : frame902.space ≤ frame904.space :=
  frame902.inclusion frame904 witness2739 (by decide)
def edge2739 : CertifiedEdge catalog where
  old := 902
  next := 904
  rank := 1
  good := by
    constructor
    · exact edge2739_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2740 : Fin frame903.rank → ℕ := ![9,2,12,16,32,64,128,256]
theorem edge2740_span : frame903.space ≤ frame1.space :=
  frame903.inclusion frame1 witness2740 (by decide)
def edge2740 : CertifiedEdge catalog where
  old := 903
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2740_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2741 : Fin frame904.rank → ℕ := ![33,2,4,8,48,64,128,256]
theorem edge2741_span : frame904.space ≤ frame1.space :=
  frame904.inclusion frame1 witness2741 (by decide)
def edge2741 : CertifiedEdge catalog where
  old := 904
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2741_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2742 : Fin frame905.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2742_span : frame905.space ≤ frame906.space :=
  frame905.inclusion frame906 witness2742 (by decide)
def edge2742 : CertifiedEdge catalog where
  old := 905
  next := 906
  rank := 1
  good := by
    constructor
    · exact edge2742_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2743 : Fin frame905.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2743_span : frame905.space ≤ frame907.space :=
  frame905.inclusion frame907 witness2743 (by decide)
def edge2743 : CertifiedEdge catalog where
  old := 905
  next := 907
  rank := 1
  good := by
    constructor
    · exact edge2743_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2744 : Fin frame906.rank → ℕ := ![129,2,132,136,144,160,192,256]
theorem edge2744_span : frame906.space ≤ frame1.space :=
  frame906.inclusion frame1 witness2744 (by decide)
def edge2744 : CertifiedEdge catalog where
  old := 906
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2744_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2745 : Fin frame907.rank → ℕ := ![129,2,4,8,16,32,192,256]
theorem edge2745_span : frame907.space ≤ frame1.space :=
  frame907.inclusion frame1 witness2745 (by decide)
def edge2745 : CertifiedEdge catalog where
  old := 907
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2745_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2746 : Fin frame908.rank → ℕ := ![65,2,4,8,16,96,128]
theorem edge2746_span : frame908.space ≤ frame903.space :=
  frame908.inclusion frame903 witness2746 (by decide)
def edge2746 : CertifiedEdge catalog where
  old := 908
  next := 903
  rank := 1
  good := by
    constructor
    · exact edge2746_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2747 : Fin frame908.rank → ℕ := ![9,2,12,16,32,64,128]
theorem edge2747_span : frame908.space ≤ frame907.space :=
  frame908.inclusion frame907 witness2747 (by decide)
def edge2747 : CertifiedEdge catalog where
  old := 908
  next := 907
  rank := 1
  good := by
    constructor
    · exact edge2747_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2748 : Fin frame909.rank → ℕ := ![1,2,68,72,16,96,128]
theorem edge2748_span : frame909.space ≤ frame904.space :=
  frame909.inclusion frame904 witness2748 (by decide)
def edge2748 : CertifiedEdge catalog where
  old := 909
  next := 904
  rank := 1
  good := by
    constructor
    · exact edge2748_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2749 : Fin frame909.rank → ℕ := ![33,2,4,8,48,64,128]
theorem edge2749_span : frame909.space ≤ frame906.space :=
  frame909.inclusion frame906 witness2749 (by decide)
def edge2749 : CertifiedEdge catalog where
  old := 909
  next := 906
  rank := 1
  good := by
    constructor
    · exact edge2749_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2750 : Fin frame910.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2750_span : frame910.space ≤ frame911.space :=
  frame910.inclusion frame911 witness2750 (by decide)
def edge2750 : CertifiedEdge catalog where
  old := 910
  next := 911
  rank := 1
  good := by
    constructor
    · exact edge2750_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2751 : Fin frame910.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2751_span : frame910.space ≤ frame912.space :=
  frame910.inclusion frame912 witness2751 (by decide)
def edge2751 : CertifiedEdge catalog where
  old := 910
  next := 912
  rank := 1
  good := by
    constructor
    · exact edge2751_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
