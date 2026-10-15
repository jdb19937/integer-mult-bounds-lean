module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2752 : Fin frame911.rank → ℕ := ![1,130,132,136,144,160,192,256]
theorem edge2752_span : frame911.space ≤ frame1.space :=
  frame911.inclusion frame1 witness2752 (by decide)
def edge2752 : CertifiedEdge catalog where
  old := 911
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2752_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2753 : Fin frame912.rank → ℕ := ![1,130,4,8,16,32,192,256]
theorem edge2753_span : frame912.space ≤ frame1.space :=
  frame912.inclusion frame1 witness2753 (by decide)
def edge2753 : CertifiedEdge catalog where
  old := 912
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2753_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2754 : Fin frame913.rank → ℕ := ![1,18,4,24,32,64,128]
theorem edge2754_span : frame913.space ≤ frame914.space :=
  frame913.inclusion frame914 witness2754 (by decide)
def edge2754 : CertifiedEdge catalog where
  old := 913
  next := 914
  rank := 1
  good := by
    constructor
    · exact edge2754_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2755 : Fin frame913.rank → ℕ := ![1,10,12,16,32,64,128]
theorem edge2755_span : frame913.space ≤ frame915.space :=
  frame913.inclusion frame915 witness2755 (by decide)
def edge2755 : CertifiedEdge catalog where
  old := 913
  next := 915
  rank := 1
  good := by
    constructor
    · exact edge2755_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2756 : Fin frame914.rank → ℕ := ![1,10,12,16,32,64,128,256]
theorem edge2756_span : frame914.space ≤ frame1.space :=
  frame914.inclusion frame1 witness2756 (by decide)
def edge2756 : CertifiedEdge catalog where
  old := 914
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2756_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2757 : Fin frame915.rank → ℕ := ![1,34,4,8,48,64,128,256]
theorem edge2757_span : frame915.space ≤ frame1.space :=
  frame915.inclusion frame1 witness2757 (by decide)
def edge2757 : CertifiedEdge catalog where
  old := 915
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2757_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2758 : Fin frame916.rank → ℕ := ![1,10,12,16,32,64,128]
theorem edge2758_span : frame916.space ≤ frame912.space :=
  frame916.inclusion frame912 witness2758 (by decide)
def edge2758 : CertifiedEdge catalog where
  old := 916
  next := 912
  rank := 1
  good := by
    constructor
    · exact edge2758_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2759 : Fin frame916.rank → ℕ := ![1,66,4,8,16,96,128]
theorem edge2759_span : frame916.space ≤ frame914.space :=
  frame916.inclusion frame914 witness2759 (by decide)
def edge2759 : CertifiedEdge catalog where
  old := 916
  next := 914
  rank := 1
  good := by
    constructor
    · exact edge2759_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2760 : Fin frame917.rank → ℕ := ![1,34,4,8,48,64,128]
theorem edge2760_span : frame917.space ≤ frame911.space :=
  frame917.inclusion frame911 witness2760 (by decide)
def edge2760 : CertifiedEdge catalog where
  old := 917
  next := 911
  rank := 1
  good := by
    constructor
    · exact edge2760_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2761 : Fin frame917.rank → ℕ := ![1,2,68,72,16,96,128]
theorem edge2761_span : frame917.space ≤ frame915.space :=
  frame917.inclusion frame915 witness2761 (by decide)
def edge2761 : CertifiedEdge catalog where
  old := 917
  next := 915
  rank := 1
  good := by
    constructor
    · exact edge2761_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2762 : Fin frame918.rank → ℕ := ![33,34,4,8,16,64,128]
theorem edge2762_span : frame918.space ≤ frame919.space :=
  frame918.inclusion frame919 witness2762 (by decide)
def edge2762 : CertifiedEdge catalog where
  old := 918
  next := 919
  rank := 1
  good := by
    constructor
    · exact edge2762_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2763 : Fin frame918.rank → ℕ := ![1,2,132,8,144,160,64]
theorem edge2763_span : frame918.space ≤ frame920.space :=
  frame918.inclusion frame920 witness2763 (by decide)
def edge2763 : CertifiedEdge catalog where
  old := 918
  next := 920
  rank := 1
  good := by
    constructor
    · exact edge2763_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2764 : Fin frame919.rank → ℕ := ![257,258,260,8,272,288,320,128]
theorem edge2764_span : frame919.space ≤ frame1.space :=
  frame919.inclusion frame1 witness2764 (by decide)
def edge2764 : CertifiedEdge catalog where
  old := 919
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2764_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2765 : Fin frame920.rank → ℕ := ![33,34,4,8,16,64,128,256]
theorem edge2765_span : frame920.space ≤ frame1.space :=
  frame920.inclusion frame1 witness2765 (by decide)
def edge2765 : CertifiedEdge catalog where
  old := 920
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2765_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2766 : Fin frame921.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2766_span : frame921.space ≤ frame922.space :=
  frame921.inclusion frame922 witness2766 (by decide)
def edge2766 : CertifiedEdge catalog where
  old := 921
  next := 922
  rank := 1
  good := by
    constructor
    · exact edge2766_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2767 : Fin frame921.rank → ℕ := ![129,130,132,136,16,160,192]
theorem edge2767_span : frame921.space ≤ frame923.space :=
  frame921.inclusion frame923 witness2767 (by decide)
def edge2767 : CertifiedEdge catalog where
  old := 921
  next := 923
  rank := 1
  good := by
    constructor
    · exact edge2767_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2768 : Fin frame922.rank → ℕ := ![129,130,132,136,16,160,192,256]
theorem edge2768_span : frame922.space ≤ frame1.space :=
  frame922.inclusion frame1 witness2768 (by decide)
def edge2768 : CertifiedEdge catalog where
  old := 922
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2768_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2769 : Fin frame923.rank → ℕ := ![257,258,4,264,272,288,64,384]
theorem edge2769_span : frame923.space ≤ frame1.space :=
  frame923.inclusion frame1 witness2769 (by decide)
def edge2769 : CertifiedEdge catalog where
  old := 923
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2769_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2770 : Fin frame924.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2770_span : frame924.space ≤ frame919.space :=
  frame924.inclusion frame919 witness2770 (by decide)
def edge2770 : CertifiedEdge catalog where
  old := 924
  next := 919
  rank := 1
  good := by
    constructor
    · exact edge2770_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2771 : Fin frame924.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2771_span : frame924.space ≤ frame923.space :=
  frame924.inclusion frame923 witness2771 (by decide)
def edge2771 : CertifiedEdge catalog where
  old := 924
  next := 923
  rank := 1
  good := by
    constructor
    · exact edge2771_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2772 : Fin frame925.rank → ℕ := ![1,2,68,72,16,96,128]
theorem edge2772_span : frame925.space ≤ frame920.space :=
  frame925.inclusion frame920 witness2772 (by decide)
def edge2772 : CertifiedEdge catalog where
  old := 925
  next := 920
  rank := 1
  good := by
    constructor
    · exact edge2772_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2773 : Fin frame925.rank → ℕ := ![33,34,4,8,16,64,128]
theorem edge2773_span : frame925.space ≤ frame922.space :=
  frame925.inclusion frame922 witness2773 (by decide)
def edge2773 : CertifiedEdge catalog where
  old := 925
  next := 922
  rank := 1
  good := by
    constructor
    · exact edge2773_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2774 : Fin frame926.rank → ℕ := ![1,2,4,8,144,32,192]
theorem edge2774_span : frame926.space ≤ frame927.space :=
  frame926.inclusion frame927 witness2774 (by decide)
def edge2774 : CertifiedEdge catalog where
  old := 926
  next := 927
  rank := 1
  good := by
    constructor
    · exact edge2774_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2775 : Fin frame926.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2775_span : frame926.space ≤ frame928.space :=
  frame926.inclusion frame928 witness2775 (by decide)
def edge2775 : CertifiedEdge catalog where
  old := 926
  next := 928
  rank := 1
  good := by
    constructor
    · exact edge2775_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2776 : Fin frame927.rank → ℕ := ![1,2,260,8,16,32,64,384]
theorem edge2776_span : frame927.space ≤ frame1.space :=
  frame927.inclusion frame1 witness2776 (by decide)
def edge2776 : CertifiedEdge catalog where
  old := 927
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2776_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2777 : Fin frame928.rank → ℕ := ![1,2,4,8,144,32,192,256]
theorem edge2777_span : frame928.space ≤ frame1.space :=
  frame928.inclusion frame1 witness2777 (by decide)
def edge2777 : CertifiedEdge catalog where
  old := 928
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2777_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2778 : Fin frame929.rank → ℕ := ![1,2,4,136,16,160,64]
theorem edge2778_span : frame929.space ≤ frame930.space :=
  frame929.inclusion frame930 witness2778 (by decide)
def edge2778 : CertifiedEdge catalog where
  old := 929
  next := 930
  rank := 1
  good := by
    constructor
    · exact edge2778_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2779 : Fin frame929.rank → ℕ := ![1,2,20,24,32,64,128]
theorem edge2779_span : frame929.space ≤ frame931.space :=
  frame929.inclusion frame931 witness2779 (by decide)
def edge2779 : CertifiedEdge catalog where
  old := 929
  next := 931
  rank := 1
  good := by
    constructor
    · exact edge2779_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2780 : Fin frame930.rank → ℕ := ![1,2,20,24,32,64,128,256]
theorem edge2780_span : frame930.space ≤ frame1.space :=
  frame930.inclusion frame1 witness2780 (by decide)
def edge2780 : CertifiedEdge catalog where
  old := 930
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2780_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2781 : Fin frame931.rank → ℕ := ![1,2,4,264,16,32,320,128]
theorem edge2781_span : frame931.space ≤ frame1.space :=
  frame931.inclusion frame1 witness2781 (by decide)
def edge2781 : CertifiedEdge catalog where
  old := 931
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2781_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2782 : Fin frame932.rank → ℕ := ![1,2,20,24,32,64,128]
theorem edge2782_span : frame932.space ≤ frame928.space :=
  frame932.inclusion frame928 witness2782 (by decide)
def edge2782 : CertifiedEdge catalog where
  old := 932
  next := 928
  rank := 1
  good := by
    constructor
    · exact edge2782_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2783 : Fin frame932.rank → ℕ := ![1,2,68,72,16,96,128]
theorem edge2783_span : frame932.space ≤ frame930.space :=
  frame932.inclusion frame930 witness2783 (by decide)
def edge2783 : CertifiedEdge catalog where
  old := 932
  next := 930
  rank := 1
  good := by
    constructor
    · exact edge2783_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
