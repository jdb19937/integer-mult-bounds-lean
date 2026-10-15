module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2784 : Fin frame933.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2784_span : frame933.space ≤ frame927.space :=
  frame933.inclusion frame927 witness2784 (by decide)
def edge2784 : CertifiedEdge catalog where
  old := 933
  next := 927
  rank := 1
  good := by
    constructor
    · exact edge2784_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2785 : Fin frame933.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2785_span : frame933.space ≤ frame931.space :=
  frame933.inclusion frame931 witness2785 (by decide)
def edge2785 : CertifiedEdge catalog where
  old := 933
  next := 931
  rank := 1
  good := by
    constructor
    · exact edge2785_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2786 : Fin frame934.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2786_span : frame934.space ≤ frame935.space :=
  frame934.inclusion frame935 witness2786 (by decide)
def edge2786 : CertifiedEdge catalog where
  old := 934
  next := 935
  rank := 1
  good := by
    constructor
    · exact edge2786_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2787 : Fin frame934.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2787_span : frame934.space ≤ frame936.space :=
  frame934.inclusion frame936 witness2787 (by decide)
def edge2787 : CertifiedEdge catalog where
  old := 934
  next := 936
  rank := 1
  good := by
    constructor
    · exact edge2787_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2788 : Fin frame935.rank → ℕ := ![1,258,4,8,16,32,64,384]
theorem edge2788_span : frame935.space ≤ frame1.space :=
  frame935.inclusion frame1 witness2788 (by decide)
def edge2788 : CertifiedEdge catalog where
  old := 935
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2788_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2789 : Fin frame936.rank → ℕ := ![1,258,260,264,272,288,64,384]
theorem edge2789_span : frame936.space ≤ frame1.space :=
  frame936.inclusion frame1 witness2789 (by decide)
def edge2789 : CertifiedEdge catalog where
  old := 936
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2789_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2790 : Fin frame937.rank → ℕ := ![1,18,20,8,32,64,128]
theorem edge2790_span : frame937.space ≤ frame938.space :=
  frame937.inclusion frame938 witness2790 (by decide)
def edge2790 : CertifiedEdge catalog where
  old := 937
  next := 938
  rank := 1
  good := by
    constructor
    · exact edge2790_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2791 : Fin frame937.rank → ℕ := ![1,18,4,24,32,64,128]
theorem edge2791_span : frame937.space ≤ frame939.space :=
  frame937.inclusion frame939 witness2791 (by decide)
def edge2791 : CertifiedEdge catalog where
  old := 937
  next := 939
  rank := 1
  good := by
    constructor
    · exact edge2791_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2792 : Fin frame938.rank → ℕ := ![1,18,4,24,32,64,128,256]
theorem edge2792_span : frame938.space ≤ frame1.space :=
  frame938.inclusion frame1 witness2792 (by decide)
def edge2792 : CertifiedEdge catalog where
  old := 938
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2792_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2793 : Fin frame939.rank → ℕ := ![1,34,36,8,16,64,128,256]
theorem edge2793_span : frame939.space ≤ frame1.space :=
  frame939.inclusion frame1 witness2793 (by decide)
def edge2793 : CertifiedEdge catalog where
  old := 939
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2793_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2794 : Fin frame940.rank → ℕ := ![1,34,36,8,16,64,128]
theorem edge2794_span : frame940.space ≤ frame935.space :=
  frame940.inclusion frame935 witness2794 (by decide)
def edge2794 : CertifiedEdge catalog where
  old := 940
  next := 935
  rank := 1
  good := by
    constructor
    · exact edge2794_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2795 : Fin frame940.rank → ℕ := ![1,130,4,8,16,32,192]
theorem edge2795_span : frame940.space ≤ frame939.space :=
  frame940.inclusion frame939 witness2795 (by decide)
def edge2795 : CertifiedEdge catalog where
  old := 940
  next := 939
  rank := 1
  good := by
    constructor
    · exact edge2795_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2796 : Fin frame941.rank → ℕ := ![1,18,4,24,32,64,128]
theorem edge2796_span : frame941.space ≤ frame936.space :=
  frame941.inclusion frame936 witness2796 (by decide)
def edge2796 : CertifiedEdge catalog where
  old := 941
  next := 936
  rank := 1
  good := by
    constructor
    · exact edge2796_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2797 : Fin frame941.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2797_span : frame941.space ≤ frame938.space :=
  frame941.inclusion frame938 witness2797 (by decide)
def edge2797 : CertifiedEdge catalog where
  old := 941
  next := 938
  rank := 1
  good := by
    constructor
    · exact edge2797_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2798 : Fin frame942.rank → ℕ := ![17,2,20,8,32,64,128]
theorem edge2798_span : frame942.space ≤ frame943.space :=
  frame942.inclusion frame943 witness2798 (by decide)
def edge2798 : CertifiedEdge catalog where
  old := 942
  next := 943
  rank := 1
  good := by
    constructor
    · exact edge2798_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2799 : Fin frame942.rank → ℕ := ![17,2,4,24,32,64,128]
theorem edge2799_span : frame942.space ≤ frame944.space :=
  frame942.inclusion frame944 witness2799 (by decide)
def edge2799 : CertifiedEdge catalog where
  old := 942
  next := 944
  rank := 1
  good := by
    constructor
    · exact edge2799_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2800 : Fin frame943.rank → ℕ := ![17,2,4,24,32,64,128,256]
theorem edge2800_span : frame943.space ≤ frame1.space :=
  frame943.inclusion frame1 witness2800 (by decide)
def edge2800 : CertifiedEdge catalog where
  old := 943
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2800_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2801 : Fin frame944.rank → ℕ := ![33,2,36,8,16,64,128,256]
theorem edge2801_span : frame944.space ≤ frame1.space :=
  frame944.inclusion frame1 witness2801 (by decide)
def edge2801 : CertifiedEdge catalog where
  old := 944
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2801_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2802 : Fin frame945.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2802_span : frame945.space ≤ frame946.space :=
  frame945.inclusion frame946 witness2802 (by decide)
def edge2802 : CertifiedEdge catalog where
  old := 945
  next := 946
  rank := 1
  good := by
    constructor
    · exact edge2802_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2803 : Fin frame945.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2803_span : frame945.space ≤ frame947.space :=
  frame945.inclusion frame947 witness2803 (by decide)
def edge2803 : CertifiedEdge catalog where
  old := 945
  next := 947
  rank := 1
  good := by
    constructor
    · exact edge2803_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2804 : Fin frame946.rank → ℕ := ![257,2,4,8,16,32,64,384]
theorem edge2804_span : frame946.space ≤ frame1.space :=
  frame946.inclusion frame1 witness2804 (by decide)
def edge2804 : CertifiedEdge catalog where
  old := 946
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2804_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2805 : Fin frame947.rank → ℕ := ![257,2,260,264,272,288,64,384]
theorem edge2805_span : frame947.space ≤ frame1.space :=
  frame947.inclusion frame1 witness2805 (by decide)
def edge2805 : CertifiedEdge catalog where
  old := 947
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2805_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2806 : Fin frame948.rank → ℕ := ![129,2,4,8,16,32,192]
theorem edge2806_span : frame948.space ≤ frame944.space :=
  frame948.inclusion frame944 witness2806 (by decide)
def edge2806 : CertifiedEdge catalog where
  old := 948
  next := 944
  rank := 1
  good := by
    constructor
    · exact edge2806_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2807 : Fin frame948.rank → ℕ := ![33,2,36,8,16,64,128]
theorem edge2807_span : frame948.space ≤ frame946.space :=
  frame948.inclusion frame946 witness2807 (by decide)
def edge2807 : CertifiedEdge catalog where
  old := 948
  next := 946
  rank := 1
  good := by
    constructor
    · exact edge2807_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2808 : Fin frame949.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2808_span : frame949.space ≤ frame943.space :=
  frame949.inclusion frame943 witness2808 (by decide)
def edge2808 : CertifiedEdge catalog where
  old := 949
  next := 943
  rank := 1
  good := by
    constructor
    · exact edge2808_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2809 : Fin frame949.rank → ℕ := ![17,2,4,24,32,64,128]
theorem edge2809_span : frame949.space ≤ frame947.space :=
  frame949.inclusion frame947 witness2809 (by decide)
def edge2809 : CertifiedEdge catalog where
  old := 949
  next := 947
  rank := 1
  good := by
    constructor
    · exact edge2809_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2810 : Fin frame950.rank → ℕ := ![1,2,132,8,16,160,192]
theorem edge2810_span : frame950.space ≤ frame951.space :=
  frame950.inclusion frame951 witness2810 (by decide)
def edge2810 : CertifiedEdge catalog where
  old := 950
  next := 951
  rank := 1
  good := by
    constructor
    · exact edge2810_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2811 : Fin frame950.rank → ℕ := ![65,2,4,72,16,32,128]
theorem edge2811_span : frame950.space ≤ frame952.space :=
  frame950.inclusion frame952 witness2811 (by decide)
def edge2811 : CertifiedEdge catalog where
  old := 950
  next := 952
  rank := 1
  good := by
    constructor
    · exact edge2811_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2812 : Fin frame951.rank → ℕ := ![65,2,4,72,16,32,128,256]
theorem edge2812_span : frame951.space ≤ frame1.space :=
  frame951.inclusion frame1 witness2812 (by decide)
def edge2812 : CertifiedEdge catalog where
  old := 951
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2812_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2813 : Fin frame952.rank → ℕ := ![257,2,260,264,16,288,320,384]
theorem edge2813_span : frame952.space ≤ frame1.space :=
  frame952.inclusion frame1 witness2813 (by decide)
def edge2813 : CertifiedEdge catalog where
  old := 952
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2813_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2814 : Fin frame953.rank → ℕ := ![129,2,132,8,16,32,64]
theorem edge2814_span : frame953.space ≤ frame954.space :=
  frame953.inclusion frame954 witness2814 (by decide)
def edge2814 : CertifiedEdge catalog where
  old := 953
  next := 954
  rank := 1
  good := by
    constructor
    · exact edge2814_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2815 : Fin frame953.rank → ℕ := ![129,2,4,8,16,160,64]
theorem edge2815_span : frame953.space ≤ frame955.space :=
  frame953.inclusion frame955 witness2815 (by decide)
def edge2815 : CertifiedEdge catalog where
  old := 953
  next := 955
  rank := 1
  good := by
    constructor
    · exact edge2815_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
