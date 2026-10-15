module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2816 : Fin frame954.rank → ℕ := ![257,2,4,8,16,288,64,128]
theorem edge2816_span : frame954.space ≤ frame1.space :=
  frame954.inclusion frame1 witness2816 (by decide)
def edge2816 : CertifiedEdge catalog where
  old := 954
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2816_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2817 : Fin frame955.rank → ℕ := ![129,2,132,8,16,32,64,256]
theorem edge2817_span : frame955.space ≤ frame1.space :=
  frame955.inclusion frame1 witness2817 (by decide)
def edge2817 : CertifiedEdge catalog where
  old := 955
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2817_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2818 : Fin frame956.rank → ℕ := ![65,2,68,8,16,32,128]
theorem edge2818_span : frame956.space ≤ frame951.space :=
  frame956.inclusion frame951 witness2818 (by decide)
def edge2818 : CertifiedEdge catalog where
  old := 956
  next := 951
  rank := 1
  good := by
    constructor
    · exact edge2818_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2819 : Fin frame956.rank → ℕ := ![65,2,4,72,16,32,128]
theorem edge2819_span : frame956.space ≤ frame955.space :=
  frame956.inclusion frame955 witness2819 (by decide)
def edge2819 : CertifiedEdge catalog where
  old := 956
  next := 955
  rank := 1
  good := by
    constructor
    · exact edge2819_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2820 : Fin frame957.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2820_span : frame957.space ≤ frame952.space :=
  frame957.inclusion frame952 witness2820 (by decide)
def edge2820 : CertifiedEdge catalog where
  old := 957
  next := 952
  rank := 1
  good := by
    constructor
    · exact edge2820_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2821 : Fin frame957.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2821_span : frame957.space ≤ frame954.space :=
  frame957.inclusion frame954 witness2821 (by decide)
def edge2821 : CertifiedEdge catalog where
  old := 957
  next := 954
  rank := 1
  good := by
    constructor
    · exact edge2821_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2822 : Fin frame958.rank → ℕ := ![1,2,132,8,16,160,192]
theorem edge2822_span : frame958.space ≤ frame959.space :=
  frame958.inclusion frame959 witness2822 (by decide)
def edge2822 : CertifiedEdge catalog where
  old := 958
  next := 959
  rank := 1
  good := by
    constructor
    · exact edge2822_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2823 : Fin frame958.rank → ℕ := ![1,66,4,72,16,32,128]
theorem edge2823_span : frame958.space ≤ frame960.space :=
  frame958.inclusion frame960 witness2823 (by decide)
def edge2823 : CertifiedEdge catalog where
  old := 958
  next := 960
  rank := 1
  good := by
    constructor
    · exact edge2823_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2824 : Fin frame959.rank → ℕ := ![1,66,4,72,16,32,128,256]
theorem edge2824_span : frame959.space ≤ frame1.space :=
  frame959.inclusion frame1 witness2824 (by decide)
def edge2824 : CertifiedEdge catalog where
  old := 959
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2824_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2825 : Fin frame960.rank → ℕ := ![1,258,260,264,16,288,320,384]
theorem edge2825_span : frame960.space ≤ frame1.space :=
  frame960.inclusion frame1 witness2825 (by decide)
def edge2825 : CertifiedEdge catalog where
  old := 960
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2825_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2826 : Fin frame961.rank → ℕ := ![1,130,132,8,16,32,64]
theorem edge2826_span : frame961.space ≤ frame962.space :=
  frame961.inclusion frame962 witness2826 (by decide)
def edge2826 : CertifiedEdge catalog where
  old := 961
  next := 962
  rank := 1
  good := by
    constructor
    · exact edge2826_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2827 : Fin frame961.rank → ℕ := ![1,130,4,8,16,160,64]
theorem edge2827_span : frame961.space ≤ frame963.space :=
  frame961.inclusion frame963 witness2827 (by decide)
def edge2827 : CertifiedEdge catalog where
  old := 961
  next := 963
  rank := 1
  good := by
    constructor
    · exact edge2827_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2828 : Fin frame962.rank → ℕ := ![1,258,4,8,16,288,64,128]
theorem edge2828_span : frame962.space ≤ frame1.space :=
  frame962.inclusion frame1 witness2828 (by decide)
def edge2828 : CertifiedEdge catalog where
  old := 962
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2828_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2829 : Fin frame963.rank → ℕ := ![1,130,132,8,16,32,64,256]
theorem edge2829_span : frame963.space ≤ frame1.space :=
  frame963.inclusion frame1 witness2829 (by decide)
def edge2829 : CertifiedEdge catalog where
  old := 963
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2829_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2830 : Fin frame964.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2830_span : frame964.space ≤ frame960.space :=
  frame964.inclusion frame960 witness2830 (by decide)
def edge2830 : CertifiedEdge catalog where
  old := 964
  next := 960
  rank := 1
  good := by
    constructor
    · exact edge2830_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2831 : Fin frame964.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2831_span : frame964.space ≤ frame962.space :=
  frame964.inclusion frame962 witness2831 (by decide)
def edge2831 : CertifiedEdge catalog where
  old := 964
  next := 962
  rank := 1
  good := by
    constructor
    · exact edge2831_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2832 : Fin frame965.rank → ℕ := ![1,66,68,8,16,32,128]
theorem edge2832_span : frame965.space ≤ frame959.space :=
  frame965.inclusion frame959 witness2832 (by decide)
def edge2832 : CertifiedEdge catalog where
  old := 965
  next := 959
  rank := 1
  good := by
    constructor
    · exact edge2832_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2833 : Fin frame965.rank → ℕ := ![1,66,4,72,16,32,128]
theorem edge2833_span : frame965.space ≤ frame963.space :=
  frame965.inclusion frame963 witness2833 (by decide)
def edge2833 : CertifiedEdge catalog where
  old := 965
  next := 963
  rank := 1
  good := by
    constructor
    · exact edge2833_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2834 : Fin frame966.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2834_span : frame966.space ≤ frame967.space :=
  frame966.inclusion frame967 witness2834 (by decide)
def edge2834 : CertifiedEdge catalog where
  old := 966
  next := 967
  rank := 1
  good := by
    constructor
    · exact edge2834_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2835 : Fin frame966.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2835_span : frame966.space ≤ frame968.space :=
  frame966.inclusion frame968 witness2835 (by decide)
def edge2835 : CertifiedEdge catalog where
  old := 966
  next := 968
  rank := 1
  good := by
    constructor
    · exact edge2835_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2836 : Fin frame967.rank → ℕ := ![1,2,68,72,16,32,128,256]
theorem edge2836_span : frame967.space ≤ frame1.space :=
  frame967.inclusion frame1 witness2836 (by decide)
def edge2836 : CertifiedEdge catalog where
  old := 967
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2836_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2837 : Fin frame968.rank → ℕ := ![1,2,4,8,80,96,128,256]
theorem edge2837_span : frame968.space ≤ frame1.space :=
  frame968.inclusion frame1 witness2837 (by decide)
def edge2837 : CertifiedEdge catalog where
  old := 968
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2837_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2838 : Fin frame969.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2838_span : frame969.space ≤ frame970.space :=
  frame969.inclusion frame970 witness2838 (by decide)
def edge2838 : CertifiedEdge catalog where
  old := 969
  next := 970
  rank := 1
  good := by
    constructor
    · exact edge2838_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2839 : Fin frame969.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2839_span : frame969.space ≤ frame971.space :=
  frame969.inclusion frame971 witness2839 (by decide)
def edge2839 : CertifiedEdge catalog where
  old := 969
  next := 971
  rank := 1
  good := by
    constructor
    · exact edge2839_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2840 : Fin frame970.rank → ℕ := ![1,2,260,8,16,288,64,128]
theorem edge2840_span : frame970.space ≤ frame1.space :=
  frame970.inclusion frame1 witness2840 (by decide)
def edge2840 : CertifiedEdge catalog where
  old := 970
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2840_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2841 : Fin frame971.rank → ℕ := ![1,2,4,264,272,32,64,128]
theorem edge2841_span : frame971.space ≤ frame1.space :=
  frame971.inclusion frame1 witness2841 (by decide)
def edge2841 : CertifiedEdge catalog where
  old := 971
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2841_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2842 : Fin frame972.rank → ℕ := ![1,2,4,136,144,32,64]
theorem edge2842_span : frame972.space ≤ frame967.space :=
  frame972.inclusion frame967 witness2842 (by decide)
def edge2842 : CertifiedEdge catalog where
  old := 972
  next := 967
  rank := 1
  good := by
    constructor
    · exact edge2842_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2843 : Fin frame972.rank → ℕ := ![1,2,68,72,16,32,128]
theorem edge2843_span : frame972.space ≤ frame971.space :=
  frame972.inclusion frame971 witness2843 (by decide)
def edge2843 : CertifiedEdge catalog where
  old := 972
  next := 971
  rank := 1
  good := by
    constructor
    · exact edge2843_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2844 : Fin frame973.rank → ℕ := ![1,2,132,8,16,160,64]
theorem edge2844_span : frame973.space ≤ frame968.space :=
  frame973.inclusion frame968 witness2844 (by decide)
def edge2844 : CertifiedEdge catalog where
  old := 973
  next := 968
  rank := 1
  good := by
    constructor
    · exact edge2844_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2845 : Fin frame973.rank → ℕ := ![1,2,4,8,80,96,128]
theorem edge2845_span : frame973.space ≤ frame970.space :=
  frame973.inclusion frame970 witness2845 (by decide)
def edge2845 : CertifiedEdge catalog where
  old := 973
  next := 970
  rank := 1
  good := by
    constructor
    · exact edge2845_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2846 : Fin frame974.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2846_span : frame974.space ≤ frame975.space :=
  frame974.inclusion frame975 witness2846 (by decide)
def edge2846 : CertifiedEdge catalog where
  old := 974
  next := 975
  rank := 1
  good := by
    constructor
    · exact edge2846_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2847 : Fin frame974.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2847_span : frame974.space ≤ frame976.space :=
  frame974.inclusion frame976 witness2847 (by decide)
def edge2847 : CertifiedEdge catalog where
  old := 974
  next := 976
  rank := 1
  good := by
    constructor
    · exact edge2847_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
