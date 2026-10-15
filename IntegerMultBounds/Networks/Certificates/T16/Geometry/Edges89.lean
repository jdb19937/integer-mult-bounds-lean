module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2848 : Fin frame975.rank → ℕ := ![257,258,260,8,272,32,320,384]
theorem edge2848_span : frame975.space ≤ frame1.space :=
  frame975.inclusion frame1 witness2848 (by decide)
def edge2848 : CertifiedEdge catalog where
  old := 975
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2848_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2849 : Fin frame976.rank → ℕ := ![257,258,4,264,16,288,320,384]
theorem edge2849_span : frame976.space ≤ frame1.space :=
  frame976.inclusion frame1 witness2849 (by decide)
def edge2849 : CertifiedEdge catalog where
  old := 976
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2849_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2850 : Fin frame977.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2850_span : frame977.space ≤ frame978.space :=
  frame977.inclusion frame978 witness2850 (by decide)
def edge2850 : CertifiedEdge catalog where
  old := 977
  next := 978
  rank := 1
  good := by
    constructor
    · exact edge2850_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2851 : Fin frame977.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2851_span : frame977.space ≤ frame979.space :=
  frame977.inclusion frame979 witness2851 (by decide)
def edge2851 : CertifiedEdge catalog where
  old := 977
  next := 979
  rank := 1
  good := by
    constructor
    · exact edge2851_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2852 : Fin frame978.rank → ℕ := ![129,130,132,136,144,160,64,256]
theorem edge2852_span : frame978.space ≤ frame1.space :=
  frame978.inclusion frame1 witness2852 (by decide)
def edge2852 : CertifiedEdge catalog where
  old := 978
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2852_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2853 : Fin frame979.rank → ℕ := ![129,130,4,8,16,32,64,256]
theorem edge2853_span : frame979.space ≤ frame1.space :=
  frame979.inclusion frame1 witness2853 (by decide)
def edge2853 : CertifiedEdge catalog where
  old := 979
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2853_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2854 : Fin frame980.rank → ℕ := ![129,130,132,136,144,160,64]
theorem edge2854_span : frame980.space ≤ frame976.space :=
  frame980.inclusion frame976 witness2854 (by decide)
def edge2854 : CertifiedEdge catalog where
  old := 980
  next := 976
  rank := 1
  good := by
    constructor
    · exact edge2854_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2855 : Fin frame980.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2855_span : frame980.space ≤ frame978.space :=
  frame980.inclusion frame978 witness2855 (by decide)
def edge2855 : CertifiedEdge catalog where
  old := 980
  next := 978
  rank := 1
  good := by
    constructor
    · exact edge2855_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2856 : Fin frame981.rank → ℕ := ![129,130,4,8,16,32,64]
theorem edge2856_span : frame981.space ≤ frame975.space :=
  frame981.inclusion frame975 witness2856 (by decide)
def edge2856 : CertifiedEdge catalog where
  old := 981
  next := 975
  rank := 1
  good := by
    constructor
    · exact edge2856_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2857 : Fin frame981.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2857_span : frame981.space ≤ frame979.space :=
  frame981.inclusion frame979 witness2857 (by decide)
def edge2857 : CertifiedEdge catalog where
  old := 981
  next := 979
  rank := 1
  good := by
    constructor
    · exact edge2857_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2858 : Fin frame982.rank → ℕ := ![129,194,132,8,144,96]
theorem edge2858_span : frame982.space ≤ frame983.space :=
  frame982.inclusion frame983 witness2858 (by decide)
def edge2858 : CertifiedEdge catalog where
  old := 982
  next := 983
  rank := 2
  good := by
    constructor
    · exact edge2858_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2859 : Fin frame982.rank → ℕ := ![193,194,196,136,80,32]
theorem edge2859_span : frame982.space ≤ frame984.space :=
  frame982.inclusion frame984 witness2859 (by decide)
def edge2859 : CertifiedEdge catalog where
  old := 982
  next := 984
  rank := 2
  good := by
    constructor
    · exact edge2859_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2860 : Fin frame983.rank → ℕ := ![1,258,4,264,272,288,320,384]
theorem edge2860_span : frame983.space ≤ frame1.space :=
  frame983.inclusion frame1 witness2860 (by decide)
def edge2860 : CertifiedEdge catalog where
  old := 983
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2860_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2861 : Fin frame984.rank → ℕ := ![1,66,4,8,16,96,128,256]
theorem edge2861_span : frame984.space ≤ frame1.space :=
  frame984.inclusion frame1 witness2861 (by decide)
def edge2861 : CertifiedEdge catalog where
  old := 984
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2861_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2862 : Fin frame985.rank → ℕ := ![5,130,136,16,32,64]
theorem edge2862_span : frame985.space ≤ frame986.space :=
  frame985.inclusion frame986 witness2862 (by decide)
def edge2862 : CertifiedEdge catalog where
  old := 985
  next := 986
  rank := 2
  good := by
    constructor
    · exact edge2862_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2863 : Fin frame985.rank → ℕ := ![5,130,8,144,32,64]
theorem edge2863_span : frame985.space ≤ frame987.space :=
  frame985.inclusion frame987 witness2863 (by decide)
def edge2863 : CertifiedEdge catalog where
  old := 985
  next := 987
  rank := 2
  good := by
    constructor
    · exact edge2863_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2864 : Fin frame986.rank → ℕ := ![1,130,4,8,144,32,64,256]
theorem edge2864_span : frame986.space ≤ frame1.space :=
  frame986.inclusion frame1 witness2864 (by decide)
def edge2864 : CertifiedEdge catalog where
  old := 986
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2864_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2865 : Fin frame987.rank → ℕ := ![1,258,4,264,16,32,64,128]
theorem edge2865_span : frame987.space ≤ frame1.space :=
  frame987.inclusion frame1 witness2865 (by decide)
def edge2865 : CertifiedEdge catalog where
  old := 987
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2865_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2866 : Fin frame988.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2866_span : frame988.space ≤ frame983.space :=
  frame988.inclusion frame983 witness2866 (by decide)
def edge2866 : CertifiedEdge catalog where
  old := 988
  next := 983
  rank := 2
  good := by
    constructor
    · exact edge2866_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2867 : Fin frame988.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2867_span : frame988.space ≤ frame987.space :=
  frame988.inclusion frame987 witness2867 (by decide)
def edge2867 : CertifiedEdge catalog where
  old := 988
  next := 987
  rank := 2
  good := by
    constructor
    · exact edge2867_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2868 : Fin frame989.rank → ℕ := ![5,66,8,80,32,128]
theorem edge2868_span : frame989.space ≤ frame984.space :=
  frame989.inclusion frame984 witness2868 (by decide)
def edge2868 : CertifiedEdge catalog where
  old := 989
  next := 984
  rank := 2
  good := by
    constructor
    · exact edge2868_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2869 : Fin frame989.rank → ℕ := ![5,66,8,16,96,128]
theorem edge2869_span : frame989.space ≤ frame986.space :=
  frame989.inclusion frame986 witness2869 (by decide)
def edge2869 : CertifiedEdge catalog where
  old := 989
  next := 986
  rank := 2
  good := by
    constructor
    · exact edge2869_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2870 : Fin frame990.rank → ℕ := ![193,194,196,136,80,32]
theorem edge2870_span : frame990.space ≤ frame991.space :=
  frame990.inclusion frame991 witness2870 (by decide)
def edge2870 : CertifiedEdge catalog where
  old := 990
  next := 991
  rank := 2
  good := by
    constructor
    · exact edge2870_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2871 : Fin frame990.rank → ℕ := ![193,130,132,8,144,96]
theorem edge2871_span : frame990.space ≤ frame992.space :=
  frame990.inclusion frame992 witness2871 (by decide)
def edge2871 : CertifiedEdge catalog where
  old := 990
  next := 992
  rank := 2
  good := by
    constructor
    · exact edge2871_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2872 : Fin frame991.rank → ℕ := ![65,2,4,8,16,96,128,256]
theorem edge2872_span : frame991.space ≤ frame1.space :=
  frame991.inclusion frame1 witness2872 (by decide)
def edge2872 : CertifiedEdge catalog where
  old := 991
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2872_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2873 : Fin frame992.rank → ℕ := ![257,2,4,264,272,288,320,384]
theorem edge2873_span : frame992.space ≤ frame1.space :=
  frame992.inclusion frame1 witness2873 (by decide)
def edge2873 : CertifiedEdge catalog where
  old := 992
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2873_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2874 : Fin frame993.rank → ℕ := ![129,6,8,144,32,64]
theorem edge2874_span : frame993.space ≤ frame994.space :=
  frame993.inclusion frame994 witness2874 (by decide)
def edge2874 : CertifiedEdge catalog where
  old := 993
  next := 994
  rank := 2
  good := by
    constructor
    · exact edge2874_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2875 : Fin frame993.rank → ℕ := ![129,6,136,16,32,64]
theorem edge2875_span : frame993.space ≤ frame995.space :=
  frame993.inclusion frame995 witness2875 (by decide)
def edge2875 : CertifiedEdge catalog where
  old := 993
  next := 995
  rank := 2
  good := by
    constructor
    · exact edge2875_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2876 : Fin frame994.rank → ℕ := ![257,2,4,264,16,32,64,128]
theorem edge2876_span : frame994.space ≤ frame1.space :=
  frame994.inclusion frame1 witness2876 (by decide)
def edge2876 : CertifiedEdge catalog where
  old := 994
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2876_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2877 : Fin frame995.rank → ℕ := ![129,2,4,8,144,32,64,256]
theorem edge2877_span : frame995.space ≤ frame1.space :=
  frame995.inclusion frame1 witness2877 (by decide)
def edge2877 : CertifiedEdge catalog where
  old := 995
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2877_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2878 : Fin frame996.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2878_span : frame996.space ≤ frame992.space :=
  frame996.inclusion frame992 witness2878 (by decide)
def edge2878 : CertifiedEdge catalog where
  old := 996
  next := 992
  rank := 2
  good := by
    constructor
    · exact edge2878_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2879 : Fin frame996.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2879_span : frame996.space ≤ frame994.space :=
  frame996.inclusion frame994 witness2879 (by decide)
def edge2879 : CertifiedEdge catalog where
  old := 996
  next := 994
  rank := 2
  good := by
    constructor
    · exact edge2879_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
