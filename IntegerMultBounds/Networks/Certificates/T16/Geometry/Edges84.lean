module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2688 : Fin frame869.rank → ℕ := ![1,2,4,72,16,96,128]
theorem edge2688_span : frame869.space ≤ frame863.space :=
  frame869.inclusion frame863 witness2688 (by decide)
def edge2688 : CertifiedEdge catalog where
  old := 869
  next := 863
  rank := 1
  good := by
    constructor
    · exact edge2688_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2689 : Fin frame869.rank → ℕ := ![1,2,68,8,16,96,128]
theorem edge2689_span : frame869.space ≤ frame867.space :=
  frame869.inclusion frame867 witness2689 (by decide)
def edge2689 : CertifiedEdge catalog where
  old := 869
  next := 867
  rank := 1
  good := by
    constructor
    · exact edge2689_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2690 : Fin frame870.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2690_span : frame870.space ≤ frame871.space :=
  frame870.inclusion frame871 witness2690 (by decide)
def edge2690 : CertifiedEdge catalog where
  old := 870
  next := 871
  rank := 1
  good := by
    constructor
    · exact edge2690_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2691 : Fin frame870.rank → ℕ := ![1,130,4,8,16,160,64]
theorem edge2691_span : frame870.space ≤ frame872.space :=
  frame870.inclusion frame872 witness2691 (by decide)
def edge2691 : CertifiedEdge catalog where
  old := 870
  next := 872
  rank := 1
  good := by
    constructor
    · exact edge2691_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2692 : Fin frame871.rank → ℕ := ![1,130,4,8,16,160,64,256]
theorem edge2692_span : frame871.space ≤ frame1.space :=
  frame871.inclusion frame1 witness2692 (by decide)
def edge2692 : CertifiedEdge catalog where
  old := 871
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2692_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2693 : Fin frame872.rank → ℕ := ![1,258,260,8,272,288,320,384]
theorem edge2693_span : frame872.space ≤ frame1.space :=
  frame872.inclusion frame1 witness2693 (by decide)
def edge2693 : CertifiedEdge catalog where
  old := 872
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2693_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2694 : Fin frame873.rank → ℕ := ![1,130,132,8,16,32,64]
theorem edge2694_span : frame873.space ≤ frame874.space :=
  frame873.inclusion frame874 witness2694 (by decide)
def edge2694 : CertifiedEdge catalog where
  old := 873
  next := 874
  rank := 1
  good := by
    constructor
    · exact edge2694_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2695 : Fin frame873.rank → ℕ := ![1,66,4,8,80,32,128]
theorem edge2695_span : frame873.space ≤ frame875.space :=
  frame873.inclusion frame875 witness2695 (by decide)
def edge2695 : CertifiedEdge catalog where
  old := 873
  next := 875
  rank := 1
  good := by
    constructor
    · exact edge2695_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2696 : Fin frame874.rank → ℕ := ![1,66,4,8,80,32,128,256]
theorem edge2696_span : frame874.space ≤ frame1.space :=
  frame874.inclusion frame1 witness2696 (by decide)
def edge2696 : CertifiedEdge catalog where
  old := 874
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2696_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2697 : Fin frame875.rank → ℕ := ![1,258,260,8,16,32,64,128]
theorem edge2697_span : frame875.space ≤ frame1.space :=
  frame875.inclusion frame1 witness2697 (by decide)
def edge2697 : CertifiedEdge catalog where
  old := 875
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2697_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2698 : Fin frame876.rank → ℕ := ![1,130,132,8,16,32,64]
theorem edge2698_span : frame876.space ≤ frame871.space :=
  frame876.inclusion frame871 witness2698 (by decide)
def edge2698 : CertifiedEdge catalog where
  old := 876
  next := 871
  rank := 1
  good := by
    constructor
    · exact edge2698_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2699 : Fin frame876.rank → ℕ := ![1,130,4,8,16,160,64]
theorem edge2699_span : frame876.space ≤ frame875.space :=
  frame876.inclusion frame875 witness2699 (by decide)
def edge2699 : CertifiedEdge catalog where
  old := 876
  next := 875
  rank := 1
  good := by
    constructor
    · exact edge2699_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2700 : Fin frame877.rank → ℕ := ![1,66,4,8,80,32,128]
theorem edge2700_span : frame877.space ≤ frame872.space :=
  frame877.inclusion frame872 witness2700 (by decide)
def edge2700 : CertifiedEdge catalog where
  old := 877
  next := 872
  rank := 1
  good := by
    constructor
    · exact edge2700_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2701 : Fin frame877.rank → ℕ := ![1,2,132,8,16,160,192]
theorem edge2701_span : frame877.space ≤ frame874.space :=
  frame877.inclusion frame874 witness2701 (by decide)
def edge2701 : CertifiedEdge catalog where
  old := 877
  next := 874
  rank := 1
  good := by
    constructor
    · exact edge2701_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2702 : Fin frame878.rank → ℕ := ![129,2,132,8,16,32,64]
theorem edge2702_span : frame878.space ≤ frame879.space :=
  frame878.inclusion frame879 witness2702 (by decide)
def edge2702 : CertifiedEdge catalog where
  old := 878
  next := 879
  rank := 1
  good := by
    constructor
    · exact edge2702_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2703 : Fin frame878.rank → ℕ := ![65,2,4,8,80,32,128]
theorem edge2703_span : frame878.space ≤ frame880.space :=
  frame878.inclusion frame880 witness2703 (by decide)
def edge2703 : CertifiedEdge catalog where
  old := 878
  next := 880
  rank := 1
  good := by
    constructor
    · exact edge2703_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2704 : Fin frame879.rank → ℕ := ![65,2,4,8,80,32,128,256]
theorem edge2704_span : frame879.space ≤ frame1.space :=
  frame879.inclusion frame1 witness2704 (by decide)
def edge2704 : CertifiedEdge catalog where
  old := 879
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2704_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2705 : Fin frame880.rank → ℕ := ![257,2,260,8,16,32,64,128]
theorem edge2705_span : frame880.space ≤ frame1.space :=
  frame880.inclusion frame1 witness2705 (by decide)
def edge2705 : CertifiedEdge catalog where
  old := 880
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2705_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2706 : Fin frame881.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2706_span : frame881.space ≤ frame882.space :=
  frame881.inclusion frame882 witness2706 (by decide)
def edge2706 : CertifiedEdge catalog where
  old := 881
  next := 882
  rank := 1
  good := by
    constructor
    · exact edge2706_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2707 : Fin frame881.rank → ℕ := ![129,2,4,8,16,160,64]
theorem edge2707_span : frame881.space ≤ frame883.space :=
  frame881.inclusion frame883 witness2707 (by decide)
def edge2707 : CertifiedEdge catalog where
  old := 881
  next := 883
  rank := 1
  good := by
    constructor
    · exact edge2707_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2708 : Fin frame882.rank → ℕ := ![129,2,4,8,16,160,64,256]
theorem edge2708_span : frame882.space ≤ frame1.space :=
  frame882.inclusion frame1 witness2708 (by decide)
def edge2708 : CertifiedEdge catalog where
  old := 882
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2708_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2709 : Fin frame883.rank → ℕ := ![257,2,260,8,272,288,320,384]
theorem edge2709_span : frame883.space ≤ frame1.space :=
  frame883.inclusion frame1 witness2709 (by decide)
def edge2709 : CertifiedEdge catalog where
  old := 883
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2709_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2710 : Fin frame884.rank → ℕ := ![129,2,4,8,16,160,64]
theorem edge2710_span : frame884.space ≤ frame880.space :=
  frame884.inclusion frame880 witness2710 (by decide)
def edge2710 : CertifiedEdge catalog where
  old := 884
  next := 880
  rank := 1
  good := by
    constructor
    · exact edge2710_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2711 : Fin frame884.rank → ℕ := ![129,2,132,8,16,32,64]
theorem edge2711_span : frame884.space ≤ frame882.space :=
  frame884.inclusion frame882 witness2711 (by decide)
def edge2711 : CertifiedEdge catalog where
  old := 884
  next := 882
  rank := 1
  good := by
    constructor
    · exact edge2711_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2712 : Fin frame885.rank → ℕ := ![1,2,132,8,16,160,192]
theorem edge2712_span : frame885.space ≤ frame879.space :=
  frame885.inclusion frame879 witness2712 (by decide)
def edge2712 : CertifiedEdge catalog where
  old := 885
  next := 879
  rank := 1
  good := by
    constructor
    · exact edge2712_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2713 : Fin frame885.rank → ℕ := ![65,2,4,8,80,32,128]
theorem edge2713_span : frame885.space ≤ frame883.space :=
  frame885.inclusion frame883 witness2713 (by decide)
def edge2713 : CertifiedEdge catalog where
  old := 885
  next := 883
  rank := 1
  good := by
    constructor
    · exact edge2713_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2714 : Fin frame886.rank → ℕ := ![1,2,132,8,16,32,192]
theorem edge2714_span : frame886.space ≤ frame887.space :=
  frame886.inclusion frame887 witness2714 (by decide)
def edge2714 : CertifiedEdge catalog where
  old := 886
  next := 887
  rank := 1
  good := by
    constructor
    · exact edge2714_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2715 : Fin frame886.rank → ℕ := ![1,2,132,8,144,32,192]
theorem edge2715_span : frame886.space ≤ frame888.space :=
  frame886.inclusion frame888 witness2715 (by decide)
def edge2715 : CertifiedEdge catalog where
  old := 886
  next := 888
  rank := 1
  good := by
    constructor
    · exact edge2715_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2716 : Fin frame887.rank → ℕ := ![1,2,4,8,272,32,64,384]
theorem edge2716_span : frame887.space ≤ frame1.space :=
  frame887.inclusion frame1 witness2716 (by decide)
def edge2716 : CertifiedEdge catalog where
  old := 887
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2716_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2717 : Fin frame888.rank → ℕ := ![1,2,132,8,16,32,192,256]
theorem edge2717_span : frame888.space ≤ frame1.space :=
  frame888.inclusion frame1 witness2717 (by decide)
def edge2717 : CertifiedEdge catalog where
  old := 888
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2717_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2718 : Fin frame889.rank → ℕ := ![1,2,36,8,48,64,128]
theorem edge2718_span : frame889.space ≤ frame890.space :=
  frame889.inclusion frame890 witness2718 (by decide)
def edge2718 : CertifiedEdge catalog where
  old := 889
  next := 890
  rank := 1
  good := by
    constructor
    · exact edge2718_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2719 : Fin frame889.rank → ℕ := ![1,2,132,8,144,160,64]
theorem edge2719_span : frame889.space ≤ frame891.space :=
  frame889.inclusion frame891 witness2719 (by decide)
def edge2719 : CertifiedEdge catalog where
  old := 889
  next := 891
  rank := 1
  good := by
    constructor
    · exact edge2719_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
