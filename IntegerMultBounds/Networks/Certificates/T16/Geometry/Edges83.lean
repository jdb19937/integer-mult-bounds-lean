module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2656 : Fin frame847.rank → ℕ := ![1,258,260,264,272,32,320,384]
theorem edge2656_span : frame847.space ≤ frame1.space :=
  frame847.inclusion frame1 witness2656 (by decide)
def edge2656 : CertifiedEdge catalog where
  old := 847
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2656_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2657 : Fin frame848.rank → ℕ := ![1,130,4,136,16,32,64,256]
theorem edge2657_span : frame848.space ≤ frame1.space :=
  frame848.inclusion frame1 witness2657 (by decide)
def edge2657 : CertifiedEdge catalog where
  old := 848
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2657_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2658 : Fin frame849.rank → ℕ := ![1,130,4,8,144,32,64]
theorem edge2658_span : frame849.space ≤ frame850.space :=
  frame849.inclusion frame850 witness2658 (by decide)
def edge2658 : CertifiedEdge catalog where
  old := 849
  next := 850
  rank := 1
  good := by
    constructor
    · exact edge2658_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2659 : Fin frame849.rank → ℕ := ![1,66,68,8,16,32,128]
theorem edge2659_span : frame849.space ≤ frame851.space :=
  frame849.inclusion frame851 witness2659 (by decide)
def edge2659 : CertifiedEdge catalog where
  old := 849
  next := 851
  rank := 1
  good := by
    constructor
    · exact edge2659_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2660 : Fin frame850.rank → ℕ := ![1,66,68,8,16,32,128,256]
theorem edge2660_span : frame850.space ≤ frame1.space :=
  frame850.inclusion frame1 witness2660 (by decide)
def edge2660 : CertifiedEdge catalog where
  old := 850
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2660_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2661 : Fin frame851.rank → ℕ := ![1,258,4,8,272,32,64,128]
theorem edge2661_span : frame851.space ≤ frame1.space :=
  frame851.inclusion frame1 witness2661 (by decide)
def edge2661 : CertifiedEdge catalog where
  old := 851
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2661_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2662 : Fin frame852.rank → ℕ := ![1,66,68,8,16,32,128]
theorem edge2662_span : frame852.space ≤ frame848.space :=
  frame852.inclusion frame848 witness2662 (by decide)
def edge2662 : CertifiedEdge catalog where
  old := 852
  next := 848
  rank := 1
  good := by
    constructor
    · exact edge2662_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2663 : Fin frame852.rank → ℕ := ![1,66,4,72,16,32,128]
theorem edge2663_span : frame852.space ≤ frame850.space :=
  frame852.inclusion frame850 witness2663 (by decide)
def edge2663 : CertifiedEdge catalog where
  old := 852
  next := 850
  rank := 1
  good := by
    constructor
    · exact edge2663_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2664 : Fin frame853.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2664_span : frame853.space ≤ frame847.space :=
  frame853.inclusion frame847 witness2664 (by decide)
def edge2664 : CertifiedEdge catalog where
  old := 853
  next := 847
  rank := 1
  good := by
    constructor
    · exact edge2664_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2665 : Fin frame853.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2665_span : frame853.space ≤ frame851.space :=
  frame853.inclusion frame851 witness2665 (by decide)
def edge2665 : CertifiedEdge catalog where
  old := 853
  next := 851
  rank := 1
  good := by
    constructor
    · exact edge2665_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2666 : Fin frame854.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2666_span : frame854.space ≤ frame855.space :=
  frame854.inclusion frame855 witness2666 (by decide)
def edge2666 : CertifiedEdge catalog where
  old := 854
  next := 855
  rank := 1
  good := by
    constructor
    · exact edge2666_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2667 : Fin frame854.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2667_span : frame854.space ≤ frame856.space :=
  frame854.inclusion frame856 witness2667 (by decide)
def edge2667 : CertifiedEdge catalog where
  old := 854
  next := 856
  rank := 1
  good := by
    constructor
    · exact edge2667_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2668 : Fin frame855.rank → ℕ := ![257,258,260,264,272,288,64,128]
theorem edge2668_span : frame855.space ≤ frame1.space :=
  frame855.inclusion frame1 witness2668 (by decide)
def edge2668 : CertifiedEdge catalog where
  old := 855
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2668_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2669 : Fin frame856.rank → ℕ := ![257,258,4,8,16,32,64,128]
theorem edge2669_span : frame856.space ≤ frame1.space :=
  frame856.inclusion frame1 witness2669 (by decide)
def edge2669 : CertifiedEdge catalog where
  old := 856
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2669_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2670 : Fin frame857.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2670_span : frame857.space ≤ frame858.space :=
  frame857.inclusion frame858 witness2670 (by decide)
def edge2670 : CertifiedEdge catalog where
  old := 857
  next := 858
  rank := 1
  good := by
    constructor
    · exact edge2670_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2671 : Fin frame857.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2671_span : frame857.space ≤ frame859.space :=
  frame857.inclusion frame859 witness2671 (by decide)
def edge2671 : CertifiedEdge catalog where
  old := 857
  next := 859
  rank := 1
  good := by
    constructor
    · exact edge2671_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2672 : Fin frame858.rank → ℕ := ![257,258,260,264,16,32,320,384]
theorem edge2672_span : frame858.space ≤ frame1.space :=
  frame858.inclusion frame1 witness2672 (by decide)
def edge2672 : CertifiedEdge catalog where
  old := 858
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2672_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2673 : Fin frame859.rank → ℕ := ![257,258,4,8,272,288,320,384]
theorem edge2673_span : frame859.space ≤ frame1.space :=
  frame859.inclusion frame1 witness2673 (by decide)
def edge2673 : CertifiedEdge catalog where
  old := 859
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2673_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2674 : Fin frame860.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2674_span : frame860.space ≤ frame855.space :=
  frame860.inclusion frame855 witness2674 (by decide)
def edge2674 : CertifiedEdge catalog where
  old := 860
  next := 855
  rank := 1
  good := by
    constructor
    · exact edge2674_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2675 : Fin frame860.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2675_span : frame860.space ≤ frame859.space :=
  frame860.inclusion frame859 witness2675 (by decide)
def edge2675 : CertifiedEdge catalog where
  old := 860
  next := 859
  rank := 1
  good := by
    constructor
    · exact edge2675_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2676 : Fin frame861.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2676_span : frame861.space ≤ frame856.space :=
  frame861.inclusion frame856 witness2676 (by decide)
def edge2676 : CertifiedEdge catalog where
  old := 861
  next := 856
  rank := 1
  good := by
    constructor
    · exact edge2676_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2677 : Fin frame861.rank → ℕ := ![1,2,132,136,16,32,192]
theorem edge2677_span : frame861.space ≤ frame858.space :=
  frame861.inclusion frame858 witness2677 (by decide)
def edge2677 : CertifiedEdge catalog where
  old := 861
  next := 858
  rank := 1
  good := by
    constructor
    · exact edge2677_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2678 : Fin frame862.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2678_span : frame862.space ≤ frame863.space :=
  frame862.inclusion frame863 witness2678 (by decide)
def edge2678 : CertifiedEdge catalog where
  old := 862
  next := 863
  rank := 1
  good := by
    constructor
    · exact edge2678_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2679 : Fin frame862.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2679_span : frame862.space ≤ frame864.space :=
  frame862.inclusion frame864 witness2679 (by decide)
def edge2679 : CertifiedEdge catalog where
  old := 862
  next := 864
  rank := 1
  good := by
    constructor
    · exact edge2679_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2680 : Fin frame863.rank → ℕ := ![1,2,132,8,16,160,64,256]
theorem edge2680_span : frame863.space ≤ frame1.space :=
  frame863.inclusion frame1 witness2680 (by decide)
def edge2680 : CertifiedEdge catalog where
  old := 863
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2680_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2681 : Fin frame864.rank → ℕ := ![1,2,4,136,144,32,64,256]
theorem edge2681_span : frame864.space ≤ frame1.space :=
  frame864.inclusion frame1 witness2681 (by decide)
def edge2681 : CertifiedEdge catalog where
  old := 864
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2681_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2682 : Fin frame865.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2682_span : frame865.space ≤ frame866.space :=
  frame865.inclusion frame866 witness2682 (by decide)
def edge2682 : CertifiedEdge catalog where
  old := 865
  next := 866
  rank := 1
  good := by
    constructor
    · exact edge2682_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2683 : Fin frame865.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2683_span : frame865.space ≤ frame867.space :=
  frame865.inclusion frame867 witness2683 (by decide)
def edge2683 : CertifiedEdge catalog where
  old := 865
  next := 867
  rank := 1
  good := by
    constructor
    · exact edge2683_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2684 : Fin frame866.rank → ℕ := ![1,2,68,8,80,32,128,256]
theorem edge2684_span : frame866.space ≤ frame1.space :=
  frame866.inclusion frame1 witness2684 (by decide)
def edge2684 : CertifiedEdge catalog where
  old := 866
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2684_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2685 : Fin frame867.rank → ℕ := ![1,2,4,72,16,96,128,256]
theorem edge2685_span : frame867.space ≤ frame1.space :=
  frame867.inclusion frame1 witness2685 (by decide)
def edge2685 : CertifiedEdge catalog where
  old := 867
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2685_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2686 : Fin frame868.rank → ℕ := ![1,2,68,8,80,32,128]
theorem edge2686_span : frame868.space ≤ frame864.space :=
  frame868.inclusion frame864 witness2686 (by decide)
def edge2686 : CertifiedEdge catalog where
  old := 868
  next := 864
  rank := 1
  good := by
    constructor
    · exact edge2686_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2687 : Fin frame868.rank → ℕ := ![1,2,4,72,80,32,128]
theorem edge2687_span : frame868.space ≤ frame866.space :=
  frame868.inclusion frame866 witness2687 (by decide)
def edge2687 : CertifiedEdge catalog where
  old := 868
  next := 866
  rank := 1
  good := by
    constructor
    · exact edge2687_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
