module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness896 : Fin frame202.rank → ℕ := ![2,8]
theorem edge896_span : frame202.space ≤ frame607.space :=
  frame202.inclusion frame607 witness896 (by decide)
def edge896 : CertifiedEdge catalog where
  old := 202
  next := 607
  rank := 2
  good := by
    constructor
    · exact edge896_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness897 : Fin frame202.rank → ℕ := ![6,112]
theorem edge897_span : frame202.space ≤ frame754.space :=
  frame202.inclusion frame754 witness897 (by decide)
def edge897 : CertifiedEdge catalog where
  old := 202
  next := 754
  rank := 5
  good := by
    constructor
    · exact edge897_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness898 : Fin frame203.rank → ℕ := ![9,2,12]
theorem edge898_span : frame203.space ≤ frame211.space :=
  frame203.inclusion frame211 witness898 (by decide)
def edge898 : CertifiedEdge catalog where
  old := 203
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge898_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness899 : Fin frame203.rank → ℕ := ![17,34,20]
theorem edge899_span : frame203.space ≤ frame640.space :=
  frame203.inclusion frame640 witness899 (by decide)
def edge899 : CertifiedEdge catalog where
  old := 203
  next := 640
  rank := 3
  good := by
    constructor
    · exact edge899_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness900 : Fin frame203.rank → ℕ := ![17,34,20]
theorem edge900_span : frame203.space ≤ frame662.space :=
  frame203.inclusion frame662 witness900 (by decide)
def edge900 : CertifiedEdge catalog where
  old := 203
  next := 662
  rank := 3
  good := by
    constructor
    · exact edge900_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness901 : Fin frame204.rank → ℕ := ![1,10,12]
theorem edge901_span : frame204.space ≤ frame211.space :=
  frame204.inclusion frame211 witness901 (by decide)
def edge901 : CertifiedEdge catalog where
  old := 204
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge901_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness902 : Fin frame204.rank → ℕ := ![33,18,20]
theorem edge902_span : frame204.space ≤ frame641.space :=
  frame204.inclusion frame641 witness902 (by decide)
def edge902 : CertifiedEdge catalog where
  old := 204
  next := 641
  rank := 3
  good := by
    constructor
    · exact edge902_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness903 : Fin frame204.rank → ℕ := ![33,18,20]
theorem edge903_span : frame204.space ≤ frame663.space :=
  frame204.inclusion frame663 witness903 (by decide)
def edge903 : CertifiedEdge catalog where
  old := 204
  next := 663
  rank := 3
  good := by
    constructor
    · exact edge903_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness904 : Fin frame205.rank → ℕ := ![1,2,4]
theorem edge904_span : frame205.space ≤ frame211.space :=
  frame205.inclusion frame211 witness904 (by decide)
def edge904 : CertifiedEdge catalog where
  old := 205
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge904_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness905 : Fin frame205.rank → ℕ := ![1,2,4]
theorem edge905_span : frame205.space ≤ frame646.space :=
  frame205.inclusion frame646 witness905 (by decide)
def edge905 : CertifiedEdge catalog where
  old := 205
  next := 646
  rank := 3
  good := by
    constructor
    · exact edge905_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness906 : Fin frame205.rank → ℕ := ![33,34,36]
theorem edge906_span : frame205.space ≤ frame656.space :=
  frame205.inclusion frame656 witness906 (by decide)
def edge906 : CertifiedEdge catalog where
  old := 205
  next := 656
  rank := 3
  good := by
    constructor
    · exact edge906_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness907 : Fin frame206.rank → ℕ := ![9,10,4]
theorem edge907_span : frame206.space ≤ frame211.space :=
  frame206.inclusion frame211 witness907 (by decide)
def edge907 : CertifiedEdge catalog where
  old := 206
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge907_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness908 : Fin frame206.rank → ℕ := ![17,18,36]
theorem edge908_span : frame206.space ≤ frame647.space :=
  frame206.inclusion frame647 witness908 (by decide)
def edge908 : CertifiedEdge catalog where
  old := 206
  next := 647
  rank := 3
  good := by
    constructor
    · exact edge908_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness909 : Fin frame206.rank → ℕ := ![17,18,36]
theorem edge909_span : frame206.space ≤ frame657.space :=
  frame206.inclusion frame657 witness909 (by decide)
def edge909 : CertifiedEdge catalog where
  old := 206
  next := 657
  rank := 3
  good := by
    constructor
    · exact edge909_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness910 : Fin frame207.rank → ℕ := ![9,2,4]
theorem edge910_span : frame207.space ≤ frame211.space :=
  frame207.inclusion frame211 witness910 (by decide)
def edge910 : CertifiedEdge catalog where
  old := 207
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge910_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness911 : Fin frame207.rank → ℕ := ![17,34,36]
theorem edge911_span : frame207.space ≤ frame714.space :=
  frame207.inclusion frame714 witness911 (by decide)
def edge911 : CertifiedEdge catalog where
  old := 207
  next := 714
  rank := 3
  good := by
    constructor
    · exact edge911_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness912 : Fin frame207.rank → ℕ := ![17,34,36]
theorem edge912_span : frame207.space ≤ frame724.space :=
  frame207.inclusion frame724 witness912 (by decide)
def edge912 : CertifiedEdge catalog where
  old := 207
  next := 724
  rank := 3
  good := by
    constructor
    · exact edge912_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness913 : Fin frame208.rank → ℕ := ![1,10,4]
theorem edge913_span : frame208.space ≤ frame211.space :=
  frame208.inclusion frame211 witness913 (by decide)
def edge913 : CertifiedEdge catalog where
  old := 208
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge913_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness914 : Fin frame208.rank → ℕ := ![33,18,36]
theorem edge914_span : frame208.space ≤ frame715.space :=
  frame208.inclusion frame715 witness914 (by decide)
def edge914 : CertifiedEdge catalog where
  old := 208
  next := 715
  rank := 3
  good := by
    constructor
    · exact edge914_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness915 : Fin frame208.rank → ℕ := ![33,18,36]
theorem edge915_span : frame208.space ≤ frame725.space :=
  frame208.inclusion frame725 witness915 (by decide)
def edge915 : CertifiedEdge catalog where
  old := 208
  next := 725
  rank := 3
  good := by
    constructor
    · exact edge915_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness916 : Fin frame209.rank → ℕ := ![1,2,12]
theorem edge916_span : frame209.space ≤ frame211.space :=
  frame209.inclusion frame211 witness916 (by decide)
def edge916 : CertifiedEdge catalog where
  old := 209
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge916_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness917 : Fin frame209.rank → ℕ := ![33,34,20]
theorem edge917_span : frame209.space ≤ frame708.space :=
  frame209.inclusion frame708 witness917 (by decide)
def edge917 : CertifiedEdge catalog where
  old := 209
  next := 708
  rank := 3
  good := by
    constructor
    · exact edge917_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness918 : Fin frame209.rank → ℕ := ![33,34,20]
theorem edge918_span : frame209.space ≤ frame730.space :=
  frame209.inclusion frame730 witness918 (by decide)
def edge918 : CertifiedEdge catalog where
  old := 209
  next := 730
  rank := 3
  good := by
    constructor
    · exact edge918_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness919 : Fin frame210.rank → ℕ := ![9,10,12]
theorem edge919_span : frame210.space ≤ frame211.space :=
  frame210.inclusion frame211 witness919 (by decide)
def edge919 : CertifiedEdge catalog where
  old := 210
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge919_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness920 : Fin frame210.rank → ℕ := ![49,50,52]
theorem edge920_span : frame210.space ≤ frame709.space :=
  frame210.inclusion frame709 witness920 (by decide)
def edge920 : CertifiedEdge catalog where
  old := 210
  next := 709
  rank := 3
  good := by
    constructor
    · exact edge920_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness921 : Fin frame210.rank → ℕ := ![17,18,20]
theorem edge921_span : frame210.space ≤ frame731.space :=
  frame210.inclusion frame731 witness921 (by decide)
def edge921 : CertifiedEdge catalog where
  old := 210
  next := 731
  rank := 3
  good := by
    constructor
    · exact edge921_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness922 : Fin frame211.rank → ℕ := ![161,162,420,240]
theorem edge922_span : frame211.space ≤ frame1.space :=
  frame211.inclusion frame1 witness922 (by decide)
def edge922 : CertifiedEdge catalog where
  old := 211
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge922_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness923 : Fin frame211.rank → ℕ := ![33,34,164,112]
theorem edge923_span : frame211.space ≤ frame415.space :=
  frame211.inclusion frame415 witness923 (by decide)
def edge923 : CertifiedEdge catalog where
  old := 211
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge923_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness924 : Fin frame211.rank → ℕ := ![97,98,228,112]
theorem edge924_span : frame211.space ≤ frame418.space :=
  frame211.inclusion frame418 witness924 (by decide)
def edge924 : CertifiedEdge catalog where
  old := 211
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge924_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness925 : Fin frame211.rank → ℕ := ![161,162,164,240]
theorem edge925_span : frame211.space ≤ frame420.space :=
  frame211.inclusion frame420 witness925 (by decide)
def edge925 : CertifiedEdge catalog where
  old := 211
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge925_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness926 : Fin frame211.rank → ℕ := ![161,162,164,240]
theorem edge926_span : frame211.space ≤ frame421.space :=
  frame211.inclusion frame421 witness926 (by decide)
def edge926 : CertifiedEdge catalog where
  old := 211
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge926_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness927 : Fin frame212.rank → ℕ := ![2]
theorem edge927_span : frame212.space ≤ frame220.space :=
  frame212.inclusion frame220 witness927 (by decide)
def edge927 : CertifiedEdge catalog where
  old := 212
  next := 220
  rank := 1
  good := by
    constructor
    · exact edge927_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
