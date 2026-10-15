module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness864 : Fin frame190.rank → ℕ := ![3]
theorem edge864_span : frame190.space ≤ frame198.space :=
  frame190.inclusion frame198 witness864 (by decide)
def edge864 : CertifiedEdge catalog where
  old := 190
  next := 198
  rank := 1
  good := by
    constructor
    · exact edge864_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness865 : Fin frame190.rank → ℕ := ![1]
theorem edge865_span : frame190.space ≤ frame201.space :=
  frame190.inclusion frame201 witness865 (by decide)
def edge865 : CertifiedEdge catalog where
  old := 190
  next := 201
  rank := 1
  good := by
    constructor
    · exact edge865_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness866 : Fin frame191.rank → ℕ := ![2,4]
theorem edge866_span : frame191.space ≤ frame553.space :=
  frame191.inclusion frame553 witness866 (by decide)
def edge866 : CertifiedEdge catalog where
  old := 191
  next := 553
  rank := 1
  good := by
    constructor
    · exact edge866_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness867 : Fin frame191.rank → ℕ := ![2,4]
theorem edge867_span : frame191.space ≤ frame555.space :=
  frame191.inclusion frame555 witness867 (by decide)
def edge867 : CertifiedEdge catalog where
  old := 191
  next := 555
  rank := 1
  good := by
    constructor
    · exact edge867_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness868 : Fin frame191.rank → ℕ := ![2,8]
theorem edge868_span : frame191.space ≤ frame606.space :=
  frame191.inclusion frame606 witness868 (by decide)
def edge868 : CertifiedEdge catalog where
  old := 191
  next := 606
  rank := 2
  good := by
    constructor
    · exact edge868_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness869 : Fin frame191.rank → ℕ := ![18,56]
theorem edge869_span : frame191.space ≤ frame610.space :=
  frame191.inclusion frame610 witness869 (by decide)
def edge869 : CertifiedEdge catalog where
  old := 191
  next := 610
  rank := 4
  good := by
    constructor
    · exact edge869_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness870 : Fin frame192.rank → ℕ := ![2,4]
theorem edge870_span : frame192.space ≤ frame204.space :=
  frame192.inclusion frame204 witness870 (by decide)
def edge870 : CertifiedEdge catalog where
  old := 192
  next := 204
  rank := 1
  good := by
    constructor
    · exact edge870_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness871 : Fin frame192.rank → ℕ := ![2,4]
theorem edge871_span : frame192.space ≤ frame210.space :=
  frame192.inclusion frame210 witness871 (by decide)
def edge871 : CertifiedEdge catalog where
  old := 192
  next := 210
  rank := 1
  good := by
    constructor
    · exact edge871_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness872 : Fin frame193.rank → ℕ := ![2,4]
theorem edge872_span : frame193.space ≤ frame206.space :=
  frame193.inclusion frame206 witness872 (by decide)
def edge872 : CertifiedEdge catalog where
  old := 193
  next := 206
  rank := 1
  good := by
    constructor
    · exact edge872_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness873 : Fin frame193.rank → ℕ := ![2,4]
theorem edge873_span : frame193.space ≤ frame208.space :=
  frame193.inclusion frame208 witness873 (by decide)
def edge873 : CertifiedEdge catalog where
  old := 193
  next := 208
  rank := 1
  good := by
    constructor
    · exact edge873_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness874 : Fin frame194.rank → ℕ := ![1,4]
theorem edge874_span : frame194.space ≤ frame553.space :=
  frame194.inclusion frame553 witness874 (by decide)
def edge874 : CertifiedEdge catalog where
  old := 194
  next := 553
  rank := 1
  good := by
    constructor
    · exact edge874_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness875 : Fin frame194.rank → ℕ := ![1,4]
theorem edge875_span : frame194.space ≤ frame554.space :=
  frame194.inclusion frame554 witness875 (by decide)
def edge875 : CertifiedEdge catalog where
  old := 194
  next := 554
  rank := 1
  good := by
    constructor
    · exact edge875_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness876 : Fin frame194.rank → ℕ := ![17,56]
theorem edge876_span : frame194.space ≤ frame608.space :=
  frame194.inclusion frame608 witness876 (by decide)
def edge876 : CertifiedEdge catalog where
  old := 194
  next := 608
  rank := 4
  good := by
    constructor
    · exact edge876_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness877 : Fin frame194.rank → ℕ := ![33,48]
theorem edge877_span : frame194.space ≤ frame756.space :=
  frame194.inclusion frame756 witness877 (by decide)
def edge877 : CertifiedEdge catalog where
  old := 194
  next := 756
  rank := 5
  good := by
    constructor
    · exact edge877_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness878 : Fin frame195.rank → ℕ := ![1,4]
theorem edge878_span : frame195.space ≤ frame204.space :=
  frame195.inclusion frame204 witness878 (by decide)
def edge878 : CertifiedEdge catalog where
  old := 195
  next := 204
  rank := 1
  good := by
    constructor
    · exact edge878_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness879 : Fin frame195.rank → ℕ := ![1,4]
theorem edge879_span : frame195.space ≤ frame209.space :=
  frame195.inclusion frame209 witness879 (by decide)
def edge879 : CertifiedEdge catalog where
  old := 195
  next := 209
  rank := 1
  good := by
    constructor
    · exact edge879_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness880 : Fin frame196.rank → ℕ := ![1,4]
theorem edge880_span : frame196.space ≤ frame205.space :=
  frame196.inclusion frame205 witness880 (by decide)
def edge880 : CertifiedEdge catalog where
  old := 196
  next := 205
  rank := 1
  good := by
    constructor
    · exact edge880_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness881 : Fin frame196.rank → ℕ := ![1,4]
theorem edge881_span : frame196.space ≤ frame208.space :=
  frame196.inclusion frame208 witness881 (by decide)
def edge881 : CertifiedEdge catalog where
  old := 196
  next := 208
  rank := 1
  good := by
    constructor
    · exact edge881_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness882 : Fin frame197.rank → ℕ := ![1,4]
theorem edge882_span : frame197.space ≤ frame206.space :=
  frame197.inclusion frame206 witness882 (by decide)
def edge882 : CertifiedEdge catalog where
  old := 197
  next := 206
  rank := 1
  good := by
    constructor
    · exact edge882_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness883 : Fin frame197.rank → ℕ := ![1,4]
theorem edge883_span : frame197.space ≤ frame207.space :=
  frame197.inclusion frame207 witness883 (by decide)
def edge883 : CertifiedEdge catalog where
  old := 197
  next := 207
  rank := 1
  good := by
    constructor
    · exact edge883_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness884 : Fin frame198.rank → ℕ := ![1,4]
theorem edge884_span : frame198.space ≤ frame203.space :=
  frame198.inclusion frame203 witness884 (by decide)
def edge884 : CertifiedEdge catalog where
  old := 198
  next := 203
  rank := 1
  good := by
    constructor
    · exact edge884_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness885 : Fin frame198.rank → ℕ := ![1,4]
theorem edge885_span : frame198.space ≤ frame210.space :=
  frame198.inclusion frame210 witness885 (by decide)
def edge885 : CertifiedEdge catalog where
  old := 198
  next := 210
  rank := 1
  good := by
    constructor
    · exact edge885_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness886 : Fin frame199.rank → ℕ := ![2,4]
theorem edge886_span : frame199.space ≤ frame205.space :=
  frame199.inclusion frame205 witness886 (by decide)
def edge886 : CertifiedEdge catalog where
  old := 199
  next := 205
  rank := 1
  good := by
    constructor
    · exact edge886_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness887 : Fin frame199.rank → ℕ := ![2,4]
theorem edge887_span : frame199.space ≤ frame207.space :=
  frame199.inclusion frame207 witness887 (by decide)
def edge887 : CertifiedEdge catalog where
  old := 199
  next := 207
  rank := 1
  good := by
    constructor
    · exact edge887_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness888 : Fin frame200.rank → ℕ := ![2,4]
theorem edge888_span : frame200.space ≤ frame203.space :=
  frame200.inclusion frame203 witness888 (by decide)
def edge888 : CertifiedEdge catalog where
  old := 200
  next := 203
  rank := 1
  good := by
    constructor
    · exact edge888_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness889 : Fin frame200.rank → ℕ := ![2,4]
theorem edge889_span : frame200.space ≤ frame209.space :=
  frame200.inclusion frame209 witness889 (by decide)
def edge889 : CertifiedEdge catalog where
  old := 200
  next := 209
  rank := 1
  good := by
    constructor
    · exact edge889_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness890 : Fin frame201.rank → ℕ := ![1,4]
theorem edge890_span : frame201.space ≤ frame552.space :=
  frame201.inclusion frame552 witness890 (by decide)
def edge890 : CertifiedEdge catalog where
  old := 201
  next := 552
  rank := 1
  good := by
    constructor
    · exact edge890_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness891 : Fin frame201.rank → ℕ := ![1,4]
theorem edge891_span : frame201.space ≤ frame555.space :=
  frame201.inclusion frame555 witness891 (by decide)
def edge891 : CertifiedEdge catalog where
  old := 201
  next := 555
  rank := 1
  good := by
    constructor
    · exact edge891_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness892 : Fin frame201.rank → ℕ := ![1,8]
theorem edge892_span : frame201.space ≤ frame605.space :=
  frame201.inclusion frame605 witness892 (by decide)
def edge892 : CertifiedEdge catalog where
  old := 201
  next := 605
  rank := 2
  good := by
    constructor
    · exact edge892_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness893 : Fin frame201.rank → ℕ := ![1,8]
theorem edge893_span : frame201.space ≤ frame609.space :=
  frame201.inclusion frame609 witness893 (by decide)
def edge893 : CertifiedEdge catalog where
  old := 201
  next := 609
  rank := 2
  good := by
    constructor
    · exact edge893_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness894 : Fin frame202.rank → ℕ := ![2,4]
theorem edge894_span : frame202.space ≤ frame552.space :=
  frame202.inclusion frame552 witness894 (by decide)
def edge894 : CertifiedEdge catalog where
  old := 202
  next := 552
  rank := 1
  good := by
    constructor
    · exact edge894_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness895 : Fin frame202.rank → ℕ := ![2,4]
theorem edge895_span : frame202.space ≤ frame554.space :=
  frame202.inclusion frame554 witness895 (by decide)
def edge895 : CertifiedEdge catalog where
  old := 202
  next := 554
  rank := 1
  good := by
    constructor
    · exact edge895_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
