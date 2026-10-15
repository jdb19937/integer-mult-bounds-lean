module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness928 : Fin frame212.rank → ℕ := ![2]
theorem edge928_span : frame212.space ≤ frame221.space :=
  frame212.inclusion frame221 witness928 (by decide)
def edge928 : CertifiedEdge catalog where
  old := 212
  next := 221
  rank := 1
  good := by
    constructor
    · exact edge928_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness929 : Fin frame212.rank → ℕ := ![2]
theorem edge929_span : frame212.space ≤ frame222.space :=
  frame212.inclusion frame222 witness929 (by decide)
def edge929 : CertifiedEdge catalog where
  old := 212
  next := 222
  rank := 1
  good := by
    constructor
    · exact edge929_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness930 : Fin frame213.rank → ℕ := ![3]
theorem edge930_span : frame213.space ≤ frame223.space :=
  frame213.inclusion frame223 witness930 (by decide)
def edge930 : CertifiedEdge catalog where
  old := 213
  next := 223
  rank := 1
  good := by
    constructor
    · exact edge930_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness931 : Fin frame213.rank → ℕ := ![1]
theorem edge931_span : frame213.space ≤ frame224.space :=
  frame213.inclusion frame224 witness931 (by decide)
def edge931 : CertifiedEdge catalog where
  old := 213
  next := 224
  rank := 1
  good := by
    constructor
    · exact edge931_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness932 : Fin frame213.rank → ℕ := ![1]
theorem edge932_span : frame213.space ≤ frame225.space :=
  frame213.inclusion frame225 witness932 (by decide)
def edge932 : CertifiedEdge catalog where
  old := 213
  next := 225
  rank := 1
  good := by
    constructor
    · exact edge932_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness933 : Fin frame214.rank → ℕ := ![1]
theorem edge933_span : frame214.space ≤ frame223.space :=
  frame214.inclusion frame223 witness933 (by decide)
def edge933 : CertifiedEdge catalog where
  old := 214
  next := 223
  rank := 1
  good := by
    constructor
    · exact edge933_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness934 : Fin frame214.rank → ℕ := ![1]
theorem edge934_span : frame214.space ≤ frame226.space :=
  frame214.inclusion frame226 witness934 (by decide)
def edge934 : CertifiedEdge catalog where
  old := 214
  next := 226
  rank := 1
  good := by
    constructor
    · exact edge934_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness935 : Fin frame214.rank → ℕ := ![1]
theorem edge935_span : frame214.space ≤ frame227.space :=
  frame214.inclusion frame227 witness935 (by decide)
def edge935 : CertifiedEdge catalog where
  old := 214
  next := 227
  rank := 1
  good := by
    constructor
    · exact edge935_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness936 : Fin frame215.rank → ℕ := ![1]
theorem edge936_span : frame215.space ≤ frame220.space :=
  frame215.inclusion frame220 witness936 (by decide)
def edge936 : CertifiedEdge catalog where
  old := 215
  next := 220
  rank := 1
  good := by
    constructor
    · exact edge936_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness937 : Fin frame215.rank → ℕ := ![2]
theorem edge937_span : frame215.space ≤ frame228.space :=
  frame215.inclusion frame228 witness937 (by decide)
def edge937 : CertifiedEdge catalog where
  old := 215
  next := 228
  rank := 1
  good := by
    constructor
    · exact edge937_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness938 : Fin frame215.rank → ℕ := ![2]
theorem edge938_span : frame215.space ≤ frame229.space :=
  frame215.inclusion frame229 witness938 (by decide)
def edge938 : CertifiedEdge catalog where
  old := 215
  next := 229
  rank := 1
  good := by
    constructor
    · exact edge938_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness939 : Fin frame216.rank → ℕ := ![3]
theorem edge939_span : frame216.space ≤ frame224.space :=
  frame216.inclusion frame224 witness939 (by decide)
def edge939 : CertifiedEdge catalog where
  old := 216
  next := 224
  rank := 1
  good := by
    constructor
    · exact edge939_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness940 : Fin frame216.rank → ℕ := ![3]
theorem edge940_span : frame216.space ≤ frame226.space :=
  frame216.inclusion frame226 witness940 (by decide)
def edge940 : CertifiedEdge catalog where
  old := 216
  next := 226
  rank := 1
  good := by
    constructor
    · exact edge940_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness941 : Fin frame216.rank → ℕ := ![1]
theorem edge941_span : frame216.space ≤ frame230.space :=
  frame216.inclusion frame230 witness941 (by decide)
def edge941 : CertifiedEdge catalog where
  old := 216
  next := 230
  rank := 1
  good := by
    constructor
    · exact edge941_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness942 : Fin frame217.rank → ℕ := ![3]
theorem edge942_span : frame217.space ≤ frame221.space :=
  frame217.inclusion frame221 witness942 (by decide)
def edge942 : CertifiedEdge catalog where
  old := 217
  next := 221
  rank := 1
  good := by
    constructor
    · exact edge942_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness943 : Fin frame217.rank → ℕ := ![3]
theorem edge943_span : frame217.space ≤ frame228.space :=
  frame217.inclusion frame228 witness943 (by decide)
def edge943 : CertifiedEdge catalog where
  old := 217
  next := 228
  rank := 1
  good := by
    constructor
    · exact edge943_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness944 : Fin frame217.rank → ℕ := ![3]
theorem edge944_span : frame217.space ≤ frame231.space :=
  frame217.inclusion frame231 witness944 (by decide)
def edge944 : CertifiedEdge catalog where
  old := 217
  next := 231
  rank := 1
  good := by
    constructor
    · exact edge944_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness945 : Fin frame218.rank → ℕ := ![1]
theorem edge945_span : frame218.space ≤ frame222.space :=
  frame218.inclusion frame222 witness945 (by decide)
def edge945 : CertifiedEdge catalog where
  old := 218
  next := 222
  rank := 1
  good := by
    constructor
    · exact edge945_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness946 : Fin frame218.rank → ℕ := ![1]
theorem edge946_span : frame218.space ≤ frame229.space :=
  frame218.inclusion frame229 witness946 (by decide)
def edge946 : CertifiedEdge catalog where
  old := 218
  next := 229
  rank := 1
  good := by
    constructor
    · exact edge946_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness947 : Fin frame218.rank → ℕ := ![1]
theorem edge947_span : frame218.space ≤ frame231.space :=
  frame218.inclusion frame231 witness947 (by decide)
def edge947 : CertifiedEdge catalog where
  old := 218
  next := 231
  rank := 1
  good := by
    constructor
    · exact edge947_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness948 : Fin frame219.rank → ℕ := ![3]
theorem edge948_span : frame219.space ≤ frame225.space :=
  frame219.inclusion frame225 witness948 (by decide)
def edge948 : CertifiedEdge catalog where
  old := 219
  next := 225
  rank := 1
  good := by
    constructor
    · exact edge948_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness949 : Fin frame219.rank → ℕ := ![3]
theorem edge949_span : frame219.space ≤ frame227.space :=
  frame219.inclusion frame227 witness949 (by decide)
def edge949 : CertifiedEdge catalog where
  old := 219
  next := 227
  rank := 1
  good := by
    constructor
    · exact edge949_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness950 : Fin frame219.rank → ℕ := ![3]
theorem edge950_span : frame219.space ≤ frame230.space :=
  frame219.inclusion frame230 witness950 (by decide)
def edge950 : CertifiedEdge catalog where
  old := 219
  next := 230
  rank := 1
  good := by
    constructor
    · exact edge950_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness951 : Fin frame220.rank → ℕ := ![2,4]
theorem edge951_span : frame220.space ≤ frame559.space :=
  frame220.inclusion frame559 witness951 (by decide)
def edge951 : CertifiedEdge catalog where
  old := 220
  next := 559
  rank := 1
  good := by
    constructor
    · exact edge951_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness952 : Fin frame220.rank → ℕ := ![2,4]
theorem edge952_span : frame220.space ≤ frame561.space :=
  frame220.inclusion frame561 witness952 (by decide)
def edge952 : CertifiedEdge catalog where
  old := 220
  next := 561
  rank := 1
  good := by
    constructor
    · exact edge952_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness953 : Fin frame220.rank → ℕ := ![4,8]
theorem edge953_span : frame220.space ≤ frame612.space :=
  frame220.inclusion frame612 witness953 (by decide)
def edge953 : CertifiedEdge catalog where
  old := 220
  next := 612
  rank := 2
  good := by
    constructor
    · exact edge953_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness954 : Fin frame220.rank → ℕ := ![16,96]
theorem edge954_span : frame220.space ≤ frame758.space :=
  frame220.inclusion frame758 witness954 (by decide)
def edge954 : CertifiedEdge catalog where
  old := 220
  next := 758
  rank := 5
  good := by
    constructor
    · exact edge954_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness955 : Fin frame221.rank → ℕ := ![2,4]
theorem edge955_span : frame221.space ≤ frame233.space :=
  frame221.inclusion frame233 witness955 (by decide)
def edge955 : CertifiedEdge catalog where
  old := 221
  next := 233
  rank := 1
  good := by
    constructor
    · exact edge955_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness956 : Fin frame221.rank → ℕ := ![2,4]
theorem edge956_span : frame221.space ≤ frame239.space :=
  frame221.inclusion frame239 witness956 (by decide)
def edge956 : CertifiedEdge catalog where
  old := 221
  next := 239
  rank := 1
  good := by
    constructor
    · exact edge956_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness957 : Fin frame222.rank → ℕ := ![2,4]
theorem edge957_span : frame222.space ≤ frame235.space :=
  frame222.inclusion frame235 witness957 (by decide)
def edge957 : CertifiedEdge catalog where
  old := 222
  next := 235
  rank := 1
  good := by
    constructor
    · exact edge957_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness958 : Fin frame222.rank → ℕ := ![2,4]
theorem edge958_span : frame222.space ≤ frame237.space :=
  frame222.inclusion frame237 witness958 (by decide)
def edge958 : CertifiedEdge catalog where
  old := 222
  next := 237
  rank := 1
  good := by
    constructor
    · exact edge958_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness959 : Fin frame223.rank → ℕ := ![1,6]
theorem edge959_span : frame223.space ≤ frame559.space :=
  frame223.inclusion frame559 witness959 (by decide)
def edge959 : CertifiedEdge catalog where
  old := 223
  next := 559
  rank := 1
  good := by
    constructor
    · exact edge959_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
