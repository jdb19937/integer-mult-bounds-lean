module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1088 : Fin frame267.rank → ℕ := ![17,18,28]
theorem edge1088_span : frame267.space ≤ frame726.space :=
  frame267.inclusion frame726 witness1088 (by decide)
def edge1088 : CertifiedEdge catalog where
  old := 267
  next := 726
  rank := 3
  good := by
    constructor
    · exact edge1088_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1089 : Fin frame268.rank → ℕ := ![1,2,12]
theorem edge1089_span : frame268.space ≤ frame269.space :=
  frame268.inclusion frame269 witness1089 (by decide)
def edge1089 : CertifiedEdge catalog where
  old := 268
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1089_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1090 : Fin frame268.rank → ℕ := ![33,34,28]
theorem edge1090_span : frame268.space ≤ frame661.space :=
  frame268.inclusion frame661 witness1090 (by decide)
def edge1090 : CertifiedEdge catalog where
  old := 268
  next := 661
  rank := 3
  good := by
    constructor
    · exact edge1090_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1091 : Fin frame268.rank → ℕ := ![33,34,28]
theorem edge1091_span : frame268.space ≤ frame727.space :=
  frame268.inclusion frame727 witness1091 (by decide)
def edge1091 : CertifiedEdge catalog where
  old := 268
  next := 727
  rank := 3
  good := by
    constructor
    · exact edge1091_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1092 : Fin frame269.rank → ℕ := ![193,194,204,240]
theorem edge1092_span : frame269.space ≤ frame1.space :=
  frame269.inclusion frame1 witness1092 (by decide)
def edge1092 : CertifiedEdge catalog where
  old := 269
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1092_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1093 : Fin frame269.rank → ℕ := ![193,194,204,240]
theorem edge1093_span : frame269.space ≤ frame416.space :=
  frame269.inclusion frame416 witness1093 (by decide)
def edge1093 : CertifiedEdge catalog where
  old := 269
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge1093_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1094 : Fin frame269.rank → ℕ := ![193,194,204,240]
theorem edge1094_span : frame269.space ≤ frame417.space :=
  frame269.inclusion frame417 witness1094 (by decide)
def edge1094 : CertifiedEdge catalog where
  old := 269
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge1094_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1095 : Fin frame269.rank → ℕ := ![193,194,204,240]
theorem edge1095_span : frame269.space ≤ frame420.space :=
  frame269.inclusion frame420 witness1095 (by decide)
def edge1095 : CertifiedEdge catalog where
  old := 269
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge1095_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1096 : Fin frame269.rank → ℕ := ![193,194,204,240]
theorem edge1096_span : frame269.space ≤ frame421.space :=
  frame269.inclusion frame421 witness1096 (by decide)
def edge1096 : CertifiedEdge catalog where
  old := 269
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge1096_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1097 : Fin frame270.rank → ℕ := ![3]
theorem edge1097_span : frame270.space ≤ frame278.space :=
  frame270.inclusion frame278 witness1097 (by decide)
def edge1097 : CertifiedEdge catalog where
  old := 270
  next := 278
  rank := 1
  good := by
    constructor
    · exact edge1097_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1098 : Fin frame270.rank → ℕ := ![3]
theorem edge1098_span : frame270.space ≤ frame279.space :=
  frame270.inclusion frame279 witness1098 (by decide)
def edge1098 : CertifiedEdge catalog where
  old := 270
  next := 279
  rank := 1
  good := by
    constructor
    · exact edge1098_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1099 : Fin frame270.rank → ℕ := ![3]
theorem edge1099_span : frame270.space ≤ frame280.space :=
  frame270.inclusion frame280 witness1099 (by decide)
def edge1099 : CertifiedEdge catalog where
  old := 270
  next := 280
  rank := 1
  good := by
    constructor
    · exact edge1099_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1100 : Fin frame271.rank → ℕ := ![3]
theorem edge1100_span : frame271.space ≤ frame281.space :=
  frame271.inclusion frame281 witness1100 (by decide)
def edge1100 : CertifiedEdge catalog where
  old := 271
  next := 281
  rank := 1
  good := by
    constructor
    · exact edge1100_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1101 : Fin frame271.rank → ℕ := ![3]
theorem edge1101_span : frame271.space ≤ frame282.space :=
  frame271.inclusion frame282 witness1101 (by decide)
def edge1101 : CertifiedEdge catalog where
  old := 271
  next := 282
  rank := 1
  good := by
    constructor
    · exact edge1101_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1102 : Fin frame271.rank → ℕ := ![3]
theorem edge1102_span : frame271.space ≤ frame283.space :=
  frame271.inclusion frame283 witness1102 (by decide)
def edge1102 : CertifiedEdge catalog where
  old := 271
  next := 283
  rank := 1
  good := by
    constructor
    · exact edge1102_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1103 : Fin frame272.rank → ℕ := ![1]
theorem edge1103_span : frame272.space ≤ frame281.space :=
  frame272.inclusion frame281 witness1103 (by decide)
def edge1103 : CertifiedEdge catalog where
  old := 272
  next := 281
  rank := 1
  good := by
    constructor
    · exact edge1103_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1104 : Fin frame272.rank → ℕ := ![1]
theorem edge1104_span : frame272.space ≤ frame284.space :=
  frame272.inclusion frame284 witness1104 (by decide)
def edge1104 : CertifiedEdge catalog where
  old := 272
  next := 284
  rank := 1
  good := by
    constructor
    · exact edge1104_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1105 : Fin frame272.rank → ℕ := ![1]
theorem edge1105_span : frame272.space ≤ frame285.space :=
  frame272.inclusion frame285 witness1105 (by decide)
def edge1105 : CertifiedEdge catalog where
  old := 272
  next := 285
  rank := 1
  good := by
    constructor
    · exact edge1105_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1106 : Fin frame273.rank → ℕ := ![1]
theorem edge1106_span : frame273.space ≤ frame278.space :=
  frame273.inclusion frame278 witness1106 (by decide)
def edge1106 : CertifiedEdge catalog where
  old := 273
  next := 278
  rank := 1
  good := by
    constructor
    · exact edge1106_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1107 : Fin frame273.rank → ℕ := ![3]
theorem edge1107_span : frame273.space ≤ frame286.space :=
  frame273.inclusion frame286 witness1107 (by decide)
def edge1107 : CertifiedEdge catalog where
  old := 273
  next := 286
  rank := 1
  good := by
    constructor
    · exact edge1107_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1108 : Fin frame273.rank → ℕ := ![3]
theorem edge1108_span : frame273.space ≤ frame287.space :=
  frame273.inclusion frame287 witness1108 (by decide)
def edge1108 : CertifiedEdge catalog where
  old := 273
  next := 287
  rank := 1
  good := by
    constructor
    · exact edge1108_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1109 : Fin frame274.rank → ℕ := ![2]
theorem edge1109_span : frame274.space ≤ frame282.space :=
  frame274.inclusion frame282 witness1109 (by decide)
def edge1109 : CertifiedEdge catalog where
  old := 274
  next := 282
  rank := 1
  good := by
    constructor
    · exact edge1109_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1110 : Fin frame274.rank → ℕ := ![2]
theorem edge1110_span : frame274.space ≤ frame284.space :=
  frame274.inclusion frame284 witness1110 (by decide)
def edge1110 : CertifiedEdge catalog where
  old := 274
  next := 284
  rank := 1
  good := by
    constructor
    · exact edge1110_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1111 : Fin frame274.rank → ℕ := ![1]
theorem edge1111_span : frame274.space ≤ frame288.space :=
  frame274.inclusion frame288 witness1111 (by decide)
def edge1111 : CertifiedEdge catalog where
  old := 274
  next := 288
  rank := 1
  good := by
    constructor
    · exact edge1111_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1112 : Fin frame275.rank → ℕ := ![1]
theorem edge1112_span : frame275.space ≤ frame279.space :=
  frame275.inclusion frame279 witness1112 (by decide)
def edge1112 : CertifiedEdge catalog where
  old := 275
  next := 279
  rank := 1
  good := by
    constructor
    · exact edge1112_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1113 : Fin frame275.rank → ℕ := ![1]
theorem edge1113_span : frame275.space ≤ frame286.space :=
  frame275.inclusion frame286 witness1113 (by decide)
def edge1113 : CertifiedEdge catalog where
  old := 275
  next := 286
  rank := 1
  good := by
    constructor
    · exact edge1113_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1114 : Fin frame275.rank → ℕ := ![3]
theorem edge1114_span : frame275.space ≤ frame289.space :=
  frame275.inclusion frame289 witness1114 (by decide)
def edge1114 : CertifiedEdge catalog where
  old := 275
  next := 289
  rank := 1
  good := by
    constructor
    · exact edge1114_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1115 : Fin frame276.rank → ℕ := ![1]
theorem edge1115_span : frame276.space ≤ frame280.space :=
  frame276.inclusion frame280 witness1115 (by decide)
def edge1115 : CertifiedEdge catalog where
  old := 276
  next := 280
  rank := 1
  good := by
    constructor
    · exact edge1115_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1116 : Fin frame276.rank → ℕ := ![1]
theorem edge1116_span : frame276.space ≤ frame287.space :=
  frame276.inclusion frame287 witness1116 (by decide)
def edge1116 : CertifiedEdge catalog where
  old := 276
  next := 287
  rank := 1
  good := by
    constructor
    · exact edge1116_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1117 : Fin frame276.rank → ℕ := ![1]
theorem edge1117_span : frame276.space ≤ frame289.space :=
  frame276.inclusion frame289 witness1117 (by decide)
def edge1117 : CertifiedEdge catalog where
  old := 276
  next := 289
  rank := 1
  good := by
    constructor
    · exact edge1117_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1118 : Fin frame277.rank → ℕ := ![2]
theorem edge1118_span : frame277.space ≤ frame283.space :=
  frame277.inclusion frame283 witness1118 (by decide)
def edge1118 : CertifiedEdge catalog where
  old := 277
  next := 283
  rank := 1
  good := by
    constructor
    · exact edge1118_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1119 : Fin frame277.rank → ℕ := ![2]
theorem edge1119_span : frame277.space ≤ frame285.space :=
  frame277.inclusion frame285 witness1119 (by decide)
def edge1119 : CertifiedEdge catalog where
  old := 277
  next := 285
  rank := 1
  good := by
    constructor
    · exact edge1119_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
