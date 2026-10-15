module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1024 : Fin frame245.rank → ℕ := ![1]
theorem edge1024_span : frame245.space ≤ frame253.space :=
  frame245.inclusion frame253 witness1024 (by decide)
def edge1024 : CertifiedEdge catalog where
  old := 245
  next := 253
  rank := 1
  good := by
    constructor
    · exact edge1024_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1025 : Fin frame245.rank → ℕ := ![1]
theorem edge1025_span : frame245.space ≤ frame255.space :=
  frame245.inclusion frame255 witness1025 (by decide)
def edge1025 : CertifiedEdge catalog where
  old := 245
  next := 255
  rank := 1
  good := by
    constructor
    · exact edge1025_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1026 : Fin frame245.rank → ℕ := ![3]
theorem edge1026_span : frame245.space ≤ frame259.space :=
  frame245.inclusion frame259 witness1026 (by decide)
def edge1026 : CertifiedEdge catalog where
  old := 245
  next := 259
  rank := 1
  good := by
    constructor
    · exact edge1026_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1027 : Fin frame246.rank → ℕ := ![1]
theorem edge1027_span : frame246.space ≤ frame250.space :=
  frame246.inclusion frame250 witness1027 (by decide)
def edge1027 : CertifiedEdge catalog where
  old := 246
  next := 250
  rank := 1
  good := by
    constructor
    · exact edge1027_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1028 : Fin frame246.rank → ℕ := ![1]
theorem edge1028_span : frame246.space ≤ frame257.space :=
  frame246.inclusion frame257 witness1028 (by decide)
def edge1028 : CertifiedEdge catalog where
  old := 246
  next := 257
  rank := 1
  good := by
    constructor
    · exact edge1028_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1029 : Fin frame246.rank → ℕ := ![1]
theorem edge1029_span : frame246.space ≤ frame260.space :=
  frame246.inclusion frame260 witness1029 (by decide)
def edge1029 : CertifiedEdge catalog where
  old := 246
  next := 260
  rank := 1
  good := by
    constructor
    · exact edge1029_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1030 : Fin frame247.rank → ℕ := ![1]
theorem edge1030_span : frame247.space ≤ frame251.space :=
  frame247.inclusion frame251 witness1030 (by decide)
def edge1030 : CertifiedEdge catalog where
  old := 247
  next := 251
  rank := 1
  good := by
    constructor
    · exact edge1030_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1031 : Fin frame247.rank → ℕ := ![1]
theorem edge1031_span : frame247.space ≤ frame258.space :=
  frame247.inclusion frame258 witness1031 (by decide)
def edge1031 : CertifiedEdge catalog where
  old := 247
  next := 258
  rank := 1
  good := by
    constructor
    · exact edge1031_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1032 : Fin frame247.rank → ℕ := ![3]
theorem edge1032_span : frame247.space ≤ frame260.space :=
  frame247.inclusion frame260 witness1032 (by decide)
def edge1032 : CertifiedEdge catalog where
  old := 247
  next := 260
  rank := 1
  good := by
    constructor
    · exact edge1032_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1033 : Fin frame248.rank → ℕ := ![1]
theorem edge1033_span : frame248.space ≤ frame254.space :=
  frame248.inclusion frame254 witness1033 (by decide)
def edge1033 : CertifiedEdge catalog where
  old := 248
  next := 254
  rank := 1
  good := by
    constructor
    · exact edge1033_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1034 : Fin frame248.rank → ℕ := ![1]
theorem edge1034_span : frame248.space ≤ frame256.space :=
  frame248.inclusion frame256 witness1034 (by decide)
def edge1034 : CertifiedEdge catalog where
  old := 248
  next := 256
  rank := 1
  good := by
    constructor
    · exact edge1034_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1035 : Fin frame248.rank → ℕ := ![1]
theorem edge1035_span : frame248.space ≤ frame259.space :=
  frame248.inclusion frame259 witness1035 (by decide)
def edge1035 : CertifiedEdge catalog where
  old := 248
  next := 259
  rank := 1
  good := by
    constructor
    · exact edge1035_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1036 : Fin frame249.rank → ℕ := ![1,4]
theorem edge1036_span : frame249.space ≤ frame565.space :=
  frame249.inclusion frame565 witness1036 (by decide)
def edge1036 : CertifiedEdge catalog where
  old := 249
  next := 565
  rank := 1
  good := by
    constructor
    · exact edge1036_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1037 : Fin frame249.rank → ℕ := ![1,4]
theorem edge1037_span : frame249.space ≤ frame567.space :=
  frame249.inclusion frame567 witness1037 (by decide)
def edge1037 : CertifiedEdge catalog where
  old := 249
  next := 567
  rank := 1
  good := by
    constructor
    · exact edge1037_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1038 : Fin frame249.rank → ℕ := ![1,12]
theorem edge1038_span : frame249.space ≤ frame617.space :=
  frame249.inclusion frame617 witness1038 (by decide)
def edge1038 : CertifiedEdge catalog where
  old := 249
  next := 617
  rank := 2
  good := by
    constructor
    · exact edge1038_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1039 : Fin frame249.rank → ℕ := ![13,16]
theorem edge1039_span : frame249.space ≤ frame621.space :=
  frame249.inclusion frame621 witness1039 (by decide)
def edge1039 : CertifiedEdge catalog where
  old := 249
  next := 621
  rank := 4
  good := by
    constructor
    · exact edge1039_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1040 : Fin frame250.rank → ℕ := ![1,4]
theorem edge1040_span : frame250.space ≤ frame262.space :=
  frame250.inclusion frame262 witness1040 (by decide)
def edge1040 : CertifiedEdge catalog where
  old := 250
  next := 262
  rank := 1
  good := by
    constructor
    · exact edge1040_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1041 : Fin frame250.rank → ℕ := ![1,4]
theorem edge1041_span : frame250.space ≤ frame268.space :=
  frame250.inclusion frame268 witness1041 (by decide)
def edge1041 : CertifiedEdge catalog where
  old := 250
  next := 268
  rank := 1
  good := by
    constructor
    · exact edge1041_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1042 : Fin frame251.rank → ℕ := ![1,4]
theorem edge1042_span : frame251.space ≤ frame264.space :=
  frame251.inclusion frame264 witness1042 (by decide)
def edge1042 : CertifiedEdge catalog where
  old := 251
  next := 264
  rank := 1
  good := by
    constructor
    · exact edge1042_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1043 : Fin frame251.rank → ℕ := ![1,4]
theorem edge1043_span : frame251.space ≤ frame266.space :=
  frame251.inclusion frame266 witness1043 (by decide)
def edge1043 : CertifiedEdge catalog where
  old := 251
  next := 266
  rank := 1
  good := by
    constructor
    · exact edge1043_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1044 : Fin frame252.rank → ℕ := ![2,4]
theorem edge1044_span : frame252.space ≤ frame565.space :=
  frame252.inclusion frame565 witness1044 (by decide)
def edge1044 : CertifiedEdge catalog where
  old := 252
  next := 565
  rank := 1
  good := by
    constructor
    · exact edge1044_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1045 : Fin frame252.rank → ℕ := ![2,4]
theorem edge1045_span : frame252.space ≤ frame566.space :=
  frame252.inclusion frame566 witness1045 (by decide)
def edge1045 : CertifiedEdge catalog where
  old := 252
  next := 566
  rank := 1
  good := by
    constructor
    · exact edge1045_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1046 : Fin frame252.rank → ℕ := ![14,16]
theorem edge1046_span : frame252.space ≤ frame619.space :=
  frame252.inclusion frame619 witness1046 (by decide)
def edge1046 : CertifiedEdge catalog where
  old := 252
  next := 619
  rank := 4
  good := by
    constructor
    · exact edge1046_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1047 : Fin frame252.rank → ℕ := ![6,56]
theorem edge1047_span : frame252.space ≤ frame764.space :=
  frame252.inclusion frame764 witness1047 (by decide)
def edge1047 : CertifiedEdge catalog where
  old := 252
  next := 764
  rank := 5
  good := by
    constructor
    · exact edge1047_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1048 : Fin frame253.rank → ℕ := ![2,4]
theorem edge1048_span : frame253.space ≤ frame262.space :=
  frame253.inclusion frame262 witness1048 (by decide)
def edge1048 : CertifiedEdge catalog where
  old := 253
  next := 262
  rank := 1
  good := by
    constructor
    · exact edge1048_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1049 : Fin frame253.rank → ℕ := ![2,4]
theorem edge1049_span : frame253.space ≤ frame267.space :=
  frame253.inclusion frame267 witness1049 (by decide)
def edge1049 : CertifiedEdge catalog where
  old := 253
  next := 267
  rank := 1
  good := by
    constructor
    · exact edge1049_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1050 : Fin frame254.rank → ℕ := ![2,4]
theorem edge1050_span : frame254.space ≤ frame263.space :=
  frame254.inclusion frame263 witness1050 (by decide)
def edge1050 : CertifiedEdge catalog where
  old := 254
  next := 263
  rank := 1
  good := by
    constructor
    · exact edge1050_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1051 : Fin frame254.rank → ℕ := ![2,4]
theorem edge1051_span : frame254.space ≤ frame266.space :=
  frame254.inclusion frame266 witness1051 (by decide)
def edge1051 : CertifiedEdge catalog where
  old := 254
  next := 266
  rank := 1
  good := by
    constructor
    · exact edge1051_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1052 : Fin frame255.rank → ℕ := ![2,4]
theorem edge1052_span : frame255.space ≤ frame264.space :=
  frame255.inclusion frame264 witness1052 (by decide)
def edge1052 : CertifiedEdge catalog where
  old := 255
  next := 264
  rank := 1
  good := by
    constructor
    · exact edge1052_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1053 : Fin frame255.rank → ℕ := ![2,4]
theorem edge1053_span : frame255.space ≤ frame265.space :=
  frame255.inclusion frame265 witness1053 (by decide)
def edge1053 : CertifiedEdge catalog where
  old := 255
  next := 265
  rank := 1
  good := by
    constructor
    · exact edge1053_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1054 : Fin frame256.rank → ℕ := ![2,4]
theorem edge1054_span : frame256.space ≤ frame261.space :=
  frame256.inclusion frame261 witness1054 (by decide)
def edge1054 : CertifiedEdge catalog where
  old := 256
  next := 261
  rank := 1
  good := by
    constructor
    · exact edge1054_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1055 : Fin frame256.rank → ℕ := ![2,4]
theorem edge1055_span : frame256.space ≤ frame268.space :=
  frame256.inclusion frame268 witness1055 (by decide)
def edge1055 : CertifiedEdge catalog where
  old := 256
  next := 268
  rank := 1
  good := by
    constructor
    · exact edge1055_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
