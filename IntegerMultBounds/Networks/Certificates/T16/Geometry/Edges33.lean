module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1056 : Fin frame257.rank → ℕ := ![1,4]
theorem edge1056_span : frame257.space ≤ frame263.space :=
  frame257.inclusion frame263 witness1056 (by decide)
def edge1056 : CertifiedEdge catalog where
  old := 257
  next := 263
  rank := 1
  good := by
    constructor
    · exact edge1056_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1057 : Fin frame257.rank → ℕ := ![1,4]
theorem edge1057_span : frame257.space ≤ frame265.space :=
  frame257.inclusion frame265 witness1057 (by decide)
def edge1057 : CertifiedEdge catalog where
  old := 257
  next := 265
  rank := 1
  good := by
    constructor
    · exact edge1057_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1058 : Fin frame258.rank → ℕ := ![1,4]
theorem edge1058_span : frame258.space ≤ frame261.space :=
  frame258.inclusion frame261 witness1058 (by decide)
def edge1058 : CertifiedEdge catalog where
  old := 258
  next := 261
  rank := 1
  good := by
    constructor
    · exact edge1058_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1059 : Fin frame258.rank → ℕ := ![1,4]
theorem edge1059_span : frame258.space ≤ frame267.space :=
  frame258.inclusion frame267 witness1059 (by decide)
def edge1059 : CertifiedEdge catalog where
  old := 258
  next := 267
  rank := 1
  good := by
    constructor
    · exact edge1059_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1060 : Fin frame259.rank → ℕ := ![2,4]
theorem edge1060_span : frame259.space ≤ frame564.space :=
  frame259.inclusion frame564 witness1060 (by decide)
def edge1060 : CertifiedEdge catalog where
  old := 259
  next := 564
  rank := 1
  good := by
    constructor
    · exact edge1060_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1061 : Fin frame259.rank → ℕ := ![2,4]
theorem edge1061_span : frame259.space ≤ frame567.space :=
  frame259.inclusion frame567 witness1061 (by decide)
def edge1061 : CertifiedEdge catalog where
  old := 259
  next := 567
  rank := 1
  good := by
    constructor
    · exact edge1061_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1062 : Fin frame259.rank → ℕ := ![2,8]
theorem edge1062_span : frame259.space ≤ frame616.space :=
  frame259.inclusion frame616 witness1062 (by decide)
def edge1062 : CertifiedEdge catalog where
  old := 259
  next := 616
  rank := 2
  good := by
    constructor
    · exact edge1062_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1063 : Fin frame259.rank → ℕ := ![2,12]
theorem edge1063_span : frame259.space ≤ frame620.space :=
  frame259.inclusion frame620 witness1063 (by decide)
def edge1063 : CertifiedEdge catalog where
  old := 259
  next := 620
  rank := 2
  good := by
    constructor
    · exact edge1063_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1064 : Fin frame260.rank → ℕ := ![1,4]
theorem edge1064_span : frame260.space ≤ frame564.space :=
  frame260.inclusion frame564 witness1064 (by decide)
def edge1064 : CertifiedEdge catalog where
  old := 260
  next := 564
  rank := 1
  good := by
    constructor
    · exact edge1064_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1065 : Fin frame260.rank → ℕ := ![1,4]
theorem edge1065_span : frame260.space ≤ frame566.space :=
  frame260.inclusion frame566 witness1065 (by decide)
def edge1065 : CertifiedEdge catalog where
  old := 260
  next := 566
  rank := 1
  good := by
    constructor
    · exact edge1065_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1066 : Fin frame260.rank → ℕ := ![1,12]
theorem edge1066_span : frame260.space ≤ frame618.space :=
  frame260.inclusion frame618 witness1066 (by decide)
def edge1066 : CertifiedEdge catalog where
  old := 260
  next := 618
  rank := 2
  good := by
    constructor
    · exact edge1066_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1067 : Fin frame260.rank → ℕ := ![33,48]
theorem edge1067_span : frame260.space ≤ frame762.space :=
  frame260.inclusion frame762 witness1067 (by decide)
def edge1067 : CertifiedEdge catalog where
  old := 260
  next := 762
  rank := 5
  good := by
    constructor
    · exact edge1067_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1068 : Fin frame261.rank → ℕ := ![9,2,12]
theorem edge1068_span : frame261.space ≤ frame269.space :=
  frame261.inclusion frame269 witness1068 (by decide)
def edge1068 : CertifiedEdge catalog where
  old := 261
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1068_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1069 : Fin frame261.rank → ℕ := ![1,50,12]
theorem edge1069_span : frame261.space ≤ frame644.space :=
  frame261.inclusion frame644 witness1069 (by decide)
def edge1069 : CertifiedEdge catalog where
  old := 261
  next := 644
  rank := 3
  good := by
    constructor
    · exact edge1069_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1070 : Fin frame261.rank → ℕ := ![1,50,12]
theorem edge1070_span : frame261.space ≤ frame710.space :=
  frame261.inclusion frame710 witness1070 (by decide)
def edge1070 : CertifiedEdge catalog where
  old := 261
  next := 710
  rank := 3
  good := by
    constructor
    · exact edge1070_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1071 : Fin frame262.rank → ℕ := ![1,10,12]
theorem edge1071_span : frame262.space ≤ frame269.space :=
  frame262.inclusion frame269 witness1071 (by decide)
def edge1071 : CertifiedEdge catalog where
  old := 262
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1071_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1072 : Fin frame262.rank → ℕ := ![49,2,12]
theorem edge1072_span : frame262.space ≤ frame645.space :=
  frame262.inclusion frame645 witness1072 (by decide)
def edge1072 : CertifiedEdge catalog where
  old := 262
  next := 645
  rank := 3
  good := by
    constructor
    · exact edge1072_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1073 : Fin frame262.rank → ℕ := ![49,2,12]
theorem edge1073_span : frame262.space ≤ frame711.space :=
  frame262.inclusion frame711 witness1073 (by decide)
def edge1073 : CertifiedEdge catalog where
  old := 262
  next := 711
  rank := 3
  good := by
    constructor
    · exact edge1073_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1074 : Fin frame263.rank → ℕ := ![1,2,4]
theorem edge1074_span : frame263.space ≤ frame269.space :=
  frame263.inclusion frame269 witness1074 (by decide)
def edge1074 : CertifiedEdge catalog where
  old := 263
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1074_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1075 : Fin frame263.rank → ℕ := ![33,34,44]
theorem edge1075_span : frame263.space ≤ frame650.space :=
  frame263.inclusion frame650 witness1075 (by decide)
def edge1075 : CertifiedEdge catalog where
  old := 263
  next := 650
  rank := 3
  good := by
    constructor
    · exact edge1075_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1076 : Fin frame263.rank → ℕ := ![33,34,44]
theorem edge1076_span : frame263.space ≤ frame704.space :=
  frame263.inclusion frame704 witness1076 (by decide)
def edge1076 : CertifiedEdge catalog where
  old := 263
  next := 704
  rank := 3
  good := by
    constructor
    · exact edge1076_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1077 : Fin frame264.rank → ℕ := ![9,10,4]
theorem edge1077_span : frame264.space ≤ frame269.space :=
  frame264.inclusion frame269 witness1077 (by decide)
def edge1077 : CertifiedEdge catalog where
  old := 264
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1077_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1078 : Fin frame264.rank → ℕ := ![17,18,44]
theorem edge1078_span : frame264.space ≤ frame651.space :=
  frame264.inclusion frame651 witness1078 (by decide)
def edge1078 : CertifiedEdge catalog where
  old := 264
  next := 651
  rank := 3
  good := by
    constructor
    · exact edge1078_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1079 : Fin frame264.rank → ℕ := ![17,18,44]
theorem edge1079_span : frame264.space ≤ frame705.space :=
  frame264.inclusion frame705 witness1079 (by decide)
def edge1079 : CertifiedEdge catalog where
  old := 264
  next := 705
  rank := 3
  good := by
    constructor
    · exact edge1079_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1080 : Fin frame265.rank → ℕ := ![1,10,4]
theorem edge1080_span : frame265.space ≤ frame269.space :=
  frame265.inclusion frame269 witness1080 (by decide)
def edge1080 : CertifiedEdge catalog where
  old := 265
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1080_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1081 : Fin frame265.rank → ℕ := ![1,50,12]
theorem edge1081_span : frame265.space ≤ frame666.space :=
  frame265.inclusion frame666 witness1081 (by decide)
def edge1081 : CertifiedEdge catalog where
  old := 265
  next := 666
  rank := 3
  good := by
    constructor
    · exact edge1081_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1082 : Fin frame265.rank → ℕ := ![1,50,12]
theorem edge1082_span : frame265.space ≤ frame720.space :=
  frame265.inclusion frame720 witness1082 (by decide)
def edge1082 : CertifiedEdge catalog where
  old := 265
  next := 720
  rank := 3
  good := by
    constructor
    · exact edge1082_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1083 : Fin frame266.rank → ℕ := ![9,2,4]
theorem edge1083_span : frame266.space ≤ frame269.space :=
  frame266.inclusion frame269 witness1083 (by decide)
def edge1083 : CertifiedEdge catalog where
  old := 266
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1083_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1084 : Fin frame266.rank → ℕ := ![49,2,12]
theorem edge1084_span : frame266.space ≤ frame667.space :=
  frame266.inclusion frame667 witness1084 (by decide)
def edge1084 : CertifiedEdge catalog where
  old := 266
  next := 667
  rank := 3
  good := by
    constructor
    · exact edge1084_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1085 : Fin frame266.rank → ℕ := ![49,2,12]
theorem edge1085_span : frame266.space ≤ frame721.space :=
  frame266.inclusion frame721 witness1085 (by decide)
def edge1085 : CertifiedEdge catalog where
  old := 266
  next := 721
  rank := 3
  good := by
    constructor
    · exact edge1085_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1086 : Fin frame267.rank → ℕ := ![9,10,12]
theorem edge1086_span : frame267.space ≤ frame269.space :=
  frame267.inclusion frame269 witness1086 (by decide)
def edge1086 : CertifiedEdge catalog where
  old := 267
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1086_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1087 : Fin frame267.rank → ℕ := ![17,18,28]
theorem edge1087_span : frame267.space ≤ frame660.space :=
  frame267.inclusion frame660 witness1087 (by decide)
def edge1087 : CertifiedEdge catalog where
  old := 267
  next := 660
  rank := 3
  good := by
    constructor
    · exact edge1087_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
