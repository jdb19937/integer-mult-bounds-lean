module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1120 : Fin frame277.rank → ℕ := ![2]
theorem edge1120_span : frame277.space ≤ frame288.space :=
  frame277.inclusion frame288 witness1120 (by decide)
def edge1120 : CertifiedEdge catalog where
  old := 277
  next := 288
  rank := 1
  good := by
    constructor
    · exact edge1120_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1121 : Fin frame278.rank → ℕ := ![3,4]
theorem edge1121_span : frame278.space ≤ frame571.space :=
  frame278.inclusion frame571 witness1121 (by decide)
def edge1121 : CertifiedEdge catalog where
  old := 278
  next := 571
  rank := 1
  good := by
    constructor
    · exact edge1121_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1122 : Fin frame278.rank → ℕ := ![5,6]
theorem edge1122_span : frame278.space ≤ frame573.space :=
  frame278.inclusion frame573 witness1122 (by decide)
def edge1122 : CertifiedEdge catalog where
  old := 278
  next := 573
  rank := 1
  good := by
    constructor
    · exact edge1122_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1123 : Fin frame278.rank → ℕ := ![7,8]
theorem edge1123_span : frame278.space ≤ frame623.space :=
  frame278.inclusion frame623 witness1123 (by decide)
def edge1123 : CertifiedEdge catalog where
  old := 278
  next := 623
  rank := 2
  good := by
    constructor
    · exact edge1123_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1124 : Fin frame278.rank → ℕ := ![119,24]
theorem edge1124_span : frame278.space ≤ frame766.space :=
  frame278.inclusion frame766 witness1124 (by decide)
def edge1124 : CertifiedEdge catalog where
  old := 278
  next := 766
  rank := 5
  good := by
    constructor
    · exact edge1124_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1125 : Fin frame279.rank → ℕ := ![5,2]
theorem edge1125_span : frame279.space ≤ frame291.space :=
  frame279.inclusion frame291 witness1125 (by decide)
def edge1125 : CertifiedEdge catalog where
  old := 279
  next := 291
  rank := 1
  good := by
    constructor
    · exact edge1125_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1126 : Fin frame279.rank → ℕ := ![5,6]
theorem edge1126_span : frame279.space ≤ frame297.space :=
  frame279.inclusion frame297 witness1126 (by decide)
def edge1126 : CertifiedEdge catalog where
  old := 279
  next := 297
  rank := 1
  good := by
    constructor
    · exact edge1126_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1127 : Fin frame280.rank → ℕ := ![1,6]
theorem edge1127_span : frame280.space ≤ frame293.space :=
  frame280.inclusion frame293 witness1127 (by decide)
def edge1127 : CertifiedEdge catalog where
  old := 280
  next := 293
  rank := 1
  good := by
    constructor
    · exact edge1127_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1128 : Fin frame280.rank → ℕ := ![1,2]
theorem edge1128_span : frame280.space ≤ frame295.space :=
  frame280.inclusion frame295 witness1128 (by decide)
def edge1128 : CertifiedEdge catalog where
  old := 280
  next := 295
  rank := 1
  good := by
    constructor
    · exact edge1128_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1129 : Fin frame281.rank → ℕ := ![2,4]
theorem edge1129_span : frame281.space ≤ frame571.space :=
  frame281.inclusion frame571 witness1129 (by decide)
def edge1129 : CertifiedEdge catalog where
  old := 281
  next := 571
  rank := 1
  good := by
    constructor
    · exact edge1129_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1130 : Fin frame281.rank → ℕ := ![2,4]
theorem edge1130_span : frame281.space ≤ frame572.space :=
  frame281.inclusion frame572 witness1130 (by decide)
def edge1130 : CertifiedEdge catalog where
  old := 281
  next := 572
  rank := 1
  good := by
    constructor
    · exact edge1130_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1131 : Fin frame281.rank → ℕ := ![68,88]
theorem edge1131_span : frame281.space ≤ frame767.space :=
  frame281.inclusion frame767 witness1131 (by decide)
def edge1131 : CertifiedEdge catalog where
  old := 281
  next := 767
  rank := 5
  good := by
    constructor
    · exact edge1131_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1132 : Fin frame281.rank → ℕ := ![4,24]
theorem edge1132_span : frame281.space ≤ frame768.space :=
  frame281.inclusion frame768 witness1132 (by decide)
def edge1132 : CertifiedEdge catalog where
  old := 281
  next := 768
  rank := 5
  good := by
    constructor
    · exact edge1132_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1133 : Fin frame282.rank → ℕ := ![2,4]
theorem edge1133_span : frame282.space ≤ frame291.space :=
  frame282.inclusion frame291 witness1133 (by decide)
def edge1133 : CertifiedEdge catalog where
  old := 282
  next := 291
  rank := 1
  good := by
    constructor
    · exact edge1133_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1134 : Fin frame282.rank → ℕ := ![2,4]
theorem edge1134_span : frame282.space ≤ frame296.space :=
  frame282.inclusion frame296 witness1134 (by decide)
def edge1134 : CertifiedEdge catalog where
  old := 282
  next := 296
  rank := 1
  good := by
    constructor
    · exact edge1134_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1135 : Fin frame283.rank → ℕ := ![2,4]
theorem edge1135_span : frame283.space ≤ frame292.space :=
  frame283.inclusion frame292 witness1135 (by decide)
def edge1135 : CertifiedEdge catalog where
  old := 283
  next := 292
  rank := 1
  good := by
    constructor
    · exact edge1135_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1136 : Fin frame283.rank → ℕ := ![2,4]
theorem edge1136_span : frame283.space ≤ frame295.space :=
  frame283.inclusion frame295 witness1136 (by decide)
def edge1136 : CertifiedEdge catalog where
  old := 283
  next := 295
  rank := 1
  good := by
    constructor
    · exact edge1136_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1137 : Fin frame284.rank → ℕ := ![2,4]
theorem edge1137_span : frame284.space ≤ frame293.space :=
  frame284.inclusion frame293 witness1137 (by decide)
def edge1137 : CertifiedEdge catalog where
  old := 284
  next := 293
  rank := 1
  good := by
    constructor
    · exact edge1137_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1138 : Fin frame284.rank → ℕ := ![2,4]
theorem edge1138_span : frame284.space ≤ frame294.space :=
  frame284.inclusion frame294 witness1138 (by decide)
def edge1138 : CertifiedEdge catalog where
  old := 284
  next := 294
  rank := 1
  good := by
    constructor
    · exact edge1138_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1139 : Fin frame285.rank → ℕ := ![2,4]
theorem edge1139_span : frame285.space ≤ frame290.space :=
  frame285.inclusion frame290 witness1139 (by decide)
def edge1139 : CertifiedEdge catalog where
  old := 285
  next := 290
  rank := 1
  good := by
    constructor
    · exact edge1139_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1140 : Fin frame285.rank → ℕ := ![2,4]
theorem edge1140_span : frame285.space ≤ frame297.space :=
  frame285.inclusion frame297 witness1140 (by decide)
def edge1140 : CertifiedEdge catalog where
  old := 285
  next := 297
  rank := 1
  good := by
    constructor
    · exact edge1140_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1141 : Fin frame286.rank → ℕ := ![5,2]
theorem edge1141_span : frame286.space ≤ frame292.space :=
  frame286.inclusion frame292 witness1141 (by decide)
def edge1141 : CertifiedEdge catalog where
  old := 286
  next := 292
  rank := 1
  good := by
    constructor
    · exact edge1141_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1142 : Fin frame286.rank → ℕ := ![5,6]
theorem edge1142_span : frame286.space ≤ frame294.space :=
  frame286.inclusion frame294 witness1142 (by decide)
def edge1142 : CertifiedEdge catalog where
  old := 286
  next := 294
  rank := 1
  good := by
    constructor
    · exact edge1142_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1143 : Fin frame287.rank → ℕ := ![1,6]
theorem edge1143_span : frame287.space ≤ frame290.space :=
  frame287.inclusion frame290 witness1143 (by decide)
def edge1143 : CertifiedEdge catalog where
  old := 287
  next := 290
  rank := 1
  good := by
    constructor
    · exact edge1143_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1144 : Fin frame287.rank → ℕ := ![1,2]
theorem edge1144_span : frame287.space ≤ frame296.space :=
  frame287.inclusion frame296 witness1144 (by decide)
def edge1144 : CertifiedEdge catalog where
  old := 287
  next := 296
  rank := 1
  good := by
    constructor
    · exact edge1144_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1145 : Fin frame288.rank → ℕ := ![2,4]
theorem edge1145_span : frame288.space ≤ frame570.space :=
  frame288.inclusion frame570 witness1145 (by decide)
def edge1145 : CertifiedEdge catalog where
  old := 288
  next := 570
  rank := 1
  good := by
    constructor
    · exact edge1145_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1146 : Fin frame288.rank → ℕ := ![2,4]
theorem edge1146_span : frame288.space ≤ frame573.space :=
  frame288.inclusion frame573 witness1146 (by decide)
def edge1146 : CertifiedEdge catalog where
  old := 288
  next := 573
  rank := 1
  good := by
    constructor
    · exact edge1146_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1147 : Fin frame288.rank → ℕ := ![4,8]
theorem edge1147_span : frame288.space ≤ frame622.space :=
  frame288.inclusion frame622 witness1147 (by decide)
def edge1147 : CertifiedEdge catalog where
  old := 288
  next := 622
  rank := 2
  good := by
    constructor
    · exact edge1147_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1148 : Fin frame288.rank → ℕ := ![2,4]
theorem edge1148_span : frame288.space ≤ frame625.space :=
  frame288.inclusion frame625 witness1148 (by decide)
def edge1148 : CertifiedEdge catalog where
  old := 288
  next := 625
  rank := 2
  good := by
    constructor
    · exact edge1148_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1149 : Fin frame289.rank → ℕ := ![1,6]
theorem edge1149_span : frame289.space ≤ frame570.space :=
  frame289.inclusion frame570 witness1149 (by decide)
def edge1149 : CertifiedEdge catalog where
  old := 289
  next := 570
  rank := 1
  good := by
    constructor
    · exact edge1149_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1150 : Fin frame289.rank → ℕ := ![1,4]
theorem edge1150_span : frame289.space ≤ frame572.space :=
  frame289.inclusion frame572 witness1150 (by decide)
def edge1150 : CertifiedEdge catalog where
  old := 289
  next := 572
  rank := 1
  good := by
    constructor
    · exact edge1150_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1151 : Fin frame289.rank → ℕ := ![9,4]
theorem edge1151_span : frame289.space ≤ frame624.space :=
  frame289.inclusion frame624 witness1151 (by decide)
def edge1151 : CertifiedEdge catalog where
  old := 289
  next := 624
  rank := 2
  good := by
    constructor
    · exact edge1151_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
