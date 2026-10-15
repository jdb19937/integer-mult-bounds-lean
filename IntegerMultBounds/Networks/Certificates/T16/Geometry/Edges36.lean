module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1152 : Fin frame289.rank → ℕ := ![35,24]
theorem edge1152_span : frame289.space ≤ frame766.space :=
  frame289.inclusion frame766 witness1152 (by decide)
def edge1152 : CertifiedEdge catalog where
  old := 289
  next := 766
  rank := 5
  good := by
    constructor
    · exact edge1152_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1153 : Fin frame290.rank → ℕ := ![1,2,8]
theorem edge1153_span : frame290.space ≤ frame298.space :=
  frame290.inclusion frame298 witness1153 (by decide)
def edge1153 : CertifiedEdge catalog where
  old := 290
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1153_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1154 : Fin frame290.rank → ℕ := ![1,34,56]
theorem edge1154_span : frame290.space ≤ frame642.space :=
  frame290.inclusion frame642 witness1154 (by decide)
def edge1154 : CertifiedEdge catalog where
  old := 290
  next := 642
  rank := 3
  good := by
    constructor
    · exact edge1154_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1155 : Fin frame290.rank → ℕ := ![19,4,40]
theorem edge1155_span : frame290.space ≤ frame686.space :=
  frame290.inclusion frame686 witness1155 (by decide)
def edge1155 : CertifiedEdge catalog where
  old := 290
  next := 686
  rank := 3
  good := by
    constructor
    · exact edge1155_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1156 : Fin frame291.rank → ℕ := ![9,10,4]
theorem edge1156_span : frame291.space ≤ frame298.space :=
  frame291.inclusion frame298 witness1156 (by decide)
def edge1156 : CertifiedEdge catalog where
  old := 291
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1156_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1157 : Fin frame291.rank → ℕ := ![57,18,20]
theorem edge1157_span : frame291.space ≤ frame643.space :=
  frame291.inclusion frame643 witness1157 (by decide)
def edge1157 : CertifiedEdge catalog where
  old := 291
  next := 643
  rank := 3
  good := by
    constructor
    · exact edge1157_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1158 : Fin frame291.rank → ℕ := ![51,52,40]
theorem edge1158_span : frame291.space ≤ frame687.space :=
  frame291.inclusion frame687 witness1158 (by decide)
def edge1158 : CertifiedEdge catalog where
  old := 291
  next := 687
  rank := 3
  good := by
    constructor
    · exact edge1158_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1159 : Fin frame292.rank → ℕ := ![5,6,8]
theorem edge1159_span : frame292.space ≤ frame298.space :=
  frame292.inclusion frame298 witness1159 (by decide)
def edge1159 : CertifiedEdge catalog where
  old := 292
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1159_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1160 : Fin frame292.rank → ℕ := ![43,44,48]
theorem edge1160_span : frame292.space ≤ frame650.space :=
  frame292.inclusion frame650 witness1160 (by decide)
def edge1160 : CertifiedEdge catalog where
  old := 292
  next := 650
  rank := 3
  good := by
    constructor
    · exact edge1160_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1161 : Fin frame292.rank → ℕ := ![57,18,20]
theorem edge1161_span : frame292.space ≤ frame696.space :=
  frame292.inclusion frame696 witness1161 (by decide)
def edge1161 : CertifiedEdge catalog where
  old := 292
  next := 696
  rank := 3
  good := by
    constructor
    · exact edge1161_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1162 : Fin frame293.rank → ℕ := ![1,2,4]
theorem edge1162_span : frame293.space ≤ frame298.space :=
  frame293.inclusion frame298 witness1162 (by decide)
def edge1162 : CertifiedEdge catalog where
  old := 293
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1162_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1163 : Fin frame293.rank → ℕ := ![19,4,40]
theorem edge1163_span : frame293.space ≤ frame651.space :=
  frame293.inclusion frame651 witness1163 (by decide)
def edge1163 : CertifiedEdge catalog where
  old := 293
  next := 651
  rank := 3
  good := by
    constructor
    · exact edge1163_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1164 : Fin frame293.rank → ℕ := ![1,34,52]
theorem edge1164_span : frame293.space ≤ frame697.space :=
  frame293.inclusion frame697 witness1164 (by decide)
def edge1164 : CertifiedEdge catalog where
  old := 293
  next := 697
  rank := 3
  good := by
    constructor
    · exact edge1164_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1165 : Fin frame294.rank → ℕ := ![9,2,4]
theorem edge1165_span : frame294.space ≤ frame298.space :=
  frame294.inclusion frame298 witness1165 (by decide)
def edge1165 : CertifiedEdge catalog where
  old := 294
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1165_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1166 : Fin frame294.rank → ℕ := ![51,4,8]
theorem edge1166_span : frame294.space ≤ frame674.space :=
  frame294.inclusion frame674 witness1166 (by decide)
def edge1166 : CertifiedEdge catalog where
  old := 294
  next := 674
  rank := 3
  good := by
    constructor
    · exact edge1166_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1167 : Fin frame294.rank → ℕ := ![25,34,36]
theorem edge1167_span : frame294.space ≤ frame722.space :=
  frame294.inclusion frame722 witness1167 (by decide)
def edge1167 : CertifiedEdge catalog where
  old := 294
  next := 722
  rank := 3
  good := by
    constructor
    · exact edge1167_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1168 : Fin frame295.rank → ℕ := ![1,6,8]
theorem edge1168_span : frame295.space ≤ frame298.space :=
  frame295.inclusion frame298 witness1168 (by decide)
def edge1168 : CertifiedEdge catalog where
  old := 295
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1168_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1169 : Fin frame295.rank → ℕ := ![35,12,16]
theorem edge1169_span : frame295.space ≤ frame675.space :=
  frame295.inclusion frame675 witness1169 (by decide)
def edge1169 : CertifiedEdge catalog where
  old := 295
  next := 675
  rank := 3
  good := by
    constructor
    · exact edge1169_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1170 : Fin frame295.rank → ℕ := ![17,38,40]
theorem edge1170_span : frame295.space ≤ frame723.space :=
  frame295.inclusion frame723 witness1170 (by decide)
def edge1170 : CertifiedEdge catalog where
  old := 295
  next := 723
  rank := 3
  good := by
    constructor
    · exact edge1170_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1171 : Fin frame296.rank → ℕ := ![1,10,4]
theorem edge1171_span : frame296.space ≤ frame298.space :=
  frame296.inclusion frame298 witness1171 (by decide)
def edge1171 : CertifiedEdge catalog where
  old := 296
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1171_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1172 : Fin frame296.rank → ℕ := ![17,42,36]
theorem edge1172_span : frame296.space ≤ frame684.space :=
  frame296.inclusion frame684 witness1172 (by decide)
def edge1172 : CertifiedEdge catalog where
  old := 296
  next := 684
  rank := 3
  good := by
    constructor
    · exact edge1172_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1173 : Fin frame296.rank → ℕ := ![35,20,8]
theorem edge1173_span : frame296.space ≤ frame730.space :=
  frame296.inclusion frame730 witness1173 (by decide)
def edge1173 : CertifiedEdge catalog where
  old := 296
  next := 730
  rank := 3
  good := by
    constructor
    · exact edge1173_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1174 : Fin frame297.rank → ℕ := ![5,2,8]
theorem edge1174_span : frame297.space ≤ frame298.space :=
  frame297.inclusion frame298 witness1174 (by decide)
def edge1174 : CertifiedEdge catalog where
  old := 297
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1174_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1175 : Fin frame297.rank → ℕ := ![21,34,40]
theorem edge1175_span : frame297.space ≤ frame685.space :=
  frame297.inclusion frame685 witness1175 (by decide)
def edge1175 : CertifiedEdge catalog where
  old := 297
  next := 685
  rank := 3
  good := by
    constructor
    · exact edge1175_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1176 : Fin frame297.rank → ℕ := ![43,4,16]
theorem edge1176_span : frame297.space ≤ frame731.space :=
  frame297.inclusion frame731 witness1176 (by decide)
def edge1176 : CertifiedEdge catalog where
  old := 297
  next := 731
  rank := 3
  good := by
    constructor
    · exact edge1176_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1177 : Fin frame298.rank → ℕ := ![35,388,328,208]
theorem edge1177_span : frame298.space ≤ frame1.space :=
  frame298.inclusion frame1 witness1177 (by decide)
def edge1177 : CertifiedEdge catalog where
  old := 298
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1177_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1178 : Fin frame298.rank → ℕ := ![35,132,72,208]
theorem edge1178_span : frame298.space ≤ frame416.space :=
  frame298.inclusion frame416 witness1178 (by decide)
def edge1178 : CertifiedEdge catalog where
  old := 298
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge1178_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1179 : Fin frame298.rank → ℕ := ![35,196,136,80]
theorem edge1179_span : frame298.space ≤ frame418.space :=
  frame298.inclusion frame418 witness1179 (by decide)
def edge1179 : CertifiedEdge catalog where
  old := 298
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge1179_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1180 : Fin frame298.rank → ℕ := ![35,132,200,80]
theorem edge1180_span : frame298.space ≤ frame419.space :=
  frame298.inclusion frame419 witness1180 (by decide)
def edge1180 : CertifiedEdge catalog where
  old := 298
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge1180_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1181 : Fin frame298.rank → ℕ := ![35,132,72,208]
theorem edge1181_span : frame298.space ≤ frame421.space :=
  frame298.inclusion frame421 witness1181 (by decide)
def edge1181 : CertifiedEdge catalog where
  old := 298
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge1181_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1182 : Fin frame299.rank → ℕ := ![3]
theorem edge1182_span : frame299.space ≤ frame307.space :=
  frame299.inclusion frame307 witness1182 (by decide)
def edge1182 : CertifiedEdge catalog where
  old := 299
  next := 307
  rank := 1
  good := by
    constructor
    · exact edge1182_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1183 : Fin frame299.rank → ℕ := ![1]
theorem edge1183_span : frame299.space ≤ frame308.space :=
  frame299.inclusion frame308 witness1183 (by decide)
def edge1183 : CertifiedEdge catalog where
  old := 299
  next := 308
  rank := 1
  good := by
    constructor
    · exact edge1183_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
