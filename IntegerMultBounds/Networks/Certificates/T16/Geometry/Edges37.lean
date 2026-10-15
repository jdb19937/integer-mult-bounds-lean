module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1184 : Fin frame299.rank → ℕ := ![1]
theorem edge1184_span : frame299.space ≤ frame309.space :=
  frame299.inclusion frame309 witness1184 (by decide)
def edge1184 : CertifiedEdge catalog where
  old := 299
  next := 309
  rank := 1
  good := by
    constructor
    · exact edge1184_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1185 : Fin frame300.rank → ℕ := ![1]
theorem edge1185_span : frame300.space ≤ frame310.space :=
  frame300.inclusion frame310 witness1185 (by decide)
def edge1185 : CertifiedEdge catalog where
  old := 300
  next := 310
  rank := 1
  good := by
    constructor
    · exact edge1185_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1186 : Fin frame300.rank → ℕ := ![1]
theorem edge1186_span : frame300.space ≤ frame311.space :=
  frame300.inclusion frame311 witness1186 (by decide)
def edge1186 : CertifiedEdge catalog where
  old := 300
  next := 311
  rank := 1
  good := by
    constructor
    · exact edge1186_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1187 : Fin frame300.rank → ℕ := ![1]
theorem edge1187_span : frame300.space ≤ frame312.space :=
  frame300.inclusion frame312 witness1187 (by decide)
def edge1187 : CertifiedEdge catalog where
  old := 300
  next := 312
  rank := 1
  good := by
    constructor
    · exact edge1187_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1188 : Fin frame301.rank → ℕ := ![3]
theorem edge1188_span : frame301.space ≤ frame310.space :=
  frame301.inclusion frame310 witness1188 (by decide)
def edge1188 : CertifiedEdge catalog where
  old := 301
  next := 310
  rank := 1
  good := by
    constructor
    · exact edge1188_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1189 : Fin frame301.rank → ℕ := ![1]
theorem edge1189_span : frame301.space ≤ frame313.space :=
  frame301.inclusion frame313 witness1189 (by decide)
def edge1189 : CertifiedEdge catalog where
  old := 301
  next := 313
  rank := 1
  good := by
    constructor
    · exact edge1189_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1190 : Fin frame301.rank → ℕ := ![1]
theorem edge1190_span : frame301.space ≤ frame314.space :=
  frame301.inclusion frame314 witness1190 (by decide)
def edge1190 : CertifiedEdge catalog where
  old := 301
  next := 314
  rank := 1
  good := by
    constructor
    · exact edge1190_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1191 : Fin frame302.rank → ℕ := ![1]
theorem edge1191_span : frame302.space ≤ frame307.space :=
  frame302.inclusion frame307 witness1191 (by decide)
def edge1191 : CertifiedEdge catalog where
  old := 302
  next := 307
  rank := 1
  good := by
    constructor
    · exact edge1191_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1192 : Fin frame302.rank → ℕ := ![1]
theorem edge1192_span : frame302.space ≤ frame315.space :=
  frame302.inclusion frame315 witness1192 (by decide)
def edge1192 : CertifiedEdge catalog where
  old := 302
  next := 315
  rank := 1
  good := by
    constructor
    · exact edge1192_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1193 : Fin frame302.rank → ℕ := ![1]
theorem edge1193_span : frame302.space ≤ frame316.space :=
  frame302.inclusion frame316 witness1193 (by decide)
def edge1193 : CertifiedEdge catalog where
  old := 302
  next := 316
  rank := 1
  good := by
    constructor
    · exact edge1193_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1194 : Fin frame303.rank → ℕ := ![3]
theorem edge1194_span : frame303.space ≤ frame311.space :=
  frame303.inclusion frame311 witness1194 (by decide)
def edge1194 : CertifiedEdge catalog where
  old := 303
  next := 311
  rank := 1
  good := by
    constructor
    · exact edge1194_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1195 : Fin frame303.rank → ℕ := ![3]
theorem edge1195_span : frame303.space ≤ frame313.space :=
  frame303.inclusion frame313 witness1195 (by decide)
def edge1195 : CertifiedEdge catalog where
  old := 303
  next := 313
  rank := 1
  good := by
    constructor
    · exact edge1195_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1196 : Fin frame303.rank → ℕ := ![3]
theorem edge1196_span : frame303.space ≤ frame317.space :=
  frame303.inclusion frame317 witness1196 (by decide)
def edge1196 : CertifiedEdge catalog where
  old := 303
  next := 317
  rank := 1
  good := by
    constructor
    · exact edge1196_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1197 : Fin frame304.rank → ℕ := ![3]
theorem edge1197_span : frame304.space ≤ frame308.space :=
  frame304.inclusion frame308 witness1197 (by decide)
def edge1197 : CertifiedEdge catalog where
  old := 304
  next := 308
  rank := 1
  good := by
    constructor
    · exact edge1197_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1198 : Fin frame304.rank → ℕ := ![3]
theorem edge1198_span : frame304.space ≤ frame315.space :=
  frame304.inclusion frame315 witness1198 (by decide)
def edge1198 : CertifiedEdge catalog where
  old := 304
  next := 315
  rank := 1
  good := by
    constructor
    · exact edge1198_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1199 : Fin frame304.rank → ℕ := ![1]
theorem edge1199_span : frame304.space ≤ frame318.space :=
  frame304.inclusion frame318 witness1199 (by decide)
def edge1199 : CertifiedEdge catalog where
  old := 304
  next := 318
  rank := 1
  good := by
    constructor
    · exact edge1199_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1200 : Fin frame305.rank → ℕ := ![3]
theorem edge1200_span : frame305.space ≤ frame309.space :=
  frame305.inclusion frame309 witness1200 (by decide)
def edge1200 : CertifiedEdge catalog where
  old := 305
  next := 309
  rank := 1
  good := by
    constructor
    · exact edge1200_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1201 : Fin frame305.rank → ℕ := ![3]
theorem edge1201_span : frame305.space ≤ frame316.space :=
  frame305.inclusion frame316 witness1201 (by decide)
def edge1201 : CertifiedEdge catalog where
  old := 305
  next := 316
  rank := 1
  good := by
    constructor
    · exact edge1201_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1202 : Fin frame305.rank → ℕ := ![3]
theorem edge1202_span : frame305.space ≤ frame318.space :=
  frame305.inclusion frame318 witness1202 (by decide)
def edge1202 : CertifiedEdge catalog where
  old := 305
  next := 318
  rank := 1
  good := by
    constructor
    · exact edge1202_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1203 : Fin frame306.rank → ℕ := ![3]
theorem edge1203_span : frame306.space ≤ frame312.space :=
  frame306.inclusion frame312 witness1203 (by decide)
def edge1203 : CertifiedEdge catalog where
  old := 306
  next := 312
  rank := 1
  good := by
    constructor
    · exact edge1203_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1204 : Fin frame306.rank → ℕ := ![3]
theorem edge1204_span : frame306.space ≤ frame314.space :=
  frame306.inclusion frame314 witness1204 (by decide)
def edge1204 : CertifiedEdge catalog where
  old := 306
  next := 314
  rank := 1
  good := by
    constructor
    · exact edge1204_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1205 : Fin frame306.rank → ℕ := ![1]
theorem edge1205_span : frame306.space ≤ frame317.space :=
  frame306.inclusion frame317 witness1205 (by decide)
def edge1205 : CertifiedEdge catalog where
  old := 306
  next := 317
  rank := 1
  good := by
    constructor
    · exact edge1205_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1206 : Fin frame307.rank → ℕ := ![2,4]
theorem edge1206_span : frame307.space ≤ frame577.space :=
  frame307.inclusion frame577 witness1206 (by decide)
def edge1206 : CertifiedEdge catalog where
  old := 307
  next := 577
  rank := 1
  good := by
    constructor
    · exact edge1206_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1207 : Fin frame307.rank → ℕ := ![2,4]
theorem edge1207_span : frame307.space ≤ frame579.space :=
  frame307.inclusion frame579 witness1207 (by decide)
def edge1207 : CertifiedEdge catalog where
  old := 307
  next := 579
  rank := 1
  good := by
    constructor
    · exact edge1207_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1208 : Fin frame307.rank → ℕ := ![2,8]
theorem edge1208_span : frame307.space ≤ frame627.space :=
  frame307.inclusion frame627 witness1208 (by decide)
def edge1208 : CertifiedEdge catalog where
  old := 307
  next := 627
  rank := 2
  good := by
    constructor
    · exact edge1208_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1209 : Fin frame307.rank → ℕ := ![66,88]
theorem edge1209_span : frame307.space ≤ frame770.space :=
  frame307.inclusion frame770 witness1209 (by decide)
def edge1209 : CertifiedEdge catalog where
  old := 307
  next := 770
  rank := 5
  good := by
    constructor
    · exact edge1209_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1210 : Fin frame308.rank → ℕ := ![2,4]
theorem edge1210_span : frame308.space ≤ frame320.space :=
  frame308.inclusion frame320 witness1210 (by decide)
def edge1210 : CertifiedEdge catalog where
  old := 308
  next := 320
  rank := 1
  good := by
    constructor
    · exact edge1210_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1211 : Fin frame308.rank → ℕ := ![2,4]
theorem edge1211_span : frame308.space ≤ frame326.space :=
  frame308.inclusion frame326 witness1211 (by decide)
def edge1211 : CertifiedEdge catalog where
  old := 308
  next := 326
  rank := 1
  good := by
    constructor
    · exact edge1211_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1212 : Fin frame309.rank → ℕ := ![2,4]
theorem edge1212_span : frame309.space ≤ frame322.space :=
  frame309.inclusion frame322 witness1212 (by decide)
def edge1212 : CertifiedEdge catalog where
  old := 309
  next := 322
  rank := 1
  good := by
    constructor
    · exact edge1212_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1213 : Fin frame309.rank → ℕ := ![2,4]
theorem edge1213_span : frame309.space ≤ frame324.space :=
  frame309.inclusion frame324 witness1213 (by decide)
def edge1213 : CertifiedEdge catalog where
  old := 309
  next := 324
  rank := 1
  good := by
    constructor
    · exact edge1213_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1214 : Fin frame310.rank → ℕ := ![1,4]
theorem edge1214_span : frame310.space ≤ frame577.space :=
  frame310.inclusion frame577 witness1214 (by decide)
def edge1214 : CertifiedEdge catalog where
  old := 310
  next := 577
  rank := 1
  good := by
    constructor
    · exact edge1214_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1215 : Fin frame310.rank → ℕ := ![1,4]
theorem edge1215_span : frame310.space ≤ frame578.space :=
  frame310.inclusion frame578 witness1215 (by decide)
def edge1215 : CertifiedEdge catalog where
  old := 310
  next := 578
  rank := 1
  good := by
    constructor
    · exact edge1215_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
