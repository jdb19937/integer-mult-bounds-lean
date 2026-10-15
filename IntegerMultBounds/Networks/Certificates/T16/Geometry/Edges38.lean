module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1216 : Fin frame310.rank → ℕ := ![65,88]
theorem edge1216_span : frame310.space ≤ frame771.space :=
  frame310.inclusion frame771 witness1216 (by decide)
def edge1216 : CertifiedEdge catalog where
  old := 310
  next := 771
  rank := 5
  good := by
    constructor
    · exact edge1216_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1217 : Fin frame310.rank → ℕ := ![65,72]
theorem edge1217_span : frame310.space ≤ frame772.space :=
  frame310.inclusion frame772 witness1217 (by decide)
def edge1217 : CertifiedEdge catalog where
  old := 310
  next := 772
  rank := 5
  good := by
    constructor
    · exact edge1217_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1218 : Fin frame311.rank → ℕ := ![1,4]
theorem edge1218_span : frame311.space ≤ frame320.space :=
  frame311.inclusion frame320 witness1218 (by decide)
def edge1218 : CertifiedEdge catalog where
  old := 311
  next := 320
  rank := 1
  good := by
    constructor
    · exact edge1218_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1219 : Fin frame311.rank → ℕ := ![1,4]
theorem edge1219_span : frame311.space ≤ frame325.space :=
  frame311.inclusion frame325 witness1219 (by decide)
def edge1219 : CertifiedEdge catalog where
  old := 311
  next := 325
  rank := 1
  good := by
    constructor
    · exact edge1219_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1220 : Fin frame312.rank → ℕ := ![1,4]
theorem edge1220_span : frame312.space ≤ frame321.space :=
  frame312.inclusion frame321 witness1220 (by decide)
def edge1220 : CertifiedEdge catalog where
  old := 312
  next := 321
  rank := 1
  good := by
    constructor
    · exact edge1220_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1221 : Fin frame312.rank → ℕ := ![1,4]
theorem edge1221_span : frame312.space ≤ frame324.space :=
  frame312.inclusion frame324 witness1221 (by decide)
def edge1221 : CertifiedEdge catalog where
  old := 312
  next := 324
  rank := 1
  good := by
    constructor
    · exact edge1221_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1222 : Fin frame313.rank → ℕ := ![1,4]
theorem edge1222_span : frame313.space ≤ frame322.space :=
  frame313.inclusion frame322 witness1222 (by decide)
def edge1222 : CertifiedEdge catalog where
  old := 313
  next := 322
  rank := 1
  good := by
    constructor
    · exact edge1222_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1223 : Fin frame313.rank → ℕ := ![1,4]
theorem edge1223_span : frame313.space ≤ frame323.space :=
  frame313.inclusion frame323 witness1223 (by decide)
def edge1223 : CertifiedEdge catalog where
  old := 313
  next := 323
  rank := 1
  good := by
    constructor
    · exact edge1223_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1224 : Fin frame314.rank → ℕ := ![1,4]
theorem edge1224_span : frame314.space ≤ frame319.space :=
  frame314.inclusion frame319 witness1224 (by decide)
def edge1224 : CertifiedEdge catalog where
  old := 314
  next := 319
  rank := 1
  good := by
    constructor
    · exact edge1224_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1225 : Fin frame314.rank → ℕ := ![1,4]
theorem edge1225_span : frame314.space ≤ frame326.space :=
  frame314.inclusion frame326 witness1225 (by decide)
def edge1225 : CertifiedEdge catalog where
  old := 314
  next := 326
  rank := 1
  good := by
    constructor
    · exact edge1225_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1226 : Fin frame315.rank → ℕ := ![2,4]
theorem edge1226_span : frame315.space ≤ frame321.space :=
  frame315.inclusion frame321 witness1226 (by decide)
def edge1226 : CertifiedEdge catalog where
  old := 315
  next := 321
  rank := 1
  good := by
    constructor
    · exact edge1226_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1227 : Fin frame315.rank → ℕ := ![2,4]
theorem edge1227_span : frame315.space ≤ frame323.space :=
  frame315.inclusion frame323 witness1227 (by decide)
def edge1227 : CertifiedEdge catalog where
  old := 315
  next := 323
  rank := 1
  good := by
    constructor
    · exact edge1227_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1228 : Fin frame316.rank → ℕ := ![2,4]
theorem edge1228_span : frame316.space ≤ frame319.space :=
  frame316.inclusion frame319 witness1228 (by decide)
def edge1228 : CertifiedEdge catalog where
  old := 316
  next := 319
  rank := 1
  good := by
    constructor
    · exact edge1228_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1229 : Fin frame316.rank → ℕ := ![2,4]
theorem edge1229_span : frame316.space ≤ frame325.space :=
  frame316.inclusion frame325 witness1229 (by decide)
def edge1229 : CertifiedEdge catalog where
  old := 316
  next := 325
  rank := 1
  good := by
    constructor
    · exact edge1229_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1230 : Fin frame317.rank → ℕ := ![1,4]
theorem edge1230_span : frame317.space ≤ frame576.space :=
  frame317.inclusion frame576 witness1230 (by decide)
def edge1230 : CertifiedEdge catalog where
  old := 317
  next := 576
  rank := 1
  good := by
    constructor
    · exact edge1230_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1231 : Fin frame317.rank → ℕ := ![1,4]
theorem edge1231_span : frame317.space ≤ frame579.space :=
  frame317.inclusion frame579 witness1231 (by decide)
def edge1231 : CertifiedEdge catalog where
  old := 317
  next := 579
  rank := 1
  good := by
    constructor
    · exact edge1231_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1232 : Fin frame317.rank → ℕ := ![1,12]
theorem edge1232_span : frame317.space ≤ frame626.space :=
  frame317.inclusion frame626 witness1232 (by decide)
def edge1232 : CertifiedEdge catalog where
  old := 317
  next := 626
  rank := 2
  good := by
    constructor
    · exact edge1232_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1233 : Fin frame317.rank → ℕ := ![9,4]
theorem edge1233_span : frame317.space ≤ frame629.space :=
  frame317.inclusion frame629 witness1233 (by decide)
def edge1233 : CertifiedEdge catalog where
  old := 317
  next := 629
  rank := 2
  good := by
    constructor
    · exact edge1233_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1234 : Fin frame318.rank → ℕ := ![2,4]
theorem edge1234_span : frame318.space ≤ frame576.space :=
  frame318.inclusion frame576 witness1234 (by decide)
def edge1234 : CertifiedEdge catalog where
  old := 318
  next := 576
  rank := 1
  good := by
    constructor
    · exact edge1234_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1235 : Fin frame318.rank → ℕ := ![2,4]
theorem edge1235_span : frame318.space ≤ frame578.space :=
  frame318.inclusion frame578 witness1235 (by decide)
def edge1235 : CertifiedEdge catalog where
  old := 318
  next := 578
  rank := 1
  good := by
    constructor
    · exact edge1235_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1236 : Fin frame318.rank → ℕ := ![10,4]
theorem edge1236_span : frame318.space ≤ frame628.space :=
  frame318.inclusion frame628 witness1236 (by decide)
def edge1236 : CertifiedEdge catalog where
  old := 318
  next := 628
  rank := 2
  good := by
    constructor
    · exact edge1236_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1237 : Fin frame318.rank → ℕ := ![6,88]
theorem edge1237_span : frame318.space ≤ frame770.space :=
  frame318.inclusion frame770 witness1237 (by decide)
def edge1237 : CertifiedEdge catalog where
  old := 318
  next := 770
  rank := 5
  good := by
    constructor
    · exact edge1237_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1238 : Fin frame319.rank → ℕ := ![9,2,12]
theorem edge1238_span : frame319.space ≤ frame327.space :=
  frame319.inclusion frame327 witness1238 (by decide)
def edge1238 : CertifiedEdge catalog where
  old := 319
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1238_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1239 : Fin frame319.rank → ℕ := ![9,34,12]
theorem edge1239_span : frame319.space ≤ frame644.space :=
  frame319.inclusion frame644 witness1239 (by decide)
def edge1239 : CertifiedEdge catalog where
  old := 319
  next := 644
  rank := 3
  good := by
    constructor
    · exact edge1239_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1240 : Fin frame319.rank → ℕ := ![9,34,12]
theorem edge1240_span : frame319.space ≤ frame694.space :=
  frame319.inclusion frame694 witness1240 (by decide)
def edge1240 : CertifiedEdge catalog where
  old := 319
  next := 694
  rank := 3
  good := by
    constructor
    · exact edge1240_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1241 : Fin frame320.rank → ℕ := ![1,10,12]
theorem edge1241_span : frame320.space ≤ frame327.space :=
  frame320.inclusion frame327 witness1241 (by decide)
def edge1241 : CertifiedEdge catalog where
  old := 320
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1241_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1242 : Fin frame320.rank → ℕ := ![33,10,12]
theorem edge1242_span : frame320.space ≤ frame645.space :=
  frame320.inclusion frame645 witness1242 (by decide)
def edge1242 : CertifiedEdge catalog where
  old := 320
  next := 645
  rank := 3
  good := by
    constructor
    · exact edge1242_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1243 : Fin frame320.rank → ℕ := ![33,10,12]
theorem edge1243_span : frame320.space ≤ frame695.space :=
  frame320.inclusion frame695 witness1243 (by decide)
def edge1243 : CertifiedEdge catalog where
  old := 320
  next := 695
  rank := 3
  good := by
    constructor
    · exact edge1243_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1244 : Fin frame321.rank → ℕ := ![1,2,4]
theorem edge1244_span : frame321.space ≤ frame327.space :=
  frame321.inclusion frame327 witness1244 (by decide)
def edge1244 : CertifiedEdge catalog where
  old := 321
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1244_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1245 : Fin frame321.rank → ℕ := ![1,2,4]
theorem edge1245_span : frame321.space ≤ frame652.space :=
  frame321.inclusion frame652 witness1245 (by decide)
def edge1245 : CertifiedEdge catalog where
  old := 321
  next := 652
  rank := 3
  good := by
    constructor
    · exact edge1245_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1246 : Fin frame321.rank → ℕ := ![1,2,4]
theorem edge1246_span : frame321.space ≤ frame688.space :=
  frame321.inclusion frame688 witness1246 (by decide)
def edge1246 : CertifiedEdge catalog where
  old := 321
  next := 688
  rank := 3
  good := by
    constructor
    · exact edge1246_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1247 : Fin frame322.rank → ℕ := ![9,10,4]
theorem edge1247_span : frame322.space ≤ frame327.space :=
  frame322.inclusion frame327 witness1247 (by decide)
def edge1247 : CertifiedEdge catalog where
  old := 322
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1247_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
