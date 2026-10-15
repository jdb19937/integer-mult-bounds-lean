module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1248 : Fin frame322.rank → ℕ := ![9,10,20]
theorem edge1248_span : frame322.space ≤ frame653.space :=
  frame322.inclusion frame653 witness1248 (by decide)
def edge1248 : CertifiedEdge catalog where
  old := 322
  next := 653
  rank := 3
  good := by
    constructor
    · exact edge1248_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1249 : Fin frame322.rank → ℕ := ![9,10,20]
theorem edge1249_span : frame322.space ≤ frame689.space :=
  frame322.inclusion frame689 witness1249 (by decide)
def edge1249 : CertifiedEdge catalog where
  old := 322
  next := 689
  rank := 3
  good := by
    constructor
    · exact edge1249_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1250 : Fin frame323.rank → ℕ := ![9,2,4]
theorem edge1250_span : frame323.space ≤ frame327.space :=
  frame323.inclusion frame327 witness1250 (by decide)
def edge1250 : CertifiedEdge catalog where
  old := 323
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1250_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1251 : Fin frame323.rank → ℕ := ![25,2,36]
theorem edge1251_span : frame323.space ≤ frame682.space :=
  frame323.inclusion frame682 witness1251 (by decide)
def edge1251 : CertifiedEdge catalog where
  old := 323
  next := 682
  rank := 3
  good := by
    constructor
    · exact edge1251_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1252 : Fin frame323.rank → ℕ := ![25,2,36]
theorem edge1252_span : frame323.space ≤ frame724.space :=
  frame323.inclusion frame724 witness1252 (by decide)
def edge1252 : CertifiedEdge catalog where
  old := 323
  next := 724
  rank := 3
  good := by
    constructor
    · exact edge1252_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1253 : Fin frame324.rank → ℕ := ![1,10,4]
theorem edge1253_span : frame324.space ≤ frame327.space :=
  frame324.inclusion frame327 witness1253 (by decide)
def edge1253 : CertifiedEdge catalog where
  old := 324
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1253_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1254 : Fin frame324.rank → ℕ := ![1,26,36]
theorem edge1254_span : frame324.space ≤ frame683.space :=
  frame324.inclusion frame683 witness1254 (by decide)
def edge1254 : CertifiedEdge catalog where
  old := 324
  next := 683
  rank := 3
  good := by
    constructor
    · exact edge1254_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1255 : Fin frame324.rank → ℕ := ![1,26,36]
theorem edge1255_span : frame324.space ≤ frame725.space :=
  frame324.inclusion frame725 witness1255 (by decide)
def edge1255 : CertifiedEdge catalog where
  old := 324
  next := 725
  rank := 3
  good := by
    constructor
    · exact edge1255_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1256 : Fin frame325.rank → ℕ := ![1,2,12]
theorem edge1256_span : frame325.space ≤ frame327.space :=
  frame325.inclusion frame327 witness1256 (by decide)
def edge1256 : CertifiedEdge catalog where
  old := 325
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1256_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1257 : Fin frame325.rank → ℕ := ![33,34,28]
theorem edge1257_span : frame325.space ≤ frame676.space :=
  frame325.inclusion frame676 witness1257 (by decide)
def edge1257 : CertifiedEdge catalog where
  old := 325
  next := 676
  rank := 3
  good := by
    constructor
    · exact edge1257_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1258 : Fin frame325.rank → ℕ := ![33,34,28]
theorem edge1258_span : frame325.space ≤ frame732.space :=
  frame325.inclusion frame732 witness1258 (by decide)
def edge1258 : CertifiedEdge catalog where
  old := 325
  next := 732
  rank := 3
  good := by
    constructor
    · exact edge1258_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1259 : Fin frame326.rank → ℕ := ![9,10,12]
theorem edge1259_span : frame326.space ≤ frame327.space :=
  frame326.inclusion frame327 witness1259 (by decide)
def edge1259 : CertifiedEdge catalog where
  old := 326
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1259_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1260 : Fin frame326.rank → ℕ := ![25,26,28]
theorem edge1260_span : frame326.space ≤ frame677.space :=
  frame326.inclusion frame677 witness1260 (by decide)
def edge1260 : CertifiedEdge catalog where
  old := 326
  next := 677
  rank := 3
  good := by
    constructor
    · exact edge1260_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1261 : Fin frame326.rank → ℕ := ![25,26,28]
theorem edge1261_span : frame326.space ≤ frame733.space :=
  frame326.inclusion frame733 witness1261 (by decide)
def edge1261 : CertifiedEdge catalog where
  old := 326
  next := 733
  rank := 3
  good := by
    constructor
    · exact edge1261_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1262 : Fin frame327.rank → ℕ := ![385,386,420,408]
theorem edge1262_span : frame327.space ≤ frame1.space :=
  frame327.inclusion frame1 witness1262 (by decide)
def edge1262 : CertifiedEdge catalog where
  old := 327
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1262_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1263 : Fin frame327.rank → ℕ := ![129,130,164,152]
theorem edge1263_span : frame327.space ≤ frame416.space :=
  frame327.inclusion frame416 witness1263 (by decide)
def edge1263 : CertifiedEdge catalog where
  old := 327
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge1263_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1264 : Fin frame327.rank → ℕ := ![193,194,228,216]
theorem edge1264_span : frame327.space ≤ frame418.space :=
  frame327.inclusion frame418 witness1264 (by decide)
def edge1264 : CertifiedEdge catalog where
  old := 327
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge1264_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1265 : Fin frame327.rank → ℕ := ![129,130,164,152]
theorem edge1265_span : frame327.space ≤ frame420.space :=
  frame327.inclusion frame420 witness1265 (by decide)
def edge1265 : CertifiedEdge catalog where
  old := 327
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge1265_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1266 : Fin frame327.rank → ℕ := ![193,194,228,216]
theorem edge1266_span : frame327.space ≤ frame422.space :=
  frame327.inclusion frame422 witness1266 (by decide)
def edge1266 : CertifiedEdge catalog where
  old := 327
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge1266_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1267 : Fin frame328.rank → ℕ := ![1]
theorem edge1267_span : frame328.space ≤ frame336.space :=
  frame328.inclusion frame336 witness1267 (by decide)
def edge1267 : CertifiedEdge catalog where
  old := 328
  next := 336
  rank := 1
  good := by
    constructor
    · exact edge1267_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1268 : Fin frame328.rank → ℕ := ![1]
theorem edge1268_span : frame328.space ≤ frame337.space :=
  frame328.inclusion frame337 witness1268 (by decide)
def edge1268 : CertifiedEdge catalog where
  old := 328
  next := 337
  rank := 1
  good := by
    constructor
    · exact edge1268_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1269 : Fin frame328.rank → ℕ := ![1]
theorem edge1269_span : frame328.space ≤ frame338.space :=
  frame328.inclusion frame338 witness1269 (by decide)
def edge1269 : CertifiedEdge catalog where
  old := 328
  next := 338
  rank := 1
  good := by
    constructor
    · exact edge1269_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1270 : Fin frame329.rank → ℕ := ![1]
theorem edge1270_span : frame329.space ≤ frame339.space :=
  frame329.inclusion frame339 witness1270 (by decide)
def edge1270 : CertifiedEdge catalog where
  old := 329
  next := 339
  rank := 1
  good := by
    constructor
    · exact edge1270_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1271 : Fin frame329.rank → ℕ := ![1]
theorem edge1271_span : frame329.space ≤ frame340.space :=
  frame329.inclusion frame340 witness1271 (by decide)
def edge1271 : CertifiedEdge catalog where
  old := 329
  next := 340
  rank := 1
  good := by
    constructor
    · exact edge1271_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1272 : Fin frame329.rank → ℕ := ![1]
theorem edge1272_span : frame329.space ≤ frame341.space :=
  frame329.inclusion frame341 witness1272 (by decide)
def edge1272 : CertifiedEdge catalog where
  old := 329
  next := 341
  rank := 1
  good := by
    constructor
    · exact edge1272_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1273 : Fin frame330.rank → ℕ := ![3]
theorem edge1273_span : frame330.space ≤ frame339.space :=
  frame330.inclusion frame339 witness1273 (by decide)
def edge1273 : CertifiedEdge catalog where
  old := 330
  next := 339
  rank := 1
  good := by
    constructor
    · exact edge1273_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1274 : Fin frame330.rank → ℕ := ![1]
theorem edge1274_span : frame330.space ≤ frame342.space :=
  frame330.inclusion frame342 witness1274 (by decide)
def edge1274 : CertifiedEdge catalog where
  old := 330
  next := 342
  rank := 1
  good := by
    constructor
    · exact edge1274_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1275 : Fin frame330.rank → ℕ := ![1]
theorem edge1275_span : frame330.space ≤ frame343.space :=
  frame330.inclusion frame343 witness1275 (by decide)
def edge1275 : CertifiedEdge catalog where
  old := 330
  next := 343
  rank := 1
  good := by
    constructor
    · exact edge1275_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1276 : Fin frame331.rank → ℕ := ![3]
theorem edge1276_span : frame331.space ≤ frame336.space :=
  frame331.inclusion frame336 witness1276 (by decide)
def edge1276 : CertifiedEdge catalog where
  old := 331
  next := 336
  rank := 1
  good := by
    constructor
    · exact edge1276_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1277 : Fin frame331.rank → ℕ := ![1]
theorem edge1277_span : frame331.space ≤ frame344.space :=
  frame331.inclusion frame344 witness1277 (by decide)
def edge1277 : CertifiedEdge catalog where
  old := 331
  next := 344
  rank := 1
  good := by
    constructor
    · exact edge1277_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1278 : Fin frame331.rank → ℕ := ![1]
theorem edge1278_span : frame331.space ≤ frame345.space :=
  frame331.inclusion frame345 witness1278 (by decide)
def edge1278 : CertifiedEdge catalog where
  old := 331
  next := 345
  rank := 1
  good := by
    constructor
    · exact edge1278_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1279 : Fin frame332.rank → ℕ := ![3]
theorem edge1279_span : frame332.space ≤ frame340.space :=
  frame332.inclusion frame340 witness1279 (by decide)
def edge1279 : CertifiedEdge catalog where
  old := 332
  next := 340
  rank := 1
  good := by
    constructor
    · exact edge1279_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
