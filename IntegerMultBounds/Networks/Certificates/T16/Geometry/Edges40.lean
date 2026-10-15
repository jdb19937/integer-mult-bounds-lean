module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1280 : Fin frame332.rank → ℕ := ![3]
theorem edge1280_span : frame332.space ≤ frame342.space :=
  frame332.inclusion frame342 witness1280 (by decide)
def edge1280 : CertifiedEdge catalog where
  old := 332
  next := 342
  rank := 1
  good := by
    constructor
    · exact edge1280_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1281 : Fin frame332.rank → ℕ := ![1]
theorem edge1281_span : frame332.space ≤ frame346.space :=
  frame332.inclusion frame346 witness1281 (by decide)
def edge1281 : CertifiedEdge catalog where
  old := 332
  next := 346
  rank := 1
  good := by
    constructor
    · exact edge1281_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1282 : Fin frame333.rank → ℕ := ![3]
theorem edge1282_span : frame333.space ≤ frame337.space :=
  frame333.inclusion frame337 witness1282 (by decide)
def edge1282 : CertifiedEdge catalog where
  old := 333
  next := 337
  rank := 1
  good := by
    constructor
    · exact edge1282_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1283 : Fin frame333.rank → ℕ := ![3]
theorem edge1283_span : frame333.space ≤ frame344.space :=
  frame333.inclusion frame344 witness1283 (by decide)
def edge1283 : CertifiedEdge catalog where
  old := 333
  next := 344
  rank := 1
  good := by
    constructor
    · exact edge1283_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1284 : Fin frame333.rank → ℕ := ![1]
theorem edge1284_span : frame333.space ≤ frame347.space :=
  frame333.inclusion frame347 witness1284 (by decide)
def edge1284 : CertifiedEdge catalog where
  old := 333
  next := 347
  rank := 1
  good := by
    constructor
    · exact edge1284_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1285 : Fin frame334.rank → ℕ := ![3]
theorem edge1285_span : frame334.space ≤ frame338.space :=
  frame334.inclusion frame338 witness1285 (by decide)
def edge1285 : CertifiedEdge catalog where
  old := 334
  next := 338
  rank := 1
  good := by
    constructor
    · exact edge1285_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1286 : Fin frame334.rank → ℕ := ![3]
theorem edge1286_span : frame334.space ≤ frame345.space :=
  frame334.inclusion frame345 witness1286 (by decide)
def edge1286 : CertifiedEdge catalog where
  old := 334
  next := 345
  rank := 1
  good := by
    constructor
    · exact edge1286_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1287 : Fin frame334.rank → ℕ := ![3]
theorem edge1287_span : frame334.space ≤ frame347.space :=
  frame334.inclusion frame347 witness1287 (by decide)
def edge1287 : CertifiedEdge catalog where
  old := 334
  next := 347
  rank := 1
  good := by
    constructor
    · exact edge1287_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1288 : Fin frame335.rank → ℕ := ![3]
theorem edge1288_span : frame335.space ≤ frame341.space :=
  frame335.inclusion frame341 witness1288 (by decide)
def edge1288 : CertifiedEdge catalog where
  old := 335
  next := 341
  rank := 1
  good := by
    constructor
    · exact edge1288_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1289 : Fin frame335.rank → ℕ := ![3]
theorem edge1289_span : frame335.space ≤ frame343.space :=
  frame335.inclusion frame343 witness1289 (by decide)
def edge1289 : CertifiedEdge catalog where
  old := 335
  next := 343
  rank := 1
  good := by
    constructor
    · exact edge1289_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1290 : Fin frame335.rank → ℕ := ![3]
theorem edge1290_span : frame335.space ≤ frame346.space :=
  frame335.inclusion frame346 witness1290 (by decide)
def edge1290 : CertifiedEdge catalog where
  old := 335
  next := 346
  rank := 1
  good := by
    constructor
    · exact edge1290_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1291 : Fin frame336.rank → ℕ := ![1,4]
theorem edge1291_span : frame336.space ≤ frame455.space :=
  frame336.inclusion frame455 witness1291 (by decide)
def edge1291 : CertifiedEdge catalog where
  old := 336
  next := 455
  rank := 1
  good := by
    constructor
    · exact edge1291_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1292 : Fin frame336.rank → ℕ := ![33,40]
theorem edge1292_span : frame336.space ≤ frame461.space :=
  frame336.inclusion frame461 witness1292 (by decide)
def edge1292 : CertifiedEdge catalog where
  old := 336
  next := 461
  rank := 4
  good := by
    constructor
    · exact edge1292_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1293 : Fin frame336.rank → ℕ := ![1,6]
theorem edge1293_span : frame336.space ≤ frame469.space :=
  frame336.inclusion frame469 witness1293 (by decide)
def edge1293 : CertifiedEdge catalog where
  old := 336
  next := 469
  rank := 1
  good := by
    constructor
    · exact edge1293_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1294 : Fin frame336.rank → ℕ := ![17,24]
theorem edge1294_span : frame336.space ≤ frame475.space :=
  frame336.inclusion frame475 witness1294 (by decide)
def edge1294 : CertifiedEdge catalog where
  old := 336
  next := 475
  rank := 4
  good := by
    constructor
    · exact edge1294_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1295 : Fin frame337.rank → ℕ := ![1,4]
theorem edge1295_span : frame337.space ≤ frame349.space :=
  frame337.inclusion frame349 witness1295 (by decide)
def edge1295 : CertifiedEdge catalog where
  old := 337
  next := 349
  rank := 1
  good := by
    constructor
    · exact edge1295_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1296 : Fin frame337.rank → ℕ := ![1,4]
theorem edge1296_span : frame337.space ≤ frame355.space :=
  frame337.inclusion frame355 witness1296 (by decide)
def edge1296 : CertifiedEdge catalog where
  old := 337
  next := 355
  rank := 1
  good := by
    constructor
    · exact edge1296_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1297 : Fin frame338.rank → ℕ := ![1,4]
theorem edge1297_span : frame338.space ≤ frame351.space :=
  frame338.inclusion frame351 witness1297 (by decide)
def edge1297 : CertifiedEdge catalog where
  old := 338
  next := 351
  rank := 1
  good := by
    constructor
    · exact edge1297_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1298 : Fin frame338.rank → ℕ := ![1,4]
theorem edge1298_span : frame338.space ≤ frame353.space :=
  frame338.inclusion frame353 witness1298 (by decide)
def edge1298 : CertifiedEdge catalog where
  old := 338
  next := 353
  rank := 1
  good := by
    constructor
    · exact edge1298_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1299 : Fin frame339.rank → ℕ := ![1,4]
theorem edge1299_span : frame339.space ≤ frame454.space :=
  frame339.inclusion frame454 witness1299 (by decide)
def edge1299 : CertifiedEdge catalog where
  old := 339
  next := 454
  rank := 1
  good := by
    constructor
    · exact edge1299_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1300 : Fin frame339.rank → ℕ := ![2,8]
theorem edge1300_span : frame339.space ≤ frame458.space :=
  frame339.inclusion frame458 witness1300 (by decide)
def edge1300 : CertifiedEdge catalog where
  old := 339
  next := 458
  rank := 3
  good := by
    constructor
    · exact edge1300_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1301 : Fin frame339.rank → ℕ := ![1,6]
theorem edge1301_span : frame339.space ≤ frame526.space :=
  frame339.inclusion frame526 witness1301 (by decide)
def edge1301 : CertifiedEdge catalog where
  old := 339
  next := 526
  rank := 1
  good := by
    constructor
    · exact edge1301_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1302 : Fin frame339.rank → ℕ := ![2,8]
theorem edge1302_span : frame339.space ≤ frame530.space :=
  frame339.inclusion frame530 witness1302 (by decide)
def edge1302 : CertifiedEdge catalog where
  old := 339
  next := 530
  rank := 2
  good := by
    constructor
    · exact edge1302_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1303 : Fin frame340.rank → ℕ := ![2,4]
theorem edge1303_span : frame340.space ≤ frame349.space :=
  frame340.inclusion frame349 witness1303 (by decide)
def edge1303 : CertifiedEdge catalog where
  old := 340
  next := 349
  rank := 1
  good := by
    constructor
    · exact edge1303_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1304 : Fin frame340.rank → ℕ := ![2,4]
theorem edge1304_span : frame340.space ≤ frame354.space :=
  frame340.inclusion frame354 witness1304 (by decide)
def edge1304 : CertifiedEdge catalog where
  old := 340
  next := 354
  rank := 1
  good := by
    constructor
    · exact edge1304_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1305 : Fin frame341.rank → ℕ := ![2,4]
theorem edge1305_span : frame341.space ≤ frame350.space :=
  frame341.inclusion frame350 witness1305 (by decide)
def edge1305 : CertifiedEdge catalog where
  old := 341
  next := 350
  rank := 1
  good := by
    constructor
    · exact edge1305_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1306 : Fin frame341.rank → ℕ := ![2,4]
theorem edge1306_span : frame341.space ≤ frame353.space :=
  frame341.inclusion frame353 witness1306 (by decide)
def edge1306 : CertifiedEdge catalog where
  old := 341
  next := 353
  rank := 1
  good := by
    constructor
    · exact edge1306_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1307 : Fin frame342.rank → ℕ := ![2,4]
theorem edge1307_span : frame342.space ≤ frame351.space :=
  frame342.inclusion frame351 witness1307 (by decide)
def edge1307 : CertifiedEdge catalog where
  old := 342
  next := 351
  rank := 1
  good := by
    constructor
    · exact edge1307_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1308 : Fin frame342.rank → ℕ := ![2,4]
theorem edge1308_span : frame342.space ≤ frame352.space :=
  frame342.inclusion frame352 witness1308 (by decide)
def edge1308 : CertifiedEdge catalog where
  old := 342
  next := 352
  rank := 1
  good := by
    constructor
    · exact edge1308_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1309 : Fin frame343.rank → ℕ := ![2,4]
theorem edge1309_span : frame343.space ≤ frame348.space :=
  frame343.inclusion frame348 witness1309 (by decide)
def edge1309 : CertifiedEdge catalog where
  old := 343
  next := 348
  rank := 1
  good := by
    constructor
    · exact edge1309_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1310 : Fin frame343.rank → ℕ := ![2,4]
theorem edge1310_span : frame343.space ≤ frame355.space :=
  frame343.inclusion frame355 witness1310 (by decide)
def edge1310 : CertifiedEdge catalog where
  old := 343
  next := 355
  rank := 1
  good := by
    constructor
    · exact edge1310_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1311 : Fin frame344.rank → ℕ := ![1,4]
theorem edge1311_span : frame344.space ≤ frame350.space :=
  frame344.inclusion frame350 witness1311 (by decide)
def edge1311 : CertifiedEdge catalog where
  old := 344
  next := 350
  rank := 1
  good := by
    constructor
    · exact edge1311_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
