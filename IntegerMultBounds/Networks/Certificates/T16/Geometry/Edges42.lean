module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1344 : Fin frame355.rank → ℕ := ![1,10,4]
theorem edge1344_span : frame355.space ≤ frame356.space :=
  frame355.inclusion frame356 witness1344 (by decide)
def edge1344 : CertifiedEdge catalog where
  old := 355
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1344_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1345 : Fin frame355.rank → ℕ := ![33,10,36]
theorem edge1345_span : frame355.space ≤ frame683.space :=
  frame355.inclusion frame683 witness1345 (by decide)
def edge1345 : CertifiedEdge catalog where
  old := 355
  next := 683
  rank := 3
  good := by
    constructor
    · exact edge1345_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1346 : Fin frame355.rank → ℕ := ![1,26,36]
theorem edge1346_span : frame355.space ≤ frame715.space :=
  frame355.inclusion frame715 witness1346 (by decide)
def edge1346 : CertifiedEdge catalog where
  old := 355
  next := 715
  rank := 3
  good := by
    constructor
    · exact edge1346_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1347 : Fin frame356.rank → ℕ := ![289,290,420,360]
theorem edge1347_span : frame356.space ≤ frame1.space :=
  frame356.inclusion frame1 witness1347 (by decide)
def edge1347 : CertifiedEdge catalog where
  old := 356
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1347_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1348 : Fin frame356.rank → ℕ := ![33,34,164,104]
theorem edge1348_span : frame356.space ≤ frame417.space :=
  frame356.inclusion frame417 witness1348 (by decide)
def edge1348 : CertifiedEdge catalog where
  old := 356
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge1348_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1349 : Fin frame356.rank → ℕ := ![161,162,228,168]
theorem edge1349_span : frame356.space ≤ frame418.space :=
  frame356.inclusion frame418 witness1349 (by decide)
def edge1349 : CertifiedEdge catalog where
  old := 356
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge1349_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1350 : Fin frame356.rank → ℕ := ![161,162,164,232]
theorem edge1350_span : frame356.space ≤ frame419.space :=
  frame356.inclusion frame419 witness1350 (by decide)
def edge1350 : CertifiedEdge catalog where
  old := 356
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge1350_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1351 : Fin frame356.rank → ℕ := ![33,34,164,104]
theorem edge1351_span : frame356.space ≤ frame420.space :=
  frame356.inclusion frame420 witness1351 (by decide)
def edge1351 : CertifiedEdge catalog where
  old := 356
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge1351_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1352 : Fin frame357.rank → ℕ := ![1]
theorem edge1352_span : frame357.space ≤ frame365.space :=
  frame357.inclusion frame365 witness1352 (by decide)
def edge1352 : CertifiedEdge catalog where
  old := 357
  next := 365
  rank := 1
  good := by
    constructor
    · exact edge1352_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1353 : Fin frame357.rank → ℕ := ![1]
theorem edge1353_span : frame357.space ≤ frame366.space :=
  frame357.inclusion frame366 witness1353 (by decide)
def edge1353 : CertifiedEdge catalog where
  old := 357
  next := 366
  rank := 1
  good := by
    constructor
    · exact edge1353_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1354 : Fin frame357.rank → ℕ := ![1]
theorem edge1354_span : frame357.space ≤ frame367.space :=
  frame357.inclusion frame367 witness1354 (by decide)
def edge1354 : CertifiedEdge catalog where
  old := 357
  next := 367
  rank := 1
  good := by
    constructor
    · exact edge1354_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1355 : Fin frame358.rank → ℕ := ![3]
theorem edge1355_span : frame358.space ≤ frame368.space :=
  frame358.inclusion frame368 witness1355 (by decide)
def edge1355 : CertifiedEdge catalog where
  old := 358
  next := 368
  rank := 1
  good := by
    constructor
    · exact edge1355_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1356 : Fin frame358.rank → ℕ := ![3]
theorem edge1356_span : frame358.space ≤ frame369.space :=
  frame358.inclusion frame369 witness1356 (by decide)
def edge1356 : CertifiedEdge catalog where
  old := 358
  next := 369
  rank := 1
  good := by
    constructor
    · exact edge1356_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1357 : Fin frame358.rank → ℕ := ![3]
theorem edge1357_span : frame358.space ≤ frame370.space :=
  frame358.inclusion frame370 witness1357 (by decide)
def edge1357 : CertifiedEdge catalog where
  old := 358
  next := 370
  rank := 1
  good := by
    constructor
    · exact edge1357_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1358 : Fin frame359.rank → ℕ := ![1]
theorem edge1358_span : frame359.space ≤ frame368.space :=
  frame359.inclusion frame368 witness1358 (by decide)
def edge1358 : CertifiedEdge catalog where
  old := 359
  next := 368
  rank := 1
  good := by
    constructor
    · exact edge1358_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1359 : Fin frame359.rank → ℕ := ![3]
theorem edge1359_span : frame359.space ≤ frame371.space :=
  frame359.inclusion frame371 witness1359 (by decide)
def edge1359 : CertifiedEdge catalog where
  old := 359
  next := 371
  rank := 1
  good := by
    constructor
    · exact edge1359_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1360 : Fin frame359.rank → ℕ := ![3]
theorem edge1360_span : frame359.space ≤ frame372.space :=
  frame359.inclusion frame372 witness1360 (by decide)
def edge1360 : CertifiedEdge catalog where
  old := 359
  next := 372
  rank := 1
  good := by
    constructor
    · exact edge1360_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1361 : Fin frame360.rank → ℕ := ![3]
theorem edge1361_span : frame360.space ≤ frame365.space :=
  frame360.inclusion frame365 witness1361 (by decide)
def edge1361 : CertifiedEdge catalog where
  old := 360
  next := 365
  rank := 1
  good := by
    constructor
    · exact edge1361_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1362 : Fin frame360.rank → ℕ := ![3]
theorem edge1362_span : frame360.space ≤ frame373.space :=
  frame360.inclusion frame373 witness1362 (by decide)
def edge1362 : CertifiedEdge catalog where
  old := 360
  next := 373
  rank := 1
  good := by
    constructor
    · exact edge1362_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1363 : Fin frame360.rank → ℕ := ![1]
theorem edge1363_span : frame360.space ≤ frame374.space :=
  frame360.inclusion frame374 witness1363 (by decide)
def edge1363 : CertifiedEdge catalog where
  old := 360
  next := 374
  rank := 1
  good := by
    constructor
    · exact edge1363_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1364 : Fin frame361.rank → ℕ := ![1]
theorem edge1364_span : frame361.space ≤ frame369.space :=
  frame361.inclusion frame369 witness1364 (by decide)
def edge1364 : CertifiedEdge catalog where
  old := 361
  next := 369
  rank := 1
  good := by
    constructor
    · exact edge1364_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1365 : Fin frame361.rank → ℕ := ![1]
theorem edge1365_span : frame361.space ≤ frame371.space :=
  frame361.inclusion frame371 witness1365 (by decide)
def edge1365 : CertifiedEdge catalog where
  old := 361
  next := 371
  rank := 1
  good := by
    constructor
    · exact edge1365_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1366 : Fin frame361.rank → ℕ := ![1]
theorem edge1366_span : frame361.space ≤ frame375.space :=
  frame361.inclusion frame375 witness1366 (by decide)
def edge1366 : CertifiedEdge catalog where
  old := 361
  next := 375
  rank := 1
  good := by
    constructor
    · exact edge1366_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1367 : Fin frame362.rank → ℕ := ![2]
theorem edge1367_span : frame362.space ≤ frame366.space :=
  frame362.inclusion frame366 witness1367 (by decide)
def edge1367 : CertifiedEdge catalog where
  old := 362
  next := 366
  rank := 1
  good := by
    constructor
    · exact edge1367_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1368 : Fin frame362.rank → ℕ := ![2]
theorem edge1368_span : frame362.space ≤ frame373.space :=
  frame362.inclusion frame373 witness1368 (by decide)
def edge1368 : CertifiedEdge catalog where
  old := 362
  next := 373
  rank := 1
  good := by
    constructor
    · exact edge1368_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1369 : Fin frame362.rank → ℕ := ![3]
theorem edge1369_span : frame362.space ≤ frame376.space :=
  frame362.inclusion frame376 witness1369 (by decide)
def edge1369 : CertifiedEdge catalog where
  old := 362
  next := 376
  rank := 1
  good := by
    constructor
    · exact edge1369_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1370 : Fin frame363.rank → ℕ := ![2]
theorem edge1370_span : frame363.space ≤ frame367.space :=
  frame363.inclusion frame367 witness1370 (by decide)
def edge1370 : CertifiedEdge catalog where
  old := 363
  next := 367
  rank := 1
  good := by
    constructor
    · exact edge1370_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1371 : Fin frame363.rank → ℕ := ![2]
theorem edge1371_span : frame363.space ≤ frame374.space :=
  frame363.inclusion frame374 witness1371 (by decide)
def edge1371 : CertifiedEdge catalog where
  old := 363
  next := 374
  rank := 1
  good := by
    constructor
    · exact edge1371_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1372 : Fin frame363.rank → ℕ := ![2]
theorem edge1372_span : frame363.space ≤ frame376.space :=
  frame363.inclusion frame376 witness1372 (by decide)
def edge1372 : CertifiedEdge catalog where
  old := 363
  next := 376
  rank := 1
  good := by
    constructor
    · exact edge1372_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1373 : Fin frame364.rank → ℕ := ![1]
theorem edge1373_span : frame364.space ≤ frame370.space :=
  frame364.inclusion frame370 witness1373 (by decide)
def edge1373 : CertifiedEdge catalog where
  old := 364
  next := 370
  rank := 1
  good := by
    constructor
    · exact edge1373_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1374 : Fin frame364.rank → ℕ := ![1]
theorem edge1374_span : frame364.space ≤ frame372.space :=
  frame364.inclusion frame372 witness1374 (by decide)
def edge1374 : CertifiedEdge catalog where
  old := 364
  next := 372
  rank := 1
  good := by
    constructor
    · exact edge1374_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1375 : Fin frame364.rank → ℕ := ![3]
theorem edge1375_span : frame364.space ≤ frame375.space :=
  frame364.inclusion frame375 witness1375 (by decide)
def edge1375 : CertifiedEdge catalog where
  old := 364
  next := 375
  rank := 1
  good := by
    constructor
    · exact edge1375_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
