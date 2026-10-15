module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1408 : Fin frame377.rank → ℕ := ![5,6,8]
theorem edge1408_span : frame377.space ≤ frame385.space :=
  frame377.inclusion frame385 witness1408 (by decide)
def edge1408 : CertifiedEdge catalog where
  old := 377
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1408_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1409 : Fin frame377.rank → ℕ := ![43,44,48]
theorem edge1409_span : frame377.space ≤ frame660.space :=
  frame377.inclusion frame660 witness1409 (by decide)
def edge1409 : CertifiedEdge catalog where
  old := 377
  next := 660
  rank := 3
  good := by
    constructor
    · exact edge1409_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1410 : Fin frame377.rank → ℕ := ![57,10,12]
theorem edge1410_span : frame377.space ≤ frame700.space :=
  frame377.inclusion frame700 witness1410 (by decide)
def edge1410 : CertifiedEdge catalog where
  old := 377
  next := 700
  rank := 3
  good := by
    constructor
    · exact edge1410_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1411 : Fin frame378.rank → ℕ := ![1,2,12]
theorem edge1411_span : frame378.space ≤ frame385.space :=
  frame378.inclusion frame385 witness1411 (by decide)
def edge1411 : CertifiedEdge catalog where
  old := 378
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1411_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1412 : Fin frame378.rank → ℕ := ![35,4,24]
theorem edge1412_span : frame378.space ≤ frame661.space :=
  frame378.inclusion frame661 witness1412 (by decide)
def edge1412 : CertifiedEdge catalog where
  old := 378
  next := 661
  rank := 3
  good := by
    constructor
    · exact edge1412_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1413 : Fin frame378.rank → ℕ := ![1,34,44]
theorem edge1413_span : frame378.space ≤ frame701.space :=
  frame378.inclusion frame701 witness1413 (by decide)
def edge1413 : CertifiedEdge catalog where
  old := 378
  next := 701
  rank := 3
  good := by
    constructor
    · exact edge1413_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1414 : Fin frame379.rank → ℕ := ![9,10,12]
theorem edge1414_span : frame379.space ≤ frame385.space :=
  frame379.inclusion frame385 witness1414 (by decide)
def edge1414 : CertifiedEdge catalog where
  old := 379
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1414_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1415 : Fin frame379.rank → ℕ := ![57,10,12]
theorem edge1415_span : frame379.space ≤ frame668.space :=
  frame379.inclusion frame668 witness1415 (by decide)
def edge1415 : CertifiedEdge catalog where
  old := 379
  next := 668
  rank := 3
  good := by
    constructor
    · exact edge1415_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1416 : Fin frame379.rank → ℕ := ![51,52,24]
theorem edge1416_span : frame379.space ≤ frame692.space :=
  frame379.inclusion frame692 witness1416 (by decide)
def edge1416 : CertifiedEdge catalog where
  old := 379
  next := 692
  rank := 3
  good := by
    constructor
    · exact edge1416_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1417 : Fin frame380.rank → ℕ := ![1,2,8]
theorem edge1417_span : frame380.space ≤ frame385.space :=
  frame380.inclusion frame385 witness1417 (by decide)
def edge1417 : CertifiedEdge catalog where
  old := 380
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1417_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1418 : Fin frame380.rank → ℕ := ![1,18,56]
theorem edge1418_span : frame380.space ≤ frame669.space :=
  frame380.inclusion frame669 witness1418 (by decide)
def edge1418 : CertifiedEdge catalog where
  old := 380
  next := 669
  rank := 3
  good := by
    constructor
    · exact edge1418_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1419 : Fin frame380.rank → ℕ := ![35,4,24]
theorem edge1419_span : frame380.space ≤ frame693.space :=
  frame380.inclusion frame693 witness1419 (by decide)
def edge1419 : CertifiedEdge catalog where
  old := 380
  next := 693
  rank := 3
  good := by
    constructor
    · exact edge1419_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1420 : Fin frame381.rank → ℕ := ![1,10,12]
theorem edge1420_span : frame381.space ≤ frame385.space :=
  frame381.inclusion frame385 witness1420 (by decide)
def edge1420 : CertifiedEdge catalog where
  old := 381
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1420_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1421 : Fin frame381.rank → ℕ := ![1,42,12]
theorem edge1421_span : frame381.space ≤ frame684.space :=
  frame381.inclusion frame684 witness1421 (by decide)
def edge1421 : CertifiedEdge catalog where
  old := 381
  next := 684
  rank := 3
  good := by
    constructor
    · exact edge1421_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1422 : Fin frame381.rank → ℕ := ![35,20,8]
theorem edge1422_span : frame381.space ≤ frame708.space :=
  frame381.inclusion frame708 witness1422 (by decide)
def edge1422 : CertifiedEdge catalog where
  old := 381
  next := 708
  rank := 3
  good := by
    constructor
    · exact edge1422_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1423 : Fin frame382.rank → ℕ := ![5,2,8]
theorem edge1423_span : frame382.space ≤ frame385.space :=
  frame382.inclusion frame385 witness1423 (by decide)
def edge1423 : CertifiedEdge catalog where
  old := 382
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1423_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1424 : Fin frame382.rank → ℕ := ![53,18,24]
theorem edge1424_span : frame382.space ≤ frame685.space :=
  frame382.inclusion frame685 witness1424 (by decide)
def edge1424 : CertifiedEdge catalog where
  old := 382
  next := 685
  rank := 3
  good := by
    constructor
    · exact edge1424_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1425 : Fin frame382.rank → ℕ := ![43,4,48]
theorem edge1425_span : frame382.space ≤ frame709.space :=
  frame382.inclusion frame709 witness1425 (by decide)
def edge1425 : CertifiedEdge catalog where
  old := 382
  next := 709
  rank := 3
  good := by
    constructor
    · exact edge1425_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1426 : Fin frame383.rank → ℕ := ![1,6,8]
theorem edge1426_span : frame383.space ≤ frame385.space :=
  frame383.inclusion frame385 witness1426 (by decide)
def edge1426 : CertifiedEdge catalog where
  old := 383
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1426_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1427 : Fin frame383.rank → ℕ := ![35,12,16]
theorem edge1427_span : frame383.space ≤ frame676.space :=
  frame383.inclusion frame676 witness1427 (by decide)
def edge1427 : CertifiedEdge catalog where
  old := 383
  next := 676
  rank := 3
  good := by
    constructor
    · exact edge1427_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1428 : Fin frame383.rank → ℕ := ![33,22,24]
theorem edge1428_span : frame383.space ≤ frame716.space :=
  frame383.inclusion frame716 witness1428 (by decide)
def edge1428 : CertifiedEdge catalog where
  old := 383
  next := 716
  rank := 3
  good := by
    constructor
    · exact edge1428_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1429 : Fin frame384.rank → ℕ := ![9,2,12]
theorem edge1429_span : frame384.space ≤ frame385.space :=
  frame384.inclusion frame385 witness1429 (by decide)
def edge1429 : CertifiedEdge catalog where
  old := 384
  next := 385
  rank := 1
  good := by
    constructor
    · exact edge1429_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1430 : Fin frame384.rank → ℕ := ![51,4,24]
theorem edge1430_span : frame384.space ≤ frame677.space :=
  frame384.inclusion frame677 witness1430 (by decide)
def edge1430 : CertifiedEdge catalog where
  old := 384
  next := 677
  rank := 3
  good := by
    constructor
    · exact edge1430_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1431 : Fin frame384.rank → ℕ := ![25,34,36]
theorem edge1431_span : frame384.space ≤ frame717.space :=
  frame384.inclusion frame717 witness1431 (by decide)
def edge1431 : CertifiedEdge catalog where
  old := 384
  next := 717
  rank := 3
  good := by
    constructor
    · exact edge1431_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1432 : Fin frame385.rank → ℕ := ![131,292,360,112]
theorem edge1432_span : frame385.space ≤ frame1.space :=
  frame385.inclusion frame1 witness1432 (by decide)
def edge1432 : CertifiedEdge catalog where
  old := 385
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1432_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1433 : Fin frame385.rank → ℕ := ![131,36,104,112]
theorem edge1433_span : frame385.space ≤ frame417.space :=
  frame385.inclusion frame417 witness1433 (by decide)
def edge1433 : CertifiedEdge catalog where
  old := 385
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge1433_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1434 : Fin frame385.rank → ℕ := ![67,164,168,48]
theorem edge1434_span : frame385.space ≤ frame418.space :=
  frame385.inclusion frame418 witness1434 (by decide)
def edge1434 : CertifiedEdge catalog where
  old := 385
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge1434_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1435 : Fin frame385.rank → ℕ := ![131,36,104,112]
theorem edge1435_span : frame385.space ≤ frame421.space :=
  frame385.inclusion frame421 witness1435 (by decide)
def edge1435 : CertifiedEdge catalog where
  old := 385
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge1435_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1436 : Fin frame385.rank → ℕ := ![67,164,168,48]
theorem edge1436_span : frame385.space ≤ frame422.space :=
  frame385.inclusion frame422 witness1436 (by decide)
def edge1436 : CertifiedEdge catalog where
  old := 385
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge1436_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1437 : Fin frame386.rank → ℕ := ![1]
theorem edge1437_span : frame386.space ≤ frame394.space :=
  frame386.inclusion frame394 witness1437 (by decide)
def edge1437 : CertifiedEdge catalog where
  old := 386
  next := 394
  rank := 1
  good := by
    constructor
    · exact edge1437_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1438 : Fin frame386.rank → ℕ := ![1]
theorem edge1438_span : frame386.space ≤ frame395.space :=
  frame386.inclusion frame395 witness1438 (by decide)
def edge1438 : CertifiedEdge catalog where
  old := 386
  next := 395
  rank := 1
  good := by
    constructor
    · exact edge1438_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1439 : Fin frame386.rank → ℕ := ![3]
theorem edge1439_span : frame386.space ≤ frame396.space :=
  frame386.inclusion frame396 witness1439 (by decide)
def edge1439 : CertifiedEdge catalog where
  old := 386
  next := 396
  rank := 1
  good := by
    constructor
    · exact edge1439_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
