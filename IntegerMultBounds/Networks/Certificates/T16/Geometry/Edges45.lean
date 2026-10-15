module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1440 : Fin frame387.rank → ℕ := ![3]
theorem edge1440_span : frame387.space ≤ frame397.space :=
  frame387.inclusion frame397 witness1440 (by decide)
def edge1440 : CertifiedEdge catalog where
  old := 387
  next := 397
  rank := 1
  good := by
    constructor
    · exact edge1440_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1441 : Fin frame387.rank → ℕ := ![3]
theorem edge1441_span : frame387.space ≤ frame398.space :=
  frame387.inclusion frame398 witness1441 (by decide)
def edge1441 : CertifiedEdge catalog where
  old := 387
  next := 398
  rank := 1
  good := by
    constructor
    · exact edge1441_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1442 : Fin frame387.rank → ℕ := ![1]
theorem edge1442_span : frame387.space ≤ frame399.space :=
  frame387.inclusion frame399 witness1442 (by decide)
def edge1442 : CertifiedEdge catalog where
  old := 387
  next := 399
  rank := 1
  good := by
    constructor
    · exact edge1442_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1443 : Fin frame388.rank → ℕ := ![1]
theorem edge1443_span : frame388.space ≤ frame397.space :=
  frame388.inclusion frame397 witness1443 (by decide)
def edge1443 : CertifiedEdge catalog where
  old := 388
  next := 397
  rank := 1
  good := by
    constructor
    · exact edge1443_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1444 : Fin frame388.rank → ℕ := ![1]
theorem edge1444_span : frame388.space ≤ frame400.space :=
  frame388.inclusion frame400 witness1444 (by decide)
def edge1444 : CertifiedEdge catalog where
  old := 388
  next := 400
  rank := 1
  good := by
    constructor
    · exact edge1444_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1445 : Fin frame388.rank → ℕ := ![1]
theorem edge1445_span : frame388.space ≤ frame401.space :=
  frame388.inclusion frame401 witness1445 (by decide)
def edge1445 : CertifiedEdge catalog where
  old := 388
  next := 401
  rank := 1
  good := by
    constructor
    · exact edge1445_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1446 : Fin frame389.rank → ℕ := ![3]
theorem edge1446_span : frame389.space ≤ frame394.space :=
  frame389.inclusion frame394 witness1446 (by decide)
def edge1446 : CertifiedEdge catalog where
  old := 389
  next := 394
  rank := 1
  good := by
    constructor
    · exact edge1446_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1447 : Fin frame389.rank → ℕ := ![3]
theorem edge1447_span : frame389.space ≤ frame402.space :=
  frame389.inclusion frame402 witness1447 (by decide)
def edge1447 : CertifiedEdge catalog where
  old := 389
  next := 402
  rank := 1
  good := by
    constructor
    · exact edge1447_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1448 : Fin frame389.rank → ℕ := ![3]
theorem edge1448_span : frame389.space ≤ frame403.space :=
  frame389.inclusion frame403 witness1448 (by decide)
def edge1448 : CertifiedEdge catalog where
  old := 389
  next := 403
  rank := 1
  good := by
    constructor
    · exact edge1448_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1449 : Fin frame390.rank → ℕ := ![1]
theorem edge1449_span : frame390.space ≤ frame398.space :=
  frame390.inclusion frame398 witness1449 (by decide)
def edge1449 : CertifiedEdge catalog where
  old := 390
  next := 398
  rank := 1
  good := by
    constructor
    · exact edge1449_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1450 : Fin frame390.rank → ℕ := ![3]
theorem edge1450_span : frame390.space ≤ frame400.space :=
  frame390.inclusion frame400 witness1450 (by decide)
def edge1450 : CertifiedEdge catalog where
  old := 390
  next := 400
  rank := 1
  good := by
    constructor
    · exact edge1450_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1451 : Fin frame390.rank → ℕ := ![1]
theorem edge1451_span : frame390.space ≤ frame404.space :=
  frame390.inclusion frame404 witness1451 (by decide)
def edge1451 : CertifiedEdge catalog where
  old := 390
  next := 404
  rank := 1
  good := by
    constructor
    · exact edge1451_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1452 : Fin frame391.rank → ℕ := ![3]
theorem edge1452_span : frame391.space ≤ frame395.space :=
  frame391.inclusion frame395 witness1452 (by decide)
def edge1452 : CertifiedEdge catalog where
  old := 391
  next := 395
  rank := 1
  good := by
    constructor
    · exact edge1452_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1453 : Fin frame391.rank → ℕ := ![1]
theorem edge1453_span : frame391.space ≤ frame402.space :=
  frame391.inclusion frame402 witness1453 (by decide)
def edge1453 : CertifiedEdge catalog where
  old := 391
  next := 402
  rank := 1
  good := by
    constructor
    · exact edge1453_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1454 : Fin frame391.rank → ℕ := ![3]
theorem edge1454_span : frame391.space ≤ frame405.space :=
  frame391.inclusion frame405 witness1454 (by decide)
def edge1454 : CertifiedEdge catalog where
  old := 391
  next := 405
  rank := 1
  good := by
    constructor
    · exact edge1454_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1455 : Fin frame392.rank → ℕ := ![1]
theorem edge1455_span : frame392.space ≤ frame396.space :=
  frame392.inclusion frame396 witness1455 (by decide)
def edge1455 : CertifiedEdge catalog where
  old := 392
  next := 396
  rank := 1
  good := by
    constructor
    · exact edge1455_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1456 : Fin frame392.rank → ℕ := ![1]
theorem edge1456_span : frame392.space ≤ frame403.space :=
  frame392.inclusion frame403 witness1456 (by decide)
def edge1456 : CertifiedEdge catalog where
  old := 392
  next := 403
  rank := 1
  good := by
    constructor
    · exact edge1456_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1457 : Fin frame392.rank → ℕ := ![1]
theorem edge1457_span : frame392.space ≤ frame405.space :=
  frame392.inclusion frame405 witness1457 (by decide)
def edge1457 : CertifiedEdge catalog where
  old := 392
  next := 405
  rank := 1
  good := by
    constructor
    · exact edge1457_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1458 : Fin frame393.rank → ℕ := ![3]
theorem edge1458_span : frame393.space ≤ frame399.space :=
  frame393.inclusion frame399 witness1458 (by decide)
def edge1458 : CertifiedEdge catalog where
  old := 393
  next := 399
  rank := 1
  good := by
    constructor
    · exact edge1458_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1459 : Fin frame393.rank → ℕ := ![3]
theorem edge1459_span : frame393.space ≤ frame401.space :=
  frame393.inclusion frame401 witness1459 (by decide)
def edge1459 : CertifiedEdge catalog where
  old := 393
  next := 401
  rank := 1
  good := by
    constructor
    · exact edge1459_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1460 : Fin frame393.rank → ℕ := ![3]
theorem edge1460_span : frame393.space ≤ frame404.space :=
  frame393.inclusion frame404 witness1460 (by decide)
def edge1460 : CertifiedEdge catalog where
  old := 393
  next := 404
  rank := 1
  good := by
    constructor
    · exact edge1460_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1461 : Fin frame394.rank → ℕ := ![1,4]
theorem edge1461_span : frame394.space ≤ frame468.space :=
  frame394.inclusion frame468 witness1461 (by decide)
def edge1461 : CertifiedEdge catalog where
  old := 394
  next := 468
  rank := 1
  good := by
    constructor
    · exact edge1461_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1462 : Fin frame394.rank → ℕ := ![18,40]
theorem edge1462_span : frame394.space ≤ frame474.space :=
  frame394.inclusion frame474 witness1462 (by decide)
def edge1462 : CertifiedEdge catalog where
  old := 394
  next := 474
  rank := 4
  good := by
    constructor
    · exact edge1462_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1463 : Fin frame394.rank → ℕ := ![2,4]
theorem edge1463_span : frame394.space ≤ frame481.space :=
  frame394.inclusion frame481 witness1463 (by decide)
def edge1463 : CertifiedEdge catalog where
  old := 394
  next := 481
  rank := 1
  good := by
    constructor
    · exact edge1463_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1464 : Fin frame394.rank → ℕ := ![18,40]
theorem edge1464_span : frame394.space ≤ frame487.space :=
  frame394.inclusion frame487 witness1464 (by decide)
def edge1464 : CertifiedEdge catalog where
  old := 394
  next := 487
  rank := 4
  good := by
    constructor
    · exact edge1464_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1465 : Fin frame395.rank → ℕ := ![2,4]
theorem edge1465_span : frame395.space ≤ frame407.space :=
  frame395.inclusion frame407 witness1465 (by decide)
def edge1465 : CertifiedEdge catalog where
  old := 395
  next := 407
  rank := 1
  good := by
    constructor
    · exact edge1465_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1466 : Fin frame395.rank → ℕ := ![2,4]
theorem edge1466_span : frame395.space ≤ frame413.space :=
  frame395.inclusion frame413 witness1466 (by decide)
def edge1466 : CertifiedEdge catalog where
  old := 395
  next := 413
  rank := 1
  good := by
    constructor
    · exact edge1466_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1467 : Fin frame396.rank → ℕ := ![2,4]
theorem edge1467_span : frame396.space ≤ frame409.space :=
  frame396.inclusion frame409 witness1467 (by decide)
def edge1467 : CertifiedEdge catalog where
  old := 396
  next := 409
  rank := 1
  good := by
    constructor
    · exact edge1467_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1468 : Fin frame396.rank → ℕ := ![2,4]
theorem edge1468_span : frame396.space ≤ frame411.space :=
  frame396.inclusion frame411 witness1468 (by decide)
def edge1468 : CertifiedEdge catalog where
  old := 396
  next := 411
  rank := 1
  good := by
    constructor
    · exact edge1468_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1469 : Fin frame397.rank → ℕ := ![5,6]
theorem edge1469_span : frame397.space ≤ frame469.space :=
  frame397.inclusion frame469 witness1469 (by decide)
def edge1469 : CertifiedEdge catalog where
  old := 397
  next := 469
  rank := 1
  good := by
    constructor
    · exact edge1469_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1470 : Fin frame397.rank → ℕ := ![9,12]
theorem edge1470_span : frame397.space ≤ frame471.space :=
  frame397.inclusion frame471 witness1470 (by decide)
def edge1470 : CertifiedEdge catalog where
  old := 397
  next := 471
  rank := 2
  good := by
    constructor
    · exact edge1470_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1471 : Fin frame397.rank → ℕ := ![1,2]
theorem edge1471_span : frame397.space ≤ frame494.space :=
  frame397.inclusion frame494 witness1471 (by decide)
def edge1471 : CertifiedEdge catalog where
  old := 397
  next := 494
  rank := 1
  good := by
    constructor
    · exact edge1471_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
