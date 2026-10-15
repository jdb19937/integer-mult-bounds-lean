module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1472 : Fin frame397.rank → ℕ := ![9,12]
theorem edge1472_span : frame397.space ≤ frame496.space :=
  frame397.inclusion frame496 witness1472 (by decide)
def edge1472 : CertifiedEdge catalog where
  old := 397
  next := 496
  rank := 2
  good := by
    constructor
    · exact edge1472_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1473 : Fin frame398.rank → ℕ := ![1,4]
theorem edge1473_span : frame398.space ≤ frame407.space :=
  frame398.inclusion frame407 witness1473 (by decide)
def edge1473 : CertifiedEdge catalog where
  old := 398
  next := 407
  rank := 1
  good := by
    constructor
    · exact edge1473_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1474 : Fin frame398.rank → ℕ := ![1,4]
theorem edge1474_span : frame398.space ≤ frame412.space :=
  frame398.inclusion frame412 witness1474 (by decide)
def edge1474 : CertifiedEdge catalog where
  old := 398
  next := 412
  rank := 1
  good := by
    constructor
    · exact edge1474_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1475 : Fin frame399.rank → ℕ := ![1,4]
theorem edge1475_span : frame399.space ≤ frame408.space :=
  frame399.inclusion frame408 witness1475 (by decide)
def edge1475 : CertifiedEdge catalog where
  old := 399
  next := 408
  rank := 1
  good := by
    constructor
    · exact edge1475_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1476 : Fin frame399.rank → ℕ := ![1,4]
theorem edge1476_span : frame399.space ≤ frame411.space :=
  frame399.inclusion frame411 witness1476 (by decide)
def edge1476 : CertifiedEdge catalog where
  old := 399
  next := 411
  rank := 1
  good := by
    constructor
    · exact edge1476_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1477 : Fin frame400.rank → ℕ := ![1,4]
theorem edge1477_span : frame400.space ≤ frame409.space :=
  frame400.inclusion frame409 witness1477 (by decide)
def edge1477 : CertifiedEdge catalog where
  old := 400
  next := 409
  rank := 1
  good := by
    constructor
    · exact edge1477_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1478 : Fin frame400.rank → ℕ := ![1,4]
theorem edge1478_span : frame400.space ≤ frame410.space :=
  frame400.inclusion frame410 witness1478 (by decide)
def edge1478 : CertifiedEdge catalog where
  old := 400
  next := 410
  rank := 1
  good := by
    constructor
    · exact edge1478_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1479 : Fin frame401.rank → ℕ := ![1,4]
theorem edge1479_span : frame401.space ≤ frame406.space :=
  frame401.inclusion frame406 witness1479 (by decide)
def edge1479 : CertifiedEdge catalog where
  old := 401
  next := 406
  rank := 1
  good := by
    constructor
    · exact edge1479_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1480 : Fin frame401.rank → ℕ := ![1,4]
theorem edge1480_span : frame401.space ≤ frame413.space :=
  frame401.inclusion frame413 witness1480 (by decide)
def edge1480 : CertifiedEdge catalog where
  old := 401
  next := 413
  rank := 1
  good := by
    constructor
    · exact edge1480_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1481 : Fin frame402.rank → ℕ := ![2,4]
theorem edge1481_span : frame402.space ≤ frame408.space :=
  frame402.inclusion frame408 witness1481 (by decide)
def edge1481 : CertifiedEdge catalog where
  old := 402
  next := 408
  rank := 1
  good := by
    constructor
    · exact edge1481_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1482 : Fin frame402.rank → ℕ := ![2,4]
theorem edge1482_span : frame402.space ≤ frame410.space :=
  frame402.inclusion frame410 witness1482 (by decide)
def edge1482 : CertifiedEdge catalog where
  old := 402
  next := 410
  rank := 1
  good := by
    constructor
    · exact edge1482_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1483 : Fin frame403.rank → ℕ := ![2,4]
theorem edge1483_span : frame403.space ≤ frame406.space :=
  frame403.inclusion frame406 witness1483 (by decide)
def edge1483 : CertifiedEdge catalog where
  old := 403
  next := 406
  rank := 1
  good := by
    constructor
    · exact edge1483_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1484 : Fin frame403.rank → ℕ := ![2,4]
theorem edge1484_span : frame403.space ≤ frame412.space :=
  frame403.inclusion frame412 witness1484 (by decide)
def edge1484 : CertifiedEdge catalog where
  old := 403
  next := 412
  rank := 1
  good := by
    constructor
    · exact edge1484_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1485 : Fin frame404.rank → ℕ := ![1,4]
theorem edge1485_span : frame404.space ≤ frame482.space :=
  frame404.inclusion frame482 witness1485 (by decide)
def edge1485 : CertifiedEdge catalog where
  old := 404
  next := 482
  rank := 1
  good := by
    constructor
    · exact edge1485_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1486 : Fin frame404.rank → ℕ := ![1,8]
theorem edge1486_span : frame404.space ≤ frame484.space :=
  frame404.inclusion frame484 witness1486 (by decide)
def edge1486 : CertifiedEdge catalog where
  old := 404
  next := 484
  rank := 2
  good := by
    constructor
    · exact edge1486_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1487 : Fin frame404.rank → ℕ := ![1,4]
theorem edge1487_span : frame404.space ≤ frame527.space :=
  frame404.inclusion frame527 witness1487 (by decide)
def edge1487 : CertifiedEdge catalog where
  old := 404
  next := 527
  rank := 1
  good := by
    constructor
    · exact edge1487_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1488 : Fin frame404.rank → ℕ := ![1,8]
theorem edge1488_span : frame404.space ≤ frame529.space :=
  frame404.inclusion frame529 witness1488 (by decide)
def edge1488 : CertifiedEdge catalog where
  old := 404
  next := 529
  rank := 2
  good := by
    constructor
    · exact edge1488_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1489 : Fin frame405.rank → ℕ := ![2,4]
theorem edge1489_span : frame405.space ≤ frame493.space :=
  frame405.inclusion frame493 witness1489 (by decide)
def edge1489 : CertifiedEdge catalog where
  old := 405
  next := 493
  rank := 1
  good := by
    constructor
    · exact edge1489_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1490 : Fin frame405.rank → ℕ := ![34,40]
theorem edge1490_span : frame405.space ≤ frame499.space :=
  frame405.inclusion frame499 witness1490 (by decide)
def edge1490 : CertifiedEdge catalog where
  old := 405
  next := 499
  rank := 4
  good := by
    constructor
    · exact edge1490_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1491 : Fin frame405.rank → ℕ := ![5,6]
theorem edge1491_span : frame405.space ≤ frame526.space :=
  frame405.inclusion frame526 witness1491 (by decide)
def edge1491 : CertifiedEdge catalog where
  old := 405
  next := 526
  rank := 1
  good := by
    constructor
    · exact edge1491_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1492 : Fin frame405.rank → ℕ := ![34,40]
theorem edge1492_span : frame405.space ≤ frame532.space :=
  frame405.inclusion frame532 witness1492 (by decide)
def edge1492 : CertifiedEdge catalog where
  old := 405
  next := 532
  rank := 4
  good := by
    constructor
    · exact edge1492_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1493 : Fin frame406.rank → ℕ := ![1,2,12]
theorem edge1493_span : frame406.space ≤ frame414.space :=
  frame406.inclusion frame414 witness1493 (by decide)
def edge1493 : CertifiedEdge catalog where
  old := 406
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1493_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1494 : Fin frame406.rank → ℕ := ![33,34,24]
theorem edge1494_span : frame406.space ≤ frame582.space :=
  frame406.inclusion frame582 witness1494 (by decide)
def edge1494 : CertifiedEdge catalog where
  old := 406
  next := 582
  rank := 3
  good := by
    constructor
    · exact edge1494_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1495 : Fin frame406.rank → ℕ := ![17,18,40]
theorem edge1495_span : frame406.space ≤ frame583.space :=
  frame406.inclusion frame583 witness1495 (by decide)
def edge1495 : CertifiedEdge catalog where
  old := 406
  next := 583
  rank := 3
  good := by
    constructor
    · exact edge1495_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1496 : Fin frame407.rank → ℕ := ![9,10,12]
theorem edge1496_span : frame407.space ≤ frame414.space :=
  frame407.inclusion frame414 witness1496 (by decide)
def edge1496 : CertifiedEdge catalog where
  old := 407
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1496_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1497 : Fin frame407.rank → ℕ := ![17,18,24]
theorem edge1497_span : frame407.space ≤ frame584.space :=
  frame407.inclusion frame584 witness1497 (by decide)
def edge1497 : CertifiedEdge catalog where
  old := 407
  next := 584
  rank := 3
  good := by
    constructor
    · exact edge1497_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1498 : Fin frame407.rank → ℕ := ![17,18,24]
theorem edge1498_span : frame407.space ≤ frame585.space :=
  frame407.inclusion frame585 witness1498 (by decide)
def edge1498 : CertifiedEdge catalog where
  old := 407
  next := 585
  rank := 3
  good := by
    constructor
    · exact edge1498_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1499 : Fin frame408.rank → ℕ := ![5,6,8]
theorem edge1499_span : frame408.space ≤ frame414.space :=
  frame408.inclusion frame414 witness1499 (by decide)
def edge1499 : CertifiedEdge catalog where
  old := 408
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1499_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1500 : Fin frame408.rank → ℕ := ![1,2,56]
theorem edge1500_span : frame408.space ≤ frame603.space :=
  frame408.inclusion frame603 witness1500 (by decide)
def edge1500 : CertifiedEdge catalog where
  old := 408
  next := 603
  rank := 3
  good := by
    constructor
    · exact edge1500_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1501 : Fin frame408.rank → ℕ := ![41,42,16]
theorem edge1501_span : frame408.space ≤ frame614.space :=
  frame408.inclusion frame614 witness1501 (by decide)
def edge1501 : CertifiedEdge catalog where
  old := 408
  next := 614
  rank := 3
  good := by
    constructor
    · exact edge1501_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1502 : Fin frame409.rank → ℕ := ![1,2,8]
theorem edge1502_span : frame409.space ≤ frame414.space :=
  frame409.inclusion frame414 witness1502 (by decide)
def edge1502 : CertifiedEdge catalog where
  old := 409
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1502_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1503 : Fin frame409.rank → ℕ := ![33,34,48]
theorem edge1503_span : frame409.space ≤ frame586.space :=
  frame409.inclusion frame586 witness1503 (by decide)
def edge1503 : CertifiedEdge catalog where
  old := 409
  next := 586
  rank := 3
  good := by
    constructor
    · exact edge1503_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
