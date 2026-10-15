module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1504 : Fin frame409.rank → ℕ := ![33,34,48]
theorem edge1504_span : frame409.space ≤ frame587.space :=
  frame409.inclusion frame587 witness1504 (by decide)
def edge1504 : CertifiedEdge catalog where
  old := 409
  next := 587
  rank := 3
  good := by
    constructor
    · exact edge1504_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1505 : Fin frame410.rank → ℕ := ![1,6,8]
theorem edge1505_span : frame410.space ≤ frame414.space :=
  frame410.inclusion frame414 witness1505 (by decide)
def edge1505 : CertifiedEdge catalog where
  old := 410
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1505_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1506 : Fin frame410.rank → ℕ := ![49,2,56]
theorem edge1506_span : frame410.space ≤ frame608.space :=
  frame410.inclusion frame608 witness1506 (by decide)
def edge1506 : CertifiedEdge catalog where
  old := 410
  next := 608
  rank := 3
  good := by
    constructor
    · exact edge1506_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1507 : Fin frame410.rank → ℕ := ![1,42,16]
theorem edge1507_span : frame410.space ≤ frame619.space :=
  frame410.inclusion frame619 witness1507 (by decide)
def edge1507 : CertifiedEdge catalog where
  old := 410
  next := 619
  rank := 3
  good := by
    constructor
    · exact edge1507_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1508 : Fin frame411.rank → ℕ := ![5,2,8]
theorem edge1508_span : frame411.space ≤ frame414.space :=
  frame411.inclusion frame414 witness1508 (by decide)
def edge1508 : CertifiedEdge catalog where
  old := 411
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1508_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1509 : Fin frame411.rank → ℕ := ![1,50,56]
theorem edge1509_span : frame411.space ≤ frame610.space :=
  frame411.inclusion frame610 witness1509 (by decide)
def edge1509 : CertifiedEdge catalog where
  old := 411
  next := 610
  rank := 3
  good := by
    constructor
    · exact edge1509_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1510 : Fin frame411.rank → ℕ := ![41,2,16]
theorem edge1510_span : frame411.space ≤ frame621.space :=
  frame411.inclusion frame621 witness1510 (by decide)
def edge1510 : CertifiedEdge catalog where
  old := 411
  next := 621
  rank := 3
  good := by
    constructor
    · exact edge1510_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1511 : Fin frame412.rank → ℕ := ![9,2,12]
theorem edge1511_span : frame412.space ≤ frame414.space :=
  frame412.inclusion frame414 witness1511 (by decide)
def edge1511 : CertifiedEdge catalog where
  old := 412
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1511_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1512 : Fin frame412.rank → ℕ := ![17,34,24]
theorem edge1512_span : frame412.space ≤ frame588.space :=
  frame412.inclusion frame588 witness1512 (by decide)
def edge1512 : CertifiedEdge catalog where
  old := 412
  next := 588
  rank := 3
  good := by
    constructor
    · exact edge1512_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1513 : Fin frame412.rank → ℕ := ![33,18,40]
theorem edge1513_span : frame412.space ≤ frame589.space :=
  frame412.inclusion frame589 witness1513 (by decide)
def edge1513 : CertifiedEdge catalog where
  old := 412
  next := 589
  rank := 3
  good := by
    constructor
    · exact edge1513_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1514 : Fin frame413.rank → ℕ := ![1,10,12]
theorem edge1514_span : frame413.space ≤ frame414.space :=
  frame413.inclusion frame414 witness1514 (by decide)
def edge1514 : CertifiedEdge catalog where
  old := 413
  next := 414
  rank := 1
  good := by
    constructor
    · exact edge1514_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1515 : Fin frame413.rank → ℕ := ![33,18,24]
theorem edge1515_span : frame413.space ≤ frame590.space :=
  frame413.inclusion frame590 witness1515 (by decide)
def edge1515 : CertifiedEdge catalog where
  old := 413
  next := 590
  rank := 3
  good := by
    constructor
    · exact edge1515_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1516 : Fin frame413.rank → ℕ := ![17,34,40]
theorem edge1516_span : frame413.space ≤ frame591.space :=
  frame413.inclusion frame591 witness1516 (by decide)
def edge1516 : CertifiedEdge catalog where
  old := 413
  next := 591
  rank := 3
  good := by
    constructor
    · exact edge1516_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1517 : Fin frame414.rank → ℕ := ![97,98,360,240]
theorem edge1517_span : frame414.space ≤ frame1.space :=
  frame414.inclusion frame1 witness1517 (by decide)
def edge1517 : CertifiedEdge catalog where
  old := 414
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1517_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1518 : Fin frame414.rank → ℕ := ![97,98,232,112]
theorem edge1518_span : frame414.space ≤ frame419.space :=
  frame414.inclusion frame419 witness1518 (by decide)
def edge1518 : CertifiedEdge catalog where
  old := 414
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge1518_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1519 : Fin frame414.rank → ℕ := ![97,98,104,240]
theorem edge1519_span : frame414.space ≤ frame420.space :=
  frame414.inclusion frame420 witness1519 (by decide)
def edge1519 : CertifiedEdge catalog where
  old := 414
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge1519_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1520 : Fin frame414.rank → ℕ := ![97,98,104,240]
theorem edge1520_span : frame414.space ≤ frame421.space :=
  frame414.inclusion frame421 witness1520 (by decide)
def edge1520 : CertifiedEdge catalog where
  old := 414
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge1520_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1521 : Fin frame414.rank → ℕ := ![33,34,168,112]
theorem edge1521_span : frame414.space ≤ frame422.space :=
  frame414.inclusion frame422 witness1521 (by decide)
def edge1521 : CertifiedEdge catalog where
  old := 414
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge1521_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1522 : Fin frame415.rank → ℕ := ![1,2,4,136,16,160,64,256]
theorem edge1522_span : frame415.space ≤ frame1.space :=
  frame415.inclusion frame1 witness1522 (by decide)
def edge1522 : CertifiedEdge catalog where
  old := 415
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1522_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1523 : Fin frame416.rank → ℕ := ![1,2,4,8,16,32,320,384]
theorem edge1523_span : frame416.space ≤ frame1.space :=
  frame416.inclusion frame1 witness1523 (by decide)
def edge1523 : CertifiedEdge catalog where
  old := 416
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1523_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1524 : Fin frame417.rank → ℕ := ![1,2,4,8,272,288,64,128]
theorem edge1524_span : frame417.space ≤ frame1.space :=
  frame417.inclusion frame1 witness1524 (by decide)
def edge1524 : CertifiedEdge catalog where
  old := 417
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1524_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1525 : Fin frame418.rank → ℕ := ![1,2,4,72,80,32,128,256]
theorem edge1525_span : frame418.space ≤ frame1.space :=
  frame418.inclusion frame1 witness1525 (by decide)
def edge1525 : CertifiedEdge catalog where
  old := 418
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1525_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1526 : Fin frame419.rank → ℕ := ![1,2,132,8,144,32,64,256]
theorem edge1526_span : frame419.space ≤ frame1.space :=
  frame419.inclusion frame1 witness1526 (by decide)
def edge1526 : CertifiedEdge catalog where
  old := 419
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1526_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1527 : Fin frame420.rank → ℕ := ![1,2,260,264,272,288,320,384]
theorem edge1527_span : frame420.space ≤ frame1.space :=
  frame420.inclusion frame1 witness1527 (by decide)
def edge1527 : CertifiedEdge catalog where
  old := 420
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1527_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1528 : Fin frame421.rank → ℕ := ![1,2,260,264,16,32,64,128]
theorem edge1528_span : frame421.space ≤ frame1.space :=
  frame421.inclusion frame1 witness1528 (by decide)
def edge1528 : CertifiedEdge catalog where
  old := 421
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1528_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1529 : Fin frame422.rank → ℕ := ![1,2,68,8,16,96,128,256]
theorem edge1529_span : frame422.space ≤ frame1.space :=
  frame422.inclusion frame1 witness1529 (by decide)
def edge1529 : CertifiedEdge catalog where
  old := 422
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge1529_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1530 : Fin frame423.rank → ℕ := ![3]
theorem edge1530_span : frame423.space ≤ frame17.space :=
  frame423.inclusion frame17 witness1530 (by decide)
def edge1530 : CertifiedEdge catalog where
  old := 423
  next := 17
  rank := 1
  good := by
    constructor
    · exact edge1530_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1531 : Fin frame423.rank → ℕ := ![1]
theorem edge1531_span : frame423.space ≤ frame28.space :=
  frame423.inclusion frame28 witness1531 (by decide)
def edge1531 : CertifiedEdge catalog where
  old := 423
  next := 28
  rank := 1
  good := by
    constructor
    · exact edge1531_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1532 : Fin frame423.rank → ℕ := ![2]
theorem edge1532_span : frame423.space ≤ frame46.space :=
  frame423.inclusion frame46 witness1532 (by decide)
def edge1532 : CertifiedEdge catalog where
  old := 423
  next := 46
  rank := 1
  good := by
    constructor
    · exact edge1532_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1533 : Fin frame423.rank → ℕ := ![2]
theorem edge1533_span : frame423.space ≤ frame57.space :=
  frame423.inclusion frame57 witness1533 (by decide)
def edge1533 : CertifiedEdge catalog where
  old := 423
  next := 57
  rank := 1
  good := by
    constructor
    · exact edge1533_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1534 : Fin frame423.rank → ℕ := ![2]
theorem edge1534_span : frame423.space ≤ frame75.space :=
  frame423.inclusion frame75 witness1534 (by decide)
def edge1534 : CertifiedEdge catalog where
  old := 423
  next := 75
  rank := 1
  good := by
    constructor
    · exact edge1534_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1535 : Fin frame423.rank → ℕ := ![2]
theorem edge1535_span : frame423.space ≤ frame86.space :=
  frame423.inclusion frame86 witness1535 (by decide)
def edge1535 : CertifiedEdge catalog where
  old := 423
  next := 86
  rank := 1
  good := by
    constructor
    · exact edge1535_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
