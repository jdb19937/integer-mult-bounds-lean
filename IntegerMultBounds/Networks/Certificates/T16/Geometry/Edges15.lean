module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness480 : Fin frame60.rank → ℕ := ![1,42,20]
theorem edge480_span : frame60.space ≤ frame662.space :=
  frame60.inclusion frame662 witness480 (by decide)
def edge480 : CertifiedEdge catalog where
  old := 60
  next := 662
  rank := 3
  good := by
    constructor
    · exact edge480_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness481 : Fin frame60.rank → ℕ := ![1,42,20]
theorem edge481_span : frame60.space ≤ frame678.space :=
  frame60.inclusion frame678 witness481 (by decide)
def edge481 : CertifiedEdge catalog where
  old := 60
  next := 678
  rank := 3
  good := by
    constructor
    · exact edge481_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness482 : Fin frame61.rank → ℕ := ![9,2,4]
theorem edge482_span : frame61.space ≤ frame66.space :=
  frame61.inclusion frame66 witness482 (by decide)
def edge482 : CertifiedEdge catalog where
  old := 61
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge482_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness483 : Fin frame61.rank → ℕ := ![41,2,20]
theorem edge483_span : frame61.space ≤ frame663.space :=
  frame61.inclusion frame663 witness483 (by decide)
def edge483 : CertifiedEdge catalog where
  old := 61
  next := 663
  rank := 3
  good := by
    constructor
    · exact edge483_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness484 : Fin frame61.rank → ℕ := ![41,2,20]
theorem edge484_span : frame61.space ≤ frame679.space :=
  frame61.inclusion frame679 witness484 (by decide)
def edge484 : CertifiedEdge catalog where
  old := 61
  next := 679
  rank := 3
  good := by
    constructor
    · exact edge484_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness485 : Fin frame62.rank → ℕ := ![9,10,4]
theorem edge485_span : frame62.space ≤ frame66.space :=
  frame62.inclusion frame66 witness485 (by decide)
def edge485 : CertifiedEdge catalog where
  old := 62
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge485_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness486 : Fin frame62.rank → ℕ := ![17,18,44]
theorem edge486_span : frame62.space ≤ frame686.space :=
  frame62.inclusion frame686 witness486 (by decide)
def edge486 : CertifiedEdge catalog where
  old := 62
  next := 686
  rank := 3
  good := by
    constructor
    · exact edge486_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness487 : Fin frame62.rank → ℕ := ![9,10,52]
theorem edge487_span : frame62.space ≤ frame702.space :=
  frame62.inclusion frame702 witness487 (by decide)
def edge487 : CertifiedEdge catalog where
  old := 62
  next := 702
  rank := 3
  good := by
    constructor
    · exact edge487_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness488 : Fin frame63.rank → ℕ := ![1,2,4]
theorem edge488_span : frame63.space ≤ frame66.space :=
  frame63.inclusion frame66 witness488 (by decide)
def edge488 : CertifiedEdge catalog where
  old := 63
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge488_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness489 : Fin frame63.rank → ℕ := ![33,34,52]
theorem edge489_span : frame63.space ≤ frame687.space :=
  frame63.inclusion frame687 witness489 (by decide)
def edge489 : CertifiedEdge catalog where
  old := 63
  next := 687
  rank := 3
  good := by
    constructor
    · exact edge489_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness490 : Fin frame63.rank → ℕ := ![33,34,36]
theorem edge490_span : frame63.space ≤ frame703.space :=
  frame63.inclusion frame703 witness490 (by decide)
def edge490 : CertifiedEdge catalog where
  old := 63
  next := 703
  rank := 3
  good := by
    constructor
    · exact edge490_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness491 : Fin frame64.rank → ℕ := ![9,2,12]
theorem edge491_span : frame64.space ≤ frame66.space :=
  frame64.inclusion frame66 witness491 (by decide)
def edge491 : CertifiedEdge catalog where
  old := 64
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge491_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness492 : Fin frame64.rank → ℕ := ![1,50,12]
theorem edge492_span : frame64.space ≤ frame694.space :=
  frame64.inclusion frame694 witness492 (by decide)
def edge492 : CertifiedEdge catalog where
  old := 64
  next := 694
  rank := 3
  good := by
    constructor
    · exact edge492_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness493 : Fin frame64.rank → ℕ := ![9,18,12]
theorem edge493_span : frame64.space ≤ frame710.space :=
  frame64.inclusion frame710 witness493 (by decide)
def edge493 : CertifiedEdge catalog where
  old := 64
  next := 710
  rank := 3
  good := by
    constructor
    · exact edge493_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness494 : Fin frame65.rank → ℕ := ![1,10,12]
theorem edge494_span : frame65.space ≤ frame66.space :=
  frame65.inclusion frame66 witness494 (by decide)
def edge494 : CertifiedEdge catalog where
  old := 65
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge494_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness495 : Fin frame65.rank → ℕ := ![49,2,12]
theorem edge495_span : frame65.space ≤ frame695.space :=
  frame65.inclusion frame695 witness495 (by decide)
def edge495 : CertifiedEdge catalog where
  old := 65
  next := 695
  rank := 3
  good := by
    constructor
    · exact edge495_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness496 : Fin frame65.rank → ℕ := ![17,10,12]
theorem edge496_span : frame65.space ≤ frame711.space :=
  frame65.inclusion frame711 witness496 (by decide)
def edge496 : CertifiedEdge catalog where
  old := 65
  next := 711
  rank := 3
  good := by
    constructor
    · exact edge496_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness497 : Fin frame66.rank → ℕ := ![321,322,340,360]
theorem edge497_span : frame66.space ≤ frame1.space :=
  frame66.inclusion frame1 witness497 (by decide)
def edge497 : CertifiedEdge catalog where
  old := 66
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge497_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness498 : Fin frame66.rank → ℕ := ![193,194,212,232]
theorem edge498_span : frame66.space ≤ frame415.space :=
  frame66.inclusion frame415 witness498 (by decide)
def edge498 : CertifiedEdge catalog where
  old := 66
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge498_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness499 : Fin frame66.rank → ℕ := ![65,66,84,104]
theorem edge499_span : frame66.space ≤ frame416.space :=
  frame66.inclusion frame416 witness499 (by decide)
def edge499 : CertifiedEdge catalog where
  old := 66
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge499_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness500 : Fin frame66.rank → ℕ := ![193,194,212,232]
theorem edge500_span : frame66.space ≤ frame419.space :=
  frame66.inclusion frame419 witness500 (by decide)
def edge500 : CertifiedEdge catalog where
  old := 66
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge500_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness501 : Fin frame66.rank → ℕ := ![65,66,84,104]
theorem edge501_span : frame66.space ≤ frame420.space :=
  frame66.inclusion frame420 witness501 (by decide)
def edge501 : CertifiedEdge catalog where
  old := 66
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge501_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness502 : Fin frame67.rank → ℕ := ![1]
theorem edge502_span : frame67.space ≤ frame75.space :=
  frame67.inclusion frame75 witness502 (by decide)
def edge502 : CertifiedEdge catalog where
  old := 67
  next := 75
  rank := 1
  good := by
    constructor
    · exact edge502_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness503 : Fin frame67.rank → ℕ := ![1]
theorem edge503_span : frame67.space ≤ frame76.space :=
  frame67.inclusion frame76 witness503 (by decide)
def edge503 : CertifiedEdge catalog where
  old := 67
  next := 76
  rank := 1
  good := by
    constructor
    · exact edge503_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness504 : Fin frame67.rank → ℕ := ![1]
theorem edge504_span : frame67.space ≤ frame77.space :=
  frame67.inclusion frame77 witness504 (by decide)
def edge504 : CertifiedEdge catalog where
  old := 67
  next := 77
  rank := 1
  good := by
    constructor
    · exact edge504_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness505 : Fin frame68.rank → ℕ := ![1]
theorem edge505_span : frame68.space ≤ frame78.space :=
  frame68.inclusion frame78 witness505 (by decide)
def edge505 : CertifiedEdge catalog where
  old := 68
  next := 78
  rank := 1
  good := by
    constructor
    · exact edge505_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness506 : Fin frame68.rank → ℕ := ![2]
theorem edge506_span : frame68.space ≤ frame79.space :=
  frame68.inclusion frame79 witness506 (by decide)
def edge506 : CertifiedEdge catalog where
  old := 68
  next := 79
  rank := 1
  good := by
    constructor
    · exact edge506_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness507 : Fin frame68.rank → ℕ := ![2]
theorem edge507_span : frame68.space ≤ frame80.space :=
  frame68.inclusion frame80 witness507 (by decide)
def edge507 : CertifiedEdge catalog where
  old := 68
  next := 80
  rank := 1
  good := by
    constructor
    · exact edge507_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness508 : Fin frame69.rank → ℕ := ![2]
theorem edge508_span : frame69.space ≤ frame78.space :=
  frame69.inclusion frame78 witness508 (by decide)
def edge508 : CertifiedEdge catalog where
  old := 69
  next := 78
  rank := 1
  good := by
    constructor
    · exact edge508_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness509 : Fin frame69.rank → ℕ := ![2]
theorem edge509_span : frame69.space ≤ frame81.space :=
  frame69.inclusion frame81 witness509 (by decide)
def edge509 : CertifiedEdge catalog where
  old := 69
  next := 81
  rank := 1
  good := by
    constructor
    · exact edge509_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness510 : Fin frame69.rank → ℕ := ![2]
theorem edge510_span : frame69.space ≤ frame82.space :=
  frame69.inclusion frame82 witness510 (by decide)
def edge510 : CertifiedEdge catalog where
  old := 69
  next := 82
  rank := 1
  good := by
    constructor
    · exact edge510_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness511 : Fin frame70.rank → ℕ := ![3]
theorem edge511_span : frame70.space ≤ frame75.space :=
  frame70.inclusion frame75 witness511 (by decide)
def edge511 : CertifiedEdge catalog where
  old := 70
  next := 75
  rank := 1
  good := by
    constructor
    · exact edge511_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
