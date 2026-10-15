module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness416 : Fin frame37.rank → ℕ := ![7,72,144,224]
theorem edge416_span : frame37.space ≤ frame418.space :=
  frame37.inclusion frame418 witness416 (by decide)
def edge416 : CertifiedEdge catalog where
  old := 37
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge416_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness417 : Fin frame38.rank → ℕ := ![1]
theorem edge417_span : frame38.space ≤ frame46.space :=
  frame38.inclusion frame46 witness417 (by decide)
def edge417 : CertifiedEdge catalog where
  old := 38
  next := 46
  rank := 1
  good := by
    constructor
    · exact edge417_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness418 : Fin frame38.rank → ℕ := ![3]
theorem edge418_span : frame38.space ≤ frame47.space :=
  frame38.inclusion frame47 witness418 (by decide)
def edge418 : CertifiedEdge catalog where
  old := 38
  next := 47
  rank := 1
  good := by
    constructor
    · exact edge418_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness419 : Fin frame38.rank → ℕ := ![3]
theorem edge419_span : frame38.space ≤ frame48.space :=
  frame38.inclusion frame48 witness419 (by decide)
def edge419 : CertifiedEdge catalog where
  old := 38
  next := 48
  rank := 1
  good := by
    constructor
    · exact edge419_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness420 : Fin frame39.rank → ℕ := ![1]
theorem edge420_span : frame39.space ≤ frame49.space :=
  frame39.inclusion frame49 witness420 (by decide)
def edge420 : CertifiedEdge catalog where
  old := 39
  next := 49
  rank := 1
  good := by
    constructor
    · exact edge420_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness421 : Fin frame39.rank → ℕ := ![3]
theorem edge421_span : frame39.space ≤ frame50.space :=
  frame39.inclusion frame50 witness421 (by decide)
def edge421 : CertifiedEdge catalog where
  old := 39
  next := 50
  rank := 1
  good := by
    constructor
    · exact edge421_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness422 : Fin frame39.rank → ℕ := ![3]
theorem edge422_span : frame39.space ≤ frame51.space :=
  frame39.inclusion frame51 witness422 (by decide)
def edge422 : CertifiedEdge catalog where
  old := 39
  next := 51
  rank := 1
  good := by
    constructor
    · exact edge422_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness423 : Fin frame40.rank → ℕ := ![3]
theorem edge423_span : frame40.space ≤ frame49.space :=
  frame40.inclusion frame49 witness423 (by decide)
def edge423 : CertifiedEdge catalog where
  old := 40
  next := 49
  rank := 1
  good := by
    constructor
    · exact edge423_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness424 : Fin frame40.rank → ℕ := ![3]
theorem edge424_span : frame40.space ≤ frame52.space :=
  frame40.inclusion frame52 witness424 (by decide)
def edge424 : CertifiedEdge catalog where
  old := 40
  next := 52
  rank := 1
  good := by
    constructor
    · exact edge424_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness425 : Fin frame40.rank → ℕ := ![3]
theorem edge425_span : frame40.space ≤ frame53.space :=
  frame40.inclusion frame53 witness425 (by decide)
def edge425 : CertifiedEdge catalog where
  old := 40
  next := 53
  rank := 1
  good := by
    constructor
    · exact edge425_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness426 : Fin frame41.rank → ℕ := ![3]
theorem edge426_span : frame41.space ≤ frame46.space :=
  frame41.inclusion frame46 witness426 (by decide)
def edge426 : CertifiedEdge catalog where
  old := 41
  next := 46
  rank := 1
  good := by
    constructor
    · exact edge426_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness427 : Fin frame41.rank → ℕ := ![3]
theorem edge427_span : frame41.space ≤ frame54.space :=
  frame41.inclusion frame54 witness427 (by decide)
def edge427 : CertifiedEdge catalog where
  old := 41
  next := 54
  rank := 1
  good := by
    constructor
    · exact edge427_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness428 : Fin frame41.rank → ℕ := ![3]
theorem edge428_span : frame41.space ≤ frame55.space :=
  frame41.inclusion frame55 witness428 (by decide)
def edge428 : CertifiedEdge catalog where
  old := 41
  next := 55
  rank := 1
  good := by
    constructor
    · exact edge428_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness429 : Fin frame42.rank → ℕ := ![1]
theorem edge429_span : frame42.space ≤ frame50.space :=
  frame42.inclusion frame50 witness429 (by decide)
def edge429 : CertifiedEdge catalog where
  old := 42
  next := 50
  rank := 1
  good := by
    constructor
    · exact edge429_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness430 : Fin frame42.rank → ℕ := ![1]
theorem edge430_span : frame42.space ≤ frame52.space :=
  frame42.inclusion frame52 witness430 (by decide)
def edge430 : CertifiedEdge catalog where
  old := 42
  next := 52
  rank := 1
  good := by
    constructor
    · exact edge430_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness431 : Fin frame42.rank → ℕ := ![3]
theorem edge431_span : frame42.space ≤ frame56.space :=
  frame42.inclusion frame56 witness431 (by decide)
def edge431 : CertifiedEdge catalog where
  old := 42
  next := 56
  rank := 1
  good := by
    constructor
    · exact edge431_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness432 : Fin frame43.rank → ℕ := ![1]
theorem edge432_span : frame43.space ≤ frame47.space :=
  frame43.inclusion frame47 witness432 (by decide)
def edge432 : CertifiedEdge catalog where
  old := 43
  next := 47
  rank := 1
  good := by
    constructor
    · exact edge432_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness433 : Fin frame43.rank → ℕ := ![1]
theorem edge433_span : frame43.space ≤ frame54.space :=
  frame43.inclusion frame54 witness433 (by decide)
def edge433 : CertifiedEdge catalog where
  old := 43
  next := 54
  rank := 1
  good := by
    constructor
    · exact edge433_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness434 : Fin frame43.rank → ℕ := ![3]
theorem edge434_span : frame43.space ≤ frame57.space :=
  frame43.inclusion frame57 witness434 (by decide)
def edge434 : CertifiedEdge catalog where
  old := 43
  next := 57
  rank := 1
  good := by
    constructor
    · exact edge434_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness435 : Fin frame44.rank → ℕ := ![1]
theorem edge435_span : frame44.space ≤ frame48.space :=
  frame44.inclusion frame48 witness435 (by decide)
def edge435 : CertifiedEdge catalog where
  old := 44
  next := 48
  rank := 1
  good := by
    constructor
    · exact edge435_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness436 : Fin frame44.rank → ℕ := ![1]
theorem edge436_span : frame44.space ≤ frame55.space :=
  frame44.inclusion frame55 witness436 (by decide)
def edge436 : CertifiedEdge catalog where
  old := 44
  next := 55
  rank := 1
  good := by
    constructor
    · exact edge436_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness437 : Fin frame44.rank → ℕ := ![1]
theorem edge437_span : frame44.space ≤ frame57.space :=
  frame44.inclusion frame57 witness437 (by decide)
def edge437 : CertifiedEdge catalog where
  old := 44
  next := 57
  rank := 1
  good := by
    constructor
    · exact edge437_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness438 : Fin frame45.rank → ℕ := ![1]
theorem edge438_span : frame45.space ≤ frame51.space :=
  frame45.inclusion frame51 witness438 (by decide)
def edge438 : CertifiedEdge catalog where
  old := 45
  next := 51
  rank := 1
  good := by
    constructor
    · exact edge438_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness439 : Fin frame45.rank → ℕ := ![1]
theorem edge439_span : frame45.space ≤ frame53.space :=
  frame45.inclusion frame53 witness439 (by decide)
def edge439 : CertifiedEdge catalog where
  old := 45
  next := 53
  rank := 1
  good := by
    constructor
    · exact edge439_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness440 : Fin frame45.rank → ℕ := ![1]
theorem edge440_span : frame45.space ≤ frame56.space :=
  frame45.inclusion frame56 witness440 (by decide)
def edge440 : CertifiedEdge catalog where
  old := 45
  next := 56
  rank := 1
  good := by
    constructor
    · exact edge440_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness441 : Fin frame46.rank → ℕ := ![1,6]
theorem edge441_span : frame46.space ≤ frame440.space :=
  frame46.inclusion frame440 witness441 (by decide)
def edge441 : CertifiedEdge catalog where
  old := 46
  next := 440
  rank := 1
  good := by
    constructor
    · exact edge441_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness442 : Fin frame46.rank → ℕ := ![22,40]
theorem edge442_span : frame46.space ≤ frame446.space :=
  frame46.inclusion frame446 witness442 (by decide)
def edge442 : CertifiedEdge catalog where
  old := 46
  next := 446
  rank := 4
  good := by
    constructor
    · exact edge442_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness443 : Fin frame46.rank → ℕ := ![2,4]
theorem edge443_span : frame46.space ≤ frame467.space :=
  frame46.inclusion frame467 witness443 (by decide)
def edge443 : CertifiedEdge catalog where
  old := 46
  next := 467
  rank := 1
  good := by
    constructor
    · exact edge443_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness444 : Fin frame46.rank → ℕ := ![22,40]
theorem edge444_span : frame46.space ≤ frame473.space :=
  frame46.inclusion frame473 witness444 (by decide)
def edge444 : CertifiedEdge catalog where
  old := 46
  next := 473
  rank := 4
  good := by
    constructor
    · exact edge444_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness445 : Fin frame47.rank → ℕ := ![2,4]
theorem edge445_span : frame47.space ≤ frame59.space :=
  frame47.inclusion frame59 witness445 (by decide)
def edge445 : CertifiedEdge catalog where
  old := 47
  next := 59
  rank := 1
  good := by
    constructor
    · exact edge445_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness446 : Fin frame47.rank → ℕ := ![2,4]
theorem edge446_span : frame47.space ≤ frame65.space :=
  frame47.inclusion frame65 witness446 (by decide)
def edge446 : CertifiedEdge catalog where
  old := 47
  next := 65
  rank := 1
  good := by
    constructor
    · exact edge446_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness447 : Fin frame48.rank → ℕ := ![2,4]
theorem edge447_span : frame48.space ≤ frame61.space :=
  frame48.inclusion frame61 witness447 (by decide)
def edge447 : CertifiedEdge catalog where
  old := 48
  next := 61
  rank := 1
  good := by
    constructor
    · exact edge447_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
