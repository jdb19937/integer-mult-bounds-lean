module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness448 : Fin frame48.rank → ℕ := ![2,4]
theorem edge448_span : frame48.space ≤ frame63.space :=
  frame48.inclusion frame63 witness448 (by decide)
def edge448 : CertifiedEdge catalog where
  old := 48
  next := 63
  rank := 1
  good := by
    constructor
    · exact edge448_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness449 : Fin frame49.rank → ℕ := ![1,4]
theorem edge449_span : frame49.space ≤ frame439.space :=
  frame49.inclusion frame439 witness449 (by decide)
def edge449 : CertifiedEdge catalog where
  old := 49
  next := 439
  rank := 1
  good := by
    constructor
    · exact edge449_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness450 : Fin frame49.rank → ℕ := ![1,12]
theorem edge450_span : frame49.space ≤ frame443.space :=
  frame49.inclusion frame443 witness450 (by decide)
def edge450 : CertifiedEdge catalog where
  old := 49
  next := 443
  rank := 2
  good := by
    constructor
    · exact edge450_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness451 : Fin frame49.rank → ℕ := ![1,4]
theorem edge451_span : frame49.space ≤ frame525.space :=
  frame49.inclusion frame525 witness451 (by decide)
def edge451 : CertifiedEdge catalog where
  old := 49
  next := 525
  rank := 1
  good := by
    constructor
    · exact edge451_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness452 : Fin frame49.rank → ℕ := ![1,12]
theorem edge452_span : frame49.space ≤ frame528.space :=
  frame49.inclusion frame528 witness452 (by decide)
def edge452 : CertifiedEdge catalog where
  old := 49
  next := 528
  rank := 2
  good := by
    constructor
    · exact edge452_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness453 : Fin frame50.rank → ℕ := ![1,4]
theorem edge453_span : frame50.space ≤ frame59.space :=
  frame50.inclusion frame59 witness453 (by decide)
def edge453 : CertifiedEdge catalog where
  old := 50
  next := 59
  rank := 1
  good := by
    constructor
    · exact edge453_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness454 : Fin frame50.rank → ℕ := ![1,4]
theorem edge454_span : frame50.space ≤ frame64.space :=
  frame50.inclusion frame64 witness454 (by decide)
def edge454 : CertifiedEdge catalog where
  old := 50
  next := 64
  rank := 1
  good := by
    constructor
    · exact edge454_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness455 : Fin frame51.rank → ℕ := ![1,4]
theorem edge455_span : frame51.space ≤ frame60.space :=
  frame51.inclusion frame60 witness455 (by decide)
def edge455 : CertifiedEdge catalog where
  old := 51
  next := 60
  rank := 1
  good := by
    constructor
    · exact edge455_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness456 : Fin frame51.rank → ℕ := ![1,4]
theorem edge456_span : frame51.space ≤ frame63.space :=
  frame51.inclusion frame63 witness456 (by decide)
def edge456 : CertifiedEdge catalog where
  old := 51
  next := 63
  rank := 1
  good := by
    constructor
    · exact edge456_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness457 : Fin frame52.rank → ℕ := ![1,4]
theorem edge457_span : frame52.space ≤ frame61.space :=
  frame52.inclusion frame61 witness457 (by decide)
def edge457 : CertifiedEdge catalog where
  old := 52
  next := 61
  rank := 1
  good := by
    constructor
    · exact edge457_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness458 : Fin frame52.rank → ℕ := ![1,4]
theorem edge458_span : frame52.space ≤ frame62.space :=
  frame52.inclusion frame62 witness458 (by decide)
def edge458 : CertifiedEdge catalog where
  old := 52
  next := 62
  rank := 1
  good := by
    constructor
    · exact edge458_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness459 : Fin frame53.rank → ℕ := ![1,4]
theorem edge459_span : frame53.space ≤ frame58.space :=
  frame53.inclusion frame58 witness459 (by decide)
def edge459 : CertifiedEdge catalog where
  old := 53
  next := 58
  rank := 1
  good := by
    constructor
    · exact edge459_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness460 : Fin frame53.rank → ℕ := ![1,4]
theorem edge460_span : frame53.space ≤ frame65.space :=
  frame53.inclusion frame65 witness460 (by decide)
def edge460 : CertifiedEdge catalog where
  old := 53
  next := 65
  rank := 1
  good := by
    constructor
    · exact edge460_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness461 : Fin frame54.rank → ℕ := ![2,4]
theorem edge461_span : frame54.space ≤ frame60.space :=
  frame54.inclusion frame60 witness461 (by decide)
def edge461 : CertifiedEdge catalog where
  old := 54
  next := 60
  rank := 1
  good := by
    constructor
    · exact edge461_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness462 : Fin frame54.rank → ℕ := ![2,4]
theorem edge462_span : frame54.space ≤ frame62.space :=
  frame54.inclusion frame62 witness462 (by decide)
def edge462 : CertifiedEdge catalog where
  old := 54
  next := 62
  rank := 1
  good := by
    constructor
    · exact edge462_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness463 : Fin frame55.rank → ℕ := ![2,4]
theorem edge463_span : frame55.space ≤ frame58.space :=
  frame55.inclusion frame58 witness463 (by decide)
def edge463 : CertifiedEdge catalog where
  old := 55
  next := 58
  rank := 1
  good := by
    constructor
    · exact edge463_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness464 : Fin frame55.rank → ℕ := ![2,4]
theorem edge464_span : frame55.space ≤ frame64.space :=
  frame55.inclusion frame64 witness464 (by decide)
def edge464 : CertifiedEdge catalog where
  old := 55
  next := 64
  rank := 1
  good := by
    constructor
    · exact edge464_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness465 : Fin frame56.rank → ℕ := ![1,4]
theorem edge465_span : frame56.space ≤ frame467.space :=
  frame56.inclusion frame467 witness465 (by decide)
def edge465 : CertifiedEdge catalog where
  old := 56
  next := 467
  rank := 1
  good := by
    constructor
    · exact edge465_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness466 : Fin frame56.rank → ℕ := ![1,8]
theorem edge466_span : frame56.space ≤ frame470.space :=
  frame56.inclusion frame470 witness466 (by decide)
def edge466 : CertifiedEdge catalog where
  old := 56
  next := 470
  rank := 2
  good := by
    constructor
    · exact edge466_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness467 : Fin frame56.rank → ℕ := ![1,4]
theorem edge467_span : frame56.space ≤ frame505.space :=
  frame56.inclusion frame505 witness467 (by decide)
def edge467 : CertifiedEdge catalog where
  old := 56
  next := 505
  rank := 1
  good := by
    constructor
    · exact edge467_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness468 : Fin frame56.rank → ℕ := ![1,8]
theorem edge468_span : frame56.space ≤ frame509.space :=
  frame56.inclusion frame509 witness468 (by decide)
def edge468 : CertifiedEdge catalog where
  old := 56
  next := 509
  rank := 2
  good := by
    constructor
    · exact edge468_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness469 : Fin frame57.rank → ℕ := ![1,4]
theorem edge469_span : frame57.space ≤ frame506.space :=
  frame57.inclusion frame506 witness469 (by decide)
def edge469 : CertifiedEdge catalog where
  old := 57
  next := 506
  rank := 1
  good := by
    constructor
    · exact edge469_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness470 : Fin frame57.rank → ℕ := ![18,24]
theorem edge470_span : frame57.space ≤ frame512.space :=
  frame57.inclusion frame512 witness470 (by decide)
def edge470 : CertifiedEdge catalog where
  old := 57
  next := 512
  rank := 4
  good := by
    constructor
    · exact edge470_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness471 : Fin frame57.rank → ℕ := ![2,4]
theorem edge471_span : frame57.space ≤ frame525.space :=
  frame57.inclusion frame525 witness471 (by decide)
def edge471 : CertifiedEdge catalog where
  old := 57
  next := 525
  rank := 1
  good := by
    constructor
    · exact edge471_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness472 : Fin frame57.rank → ℕ := ![2,24]
theorem edge472_span : frame57.space ≤ frame531.space :=
  frame57.inclusion frame531 witness472 (by decide)
def edge472 : CertifiedEdge catalog where
  old := 57
  next := 531
  rank := 4
  good := by
    constructor
    · exact edge472_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness473 : Fin frame58.rank → ℕ := ![1,2,12]
theorem edge473_span : frame58.space ≤ frame66.space :=
  frame58.inclusion frame66 witness473 (by decide)
def edge473 : CertifiedEdge catalog where
  old := 58
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge473_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness474 : Fin frame58.rank → ℕ := ![33,34,28]
theorem edge474_span : frame58.space ≤ frame654.space :=
  frame58.inclusion frame654 witness474 (by decide)
def edge474 : CertifiedEdge catalog where
  old := 58
  next := 654
  rank := 3
  good := by
    constructor
    · exact edge474_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness475 : Fin frame58.rank → ℕ := ![33,34,28]
theorem edge475_span : frame58.space ≤ frame670.space :=
  frame58.inclusion frame670 witness475 (by decide)
def edge475 : CertifiedEdge catalog where
  old := 58
  next := 670
  rank := 3
  good := by
    constructor
    · exact edge475_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness476 : Fin frame59.rank → ℕ := ![9,10,12]
theorem edge476_span : frame59.space ≤ frame66.space :=
  frame59.inclusion frame66 witness476 (by decide)
def edge476 : CertifiedEdge catalog where
  old := 59
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge476_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness477 : Fin frame59.rank → ℕ := ![9,10,28]
theorem edge477_span : frame59.space ≤ frame655.space :=
  frame59.inclusion frame655 witness477 (by decide)
def edge477 : CertifiedEdge catalog where
  old := 59
  next := 655
  rank := 3
  good := by
    constructor
    · exact edge477_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness478 : Fin frame59.rank → ℕ := ![9,10,28]
theorem edge478_span : frame59.space ≤ frame671.space :=
  frame59.inclusion frame671 witness478 (by decide)
def edge478 : CertifiedEdge catalog where
  old := 59
  next := 671
  rank := 3
  good := by
    constructor
    · exact edge478_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness479 : Fin frame60.rank → ℕ := ![1,10,4]
theorem edge479_span : frame60.space ≤ frame66.space :=
  frame60.inclusion frame66 witness479 (by decide)
def edge479 : CertifiedEdge catalog where
  old := 60
  next := 66
  rank := 1
  good := by
    constructor
    · exact edge479_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
