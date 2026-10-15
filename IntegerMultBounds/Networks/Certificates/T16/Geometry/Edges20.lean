module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness640 : Fin frame115.rank → ℕ := ![2,4]
theorem edge640_span : frame115.space ≤ frame536.space :=
  frame115.inclusion frame536 witness640 (by decide)
def edge640 : CertifiedEdge catalog where
  old := 115
  next := 536
  rank := 1
  good := by
    constructor
    · exact edge640_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness641 : Fin frame115.rank → ℕ := ![10,12]
theorem edge641_span : frame115.space ≤ frame594.space :=
  frame115.inclusion frame594 witness641 (by decide)
def edge641 : CertifiedEdge catalog where
  old := 115
  next := 594
  rank := 2
  good := by
    constructor
    · exact edge641_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness642 : Fin frame115.rank → ℕ := ![20,88]
theorem edge642_span : frame115.space ≤ frame742.space :=
  frame115.inclusion frame742 witness642 (by decide)
def edge642 : CertifiedEdge catalog where
  old := 115
  next := 742
  rank := 5
  good := by
    constructor
    · exact edge642_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness643 : Fin frame116.rank → ℕ := ![1,6,8]
theorem edge643_span : frame116.space ≤ frame124.space :=
  frame116.inclusion frame124 witness643 (by decide)
def edge643 : CertifiedEdge catalog where
  old := 116
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge643_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness644 : Fin frame116.rank → ℕ := ![17,38,40]
theorem edge644_span : frame116.space ≤ frame638.space :=
  frame116.inclusion frame638 witness644 (by decide)
def edge644 : CertifiedEdge catalog where
  old := 116
  next := 638
  rank := 3
  good := by
    constructor
    · exact edge644_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness645 : Fin frame116.rank → ℕ := ![35,12,16]
theorem edge645_span : frame116.space ≤ frame670.space :=
  frame116.inclusion frame670 witness645 (by decide)
def edge645 : CertifiedEdge catalog where
  old := 116
  next := 670
  rank := 3
  good := by
    constructor
    · exact edge645_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness646 : Fin frame117.rank → ℕ := ![9,10,4]
theorem edge646_span : frame117.space ≤ frame124.space :=
  frame117.inclusion frame124 witness646 (by decide)
def edge646 : CertifiedEdge catalog where
  old := 117
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge646_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness647 : Fin frame117.rank → ℕ := ![25,34,36]
theorem edge647_span : frame117.space ≤ frame639.space :=
  frame117.inclusion frame639 witness647 (by decide)
def edge647 : CertifiedEdge catalog where
  old := 117
  next := 639
  rank := 3
  good := by
    constructor
    · exact edge647_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness648 : Fin frame117.rank → ℕ := ![51,20,8]
theorem edge648_span : frame117.space ≤ frame671.space :=
  frame117.inclusion frame671 witness648 (by decide)
def edge648 : CertifiedEdge catalog where
  old := 117
  next := 671
  rank := 3
  good := by
    constructor
    · exact edge648_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness649 : Fin frame118.rank → ℕ := ![5,2,8]
theorem edge649_span : frame118.space ≤ frame124.space :=
  frame118.inclusion frame124 witness649 (by decide)
def edge649 : CertifiedEdge catalog where
  old := 118
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge649_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness650 : Fin frame118.rank → ℕ := ![43,4,16]
theorem edge650_span : frame118.space ≤ frame646.space :=
  frame118.inclusion frame646 witness650 (by decide)
def edge650 : CertifiedEdge catalog where
  old := 118
  next := 646
  rank := 3
  good := by
    constructor
    · exact edge650_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness651 : Fin frame118.rank → ℕ := ![53,18,24]
theorem edge651_span : frame118.space ≤ frame680.space :=
  frame118.inclusion frame680 witness651 (by decide)
def edge651 : CertifiedEdge catalog where
  old := 118
  next := 680
  rank := 3
  good := by
    constructor
    · exact edge651_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness652 : Fin frame119.rank → ℕ := ![1,2,4]
theorem edge652_span : frame119.space ≤ frame124.space :=
  frame119.inclusion frame124 witness652 (by decide)
def edge652 : CertifiedEdge catalog where
  old := 119
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge652_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness653 : Fin frame119.rank → ℕ := ![19,36,8]
theorem edge653_span : frame119.space ≤ frame647.space :=
  frame119.inclusion frame647 witness653 (by decide)
def edge653 : CertifiedEdge catalog where
  old := 119
  next := 647
  rank := 3
  good := by
    constructor
    · exact edge653_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness654 : Fin frame119.rank → ℕ := ![1,50,20]
theorem edge654_span : frame119.space ≤ frame681.space :=
  frame119.inclusion frame681 witness654 (by decide)
def edge654 : CertifiedEdge catalog where
  old := 119
  next := 681
  rank := 3
  good := by
    constructor
    · exact edge654_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness655 : Fin frame120.rank → ℕ := ![1,2,8]
theorem edge655_span : frame120.space ≤ frame124.space :=
  frame120.inclusion frame124 witness655 (by decide)
def edge655 : CertifiedEdge catalog where
  old := 120
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge655_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness656 : Fin frame120.rank → ℕ := ![19,36,40]
theorem edge656_span : frame120.space ≤ frame690.space :=
  frame120.inclusion frame690 witness656 (by decide)
def edge656 : CertifiedEdge catalog where
  old := 120
  next := 690
  rank := 3
  good := by
    constructor
    · exact edge656_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness657 : Fin frame120.rank → ℕ := ![1,50,56]
theorem edge657_span : frame120.space ≤ frame718.space :=
  frame120.inclusion frame718 witness657 (by decide)
def edge657 : CertifiedEdge catalog where
  old := 120
  next := 718
  rank := 3
  good := by
    constructor
    · exact edge657_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness658 : Fin frame121.rank → ℕ := ![9,2,4]
theorem edge658_span : frame121.space ≤ frame124.space :=
  frame121.inclusion frame124 witness658 (by decide)
def edge658 : CertifiedEdge catalog where
  old := 121
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge658_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness659 : Fin frame121.rank → ℕ := ![51,4,8]
theorem edge659_span : frame121.space ≤ frame691.space :=
  frame121.inclusion frame691 witness659 (by decide)
def edge659 : CertifiedEdge catalog where
  old := 121
  next := 691
  rank := 3
  good := by
    constructor
    · exact edge659_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness660 : Fin frame121.rank → ℕ := ![57,18,20]
theorem edge660_span : frame121.space ≤ frame719.space :=
  frame121.inclusion frame719 witness660 (by decide)
def edge660 : CertifiedEdge catalog where
  old := 121
  next := 719
  rank := 3
  good := by
    constructor
    · exact edge660_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness661 : Fin frame122.rank → ℕ := ![5,6,8]
theorem edge661_span : frame122.space ≤ frame124.space :=
  frame122.inclusion frame124 witness661 (by decide)
def edge661 : CertifiedEdge catalog where
  old := 122
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge661_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness662 : Fin frame122.rank → ℕ := ![41,18,20]
theorem edge662_span : frame122.space ≤ frame700.space :=
  frame122.inclusion frame700 witness662 (by decide)
def edge662 : CertifiedEdge catalog where
  old := 122
  next := 700
  rank := 3
  good := by
    constructor
    · exact edge662_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness663 : Fin frame122.rank → ℕ := ![11,44,48]
theorem edge663_span : frame122.space ≤ frame726.space :=
  frame122.inclusion frame726 witness663 (by decide)
def edge663 : CertifiedEdge catalog where
  old := 122
  next := 726
  rank := 3
  good := by
    constructor
    · exact edge663_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness664 : Fin frame123.rank → ℕ := ![1,10,4]
theorem edge664_span : frame123.space ≤ frame124.space :=
  frame123.inclusion frame124 witness664 (by decide)
def edge664 : CertifiedEdge catalog where
  old := 123
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge664_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness665 : Fin frame123.rank → ℕ := ![17,42,36]
theorem edge665_span : frame123.space ≤ frame701.space :=
  frame123.inclusion frame701 witness665 (by decide)
def edge665 : CertifiedEdge catalog where
  old := 123
  next := 701
  rank := 3
  good := by
    constructor
    · exact edge665_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness666 : Fin frame123.rank → ℕ := ![35,20,8]
theorem edge666_span : frame123.space ≤ frame727.space :=
  frame123.inclusion frame727 witness666 (by decide)
def edge666 : CertifiedEdge catalog where
  old := 123
  next := 727
  rank := 3
  good := by
    constructor
    · exact edge666_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness667 : Fin frame124.rank → ℕ := ![67,420,296,176]
theorem edge667_span : frame124.space ≤ frame1.space :=
  frame124.inclusion frame1 witness667 (by decide)
def edge667 : CertifiedEdge catalog where
  old := 124
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge667_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness668 : Fin frame124.rank → ℕ := ![67,164,168,48]
theorem edge668_span : frame124.space ≤ frame415.space :=
  frame124.inclusion frame415 witness668 (by decide)
def edge668 : CertifiedEdge catalog where
  old := 124
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge668_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness669 : Fin frame124.rank → ℕ := ![67,164,40,176]
theorem edge669_span : frame124.space ≤ frame417.space :=
  frame124.inclusion frame417 witness669 (by decide)
def edge669 : CertifiedEdge catalog where
  old := 124
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge669_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness670 : Fin frame124.rank → ℕ := ![67,164,168,48]
theorem edge670_span : frame124.space ≤ frame419.space :=
  frame124.inclusion frame419 witness670 (by decide)
def edge670 : CertifiedEdge catalog where
  old := 124
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge670_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness671 : Fin frame124.rank → ℕ := ![67,164,40,176]
theorem edge671_span : frame124.space ≤ frame421.space :=
  frame124.inclusion frame421 witness671 (by decide)
def edge671 : CertifiedEdge catalog where
  old := 124
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge671_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
