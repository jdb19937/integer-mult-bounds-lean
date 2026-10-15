module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness608 : Fin frame103.rank → ℕ := ![3]
theorem edge608_span : frame103.space ≤ frame109.space :=
  frame103.inclusion frame109 witness608 (by decide)
def edge608 : CertifiedEdge catalog where
  old := 103
  next := 109
  rank := 1
  good := by
    constructor
    · exact edge608_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness609 : Fin frame103.rank → ℕ := ![3]
theorem edge609_span : frame103.space ≤ frame111.space :=
  frame103.inclusion frame111 witness609 (by decide)
def edge609 : CertifiedEdge catalog where
  old := 103
  next := 111
  rank := 1
  good := by
    constructor
    · exact edge609_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness610 : Fin frame103.rank → ℕ := ![3]
theorem edge610_span : frame103.space ≤ frame114.space :=
  frame103.inclusion frame114 witness610 (by decide)
def edge610 : CertifiedEdge catalog where
  old := 103
  next := 114
  rank := 1
  good := by
    constructor
    · exact edge610_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness611 : Fin frame104.rank → ℕ := ![2,4]
theorem edge611_span : frame104.space ≤ frame535.space :=
  frame104.inclusion frame535 witness611 (by decide)
def edge611 : CertifiedEdge catalog where
  old := 104
  next := 535
  rank := 1
  good := by
    constructor
    · exact edge611_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness612 : Fin frame104.rank → ℕ := ![2,4]
theorem edge612_span : frame104.space ≤ frame537.space :=
  frame104.inclusion frame537 witness612 (by decide)
def edge612 : CertifiedEdge catalog where
  old := 104
  next := 537
  rank := 1
  good := by
    constructor
    · exact edge612_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness613 : Fin frame104.rank → ℕ := ![4,8]
theorem edge613_span : frame104.space ≤ frame593.space :=
  frame104.inclusion frame593 witness613 (by decide)
def edge613 : CertifiedEdge catalog where
  old := 104
  next := 593
  rank := 2
  good := by
    constructor
    · exact edge613_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness614 : Fin frame104.rank → ℕ := ![40,112]
theorem edge614_span : frame104.space ≤ frame742.space :=
  frame104.inclusion frame742 witness614 (by decide)
def edge614 : CertifiedEdge catalog where
  old := 104
  next := 742
  rank := 5
  good := by
    constructor
    · exact edge614_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness615 : Fin frame105.rank → ℕ := ![2,4]
theorem edge615_span : frame105.space ≤ frame117.space :=
  frame105.inclusion frame117 witness615 (by decide)
def edge615 : CertifiedEdge catalog where
  old := 105
  next := 117
  rank := 1
  good := by
    constructor
    · exact edge615_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness616 : Fin frame105.rank → ℕ := ![2,4]
theorem edge616_span : frame105.space ≤ frame123.space :=
  frame105.inclusion frame123 witness616 (by decide)
def edge616 : CertifiedEdge catalog where
  old := 105
  next := 123
  rank := 1
  good := by
    constructor
    · exact edge616_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness617 : Fin frame106.rank → ℕ := ![2,4]
theorem edge617_span : frame106.space ≤ frame119.space :=
  frame106.inclusion frame119 witness617 (by decide)
def edge617 : CertifiedEdge catalog where
  old := 106
  next := 119
  rank := 1
  good := by
    constructor
    · exact edge617_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness618 : Fin frame106.rank → ℕ := ![2,4]
theorem edge618_span : frame106.space ≤ frame121.space :=
  frame106.inclusion frame121 witness618 (by decide)
def edge618 : CertifiedEdge catalog where
  old := 106
  next := 121
  rank := 1
  good := by
    constructor
    · exact edge618_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness619 : Fin frame107.rank → ℕ := ![1,6]
theorem edge619_span : frame107.space ≤ frame535.space :=
  frame107.inclusion frame535 witness619 (by decide)
def edge619 : CertifiedEdge catalog where
  old := 107
  next := 535
  rank := 1
  good := by
    constructor
    · exact edge619_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness620 : Fin frame107.rank → ℕ := ![1,4]
theorem edge620_span : frame107.space ≤ frame536.space :=
  frame107.inclusion frame536 witness620 (by decide)
def edge620 : CertifiedEdge catalog where
  old := 107
  next := 536
  rank := 1
  good := by
    constructor
    · exact edge620_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness621 : Fin frame107.rank → ℕ := ![67,24]
theorem edge621_span : frame107.space ≤ frame743.space :=
  frame107.inclusion frame743 witness621 (by decide)
def edge621 : CertifiedEdge catalog where
  old := 107
  next := 743
  rank := 5
  good := by
    constructor
    · exact edge621_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness622 : Fin frame107.rank → ℕ := ![67,24]
theorem edge622_span : frame107.space ≤ frame744.space :=
  frame107.inclusion frame744 witness622 (by decide)
def edge622 : CertifiedEdge catalog where
  old := 107
  next := 744
  rank := 5
  good := by
    constructor
    · exact edge622_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness623 : Fin frame108.rank → ℕ := ![5,6]
theorem edge623_span : frame108.space ≤ frame117.space :=
  frame108.inclusion frame117 witness623 (by decide)
def edge623 : CertifiedEdge catalog where
  old := 108
  next := 117
  rank := 1
  good := by
    constructor
    · exact edge623_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness624 : Fin frame108.rank → ℕ := ![5,6]
theorem edge624_span : frame108.space ≤ frame122.space :=
  frame108.inclusion frame122 witness624 (by decide)
def edge624 : CertifiedEdge catalog where
  old := 108
  next := 122
  rank := 1
  good := by
    constructor
    · exact edge624_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness625 : Fin frame109.rank → ℕ := ![5,2]
theorem edge625_span : frame109.space ≤ frame118.space :=
  frame109.inclusion frame118 witness625 (by decide)
def edge625 : CertifiedEdge catalog where
  old := 109
  next := 118
  rank := 1
  good := by
    constructor
    · exact edge625_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness626 : Fin frame109.rank → ℕ := ![5,2]
theorem edge626_span : frame109.space ≤ frame121.space :=
  frame109.inclusion frame121 witness626 (by decide)
def edge626 : CertifiedEdge catalog where
  old := 109
  next := 121
  rank := 1
  good := by
    constructor
    · exact edge626_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness627 : Fin frame110.rank → ℕ := ![1,2]
theorem edge627_span : frame110.space ≤ frame119.space :=
  frame110.inclusion frame119 witness627 (by decide)
def edge627 : CertifiedEdge catalog where
  old := 110
  next := 119
  rank := 1
  good := by
    constructor
    · exact edge627_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness628 : Fin frame110.rank → ℕ := ![1,2]
theorem edge628_span : frame110.space ≤ frame120.space :=
  frame110.inclusion frame120 witness628 (by decide)
def edge628 : CertifiedEdge catalog where
  old := 110
  next := 120
  rank := 1
  good := by
    constructor
    · exact edge628_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness629 : Fin frame111.rank → ℕ := ![1,6]
theorem edge629_span : frame111.space ≤ frame116.space :=
  frame111.inclusion frame116 witness629 (by decide)
def edge629 : CertifiedEdge catalog where
  old := 111
  next := 116
  rank := 1
  good := by
    constructor
    · exact edge629_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness630 : Fin frame111.rank → ℕ := ![1,6]
theorem edge630_span : frame111.space ≤ frame123.space :=
  frame111.inclusion frame123 witness630 (by decide)
def edge630 : CertifiedEdge catalog where
  old := 111
  next := 123
  rank := 1
  good := by
    constructor
    · exact edge630_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness631 : Fin frame112.rank → ℕ := ![2,4]
theorem edge631_span : frame112.space ≤ frame118.space :=
  frame112.inclusion frame118 witness631 (by decide)
def edge631 : CertifiedEdge catalog where
  old := 112
  next := 118
  rank := 1
  good := by
    constructor
    · exact edge631_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness632 : Fin frame112.rank → ℕ := ![2,4]
theorem edge632_span : frame112.space ≤ frame120.space :=
  frame112.inclusion frame120 witness632 (by decide)
def edge632 : CertifiedEdge catalog where
  old := 112
  next := 120
  rank := 1
  good := by
    constructor
    · exact edge632_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness633 : Fin frame113.rank → ℕ := ![2,4]
theorem edge633_span : frame113.space ≤ frame116.space :=
  frame113.inclusion frame116 witness633 (by decide)
def edge633 : CertifiedEdge catalog where
  old := 113
  next := 116
  rank := 1
  good := by
    constructor
    · exact edge633_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness634 : Fin frame113.rank → ℕ := ![2,4]
theorem edge634_span : frame113.space ≤ frame122.space :=
  frame113.inclusion frame122 witness634 (by decide)
def edge634 : CertifiedEdge catalog where
  old := 113
  next := 122
  rank := 1
  good := by
    constructor
    · exact edge634_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness635 : Fin frame114.rank → ℕ := ![3,4]
theorem edge635_span : frame114.space ≤ frame534.space :=
  frame114.inclusion frame534 witness635 (by decide)
def edge635 : CertifiedEdge catalog where
  old := 114
  next := 534
  rank := 1
  good := by
    constructor
    · exact edge635_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness636 : Fin frame114.rank → ℕ := ![1,6]
theorem edge636_span : frame114.space ≤ frame537.space :=
  frame114.inclusion frame537 witness636 (by decide)
def edge636 : CertifiedEdge catalog where
  old := 114
  next := 537
  rank := 1
  good := by
    constructor
    · exact edge636_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness637 : Fin frame114.rank → ℕ := ![7,8]
theorem edge637_span : frame114.space ≤ frame592.space :=
  frame114.inclusion frame592 witness637 (by decide)
def edge637 : CertifiedEdge catalog where
  old := 114
  next := 592
  rank := 2
  good := by
    constructor
    · exact edge637_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness638 : Fin frame114.rank → ℕ := ![9,6]
theorem edge638_span : frame114.space ≤ frame595.space :=
  frame114.inclusion frame595 witness638 (by decide)
def edge638 : CertifiedEdge catalog where
  old := 114
  next := 595
  rank := 2
  good := by
    constructor
    · exact edge638_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness639 : Fin frame115.rank → ℕ := ![2,4]
theorem edge639_span : frame115.space ≤ frame534.space :=
  frame115.inclusion frame534 witness639 (by decide)
def edge639 : CertifiedEdge catalog where
  old := 115
  next := 534
  rank := 1
  good := by
    constructor
    · exact edge639_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
