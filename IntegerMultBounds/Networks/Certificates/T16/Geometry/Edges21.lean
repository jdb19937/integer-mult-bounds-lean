module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness672 : Fin frame125.rank → ℕ := ![3]
theorem edge672_span : frame125.space ≤ frame133.space :=
  frame125.inclusion frame133 witness672 (by decide)
def edge672 : CertifiedEdge catalog where
  old := 125
  next := 133
  rank := 1
  good := by
    constructor
    · exact edge672_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness673 : Fin frame125.rank → ℕ := ![3]
theorem edge673_span : frame125.space ≤ frame134.space :=
  frame125.inclusion frame134 witness673 (by decide)
def edge673 : CertifiedEdge catalog where
  old := 125
  next := 134
  rank := 1
  good := by
    constructor
    · exact edge673_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness674 : Fin frame125.rank → ℕ := ![3]
theorem edge674_span : frame125.space ≤ frame135.space :=
  frame125.inclusion frame135 witness674 (by decide)
def edge674 : CertifiedEdge catalog where
  old := 125
  next := 135
  rank := 1
  good := by
    constructor
    · exact edge674_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness675 : Fin frame126.rank → ℕ := ![1]
theorem edge675_span : frame126.space ≤ frame136.space :=
  frame126.inclusion frame136 witness675 (by decide)
def edge675 : CertifiedEdge catalog where
  old := 126
  next := 136
  rank := 1
  good := by
    constructor
    · exact edge675_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness676 : Fin frame126.rank → ℕ := ![3]
theorem edge676_span : frame126.space ≤ frame137.space :=
  frame126.inclusion frame137 witness676 (by decide)
def edge676 : CertifiedEdge catalog where
  old := 126
  next := 137
  rank := 1
  good := by
    constructor
    · exact edge676_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness677 : Fin frame126.rank → ℕ := ![3]
theorem edge677_span : frame126.space ≤ frame138.space :=
  frame126.inclusion frame138 witness677 (by decide)
def edge677 : CertifiedEdge catalog where
  old := 126
  next := 138
  rank := 1
  good := by
    constructor
    · exact edge677_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness678 : Fin frame127.rank → ℕ := ![3]
theorem edge678_span : frame127.space ≤ frame136.space :=
  frame127.inclusion frame136 witness678 (by decide)
def edge678 : CertifiedEdge catalog where
  old := 127
  next := 136
  rank := 1
  good := by
    constructor
    · exact edge678_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness679 : Fin frame127.rank → ℕ := ![3]
theorem edge679_span : frame127.space ≤ frame139.space :=
  frame127.inclusion frame139 witness679 (by decide)
def edge679 : CertifiedEdge catalog where
  old := 127
  next := 139
  rank := 1
  good := by
    constructor
    · exact edge679_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness680 : Fin frame127.rank → ℕ := ![3]
theorem edge680_span : frame127.space ≤ frame140.space :=
  frame127.inclusion frame140 witness680 (by decide)
def edge680 : CertifiedEdge catalog where
  old := 127
  next := 140
  rank := 1
  good := by
    constructor
    · exact edge680_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness681 : Fin frame128.rank → ℕ := ![1]
theorem edge681_span : frame128.space ≤ frame133.space :=
  frame128.inclusion frame133 witness681 (by decide)
def edge681 : CertifiedEdge catalog where
  old := 128
  next := 133
  rank := 1
  good := by
    constructor
    · exact edge681_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness682 : Fin frame128.rank → ℕ := ![3]
theorem edge682_span : frame128.space ≤ frame141.space :=
  frame128.inclusion frame141 witness682 (by decide)
def edge682 : CertifiedEdge catalog where
  old := 128
  next := 141
  rank := 1
  good := by
    constructor
    · exact edge682_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness683 : Fin frame128.rank → ℕ := ![3]
theorem edge683_span : frame128.space ≤ frame142.space :=
  frame128.inclusion frame142 witness683 (by decide)
def edge683 : CertifiedEdge catalog where
  old := 128
  next := 142
  rank := 1
  good := by
    constructor
    · exact edge683_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness684 : Fin frame129.rank → ℕ := ![1]
theorem edge684_span : frame129.space ≤ frame137.space :=
  frame129.inclusion frame137 witness684 (by decide)
def edge684 : CertifiedEdge catalog where
  old := 129
  next := 137
  rank := 1
  good := by
    constructor
    · exact edge684_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness685 : Fin frame129.rank → ℕ := ![1]
theorem edge685_span : frame129.space ≤ frame139.space :=
  frame129.inclusion frame139 witness685 (by decide)
def edge685 : CertifiedEdge catalog where
  old := 129
  next := 139
  rank := 1
  good := by
    constructor
    · exact edge685_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness686 : Fin frame129.rank → ℕ := ![1]
theorem edge686_span : frame129.space ≤ frame143.space :=
  frame129.inclusion frame143 witness686 (by decide)
def edge686 : CertifiedEdge catalog where
  old := 129
  next := 143
  rank := 1
  good := by
    constructor
    · exact edge686_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness687 : Fin frame130.rank → ℕ := ![1]
theorem edge687_span : frame130.space ≤ frame134.space :=
  frame130.inclusion frame134 witness687 (by decide)
def edge687 : CertifiedEdge catalog where
  old := 130
  next := 134
  rank := 1
  good := by
    constructor
    · exact edge687_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness688 : Fin frame130.rank → ℕ := ![1]
theorem edge688_span : frame130.space ≤ frame141.space :=
  frame130.inclusion frame141 witness688 (by decide)
def edge688 : CertifiedEdge catalog where
  old := 130
  next := 141
  rank := 1
  good := by
    constructor
    · exact edge688_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness689 : Fin frame130.rank → ℕ := ![3]
theorem edge689_span : frame130.space ≤ frame144.space :=
  frame130.inclusion frame144 witness689 (by decide)
def edge689 : CertifiedEdge catalog where
  old := 130
  next := 144
  rank := 1
  good := by
    constructor
    · exact edge689_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness690 : Fin frame131.rank → ℕ := ![1]
theorem edge690_span : frame131.space ≤ frame135.space :=
  frame131.inclusion frame135 witness690 (by decide)
def edge690 : CertifiedEdge catalog where
  old := 131
  next := 135
  rank := 1
  good := by
    constructor
    · exact edge690_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness691 : Fin frame131.rank → ℕ := ![1]
theorem edge691_span : frame131.space ≤ frame142.space :=
  frame131.inclusion frame142 witness691 (by decide)
def edge691 : CertifiedEdge catalog where
  old := 131
  next := 142
  rank := 1
  good := by
    constructor
    · exact edge691_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness692 : Fin frame131.rank → ℕ := ![1]
theorem edge692_span : frame131.space ≤ frame144.space :=
  frame131.inclusion frame144 witness692 (by decide)
def edge692 : CertifiedEdge catalog where
  old := 131
  next := 144
  rank := 1
  good := by
    constructor
    · exact edge692_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness693 : Fin frame132.rank → ℕ := ![1]
theorem edge693_span : frame132.space ≤ frame138.space :=
  frame132.inclusion frame138 witness693 (by decide)
def edge693 : CertifiedEdge catalog where
  old := 132
  next := 138
  rank := 1
  good := by
    constructor
    · exact edge693_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness694 : Fin frame132.rank → ℕ := ![1]
theorem edge694_span : frame132.space ≤ frame140.space :=
  frame132.inclusion frame140 witness694 (by decide)
def edge694 : CertifiedEdge catalog where
  old := 132
  next := 140
  rank := 1
  good := by
    constructor
    · exact edge694_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness695 : Fin frame132.rank → ℕ := ![3]
theorem edge695_span : frame132.space ≤ frame143.space :=
  frame132.inclusion frame143 witness695 (by decide)
def edge695 : CertifiedEdge catalog where
  old := 132
  next := 143
  rank := 1
  good := by
    constructor
    · exact edge695_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness696 : Fin frame133.rank → ℕ := ![1,4]
theorem edge696_span : frame133.space ≤ frame541.space :=
  frame133.inclusion frame541 witness696 (by decide)
def edge696 : CertifiedEdge catalog where
  old := 133
  next := 541
  rank := 1
  good := by
    constructor
    · exact edge696_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness697 : Fin frame133.rank → ℕ := ![1,4]
theorem edge697_span : frame133.space ≤ frame543.space :=
  frame133.inclusion frame543 witness697 (by decide)
def edge697 : CertifiedEdge catalog where
  old := 133
  next := 543
  rank := 1
  good := by
    constructor
    · exact edge697_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness698 : Fin frame133.rank → ℕ := ![1,12]
theorem edge698_span : frame133.space ≤ frame597.space :=
  frame133.inclusion frame597 witness698 (by decide)
def edge698 : CertifiedEdge catalog where
  old := 133
  next := 597
  rank := 2
  good := by
    constructor
    · exact edge698_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness699 : Fin frame133.rank → ℕ := ![69,24]
theorem edge699_span : frame133.space ≤ frame746.space :=
  frame133.inclusion frame746 witness699 (by decide)
def edge699 : CertifiedEdge catalog where
  old := 133
  next := 746
  rank := 5
  good := by
    constructor
    · exact edge699_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness700 : Fin frame134.rank → ℕ := ![1,4]
theorem edge700_span : frame134.space ≤ frame146.space :=
  frame134.inclusion frame146 witness700 (by decide)
def edge700 : CertifiedEdge catalog where
  old := 134
  next := 146
  rank := 1
  good := by
    constructor
    · exact edge700_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness701 : Fin frame134.rank → ℕ := ![1,4]
theorem edge701_span : frame134.space ≤ frame152.space :=
  frame134.inclusion frame152 witness701 (by decide)
def edge701 : CertifiedEdge catalog where
  old := 134
  next := 152
  rank := 1
  good := by
    constructor
    · exact edge701_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness702 : Fin frame135.rank → ℕ := ![1,4]
theorem edge702_span : frame135.space ≤ frame148.space :=
  frame135.inclusion frame148 witness702 (by decide)
def edge702 : CertifiedEdge catalog where
  old := 135
  next := 148
  rank := 1
  good := by
    constructor
    · exact edge702_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness703 : Fin frame135.rank → ℕ := ![1,4]
theorem edge703_span : frame135.space ≤ frame150.space :=
  frame135.inclusion frame150 witness703 (by decide)
def edge703 : CertifiedEdge catalog where
  old := 135
  next := 150
  rank := 1
  good := by
    constructor
    · exact edge703_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
