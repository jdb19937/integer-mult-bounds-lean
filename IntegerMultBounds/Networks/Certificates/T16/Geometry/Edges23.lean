module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness736 : Fin frame147.rank → ℕ := ![9,10,12]
theorem edge736_span : frame147.space ≤ frame672.space :=
  frame147.inclusion frame672 witness736 (by decide)
def edge736 : CertifiedEdge catalog where
  old := 147
  next := 672
  rank := 3
  good := by
    constructor
    · exact edge736_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness737 : Fin frame148.rank → ℕ := ![1,2,12]
theorem edge737_span : frame148.space ≤ frame153.space :=
  frame148.inclusion frame153 witness737 (by decide)
def edge737 : CertifiedEdge catalog where
  old := 148
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge737_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness738 : Fin frame148.rank → ℕ := ![33,34,28]
theorem edge738_span : frame148.space ≤ frame649.space :=
  frame148.inclusion frame649 witness738 (by decide)
def edge738 : CertifiedEdge catalog where
  old := 148
  next := 649
  rank := 3
  good := by
    constructor
    · exact edge738_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness739 : Fin frame148.rank → ℕ := ![17,18,12]
theorem edge739_span : frame148.space ≤ frame673.space :=
  frame148.inclusion frame673 witness739 (by decide)
def edge739 : CertifiedEdge catalog where
  old := 148
  next := 673
  rank := 3
  good := by
    constructor
    · exact edge739_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness740 : Fin frame149.rank → ℕ := ![9,2,12]
theorem edge740_span : frame149.space ≤ frame153.space :=
  frame149.inclusion frame153 witness740 (by decide)
def edge740 : CertifiedEdge catalog where
  old := 149
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge740_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness741 : Fin frame149.rank → ℕ := ![1,42,20]
theorem edge741_span : frame149.space ≤ frame698.space :=
  frame149.inclusion frame698 witness741 (by decide)
def edge741 : CertifiedEdge catalog where
  old := 149
  next := 698
  rank := 3
  good := by
    constructor
    · exact edge741_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness742 : Fin frame149.rank → ℕ := ![9,18,12]
theorem edge742_span : frame149.space ≤ frame720.space :=
  frame149.inclusion frame720 witness742 (by decide)
def edge742 : CertifiedEdge catalog where
  old := 149
  next := 720
  rank := 3
  good := by
    constructor
    · exact edge742_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness743 : Fin frame150.rank → ℕ := ![1,10,12]
theorem edge743_span : frame150.space ≤ frame153.space :=
  frame150.inclusion frame153 witness743 (by decide)
def edge743 : CertifiedEdge catalog where
  old := 150
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge743_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness744 : Fin frame150.rank → ℕ := ![41,2,20]
theorem edge744_span : frame150.space ≤ frame699.space :=
  frame150.inclusion frame699 witness744 (by decide)
def edge744 : CertifiedEdge catalog where
  old := 150
  next := 699
  rank := 3
  good := by
    constructor
    · exact edge744_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness745 : Fin frame150.rank → ℕ := ![17,10,12]
theorem edge745_span : frame150.space ≤ frame721.space :=
  frame150.inclusion frame721 witness745 (by decide)
def edge745 : CertifiedEdge catalog where
  old := 150
  next := 721
  rank := 3
  good := by
    constructor
    · exact edge745_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness746 : Fin frame151.rank → ℕ := ![1,2,4]
theorem edge746_span : frame151.space ≤ frame153.space :=
  frame151.inclusion frame153 witness746 (by decide)
def edge746 : CertifiedEdge catalog where
  old := 151
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge746_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness747 : Fin frame151.rank → ℕ := ![17,18,52]
theorem edge747_span : frame151.space ≤ frame692.space :=
  frame151.inclusion frame692 witness747 (by decide)
def edge747 : CertifiedEdge catalog where
  old := 151
  next := 692
  rank := 3
  good := by
    constructor
    · exact edge747_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness748 : Fin frame151.rank → ℕ := ![17,18,20]
theorem edge748_span : frame151.space ≤ frame728.space :=
  frame151.inclusion frame728 witness748 (by decide)
def edge748 : CertifiedEdge catalog where
  old := 151
  next := 728
  rank := 3
  good := by
    constructor
    · exact edge748_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness749 : Fin frame152.rank → ℕ := ![9,10,4]
theorem edge749_span : frame152.space ≤ frame153.space :=
  frame152.inclusion frame153 witness749 (by decide)
def edge749 : CertifiedEdge catalog where
  old := 152
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge749_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness750 : Fin frame152.rank → ℕ := ![33,34,28]
theorem edge750_span : frame152.space ≤ frame693.space :=
  frame152.inclusion frame693 witness750 (by decide)
def edge750 : CertifiedEdge catalog where
  old := 152
  next := 693
  rank := 3
  good := by
    constructor
    · exact edge750_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness751 : Fin frame152.rank → ℕ := ![9,10,20]
theorem edge751_span : frame152.space ≤ frame729.space :=
  frame152.inclusion frame729 witness751 (by decide)
def edge751 : CertifiedEdge catalog where
  old := 152
  next := 729
  rank := 3
  good := by
    constructor
    · exact edge751_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness752 : Fin frame153.rank → ℕ := ![273,274,340,408]
theorem edge752_span : frame153.space ≤ frame1.space :=
  frame153.inclusion frame1 witness752 (by decide)
def edge752 : CertifiedEdge catalog where
  old := 153
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge752_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness753 : Fin frame153.rank → ℕ := ![145,146,212,152]
theorem edge753_span : frame153.space ≤ frame415.space :=
  frame153.inclusion frame415 witness753 (by decide)
def edge753 : CertifiedEdge catalog where
  old := 153
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge753_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness754 : Fin frame153.rank → ℕ := ![17,18,84,152]
theorem edge754_span : frame153.space ≤ frame417.space :=
  frame153.inclusion frame417 witness754 (by decide)
def edge754 : CertifiedEdge catalog where
  old := 153
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge754_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness755 : Fin frame153.rank → ℕ := ![17,18,84,152]
theorem edge755_span : frame153.space ≤ frame420.space :=
  frame153.inclusion frame420 witness755 (by decide)
def edge755 : CertifiedEdge catalog where
  old := 153
  next := 420
  rank := 4
  good := by
    constructor
    · exact edge755_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness756 : Fin frame153.rank → ℕ := ![145,146,148,216]
theorem edge756_span : frame153.space ≤ frame422.space :=
  frame153.inclusion frame422 witness756 (by decide)
def edge756 : CertifiedEdge catalog where
  old := 153
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge756_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness757 : Fin frame154.rank → ℕ := ![1]
theorem edge757_span : frame154.space ≤ frame162.space :=
  frame154.inclusion frame162 witness757 (by decide)
def edge757 : CertifiedEdge catalog where
  old := 154
  next := 162
  rank := 1
  good := by
    constructor
    · exact edge757_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness758 : Fin frame154.rank → ℕ := ![3]
theorem edge758_span : frame154.space ≤ frame163.space :=
  frame154.inclusion frame163 witness758 (by decide)
def edge758 : CertifiedEdge catalog where
  old := 154
  next := 163
  rank := 1
  good := by
    constructor
    · exact edge758_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness759 : Fin frame154.rank → ℕ := ![3]
theorem edge759_span : frame154.space ≤ frame164.space :=
  frame154.inclusion frame164 witness759 (by decide)
def edge759 : CertifiedEdge catalog where
  old := 154
  next := 164
  rank := 1
  good := by
    constructor
    · exact edge759_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness760 : Fin frame155.rank → ℕ := ![3]
theorem edge760_span : frame155.space ≤ frame165.space :=
  frame155.inclusion frame165 witness760 (by decide)
def edge760 : CertifiedEdge catalog where
  old := 155
  next := 165
  rank := 1
  good := by
    constructor
    · exact edge760_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness761 : Fin frame155.rank → ℕ := ![1]
theorem edge761_span : frame155.space ≤ frame166.space :=
  frame155.inclusion frame166 witness761 (by decide)
def edge761 : CertifiedEdge catalog where
  old := 155
  next := 166
  rank := 1
  good := by
    constructor
    · exact edge761_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness762 : Fin frame155.rank → ℕ := ![1]
theorem edge762_span : frame155.space ≤ frame167.space :=
  frame155.inclusion frame167 witness762 (by decide)
def edge762 : CertifiedEdge catalog where
  old := 155
  next := 167
  rank := 1
  good := by
    constructor
    · exact edge762_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness763 : Fin frame156.rank → ℕ := ![1]
theorem edge763_span : frame156.space ≤ frame165.space :=
  frame156.inclusion frame165 witness763 (by decide)
def edge763 : CertifiedEdge catalog where
  old := 156
  next := 165
  rank := 1
  good := by
    constructor
    · exact edge763_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness764 : Fin frame156.rank → ℕ := ![1]
theorem edge764_span : frame156.space ≤ frame168.space :=
  frame156.inclusion frame168 witness764 (by decide)
def edge764 : CertifiedEdge catalog where
  old := 156
  next := 168
  rank := 1
  good := by
    constructor
    · exact edge764_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness765 : Fin frame156.rank → ℕ := ![1]
theorem edge765_span : frame156.space ≤ frame169.space :=
  frame156.inclusion frame169 witness765 (by decide)
def edge765 : CertifiedEdge catalog where
  old := 156
  next := 169
  rank := 1
  good := by
    constructor
    · exact edge765_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness766 : Fin frame157.rank → ℕ := ![3]
theorem edge766_span : frame157.space ≤ frame162.space :=
  frame157.inclusion frame162 witness766 (by decide)
def edge766 : CertifiedEdge catalog where
  old := 157
  next := 162
  rank := 1
  good := by
    constructor
    · exact edge766_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness767 : Fin frame157.rank → ℕ := ![3]
theorem edge767_span : frame157.space ≤ frame170.space :=
  frame157.inclusion frame170 witness767 (by decide)
def edge767 : CertifiedEdge catalog where
  old := 157
  next := 170
  rank := 1
  good := by
    constructor
    · exact edge767_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
