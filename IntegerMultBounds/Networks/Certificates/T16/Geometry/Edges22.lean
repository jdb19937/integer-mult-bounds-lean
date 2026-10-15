module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness704 : Fin frame136.rank → ℕ := ![2,4]
theorem edge704_span : frame136.space ≤ frame541.space :=
  frame136.inclusion frame541 witness704 (by decide)
def edge704 : CertifiedEdge catalog where
  old := 136
  next := 541
  rank := 1
  good := by
    constructor
    · exact edge704_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness705 : Fin frame136.rank → ℕ := ![2,4]
theorem edge705_span : frame136.space ≤ frame542.space :=
  frame136.inclusion frame542 witness705 (by decide)
def edge705 : CertifiedEdge catalog where
  old := 136
  next := 542
  rank := 1
  good := by
    constructor
    · exact edge705_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness706 : Fin frame136.rank → ℕ := ![70,24]
theorem edge706_span : frame136.space ≤ frame747.space :=
  frame136.inclusion frame747 witness706 (by decide)
def edge706 : CertifiedEdge catalog where
  old := 136
  next := 747
  rank := 5
  good := by
    constructor
    · exact edge706_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness707 : Fin frame136.rank → ℕ := ![6,88]
theorem edge707_span : frame136.space ≤ frame748.space :=
  frame136.inclusion frame748 witness707 (by decide)
def edge707 : CertifiedEdge catalog where
  old := 136
  next := 748
  rank := 5
  good := by
    constructor
    · exact edge707_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness708 : Fin frame137.rank → ℕ := ![2,4]
theorem edge708_span : frame137.space ≤ frame146.space :=
  frame137.inclusion frame146 witness708 (by decide)
def edge708 : CertifiedEdge catalog where
  old := 137
  next := 146
  rank := 1
  good := by
    constructor
    · exact edge708_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness709 : Fin frame137.rank → ℕ := ![2,4]
theorem edge709_span : frame137.space ≤ frame151.space :=
  frame137.inclusion frame151 witness709 (by decide)
def edge709 : CertifiedEdge catalog where
  old := 137
  next := 151
  rank := 1
  good := by
    constructor
    · exact edge709_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness710 : Fin frame138.rank → ℕ := ![2,4]
theorem edge710_span : frame138.space ≤ frame147.space :=
  frame138.inclusion frame147 witness710 (by decide)
def edge710 : CertifiedEdge catalog where
  old := 138
  next := 147
  rank := 1
  good := by
    constructor
    · exact edge710_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness711 : Fin frame138.rank → ℕ := ![2,4]
theorem edge711_span : frame138.space ≤ frame150.space :=
  frame138.inclusion frame150 witness711 (by decide)
def edge711 : CertifiedEdge catalog where
  old := 138
  next := 150
  rank := 1
  good := by
    constructor
    · exact edge711_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness712 : Fin frame139.rank → ℕ := ![2,4]
theorem edge712_span : frame139.space ≤ frame148.space :=
  frame139.inclusion frame148 witness712 (by decide)
def edge712 : CertifiedEdge catalog where
  old := 139
  next := 148
  rank := 1
  good := by
    constructor
    · exact edge712_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness713 : Fin frame139.rank → ℕ := ![2,4]
theorem edge713_span : frame139.space ≤ frame149.space :=
  frame139.inclusion frame149 witness713 (by decide)
def edge713 : CertifiedEdge catalog where
  old := 139
  next := 149
  rank := 1
  good := by
    constructor
    · exact edge713_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness714 : Fin frame140.rank → ℕ := ![2,4]
theorem edge714_span : frame140.space ≤ frame145.space :=
  frame140.inclusion frame145 witness714 (by decide)
def edge714 : CertifiedEdge catalog where
  old := 140
  next := 145
  rank := 1
  good := by
    constructor
    · exact edge714_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness715 : Fin frame140.rank → ℕ := ![2,4]
theorem edge715_span : frame140.space ≤ frame152.space :=
  frame140.inclusion frame152 witness715 (by decide)
def edge715 : CertifiedEdge catalog where
  old := 140
  next := 152
  rank := 1
  good := by
    constructor
    · exact edge715_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness716 : Fin frame141.rank → ℕ := ![1,4]
theorem edge716_span : frame141.space ≤ frame147.space :=
  frame141.inclusion frame147 witness716 (by decide)
def edge716 : CertifiedEdge catalog where
  old := 141
  next := 147
  rank := 1
  good := by
    constructor
    · exact edge716_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness717 : Fin frame141.rank → ℕ := ![1,4]
theorem edge717_span : frame141.space ≤ frame149.space :=
  frame141.inclusion frame149 witness717 (by decide)
def edge717 : CertifiedEdge catalog where
  old := 141
  next := 149
  rank := 1
  good := by
    constructor
    · exact edge717_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness718 : Fin frame142.rank → ℕ := ![1,4]
theorem edge718_span : frame142.space ≤ frame145.space :=
  frame142.inclusion frame145 witness718 (by decide)
def edge718 : CertifiedEdge catalog where
  old := 142
  next := 145
  rank := 1
  good := by
    constructor
    · exact edge718_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness719 : Fin frame142.rank → ℕ := ![1,4]
theorem edge719_span : frame142.space ≤ frame151.space :=
  frame142.inclusion frame151 witness719 (by decide)
def edge719 : CertifiedEdge catalog where
  old := 142
  next := 151
  rank := 1
  good := by
    constructor
    · exact edge719_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness720 : Fin frame143.rank → ℕ := ![2,4]
theorem edge720_span : frame143.space ≤ frame540.space :=
  frame143.inclusion frame540 witness720 (by decide)
def edge720 : CertifiedEdge catalog where
  old := 143
  next := 540
  rank := 1
  good := by
    constructor
    · exact edge720_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness721 : Fin frame143.rank → ℕ := ![2,4]
theorem edge721_span : frame143.space ≤ frame543.space :=
  frame143.inclusion frame543 witness721 (by decide)
def edge721 : CertifiedEdge catalog where
  old := 143
  next := 543
  rank := 1
  good := by
    constructor
    · exact edge721_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness722 : Fin frame143.rank → ℕ := ![2,8]
theorem edge722_span : frame143.space ≤ frame596.space :=
  frame143.inclusion frame596 witness722 (by decide)
def edge722 : CertifiedEdge catalog where
  old := 143
  next := 596
  rank := 2
  good := by
    constructor
    · exact edge722_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness723 : Fin frame143.rank → ℕ := ![10,12]
theorem edge723_span : frame143.space ≤ frame599.space :=
  frame143.inclusion frame599 witness723 (by decide)
def edge723 : CertifiedEdge catalog where
  old := 143
  next := 599
  rank := 2
  good := by
    constructor
    · exact edge723_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness724 : Fin frame144.rank → ℕ := ![1,4]
theorem edge724_span : frame144.space ≤ frame540.space :=
  frame144.inclusion frame540 witness724 (by decide)
def edge724 : CertifiedEdge catalog where
  old := 144
  next := 540
  rank := 1
  good := by
    constructor
    · exact edge724_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness725 : Fin frame144.rank → ℕ := ![1,4]
theorem edge725_span : frame144.space ≤ frame542.space :=
  frame144.inclusion frame542 witness725 (by decide)
def edge725 : CertifiedEdge catalog where
  old := 144
  next := 542
  rank := 1
  good := by
    constructor
    · exact edge725_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness726 : Fin frame144.rank → ℕ := ![9,12]
theorem edge726_span : frame144.space ≤ frame598.space :=
  frame144.inclusion frame598 witness726 (by decide)
def edge726 : CertifiedEdge catalog where
  old := 144
  next := 598
  rank := 2
  good := by
    constructor
    · exact edge726_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness727 : Fin frame144.rank → ℕ := ![17,24]
theorem edge727_span : frame144.space ≤ frame746.space :=
  frame144.inclusion frame746 witness727 (by decide)
def edge727 : CertifiedEdge catalog where
  old := 144
  next := 746
  rank := 5
  good := by
    constructor
    · exact edge727_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness728 : Fin frame145.rank → ℕ := ![1,10,4]
theorem edge728_span : frame145.space ≤ frame153.space :=
  frame145.inclusion frame153 witness728 (by decide)
def edge728 : CertifiedEdge catalog where
  old := 145
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge728_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness729 : Fin frame145.rank → ℕ := ![1,42,20]
theorem edge729_span : frame145.space ≤ frame640.space :=
  frame145.inclusion frame640 witness729 (by decide)
def edge729 : CertifiedEdge catalog where
  old := 145
  next := 640
  rank := 3
  good := by
    constructor
    · exact edge729_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness730 : Fin frame145.rank → ℕ := ![17,10,20]
theorem edge730_span : frame145.space ≤ frame678.space :=
  frame145.inclusion frame678 witness730 (by decide)
def edge730 : CertifiedEdge catalog where
  old := 145
  next := 678
  rank := 3
  good := by
    constructor
    · exact edge730_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness731 : Fin frame146.rank → ℕ := ![9,2,4]
theorem edge731_span : frame146.space ≤ frame153.space :=
  frame146.inclusion frame153 witness731 (by decide)
def edge731 : CertifiedEdge catalog where
  old := 146
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge731_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness732 : Fin frame146.rank → ℕ := ![41,2,20]
theorem edge732_span : frame146.space ≤ frame641.space :=
  frame146.inclusion frame641 witness732 (by decide)
def edge732 : CertifiedEdge catalog where
  old := 146
  next := 641
  rank := 3
  good := by
    constructor
    · exact edge732_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness733 : Fin frame146.rank → ℕ := ![9,18,20]
theorem edge733_span : frame146.space ≤ frame679.space :=
  frame146.inclusion frame679 witness733 (by decide)
def edge733 : CertifiedEdge catalog where
  old := 146
  next := 679
  rank := 3
  good := by
    constructor
    · exact edge733_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness734 : Fin frame147.rank → ℕ := ![9,10,12]
theorem edge734_span : frame147.space ≤ frame153.space :=
  frame147.inclusion frame153 witness734 (by decide)
def edge734 : CertifiedEdge catalog where
  old := 147
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge734_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness735 : Fin frame147.rank → ℕ := ![9,10,44]
theorem edge735_span : frame147.space ≤ frame648.space :=
  frame147.inclusion frame648 witness735 (by decide)
def edge735 : CertifiedEdge catalog where
  old := 147
  next := 648
  rank := 3
  good := by
    constructor
    · exact edge735_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
