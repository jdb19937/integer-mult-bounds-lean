module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1760 : Fin frame480.rank → ℕ := ![19,68,104]
theorem edge1760_span : frame480.space ≤ frame491.space :=
  frame480.inclusion frame491 witness1760 (by decide)
def edge1760 : CertifiedEdge catalog where
  old := 480
  next := 491
  rank := 4
  good := by
    constructor
    · exact edge1760_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1761 : Fin frame481.rank → ℕ := ![1,2,8]
theorem edge1761_span : frame481.space ≤ frame483.space :=
  frame481.inclusion frame483 witness1761 (by decide)
def edge1761 : CertifiedEdge catalog where
  old := 481
  next := 483
  rank := 1
  good := by
    constructor
    · exact edge1761_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1762 : Fin frame481.rank → ℕ := ![17,82,40]
theorem edge1762_span : frame481.space ≤ frame489.space :=
  frame481.inclusion frame489 witness1762 (by decide)
def edge1762 : CertifiedEdge catalog where
  old := 481
  next := 489
  rank := 4
  good := by
    constructor
    · exact edge1762_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1763 : Fin frame482.rank → ℕ := ![1,4,8]
theorem edge1763_span : frame482.space ≤ frame485.space :=
  frame482.inclusion frame485 witness1763 (by decide)
def edge1763 : CertifiedEdge catalog where
  old := 482
  next := 485
  rank := 1
  good := by
    constructor
    · exact edge1763_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1764 : Fin frame482.rank → ℕ := ![17,36,104]
theorem edge1764_span : frame482.space ≤ frame490.space :=
  frame482.inclusion frame490 witness1764 (by decide)
def edge1764 : CertifiedEdge catalog where
  old := 482
  next := 490
  rank := 4
  good := by
    constructor
    · exact edge1764_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1765 : Fin frame483.rank → ℕ := ![17,82,4,40]
theorem edge1765_span : frame483.space ≤ frame466.space :=
  frame483.inclusion frame466 witness1765 (by decide)
def edge1765 : CertifiedEdge catalog where
  old := 483
  next := 466
  rank := 3
  good := by
    constructor
    · exact edge1765_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1766 : Fin frame483.rank → ℕ := ![1,2,36,56]
theorem edge1766_span : frame483.space ≤ frame488.space :=
  frame483.inclusion frame488 witness1766 (by decide)
def edge1766 : CertifiedEdge catalog where
  old := 483
  next := 488
  rank := 2
  good := by
    constructor
    · exact edge1766_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1767 : Fin frame484.rank → ℕ := ![17,2,68,104]
theorem edge1767_span : frame484.space ≤ frame479.space :=
  frame484.inclusion frame479 witness1767 (by decide)
def edge1767 : CertifiedEdge catalog where
  old := 484
  next := 479
  rank := 3
  good := by
    constructor
    · exact edge1767_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1768 : Fin frame484.rank → ℕ := ![17,2,4,40]
theorem edge1768_span : frame484.space ≤ frame487.space :=
  frame484.inclusion frame487 witness1768 (by decide)
def edge1768 : CertifiedEdge catalog where
  old := 484
  next := 487
  rank := 2
  good := by
    constructor
    · exact edge1768_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1769 : Fin frame485.rank → ℕ := ![65,2,20,56]
theorem edge1769_span : frame485.space ≤ frame452.space :=
  frame485.inclusion frame452 witness1769 (by decide)
def edge1769 : CertifiedEdge catalog where
  old := 485
  next := 452
  rank := 3
  good := by
    constructor
    · exact edge1769_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1770 : Fin frame485.rank → ℕ := ![17,18,4,40]
theorem edge1770_span : frame485.space ≤ frame486.space :=
  frame485.inclusion frame486 witness1770 (by decide)
def edge1770 : CertifiedEdge catalog where
  old := 485
  next := 486
  rank := 2
  good := by
    constructor
    · exact edge1770_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1771 : Fin frame486.rank → ℕ := ![1,2,36,40,16,64]
theorem edge1771_span : frame486.space ≤ frame479.space :=
  frame486.inclusion frame479 witness1771 (by decide)
def edge1771 : CertifiedEdge catalog where
  old := 486
  next := 479
  rank := 1
  good := by
    constructor
    · exact edge1771_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1772 : Fin frame486.rank → ℕ := ![1,66,4,8,80,32]
theorem edge1772_span : frame486.space ≤ frame489.space :=
  frame486.inclusion frame489 witness1772 (by decide)
def edge1772 : CertifiedEdge catalog where
  old := 486
  next := 489
  rank := 1
  good := by
    constructor
    · exact edge1772_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1773 : Fin frame487.rank → ℕ := ![65,66,4,8,16,32]
theorem edge1773_span : frame487.space ≤ frame466.space :=
  frame487.inclusion frame466 witness1773 (by decide)
def edge1773 : CertifiedEdge catalog where
  old := 487
  next := 466
  rank := 1
  good := by
    constructor
    · exact edge1773_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1774 : Fin frame487.rank → ℕ := ![1,2,68,72,16,32]
theorem edge1774_span : frame487.space ≤ frame490.space :=
  frame487.inclusion frame490 witness1774 (by decide)
def edge1774 : CertifiedEdge catalog where
  old := 487
  next := 490
  rank := 1
  good := by
    constructor
    · exact edge1774_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1775 : Fin frame488.rank → ℕ := ![1,66,4,8,16,32]
theorem edge1775_span : frame488.space ≤ frame452.space :=
  frame488.inclusion frame452 witness1775 (by decide)
def edge1775 : CertifiedEdge catalog where
  old := 488
  next := 452
  rank := 1
  good := by
    constructor
    · exact edge1775_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1776 : Fin frame488.rank → ℕ := ![17,18,4,8,32,64]
theorem edge1776_span : frame488.space ≤ frame491.space :=
  frame488.inclusion frame491 witness1776 (by decide)
def edge1776 : CertifiedEdge catalog where
  old := 488
  next := 491
  rank := 1
  good := by
    constructor
    · exact edge1776_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1777 : Fin frame489.rank → ℕ := ![1,2,292,40,16,320,128]
theorem edge1777_span : frame489.space ≤ frame1.space :=
  frame489.inclusion frame1 witness1777 (by decide)
def edge1777 : CertifiedEdge catalog where
  old := 489
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1777_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1778 : Fin frame489.rank → ℕ := ![1,2,36,40,16,64,128]
theorem edge1778_span : frame489.space ≤ frame816.space :=
  frame489.inclusion frame816 witness1778 (by decide)
def edge1778 : CertifiedEdge catalog where
  old := 489
  next := 816
  rank := 1
  good := by
    constructor
    · exact edge1778_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1779 : Fin frame489.rank → ℕ := ![1,2,132,8,16,160,64]
theorem edge1779_span : frame489.space ≤ frame819.space :=
  frame489.inclusion frame819 witness1779 (by decide)
def edge1779 : CertifiedEdge catalog where
  old := 489
  next := 819
  rank := 1
  good := by
    constructor
    · exact edge1779_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1780 : Fin frame490.rank → ℕ := ![129,130,4,264,16,288,320]
theorem edge1780_span : frame490.space ≤ frame1.space :=
  frame490.inclusion frame1 witness1780 (by decide)
def edge1780 : CertifiedEdge catalog where
  old := 490
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1780_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1781 : Fin frame490.rank → ℕ := ![129,130,4,8,16,32,64]
theorem edge1781_span : frame490.space ≤ frame976.space :=
  frame490.inclusion frame976 witness1781 (by decide)
def edge1781 : CertifiedEdge catalog where
  old := 490
  next := 976
  rank := 1
  good := by
    constructor
    · exact edge1781_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1782 : Fin frame490.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1782_span : frame490.space ≤ frame979.space :=
  frame490.inclusion frame979 witness1782 (by decide)
def edge1782 : CertifiedEdge catalog where
  old := 490
  next := 979
  rank := 1
  good := by
    constructor
    · exact edge1782_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1783 : Fin frame491.rank → ℕ := ![129,2,4,264,144,288,320]
theorem edge1783_span : frame491.space ≤ frame1.space :=
  frame491.inclusion frame1 witness1783 (by decide)
def edge1783 : CertifiedEdge catalog where
  old := 491
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1783_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1784 : Fin frame491.rank → ℕ := ![129,2,4,8,144,32,64]
theorem edge1784_span : frame491.space ≤ frame992.space :=
  frame491.inclusion frame992 witness1784 (by decide)
def edge1784 : CertifiedEdge catalog where
  old := 491
  next := 992
  rank := 1
  good := by
    constructor
    · exact edge1784_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1785 : Fin frame491.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1785_span : frame491.space ≤ frame995.space :=
  frame491.inclusion frame995 witness1785 (by decide)
def edge1785 : CertifiedEdge catalog where
  old := 491
  next := 995
  rank := 1
  good := by
    constructor
    · exact edge1785_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1786 : Fin frame492.rank → ℕ := ![23,72,96]
theorem edge1786_span : frame492.space ≤ frame478.space :=
  frame492.inclusion frame478 witness1786 (by decide)
def edge1786 : CertifiedEdge catalog where
  old := 492
  next := 478
  rank := 4
  good := by
    constructor
    · exact edge1786_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1787 : Fin frame492.rank → ℕ := ![3,4,8]
theorem edge1787_span : frame492.space ≤ frame496.space :=
  frame492.inclusion frame496 witness1787 (by decide)
def edge1787 : CertifiedEdge catalog where
  old := 492
  next := 496
  rank := 1
  good := by
    constructor
    · exact edge1787_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1788 : Fin frame493.rank → ℕ := ![53,98,104]
theorem edge1788_span : frame493.space ≤ frame451.space :=
  frame493.inclusion frame451 witness1788 (by decide)
def edge1788 : CertifiedEdge catalog where
  old := 493
  next := 451
  rank := 4
  good := by
    constructor
    · exact edge1788_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1789 : Fin frame493.rank → ℕ := ![21,18,24]
theorem edge1789_span : frame493.space ≤ frame495.space :=
  frame493.inclusion frame495 witness1789 (by decide)
def edge1789 : CertifiedEdge catalog where
  old := 493
  next := 495
  rank := 2
  good := by
    constructor
    · exact edge1789_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1790 : Fin frame494.rank → ℕ := ![97,104,112]
theorem edge1790_span : frame494.space ≤ frame465.space :=
  frame494.inclusion frame465 witness1790 (by decide)
def edge1790 : CertifiedEdge catalog where
  old := 494
  next := 465
  rank := 4
  good := by
    constructor
    · exact edge1790_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1791 : Fin frame494.rank → ℕ := ![1,4,8]
theorem edge1791_span : frame494.space ≤ frame497.space :=
  frame494.inclusion frame497 witness1791 (by decide)
def edge1791 : CertifiedEdge catalog where
  old := 494
  next := 497
  rank := 1
  good := by
    constructor
    · exact edge1791_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
