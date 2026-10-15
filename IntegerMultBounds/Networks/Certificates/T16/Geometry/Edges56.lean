module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1792 : Fin frame495.rank → ℕ := ![17,2,4,8,32]
theorem edge1792_span : frame495.space ≤ frame500.space :=
  frame495.inclusion frame500 witness1792 (by decide)
def edge1792 : CertifiedEdge catalog where
  old := 495
  next := 500
  rank := 1
  good := by
    constructor
    · exact edge1792_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1793 : Fin frame495.rank → ℕ := ![81,66,68,72,96]
theorem edge1793_span : frame495.space ≤ frame502.space :=
  frame495.inclusion frame502 witness1793 (by decide)
def edge1793 : CertifiedEdge catalog where
  old := 495
  next := 502
  rank := 2
  good := by
    constructor
    · exact edge1793_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1794 : Fin frame496.rank → ℕ := ![1,22,8,32]
theorem edge1794_span : frame496.space ≤ frame499.space :=
  frame496.inclusion frame499 witness1794 (by decide)
def edge1794 : CertifiedEdge catalog where
  old := 496
  next := 499
  rank := 2
  good := by
    constructor
    · exact edge1794_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1795 : Fin frame496.rank → ℕ := ![65,86,72,96]
theorem edge1795_span : frame496.space ≤ frame503.space :=
  frame496.inclusion frame503 witness1795 (by decide)
def edge1795 : CertifiedEdge catalog where
  old := 496
  next := 503
  rank := 3
  good := by
    constructor
    · exact edge1795_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1796 : Fin frame497.rank → ℕ := ![33,6,40,48]
theorem edge1796_span : frame497.space ≤ frame498.space :=
  frame497.inclusion frame498 witness1796 (by decide)
def edge1796 : CertifiedEdge catalog where
  old := 497
  next := 498
  rank := 2
  good := by
    constructor
    · exact edge1796_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1797 : Fin frame497.rank → ℕ := ![97,70,104,112]
theorem edge1797_span : frame497.space ≤ frame501.space :=
  frame497.inclusion frame501 witness1797 (by decide)
def edge1797 : CertifiedEdge catalog where
  old := 497
  next := 501
  rank := 3
  good := by
    constructor
    · exact edge1797_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1798 : Fin frame498.rank → ℕ := ![1,66,4,8,16,96]
theorem edge1798_span : frame498.space ≤ frame451.space :=
  frame498.inclusion frame451 witness1798 (by decide)
def edge1798 : CertifiedEdge catalog where
  old := 498
  next := 451
  rank := 1
  good := by
    constructor
    · exact edge1798_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1799 : Fin frame498.rank → ℕ := ![1,66,4,8,16,32]
theorem edge1799_span : frame498.space ≤ frame503.space :=
  frame498.inclusion frame503 witness1799 (by decide)
def edge1799 : CertifiedEdge catalog where
  old := 498
  next := 503
  rank := 1
  good := by
    constructor
    · exact edge1799_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1800 : Fin frame499.rank → ℕ := ![1,2,4,8,80,96]
theorem edge1800_span : frame499.space ≤ frame465.space :=
  frame499.inclusion frame465 witness1800 (by decide)
def edge1800 : CertifiedEdge catalog where
  old := 499
  next := 465
  rank := 1
  good := by
    constructor
    · exact edge1800_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1801 : Fin frame499.rank → ℕ := ![65,66,68,72,80,96]
theorem edge1801_span : frame499.space ≤ frame502.space :=
  frame499.inclusion frame502 witness1801 (by decide)
def edge1801 : CertifiedEdge catalog where
  old := 499
  next := 502
  rank := 1
  good := by
    constructor
    · exact edge1801_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1802 : Fin frame500.rank → ℕ := ![1,66,68,72,80,96]
theorem edge1802_span : frame500.space ≤ frame478.space :=
  frame500.inclusion frame478 witness1802 (by decide)
def edge1802 : CertifiedEdge catalog where
  old := 500
  next := 478
  rank := 1
  good := by
    constructor
    · exact edge1802_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1803 : Fin frame500.rank → ℕ := ![65,2,4,8,16,96]
theorem edge1803_span : frame500.space ≤ frame501.space :=
  frame500.inclusion frame501 witness1803 (by decide)
def edge1803 : CertifiedEdge catalog where
  old := 500
  next := 501
  rank := 1
  good := by
    constructor
    · exact edge1803_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1804 : Fin frame501.rank → ℕ := ![129,130,132,392,144,288,448]
theorem edge1804_span : frame501.space ≤ frame1.space :=
  frame501.inclusion frame1 witness1804 (by decide)
def edge1804 : CertifiedEdge catalog where
  old := 501
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1804_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1805 : Fin frame501.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1805_span : frame501.space ≤ frame808.space :=
  frame501.inclusion frame808 witness1805 (by decide)
def edge1805 : CertifiedEdge catalog where
  old := 501
  next := 808
  rank := 1
  good := by
    constructor
    · exact edge1805_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1806 : Fin frame501.rank → ℕ := ![129,130,132,136,144,32,192]
theorem edge1806_span : frame501.space ≤ frame811.space :=
  frame501.inclusion frame811 witness1806 (by decide)
def edge1806 : CertifiedEdge catalog where
  old := 501
  next := 811
  rank := 1
  good := by
    constructor
    · exact edge1806_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1807 : Fin frame502.rank → ℕ := ![1,2,4,264,336,96,128]
theorem edge1807_span : frame502.space ≤ frame1.space :=
  frame502.inclusion frame1 witness1807 (by decide)
def edge1807 : CertifiedEdge catalog where
  old := 502
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1807_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1808 : Fin frame502.rank → ℕ := ![1,2,4,136,144,32,64]
theorem edge1808_span : frame502.space ≤ frame968.space :=
  frame502.inclusion frame968 witness1808 (by decide)
def edge1808 : CertifiedEdge catalog where
  old := 502
  next := 968
  rank := 1
  good := by
    constructor
    · exact edge1808_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1809 : Fin frame502.rank → ℕ := ![1,2,4,8,80,96,128]
theorem edge1809_span : frame502.space ≤ frame971.space :=
  frame502.inclusion frame971 witness1809 (by decide)
def edge1809 : CertifiedEdge catalog where
  old := 502
  next := 971
  rank := 1
  good := by
    constructor
    · exact edge1809_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1810 : Fin frame503.rank → ℕ := ![1,322,4,264,16,96,128]
theorem edge1810_span : frame503.space ≤ frame1.space :=
  frame503.inclusion frame1 witness1810 (by decide)
def edge1810 : CertifiedEdge catalog where
  old := 503
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1810_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1811 : Fin frame503.rank → ℕ := ![1,130,4,136,16,32,64]
theorem edge1811_span : frame503.space ≤ frame984.space :=
  frame503.inclusion frame984 witness1811 (by decide)
def edge1811 : CertifiedEdge catalog where
  old := 503
  next := 984
  rank := 1
  good := by
    constructor
    · exact edge1811_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1812 : Fin frame503.rank → ℕ := ![1,66,4,8,16,96,128]
theorem edge1812_span : frame503.space ≤ frame987.space :=
  frame503.inclusion frame987 witness1812 (by decide)
def edge1812 : CertifiedEdge catalog where
  old := 503
  next := 987
  rank := 1
  good := by
    constructor
    · exact edge1812_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1813 : Fin frame504.rank → ℕ := ![71,40,48]
theorem edge1813_span : frame504.space ≤ frame489.space :=
  frame504.inclusion frame489 witness1813 (by decide)
def edge1813 : CertifiedEdge catalog where
  old := 504
  next := 489
  rank := 4
  good := by
    constructor
    · exact edge1813_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1814 : Fin frame504.rank → ℕ := ![3,4,8]
theorem edge1814_span : frame504.space ≤ frame508.space :=
  frame504.inclusion frame508 witness1814 (by decide)
def edge1814 : CertifiedEdge catalog where
  old := 504
  next := 508
  rank := 1
  good := by
    constructor
    · exact edge1814_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1815 : Fin frame505.rank → ℕ := ![65,118,104]
theorem edge1815_span : frame505.space ≤ frame462.space :=
  frame505.inclusion frame462 witness1815 (by decide)
def edge1815 : CertifiedEdge catalog where
  old := 505
  next := 462
  rank := 4
  good := by
    constructor
    · exact edge1815_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1816 : Fin frame505.rank → ℕ := ![9,26,12]
theorem edge1816_span : frame505.space ≤ frame507.space :=
  frame505.inclusion frame507 witness1816 (by decide)
def edge1816 : CertifiedEdge catalog where
  old := 505
  next := 507
  rank := 2
  good := by
    constructor
    · exact edge1816_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1817 : Fin frame506.rank → ℕ := ![34,36,40]
theorem edge1817_span : frame506.space ≤ frame476.space :=
  frame506.inclusion frame476 witness1817 (by decide)
def edge1817 : CertifiedEdge catalog where
  old := 506
  next := 476
  rank := 4
  good := by
    constructor
    · exact edge1817_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1818 : Fin frame506.rank → ℕ := ![2,4,8]
theorem edge1818_span : frame506.space ≤ frame509.space :=
  frame506.inclusion frame509 witness1818 (by decide)
def edge1818 : CertifiedEdge catalog where
  old := 506
  next := 509
  rank := 1
  good := by
    constructor
    · exact edge1818_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1819 : Fin frame507.rank → ℕ := ![1,6,8,16,32]
theorem edge1819_span : frame507.space ≤ frame512.space :=
  frame507.inclusion frame512 witness1819 (by decide)
def edge1819 : CertifiedEdge catalog where
  old := 507
  next := 512
  rank := 1
  good := by
    constructor
    · exact edge1819_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1820 : Fin frame507.rank → ℕ := ![1,22,8,32,64]
theorem edge1820_span : frame507.space ≤ frame514.space :=
  frame507.inclusion frame514 witness1820 (by decide)
def edge1820 : CertifiedEdge catalog where
  old := 507
  next := 514
  rank := 2
  good := by
    constructor
    · exact edge1820_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1821 : Fin frame508.rank → ℕ := ![99,68,104,80]
theorem edge1821_span : frame508.space ≤ frame501.space :=
  frame508.inclusion frame501 witness1821 (by decide)
def edge1821 : CertifiedEdge catalog where
  old := 508
  next := 501
  rank := 3
  good := by
    constructor
    · exact edge1821_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1822 : Fin frame508.rank → ℕ := ![49,18,20,24]
theorem edge1822_span : frame508.space ≤ frame511.space :=
  frame508.inclusion frame511 witness1822 (by decide)
def edge1822 : CertifiedEdge catalog where
  old := 508
  next := 511
  rank := 2
  good := by
    constructor
    · exact edge1822_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1823 : Fin frame509.rank → ℕ := ![33,34,36,40]
theorem edge1823_span : frame509.space ≤ frame510.space :=
  frame509.inclusion frame510 witness1823 (by decide)
def edge1823 : CertifiedEdge catalog where
  old := 509
  next := 510
  rank := 2
  good := by
    constructor
    · exact edge1823_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
