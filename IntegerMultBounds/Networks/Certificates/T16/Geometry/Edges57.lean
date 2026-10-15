module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1824 : Fin frame509.rank → ℕ := ![33,34,36,40]
theorem edge1824_span : frame509.space ≤ frame513.space :=
  frame509.inclusion frame513 witness1824 (by decide)
def edge1824 : CertifiedEdge catalog where
  old := 509
  next := 513
  rank := 3
  good := by
    constructor
    · exact edge1824_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1825 : Fin frame510.rank → ℕ := ![1,2,4,40,16,64]
theorem edge1825_span : frame510.space ≤ frame462.space :=
  frame510.inclusion frame462 witness1825 (by decide)
def edge1825 : CertifiedEdge catalog where
  old := 510
  next := 462
  rank := 1
  good := by
    constructor
    · exact edge1825_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1826 : Fin frame510.rank → ℕ := ![1,2,4,40,16,64]
theorem edge1826_span : frame510.space ≤ frame501.space :=
  frame510.inclusion frame501 witness1826 (by decide)
def edge1826 : CertifiedEdge catalog where
  old := 510
  next := 501
  rank := 1
  good := by
    constructor
    · exact edge1826_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1827 : Fin frame511.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1827_span : frame511.space ≤ frame476.space :=
  frame511.inclusion frame476 witness1827 (by decide)
def edge1827 : CertifiedEdge catalog where
  old := 511
  next := 476
  rank := 1
  good := by
    constructor
    · exact edge1827_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1828 : Fin frame511.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1828_span : frame511.space ≤ frame514.space :=
  frame511.inclusion frame514 witness1828 (by decide)
def edge1828 : CertifiedEdge catalog where
  old := 511
  next := 514
  rank := 1
  good := by
    constructor
    · exact edge1828_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1829 : Fin frame512.rank → ℕ := ![1,2,20,8,32,64]
theorem edge1829_span : frame512.space ≤ frame489.space :=
  frame512.inclusion frame489 witness1829 (by decide)
def edge1829 : CertifiedEdge catalog where
  old := 512
  next := 489
  rank := 1
  good := by
    constructor
    · exact edge1829_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1830 : Fin frame512.rank → ℕ := ![1,2,20,8,32,64]
theorem edge1830_span : frame512.space ≤ frame513.space :=
  frame512.inclusion frame513 witness1830 (by decide)
def edge1830 : CertifiedEdge catalog where
  old := 512
  next := 513
  rank := 1
  good := by
    constructor
    · exact edge1830_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1831 : Fin frame513.rank → ℕ := ![1,2,4,40,304,320,128]
theorem edge1831_span : frame513.space ≤ frame1.space :=
  frame513.inclusion frame1 witness1831 (by decide)
def edge1831 : CertifiedEdge catalog where
  old := 513
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1831_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1832 : Fin frame513.rank → ℕ := ![1,2,4,40,48,64,128]
theorem edge1832_span : frame513.space ≤ frame776.space :=
  frame513.inclusion frame776 witness1832 (by decide)
def edge1832 : CertifiedEdge catalog where
  old := 513
  next := 776
  rank := 1
  good := by
    constructor
    · exact edge1832_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1833 : Fin frame513.rank → ℕ := ![1,2,4,8,144,160,64]
theorem edge1833_span : frame513.space ≤ frame779.space :=
  frame513.inclusion frame779 witness1833 (by decide)
def edge1833 : CertifiedEdge catalog where
  old := 513
  next := 779
  rank := 1
  good := by
    constructor
    · exact edge1833_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1834 : Fin frame514.rank → ℕ := ![1,290,4,40,16,320,128]
theorem edge1834_span : frame514.space ≤ frame1.space :=
  frame514.inclusion frame1 witness1834 (by decide)
def edge1834 : CertifiedEdge catalog where
  old := 514
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1834_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1835 : Fin frame514.rank → ℕ := ![1,34,4,40,16,64,128]
theorem edge1835_span : frame514.space ≤ frame792.space :=
  frame514.inclusion frame792 witness1835 (by decide)
def edge1835 : CertifiedEdge catalog where
  old := 514
  next := 792
  rank := 1
  good := by
    constructor
    · exact edge1835_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1836 : Fin frame514.rank → ℕ := ![1,130,4,8,16,160,64]
theorem edge1836_span : frame514.space ≤ frame795.space :=
  frame514.inclusion frame795 witness1836 (by decide)
def edge1836 : CertifiedEdge catalog where
  old := 514
  next := 795
  rank := 1
  good := by
    constructor
    · exact edge1836_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1837 : Fin frame515.rank → ℕ := ![7,104,80]
theorem edge1837_span : frame515.space ≤ frame490.space :=
  frame515.inclusion frame490 witness1837 (by decide)
def edge1837 : CertifiedEdge catalog where
  old := 515
  next := 490
  rank := 4
  good := by
    constructor
    · exact edge1837_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1838 : Fin frame515.rank → ℕ := ![3,4,8]
theorem edge1838_span : frame515.space ≤ frame519.space :=
  frame515.inclusion frame519 witness1838 (by decide)
def edge1838 : CertifiedEdge catalog where
  old := 515
  next := 519
  rank := 1
  good := by
    constructor
    · exact edge1838_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1839 : Fin frame516.rank → ℕ := ![66,52,56]
theorem edge1839_span : frame516.space ≤ frame448.space :=
  frame516.inclusion frame448 witness1839 (by decide)
def edge1839 : CertifiedEdge catalog where
  old := 516
  next := 448
  rank := 4
  good := by
    constructor
    · exact edge1839_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1840 : Fin frame516.rank → ℕ := ![2,4,8]
theorem edge1840_span : frame516.space ≤ frame518.space :=
  frame516.inclusion frame518 witness1840 (by decide)
def edge1840 : CertifiedEdge catalog where
  old := 516
  next := 518
  rank := 1
  good := by
    constructor
    · exact edge1840_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1841 : Fin frame517.rank → ℕ := ![5,6,104]
theorem edge1841_span : frame517.space ≤ frame477.space :=
  frame517.inclusion frame477 witness1841 (by decide)
def edge1841 : CertifiedEdge catalog where
  old := 517
  next := 477
  rank := 4
  good := by
    constructor
    · exact edge1841_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1842 : Fin frame517.rank → ℕ := ![9,2,4]
theorem edge1842_span : frame517.space ≤ frame520.space :=
  frame517.inclusion frame520 witness1842 (by decide)
def edge1842 : CertifiedEdge catalog where
  old := 517
  next := 520
  rank := 1
  good := by
    constructor
    · exact edge1842_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1843 : Fin frame518.rank → ℕ := ![1,6,40,48]
theorem edge1843_span : frame518.space ≤ frame523.space :=
  frame518.inclusion frame523 witness1843 (by decide)
def edge1843 : CertifiedEdge catalog where
  old := 518
  next := 523
  rank := 2
  good := by
    constructor
    · exact edge1843_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1844 : Fin frame518.rank → ℕ := ![1,6,104,112]
theorem edge1844_span : frame518.space ≤ frame524.space :=
  frame518.inclusion frame524 witness1844 (by decide)
def edge1844 : CertifiedEdge catalog where
  old := 518
  next := 524
  rank := 3
  good := by
    constructor
    · exact edge1844_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1845 : Fin frame519.rank → ℕ := ![67,68,40,16]
theorem edge1845_span : frame519.space ≤ frame502.space :=
  frame519.inclusion frame502 witness1845 (by decide)
def edge1845 : CertifiedEdge catalog where
  old := 519
  next := 502
  rank := 3
  good := by
    constructor
    · exact edge1845_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1846 : Fin frame519.rank → ℕ := ![1,2,52,40]
theorem edge1846_span : frame519.space ≤ frame522.space :=
  frame519.inclusion frame522 witness1846 (by decide)
def edge1846 : CertifiedEdge catalog where
  old := 519
  next := 522
  rank := 2
  good := by
    constructor
    · exact edge1846_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1847 : Fin frame520.rank → ℕ := ![5,6,40,64]
theorem edge1847_span : frame520.space ≤ frame513.space :=
  frame520.inclusion frame513 witness1847 (by decide)
def edge1847 : CertifiedEdge catalog where
  old := 520
  next := 513
  rank := 3
  good := by
    constructor
    · exact edge1847_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1848 : Fin frame520.rank → ℕ := ![1,2,20,32]
theorem edge1848_span : frame520.space ≤ frame521.space :=
  frame520.inclusion frame521 witness1848 (by decide)
def edge1848 : CertifiedEdge catalog where
  old := 520
  next := 521
  rank := 2
  good := by
    constructor
    · exact edge1848_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1849 : Fin frame521.rank → ℕ := ![1,2,4,40,48,64]
theorem edge1849_span : frame521.space ≤ frame448.space :=
  frame521.inclusion frame448 witness1849 (by decide)
def edge1849 : CertifiedEdge catalog where
  old := 521
  next := 448
  rank := 1
  good := by
    constructor
    · exact edge1849_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1850 : Fin frame521.rank → ℕ := ![5,6,8,16,32,64]
theorem edge1850_span : frame521.space ≤ frame502.space :=
  frame521.inclusion frame502 witness1850 (by decide)
def edge1850 : CertifiedEdge catalog where
  old := 521
  next := 502
  rank := 1
  good := by
    constructor
    · exact edge1850_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1851 : Fin frame522.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1851_span : frame522.space ≤ frame477.space :=
  frame522.inclusion frame477 witness1851 (by decide)
def edge1851 : CertifiedEdge catalog where
  old := 522
  next := 477
  rank := 1
  good := by
    constructor
    · exact edge1851_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1852 : Fin frame522.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1852_span : frame522.space ≤ frame524.space :=
  frame522.inclusion frame524 witness1852 (by decide)
def edge1852 : CertifiedEdge catalog where
  old := 522
  next := 524
  rank := 1
  good := by
    constructor
    · exact edge1852_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1853 : Fin frame523.rank → ℕ := ![1,2,4,40,48,64]
theorem edge1853_span : frame523.space ≤ frame490.space :=
  frame523.inclusion frame490 witness1853 (by decide)
def edge1853 : CertifiedEdge catalog where
  old := 523
  next := 490
  rank := 1
  good := by
    constructor
    · exact edge1853_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1854 : Fin frame523.rank → ℕ := ![65,66,4,8,16,32]
theorem edge1854_span : frame523.space ≤ frame513.space :=
  frame523.inclusion frame513 witness1854 (by decide)
def edge1854 : CertifiedEdge catalog where
  old := 523
  next := 513
  rank := 1
  good := by
    constructor
    · exact edge1854_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1855 : Fin frame524.rank → ℕ := ![129,2,132,264,16,288,320]
theorem edge1855_span : frame524.space ≤ frame1.space :=
  frame524.inclusion frame1 witness1855 (by decide)
def edge1855 : CertifiedEdge catalog where
  old := 524
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1855_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
