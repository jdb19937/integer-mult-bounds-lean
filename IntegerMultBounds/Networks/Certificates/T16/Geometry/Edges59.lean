module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1888 : Fin frame538.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1888_span : frame538.space ≤ frame746.space :=
  frame538.inclusion frame746 witness1888 (by decide)
def edge1888 : CertifiedEdge catalog where
  old := 538
  next := 746
  rank := 1
  good := by
    constructor
    · exact edge1888_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1889 : Fin frame538.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1889_span : frame538.space ≤ frame747.space :=
  frame538.inclusion frame747 witness1889 (by decide)
def edge1889 : CertifiedEdge catalog where
  old := 538
  next := 747
  rank := 1
  good := by
    constructor
    · exact edge1889_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1890 : Fin frame539.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1890_span : frame539.space ≤ frame748.space :=
  frame539.inclusion frame748 witness1890 (by decide)
def edge1890 : CertifiedEdge catalog where
  old := 539
  next := 748
  rank := 1
  good := by
    constructor
    · exact edge1890_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1891 : Fin frame539.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1891_span : frame539.space ≤ frame749.space :=
  frame539.inclusion frame749 witness1891 (by decide)
def edge1891 : CertifiedEdge catalog where
  old := 539
  next := 749
  rank := 1
  good := by
    constructor
    · exact edge1891_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1892 : Fin frame540.rank → ℕ := ![1,2,8]
theorem edge1892_span : frame540.space ≤ frame153.space :=
  frame540.inclusion frame153 witness1892 (by decide)
def edge1892 : CertifiedEdge catalog where
  old := 540
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge1892_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1893 : Fin frame540.rank → ℕ := ![17,18,24]
theorem edge1893_span : frame540.space ≤ frame544.space :=
  frame540.inclusion frame544 witness1893 (by decide)
def edge1893 : CertifiedEdge catalog where
  old := 540
  next := 544
  rank := 3
  good := by
    constructor
    · exact edge1893_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1894 : Fin frame540.rank → ℕ := ![1,2,8]
theorem edge1894_span : frame540.space ≤ frame592.space :=
  frame540.inclusion frame592 witness1894 (by decide)
def edge1894 : CertifiedEdge catalog where
  old := 540
  next := 592
  rank := 1
  good := by
    constructor
    · exact edge1894_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1895 : Fin frame541.rank → ℕ := ![5,6,8]
theorem edge1895_span : frame541.space ≤ frame153.space :=
  frame541.inclusion frame153 witness1895 (by decide)
def edge1895 : CertifiedEdge catalog where
  old := 541
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge1895_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1896 : Fin frame541.rank → ℕ := ![5,6,24]
theorem edge1896_span : frame541.space ≤ frame545.space :=
  frame541.inclusion frame545 witness1896 (by decide)
def edge1896 : CertifiedEdge catalog where
  old := 541
  next := 545
  rank := 3
  good := by
    constructor
    · exact edge1896_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1897 : Fin frame541.rank → ℕ := ![1,2,12]
theorem edge1897_span : frame541.space ≤ frame593.space :=
  frame541.inclusion frame593 witness1897 (by decide)
def edge1897 : CertifiedEdge catalog where
  old := 541
  next := 593
  rank := 1
  good := by
    constructor
    · exact edge1897_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1898 : Fin frame542.rank → ℕ := ![1,6,8]
theorem edge1898_span : frame542.space ≤ frame153.space :=
  frame542.inclusion frame153 witness1898 (by decide)
def edge1898 : CertifiedEdge catalog where
  old := 542
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge1898_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1899 : Fin frame542.rank → ℕ := ![1,22,40]
theorem edge1899_span : frame542.space ≤ frame589.space :=
  frame542.inclusion frame589 witness1899 (by decide)
def edge1899 : CertifiedEdge catalog where
  old := 542
  next := 589
  rank := 3
  good := by
    constructor
    · exact edge1899_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1900 : Fin frame542.rank → ℕ := ![1,2,4]
theorem edge1900_span : frame542.space ≤ frame628.space :=
  frame542.inclusion frame628 witness1900 (by decide)
def edge1900 : CertifiedEdge catalog where
  old := 542
  next := 628
  rank := 1
  good := by
    constructor
    · exact edge1900_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1901 : Fin frame543.rank → ℕ := ![5,2,8]
theorem edge1901_span : frame543.space ≤ frame153.space :=
  frame543.inclusion frame153 witness1901 (by decide)
def edge1901 : CertifiedEdge catalog where
  old := 543
  next := 153
  rank := 1
  good := by
    constructor
    · exact edge1901_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1902 : Fin frame543.rank → ℕ := ![21,2,40]
theorem edge1902_span : frame543.space ≤ frame591.space :=
  frame543.inclusion frame591 witness1902 (by decide)
def edge1902 : CertifiedEdge catalog where
  old := 543
  next := 591
  rank := 3
  good := by
    constructor
    · exact edge1902_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1903 : Fin frame543.rank → ℕ := ![1,2,4]
theorem edge1903_span : frame543.space ≤ frame629.space :=
  frame543.inclusion frame629 witness1903 (by decide)
def edge1903 : CertifiedEdge catalog where
  old := 543
  next := 629
  rank := 1
  good := by
    constructor
    · exact edge1903_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1904 : Fin frame544.rank → ℕ := ![1,2,68,72,16,32]
theorem edge1904_span : frame544.space ≤ frame742.space :=
  frame544.inclusion frame742 witness1904 (by decide)
def edge1904 : CertifiedEdge catalog where
  old := 544
  next := 742
  rank := 1
  good := by
    constructor
    · exact edge1904_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1905 : Fin frame544.rank → ℕ := ![65,66,68,72,80,96]
theorem edge1905_span : frame544.space ≤ frame743.space :=
  frame544.inclusion frame743 witness1905 (by decide)
def edge1905 : CertifiedEdge catalog where
  old := 544
  next := 743
  rank := 1
  good := by
    constructor
    · exact edge1905_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1906 : Fin frame545.rank → ℕ := ![65,66,4,8,16,32]
theorem edge1906_span : frame545.space ≤ frame744.space :=
  frame545.inclusion frame744 witness1906 (by decide)
def edge1906 : CertifiedEdge catalog where
  old := 545
  next := 744
  rank := 1
  good := by
    constructor
    · exact edge1906_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1907 : Fin frame545.rank → ℕ := ![1,2,4,8,80,96]
theorem edge1907_span : frame545.space ≤ frame745.space :=
  frame545.inclusion frame745 witness1907 (by decide)
def edge1907 : CertifiedEdge catalog where
  old := 545
  next := 745
  rank := 1
  good := by
    constructor
    · exact edge1907_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1908 : Fin frame546.rank → ℕ := ![1,4,8]
theorem edge1908_span : frame546.space ≤ frame182.space :=
  frame546.inclusion frame182 witness1908 (by decide)
def edge1908 : CertifiedEdge catalog where
  old := 546
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge1908_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1909 : Fin frame546.rank → ℕ := ![1,52,56]
theorem edge1909_span : frame546.space ≤ frame550.space :=
  frame546.inclusion frame550 witness1909 (by decide)
def edge1909 : CertifiedEdge catalog where
  old := 546
  next := 550
  rank := 3
  good := by
    constructor
    · exact edge1909_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1910 : Fin frame546.rank → ℕ := ![3,4,8]
theorem edge1910_span : frame546.space ≤ frame605.space :=
  frame546.inclusion frame605 witness1910 (by decide)
def edge1910 : CertifiedEdge catalog where
  old := 546
  next := 605
  rank := 1
  good := by
    constructor
    · exact edge1910_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1911 : Fin frame547.rank → ℕ := ![5,2,8]
theorem edge1911_span : frame547.space ≤ frame182.space :=
  frame547.inclusion frame182 witness1911 (by decide)
def edge1911 : CertifiedEdge catalog where
  old := 547
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge1911_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1912 : Fin frame547.rank → ℕ := ![53,18,24]
theorem edge1912_span : frame547.space ≤ frame551.space :=
  frame547.inclusion frame551 witness1912 (by decide)
def edge1912 : CertifiedEdge catalog where
  old := 547
  next := 551
  rank := 3
  good := by
    constructor
    · exact edge1912_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1913 : Fin frame547.rank → ℕ := ![3,4,8]
theorem edge1913_span : frame547.space ≤ frame606.space :=
  frame547.inclusion frame606 witness1913 (by decide)
def edge1913 : CertifiedEdge catalog where
  old := 547
  next := 606
  rank := 1
  good := by
    constructor
    · exact edge1913_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1914 : Fin frame548.rank → ℕ := ![1,2,8]
theorem edge1914_span : frame548.space ≤ frame182.space :=
  frame548.inclusion frame182 witness1914 (by decide)
def edge1914 : CertifiedEdge catalog where
  old := 548
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge1914_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1915 : Fin frame548.rank → ℕ := ![1,10,12]
theorem edge1915_span : frame548.space ≤ frame613.space :=
  frame548.inclusion frame613 witness1915 (by decide)
def edge1915 : CertifiedEdge catalog where
  old := 548
  next := 613
  rank := 1
  good := by
    constructor
    · exact edge1915_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1916 : Fin frame548.rank → ℕ := ![67,4,48]
theorem edge1916_span : frame548.space ≤ frame759.space :=
  frame548.inclusion frame759 witness1916 (by decide)
def edge1916 : CertifiedEdge catalog where
  old := 548
  next := 759
  rank := 4
  good := by
    constructor
    · exact edge1916_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1917 : Fin frame549.rank → ℕ := ![3,4,8]
theorem edge1917_span : frame549.space ≤ frame182.space :=
  frame549.inclusion frame182 witness1917 (by decide)
def edge1917 : CertifiedEdge catalog where
  old := 549
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge1917_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1918 : Fin frame549.rank → ℕ := ![7,40,48]
theorem edge1918_span : frame549.space ≤ frame587.space :=
  frame549.inclusion frame587 witness1918 (by decide)
def edge1918 : CertifiedEdge catalog where
  old := 549
  next := 587
  rank := 3
  good := by
    constructor
    · exact edge1918_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1919 : Fin frame549.rank → ℕ := ![9,10,12]
theorem edge1919_span : frame549.space ≤ frame615.space :=
  frame549.inclusion frame615 witness1919 (by decide)
def edge1919 : CertifiedEdge catalog where
  old := 549
  next := 615
  rank := 1
  good := by
    constructor
    · exact edge1919_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
