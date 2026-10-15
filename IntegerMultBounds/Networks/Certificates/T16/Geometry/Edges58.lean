module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1856 : Fin frame524.rank → ℕ := ![129,2,132,8,16,32,64]
theorem edge1856_span : frame524.space ≤ frame952.space :=
  frame524.inclusion frame952 witness1856 (by decide)
def edge1856 : CertifiedEdge catalog where
  old := 524
  next := 952
  rank := 1
  good := by
    constructor
    · exact edge1856_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1857 : Fin frame524.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1857_span : frame524.space ≤ frame955.space :=
  frame524.inclusion frame955 witness1857 (by decide)
def edge1857 : CertifiedEdge catalog where
  old := 524
  next := 955
  rank := 1
  good := by
    constructor
    · exact edge1857_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1858 : Fin frame525.rank → ℕ := ![21,66,104]
theorem edge1858_span : frame525.space ≤ frame491.space :=
  frame525.inclusion frame491 witness1858 (by decide)
def edge1858 : CertifiedEdge catalog where
  old := 525
  next := 491
  rank := 4
  good := by
    constructor
    · exact edge1858_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1859 : Fin frame525.rank → ℕ := ![5,2,8]
theorem edge1859_span : frame525.space ≤ frame529.space :=
  frame525.inclusion frame529 witness1859 (by decide)
def edge1859 : CertifiedEdge catalog where
  old := 525
  next := 529
  rank := 1
  good := by
    constructor
    · exact edge1859_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1860 : Fin frame526.rank → ℕ := ![18,24,32]
theorem edge1860_span : frame526.space ≤ frame449.space :=
  frame526.inclusion frame449 witness1860 (by decide)
def edge1860 : CertifiedEdge catalog where
  old := 526
  next := 449
  rank := 4
  good := by
    constructor
    · exact edge1860_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1861 : Fin frame526.rank → ℕ := ![2,4,8]
theorem edge1861_span : frame526.space ≤ frame528.space :=
  frame526.inclusion frame528 witness1861 (by decide)
def edge1861 : CertifiedEdge catalog where
  old := 526
  next := 528
  rank := 1
  good := by
    constructor
    · exact edge1861_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1862 : Fin frame527.rank → ℕ := ![81,20,40]
theorem edge1862_span : frame527.space ≤ frame463.space :=
  frame527.inclusion frame463 witness1862 (by decide)
def edge1862 : CertifiedEdge catalog where
  old := 527
  next := 463
  rank := 4
  good := by
    constructor
    · exact edge1862_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1863 : Fin frame527.rank → ℕ := ![1,4,8]
theorem edge1863_span : frame527.space ≤ frame530.space :=
  frame527.inclusion frame530 witness1863 (by decide)
def edge1863 : CertifiedEdge catalog where
  old := 527
  next := 530
  rank := 1
  good := by
    constructor
    · exact edge1863_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1864 : Fin frame528.rank → ℕ := ![21,34,40,64]
theorem edge1864_span : frame528.space ≤ frame524.space :=
  frame528.inclusion frame524 witness1864 (by decide)
def edge1864 : CertifiedEdge catalog where
  old := 528
  next := 524
  rank := 3
  good := by
    constructor
    · exact edge1864_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1865 : Fin frame528.rank → ℕ := ![21,2,8,32]
theorem edge1865_span : frame528.space ≤ frame533.space :=
  frame528.inclusion frame533 witness1865 (by decide)
def edge1865 : CertifiedEdge catalog where
  old := 528
  next := 533
  rank := 2
  good := by
    constructor
    · exact edge1865_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1866 : Fin frame529.rank → ℕ := ![81,2,68,40]
theorem edge1866_span : frame529.space ≤ frame503.space :=
  frame529.inclusion frame503 witness1866 (by decide)
def edge1866 : CertifiedEdge catalog where
  old := 529
  next := 503
  rank := 3
  good := by
    constructor
    · exact edge1866_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1867 : Fin frame529.rank → ℕ := ![17,2,4,40]
theorem edge1867_span : frame529.space ≤ frame532.space :=
  frame529.inclusion frame532 witness1867 (by decide)
def edge1867 : CertifiedEdge catalog where
  old := 529
  next := 532
  rank := 2
  good := by
    constructor
    · exact edge1867_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1868 : Fin frame530.rank → ℕ := ![81,2,20,40]
theorem edge1868_span : frame530.space ≤ frame514.space :=
  frame530.inclusion frame514 witness1868 (by decide)
def edge1868 : CertifiedEdge catalog where
  old := 530
  next := 514
  rank := 3
  good := by
    constructor
    · exact edge1868_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1869 : Fin frame530.rank → ℕ := ![33,18,4,24]
theorem edge1869_span : frame530.space ≤ frame531.space :=
  frame530.inclusion frame531 witness1869 (by decide)
def edge1869 : CertifiedEdge catalog where
  old := 530
  next := 531
  rank := 2
  good := by
    constructor
    · exact edge1869_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1870 : Fin frame531.rank → ℕ := ![1,34,4,8,48,64]
theorem edge1870_span : frame531.space ≤ frame449.space :=
  frame531.inclusion frame449 witness1870 (by decide)
def edge1870 : CertifiedEdge catalog where
  old := 531
  next := 449
  rank := 1
  good := by
    constructor
    · exact edge1870_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1871 : Fin frame531.rank → ℕ := ![17,2,20,8,32,64]
theorem edge1871_span : frame531.space ≤ frame503.space :=
  frame531.inclusion frame503 witness1871 (by decide)
def edge1871 : CertifiedEdge catalog where
  old := 531
  next := 503
  rank := 1
  good := by
    constructor
    · exact edge1871_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1872 : Fin frame532.rank → ℕ := ![65,2,68,8,16,32]
theorem edge1872_span : frame532.space ≤ frame463.space :=
  frame532.inclusion frame463 witness1872 (by decide)
def edge1872 : CertifiedEdge catalog where
  old := 532
  next := 463
  rank := 1
  good := by
    constructor
    · exact edge1872_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1873 : Fin frame532.rank → ℕ := ![1,66,4,72,16,32]
theorem edge1873_span : frame532.space ≤ frame524.space :=
  frame532.inclusion frame524 witness1873 (by decide)
def edge1873 : CertifiedEdge catalog where
  old := 532
  next := 524
  rank := 1
  good := by
    constructor
    · exact edge1873_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1874 : Fin frame533.rank → ℕ := ![1,34,4,40,16,64]
theorem edge1874_span : frame533.space ≤ frame491.space :=
  frame533.inclusion frame491 witness1874 (by decide)
def edge1874 : CertifiedEdge catalog where
  old := 533
  next := 491
  rank := 1
  good := by
    constructor
    · exact edge1874_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1875 : Fin frame533.rank → ℕ := ![65,2,4,8,80,32]
theorem edge1875_span : frame533.space ≤ frame514.space :=
  frame533.inclusion frame514 witness1875 (by decide)
def edge1875 : CertifiedEdge catalog where
  old := 533
  next := 514
  rank := 1
  good := by
    constructor
    · exact edge1875_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1876 : Fin frame534.rank → ℕ := ![9,10,12]
theorem edge1876_span : frame534.space ≤ frame124.space :=
  frame534.inclusion frame124 witness1876 (by decide)
def edge1876 : CertifiedEdge catalog where
  old := 534
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge1876_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1877 : Fin frame534.rank → ℕ := ![57,10,12]
theorem edge1877_span : frame534.space ≤ frame538.space :=
  frame534.inclusion frame538 witness1877 (by decide)
def edge1877 : CertifiedEdge catalog where
  old := 534
  next := 538
  rank := 3
  good := by
    constructor
    · exact edge1877_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1878 : Fin frame534.rank → ℕ := ![3,4,8]
theorem edge1878_span : frame534.space ≤ frame596.space :=
  frame534.inclusion frame596 witness1878 (by decide)
def edge1878 : CertifiedEdge catalog where
  old := 534
  next := 596
  rank := 1
  good := by
    constructor
    · exact edge1878_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1879 : Fin frame535.rank → ℕ := ![1,4,8]
theorem edge1879_span : frame535.space ≤ frame124.space :=
  frame535.inclusion frame124 witness1879 (by decide)
def edge1879 : CertifiedEdge catalog where
  old := 535
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge1879_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1880 : Fin frame535.rank → ℕ := ![1,20,56]
theorem edge1880_span : frame535.space ≤ frame539.space :=
  frame535.inclusion frame539 witness1880 (by decide)
def edge1880 : CertifiedEdge catalog where
  old := 535
  next := 539
  rank := 3
  good := by
    constructor
    · exact edge1880_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1881 : Fin frame535.rank → ℕ := ![3,4,8]
theorem edge1881_span : frame535.space ≤ frame597.space :=
  frame535.inclusion frame597 witness1881 (by decide)
def edge1881 : CertifiedEdge catalog where
  old := 535
  next := 597
  rank := 1
  good := by
    constructor
    · exact edge1881_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1882 : Fin frame536.rank → ℕ := ![1,10,12]
theorem edge1882_span : frame536.space ≤ frame124.space :=
  frame536.inclusion frame124 witness1882 (by decide)
def edge1882 : CertifiedEdge catalog where
  old := 536
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge1882_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1883 : Fin frame536.rank → ℕ := ![19,4,40]
theorem edge1883_span : frame536.space ≤ frame583.space :=
  frame536.inclusion frame583 witness1883 (by decide)
def edge1883 : CertifiedEdge catalog where
  old := 536
  next := 583
  rank := 3
  good := by
    constructor
    · exact edge1883_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1884 : Fin frame536.rank → ℕ := ![1,2,4]
theorem edge1884_span : frame536.space ≤ frame624.space :=
  frame536.inclusion frame624 witness1884 (by decide)
def edge1884 : CertifiedEdge catalog where
  old := 536
  next := 624
  rank := 1
  good := by
    constructor
    · exact edge1884_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1885 : Fin frame537.rank → ℕ := ![3,4,8]
theorem edge1885_span : frame537.space ≤ frame124.space :=
  frame537.inclusion frame124 witness1885 (by decide)
def edge1885 : CertifiedEdge catalog where
  old := 537
  next := 124
  rank := 1
  good := by
    constructor
    · exact edge1885_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1886 : Fin frame537.rank → ℕ := ![39,8,16]
theorem edge1886_span : frame537.space ≤ frame585.space :=
  frame537.inclusion frame585 witness1886 (by decide)
def edge1886 : CertifiedEdge catalog where
  old := 537
  next := 585
  rank := 3
  good := by
    constructor
    · exact edge1886_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1887 : Fin frame537.rank → ℕ := ![9,10,12]
theorem edge1887_span : frame537.space ≤ frame625.space :=
  frame537.inclusion frame625 witness1887 (by decide)
def edge1887 : CertifiedEdge catalog where
  old := 537
  next := 625
  rank := 1
  good := by
    constructor
    · exact edge1887_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
