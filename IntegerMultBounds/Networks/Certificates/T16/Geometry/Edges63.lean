module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2016 : Fin frame588.rank → ℕ := ![1,66,68,8,16,32]
theorem edge2016_span : frame588.space ≤ frame747.space :=
  frame588.inclusion frame747 witness2016 (by decide)
def edge2016 : CertifiedEdge catalog where
  old := 588
  next := 747
  rank := 1
  good := by
    constructor
    · exact edge2016_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2017 : Fin frame588.rank → ℕ := ![65,2,4,72,16,32]
theorem edge2017_span : frame588.space ≤ frame749.space :=
  frame588.inclusion frame749 witness2017 (by decide)
def edge2017 : CertifiedEdge catalog where
  old := 588
  next := 749
  rank := 1
  good := by
    constructor
    · exact edge2017_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2018 : Fin frame589.rank → ℕ := ![17,2,4,24,32,64]
theorem edge2018_span : frame589.space ≤ frame771.space :=
  frame589.inclusion frame771 witness2018 (by decide)
def edge2018 : CertifiedEdge catalog where
  old := 589
  next := 771
  rank := 1
  good := by
    constructor
    · exact edge2018_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2019 : Fin frame589.rank → ℕ := ![1,18,20,8,32,64]
theorem edge2019_span : frame589.space ≤ frame773.space :=
  frame589.inclusion frame773 witness2019 (by decide)
def edge2019 : CertifiedEdge catalog where
  old := 589
  next := 773
  rank := 1
  good := by
    constructor
    · exact edge2019_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2020 : Fin frame590.rank → ℕ := ![65,2,68,8,16,32]
theorem edge2020_span : frame590.space ≤ frame746.space :=
  frame590.inclusion frame746 witness2020 (by decide)
def edge2020 : CertifiedEdge catalog where
  old := 590
  next := 746
  rank := 1
  good := by
    constructor
    · exact edge2020_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2021 : Fin frame590.rank → ℕ := ![1,66,4,72,16,32]
theorem edge2021_span : frame590.space ≤ frame748.space :=
  frame590.inclusion frame748 witness2021 (by decide)
def edge2021 : CertifiedEdge catalog where
  old := 590
  next := 748
  rank := 1
  good := by
    constructor
    · exact edge2021_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2022 : Fin frame591.rank → ℕ := ![1,18,4,24,32,64]
theorem edge2022_span : frame591.space ≤ frame770.space :=
  frame591.inclusion frame770 witness2022 (by decide)
def edge2022 : CertifiedEdge catalog where
  old := 591
  next := 770
  rank := 1
  good := by
    constructor
    · exact edge2022_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2023 : Fin frame591.rank → ℕ := ![17,2,20,8,32,64]
theorem edge2023_span : frame591.space ≤ frame772.space :=
  frame591.inclusion frame772 witness2023 (by decide)
def edge2023 : CertifiedEdge catalog where
  old := 591
  next := 772
  rank := 1
  good := by
    constructor
    · exact edge2023_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2024 : Fin frame592.rank → ℕ := ![17,18,4,24]
theorem edge2024_span : frame592.space ≤ frame630.space :=
  frame592.inclusion frame630 witness2024 (by decide)
def edge2024 : CertifiedEdge catalog where
  old := 592
  next := 630
  rank := 1
  good := by
    constructor
    · exact edge2024_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2025 : Fin frame592.rank → ℕ := ![17,18,100,24]
theorem edge2025_span : frame592.space ≤ frame743.space :=
  frame592.inclusion frame743 witness2025 (by decide)
def edge2025 : CertifiedEdge catalog where
  old := 592
  next := 743
  rank := 3
  good := by
    constructor
    · exact edge2025_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2026 : Fin frame593.rank → ℕ := ![17,18,4,8]
theorem edge2026_span : frame593.space ≤ frame631.space :=
  frame593.inclusion frame631 witness2026 (by decide)
def edge2026 : CertifiedEdge catalog where
  old := 593
  next := 631
  rank := 1
  good := by
    constructor
    · exact edge2026_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2027 : Fin frame593.rank → ℕ := ![5,6,40,112]
theorem edge2027_span : frame593.space ≤ frame745.space :=
  frame593.inclusion frame745 witness2027 (by decide)
def edge2027 : CertifiedEdge catalog where
  old := 593
  next := 745
  rank := 3
  good := by
    constructor
    · exact edge2027_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2028 : Fin frame594.rank → ℕ := ![17,2,4,8]
theorem edge2028_span : frame594.space ≤ frame734.space :=
  frame594.inclusion frame734 witness2028 (by decide)
def edge2028 : CertifiedEdge catalog where
  old := 594
  next := 734
  rank := 1
  good := by
    constructor
    · exact edge2028_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2029 : Fin frame594.rank → ℕ := ![35,68,8,80]
theorem edge2029_span : frame594.space ≤ frame745.space :=
  frame594.inclusion frame745 witness2029 (by decide)
def edge2029 : CertifiedEdge catalog where
  old := 594
  next := 745
  rank := 3
  good := by
    constructor
    · exact edge2029_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2030 : Fin frame595.rank → ℕ := ![9,2,4,16]
theorem edge2030_span : frame595.space ≤ frame735.space :=
  frame595.inclusion frame735 witness2030 (by decide)
def edge2030 : CertifiedEdge catalog where
  old := 595
  next := 735
  rank := 1
  good := by
    constructor
    · exact edge2030_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2031 : Fin frame595.rank → ℕ := ![39,8,16,64]
theorem edge2031_span : frame595.space ≤ frame744.space :=
  frame595.inclusion frame744 witness2031 (by decide)
def edge2031 : CertifiedEdge catalog where
  old := 595
  next := 744
  rank := 3
  good := by
    constructor
    · exact edge2031_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2032 : Fin frame596.rank → ℕ := ![1,18,20,24]
theorem edge2032_span : frame596.space ≤ frame630.space :=
  frame596.inclusion frame630 witness2032 (by decide)
def edge2032 : CertifiedEdge catalog where
  old := 596
  next := 630
  rank := 1
  good := by
    constructor
    · exact edge2032_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2033 : Fin frame596.rank → ℕ := ![97,18,20,24]
theorem edge2033_span : frame596.space ≤ frame747.space :=
  frame596.inclusion frame747 witness2033 (by decide)
def edge2033 : CertifiedEdge catalog where
  old := 596
  next := 747
  rank := 3
  good := by
    constructor
    · exact edge2033_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2034 : Fin frame597.rank → ℕ := ![17,2,4,8]
theorem edge2034_span : frame597.space ≤ frame631.space :=
  frame597.inclusion frame631 witness2034 (by decide)
def edge2034 : CertifiedEdge catalog where
  old := 597
  next := 631
  rank := 1
  good := by
    constructor
    · exact edge2034_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2035 : Fin frame597.rank → ℕ := ![5,6,40,112]
theorem edge2035_span : frame597.space ≤ frame749.space :=
  frame597.inclusion frame749 witness2035 (by decide)
def edge2035 : CertifiedEdge catalog where
  old := 597
  next := 749
  rank := 3
  good := by
    constructor
    · exact edge2035_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2036 : Fin frame598.rank → ℕ := ![1,18,4,8]
theorem edge2036_span : frame598.space ≤ frame740.space :=
  frame598.inclusion frame740 witness2036 (by decide)
def edge2036 : CertifiedEdge catalog where
  old := 598
  next := 740
  rank := 1
  good := by
    constructor
    · exact edge2036_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2037 : Fin frame598.rank → ℕ := ![65,38,8,80]
theorem edge2037_span : frame598.space ≤ frame749.space :=
  frame598.inclusion frame749 witness2037 (by decide)
def edge2037 : CertifiedEdge catalog where
  old := 598
  next := 749
  rank := 3
  good := by
    constructor
    · exact edge2037_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2038 : Fin frame599.rank → ℕ := ![17,2,4,8]
theorem edge2038_span : frame599.space ≤ frame741.space :=
  frame599.inclusion frame741 witness2038 (by decide)
def edge2038 : CertifiedEdge catalog where
  old := 599
  next := 741
  rank := 1
  good := by
    constructor
    · exact edge2038_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2039 : Fin frame599.rank → ℕ := ![37,66,8,80]
theorem edge2039_span : frame599.space ≤ frame748.space :=
  frame599.inclusion frame748 witness2039 (by decide)
def edge2039 : CertifiedEdge catalog where
  old := 599
  next := 748
  rank := 3
  good := by
    constructor
    · exact edge2039_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2040 : Fin frame600.rank → ℕ := ![17,18,4,8]
theorem edge2040_span : frame600.space ≤ frame632.space :=
  frame600.inclusion frame632 witness2040 (by decide)
def edge2040 : CertifiedEdge catalog where
  old := 600
  next := 632
  rank := 1
  good := by
    constructor
    · exact edge2040_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2041 : Fin frame600.rank → ℕ := ![5,6,104,112]
theorem edge2041_span : frame600.space ≤ frame751.space :=
  frame600.inclusion frame751 witness2041 (by decide)
def edge2041 : CertifiedEdge catalog where
  old := 600
  next := 751
  rank := 3
  good := by
    constructor
    · exact edge2041_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2042 : Fin frame601.rank → ℕ := ![1,2,12,16]
theorem edge2042_span : frame601.space ≤ frame633.space :=
  frame601.inclusion frame633 witness2042 (by decide)
def edge2042 : CertifiedEdge catalog where
  old := 601
  next := 633
  rank := 1
  good := by
    constructor
    · exact edge2042_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2043 : Fin frame601.rank → ℕ := ![33,34,76,48]
theorem edge2043_span : frame601.space ≤ frame753.space :=
  frame601.inclusion frame753 witness2043 (by decide)
def edge2043 : CertifiedEdge catalog where
  old := 601
  next := 753
  rank := 3
  good := by
    constructor
    · exact edge2043_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2044 : Fin frame602.rank → ℕ := ![1,2,4,24]
theorem edge2044_span : frame602.space ≤ frame736.space :=
  frame602.inclusion frame736 witness2044 (by decide)
def edge2044 : CertifiedEdge catalog where
  old := 602
  next := 736
  rank := 1
  good := by
    constructor
    · exact edge2044_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2045 : Fin frame602.rank → ℕ := ![67,4,72,48]
theorem edge2045_span : frame602.space ≤ frame753.space :=
  frame602.inclusion frame753 witness2045 (by decide)
def edge2045 : CertifiedEdge catalog where
  old := 602
  next := 753
  rank := 3
  good := by
    constructor
    · exact edge2045_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2046 : Fin frame603.rank → ℕ := ![9,10,4,16,32,64]
theorem edge2046_span : frame603.space ≤ frame751.space :=
  frame603.inclusion frame751 witness2046 (by decide)
def edge2046 : CertifiedEdge catalog where
  old := 603
  next := 751
  rank := 1
  good := by
    constructor
    · exact edge2046_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2047 : Fin frame603.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2047_span : frame603.space ≤ frame761.space :=
  frame603.inclusion frame761 witness2047 (by decide)
def edge2047 : CertifiedEdge catalog where
  old := 603
  next := 761
  rank := 1
  good := by
    constructor
    · exact edge2047_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
