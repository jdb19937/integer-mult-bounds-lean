module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1952 : Fin frame562.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1952_span : frame562.space ≤ frame762.space :=
  frame562.inclusion frame762 witness1952 (by decide)
def edge1952 : CertifiedEdge catalog where
  old := 562
  next := 762
  rank := 1
  good := by
    constructor
    · exact edge1952_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1953 : Fin frame562.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1953_span : frame562.space ≤ frame763.space :=
  frame562.inclusion frame763 witness1953 (by decide)
def edge1953 : CertifiedEdge catalog where
  old := 562
  next := 763
  rank := 1
  good := by
    constructor
    · exact edge1953_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1954 : Fin frame563.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1954_span : frame563.space ≤ frame764.space :=
  frame563.inclusion frame764 witness1954 (by decide)
def edge1954 : CertifiedEdge catalog where
  old := 563
  next := 764
  rank := 1
  good := by
    constructor
    · exact edge1954_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1955 : Fin frame563.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1955_span : frame563.space ≤ frame765.space :=
  frame563.inclusion frame765 witness1955 (by decide)
def edge1955 : CertifiedEdge catalog where
  old := 563
  next := 765
  rank := 1
  good := by
    constructor
    · exact edge1955_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1956 : Fin frame564.rank → ℕ := ![1,2,8]
theorem edge1956_span : frame564.space ≤ frame269.space :=
  frame564.inclusion frame269 witness1956 (by decide)
def edge1956 : CertifiedEdge catalog where
  old := 564
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1956_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1957 : Fin frame564.rank → ℕ := ![33,34,48]
theorem edge1957_span : frame564.space ≤ frame568.space :=
  frame564.inclusion frame568 witness1957 (by decide)
def edge1957 : CertifiedEdge catalog where
  old := 564
  next := 568
  rank := 3
  good := by
    constructor
    · exact edge1957_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1958 : Fin frame564.rank → ℕ := ![1,2,8]
theorem edge1958_span : frame564.space ≤ frame611.space :=
  frame564.inclusion frame611 witness1958 (by decide)
def edge1958 : CertifiedEdge catalog where
  old := 564
  next := 611
  rank := 1
  good := by
    constructor
    · exact edge1958_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1959 : Fin frame565.rank → ℕ := ![5,6,8]
theorem edge1959_span : frame565.space ≤ frame269.space :=
  frame565.inclusion frame269 witness1959 (by decide)
def edge1959 : CertifiedEdge catalog where
  old := 565
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1959_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1960 : Fin frame565.rank → ℕ := ![5,6,56]
theorem edge1960_span : frame565.space ≤ frame569.space :=
  frame565.inclusion frame569 witness1960 (by decide)
def edge1960 : CertifiedEdge catalog where
  old := 565
  next := 569
  rank := 3
  good := by
    constructor
    · exact edge1960_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1961 : Fin frame565.rank → ℕ := ![1,2,12]
theorem edge1961_span : frame565.space ≤ frame612.space :=
  frame565.inclusion frame612 witness1961 (by decide)
def edge1961 : CertifiedEdge catalog where
  old := 565
  next := 612
  rank := 1
  good := by
    constructor
    · exact edge1961_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1962 : Fin frame566.rank → ℕ := ![1,6,8]
theorem edge1962_span : frame566.space ≤ frame269.space :=
  frame566.inclusion frame269 witness1962 (by decide)
def edge1962 : CertifiedEdge catalog where
  old := 566
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1962_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1963 : Fin frame566.rank → ℕ := ![1,6,8]
theorem edge1963_span : frame566.space ≤ frame607.space :=
  frame566.inclusion frame607 witness1963 (by decide)
def edge1963 : CertifiedEdge catalog where
  old := 566
  next := 607
  rank := 1
  good := by
    constructor
    · exact edge1963_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1964 : Fin frame566.rank → ℕ := ![65,14,112]
theorem edge1964_span : frame566.space ≤ frame755.space :=
  frame566.inclusion frame755 witness1964 (by decide)
def edge1964 : CertifiedEdge catalog where
  old := 566
  next := 755
  rank := 4
  good := by
    constructor
    · exact edge1964_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1965 : Fin frame567.rank → ℕ := ![5,2,8]
theorem edge1965_span : frame567.space ≤ frame269.space :=
  frame567.inclusion frame269 witness1965 (by decide)
def edge1965 : CertifiedEdge catalog where
  old := 567
  next := 269
  rank := 1
  good := by
    constructor
    · exact edge1965_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1966 : Fin frame567.rank → ℕ := ![5,2,8]
theorem edge1966_span : frame567.space ≤ frame609.space :=
  frame567.inclusion frame609 witness1966 (by decide)
def edge1966 : CertifiedEdge catalog where
  old := 567
  next := 609
  rank := 1
  good := by
    constructor
    · exact edge1966_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1967 : Fin frame567.rank → ℕ := ![13,66,112]
theorem edge1967_span : frame567.space ≤ frame754.space :=
  frame567.inclusion frame754 witness1967 (by decide)
def edge1967 : CertifiedEdge catalog where
  old := 567
  next := 754
  rank := 4
  good := by
    constructor
    · exact edge1967_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1968 : Fin frame568.rank → ℕ := ![1,2,36,8,48,64]
theorem edge1968_span : frame568.space ≤ frame758.space :=
  frame568.inclusion frame758 witness1968 (by decide)
def edge1968 : CertifiedEdge catalog where
  old := 568
  next := 758
  rank := 1
  good := by
    constructor
    · exact edge1968_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1969 : Fin frame568.rank → ℕ := ![65,66,68,72,80,96]
theorem edge1969_span : frame568.space ≤ frame759.space :=
  frame568.inclusion frame759 witness1969 (by decide)
def edge1969 : CertifiedEdge catalog where
  old := 568
  next := 759
  rank := 1
  good := by
    constructor
    · exact edge1969_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1970 : Fin frame569.rank → ℕ := ![9,10,4,16,32,64]
theorem edge1970_span : frame569.space ≤ frame760.space :=
  frame569.inclusion frame760 witness1970 (by decide)
def edge1970 : CertifiedEdge catalog where
  old := 569
  next := 760
  rank := 1
  good := by
    constructor
    · exact edge1970_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1971 : Fin frame569.rank → ℕ := ![1,2,4,8,80,96]
theorem edge1971_span : frame569.space ≤ frame761.space :=
  frame569.inclusion frame761 witness1971 (by decide)
def edge1971 : CertifiedEdge catalog where
  old := 569
  next := 761
  rank := 1
  good := by
    constructor
    · exact edge1971_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1972 : Fin frame570.rank → ℕ := ![1,4,8]
theorem edge1972_span : frame570.space ≤ frame298.space :=
  frame570.inclusion frame298 witness1972 (by decide)
def edge1972 : CertifiedEdge catalog where
  old := 570
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1972_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1973 : Fin frame570.rank → ℕ := ![1,20,56]
theorem edge1973_span : frame570.space ≤ frame574.space :=
  frame570.inclusion frame574 witness1973 (by decide)
def edge1973 : CertifiedEdge catalog where
  old := 570
  next := 574
  rank := 3
  good := by
    constructor
    · exact edge1973_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1974 : Fin frame570.rank → ℕ := ![3,4,8]
theorem edge1974_span : frame570.space ≤ frame626.space :=
  frame570.inclusion frame626 witness1974 (by decide)
def edge1974 : CertifiedEdge catalog where
  old := 570
  next := 626
  rank := 1
  good := by
    constructor
    · exact edge1974_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1975 : Fin frame571.rank → ℕ := ![9,2,12]
theorem edge1975_span : frame571.space ≤ frame298.space :=
  frame571.inclusion frame298 witness1975 (by decide)
def edge1975 : CertifiedEdge catalog where
  old := 571
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1975_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1976 : Fin frame571.rank → ℕ := ![57,34,36]
theorem edge1976_span : frame571.space ≤ frame575.space :=
  frame571.inclusion frame575 witness1976 (by decide)
def edge1976 : CertifiedEdge catalog where
  old := 571
  next := 575
  rank := 3
  good := by
    constructor
    · exact edge1976_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1977 : Fin frame571.rank → ℕ := ![3,4,8]
theorem edge1977_span : frame571.space ≤ frame627.space :=
  frame571.inclusion frame627 witness1977 (by decide)
def edge1977 : CertifiedEdge catalog where
  old := 571
  next := 627
  rank := 1
  good := by
    constructor
    · exact edge1977_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1978 : Fin frame572.rank → ℕ := ![1,2,12]
theorem edge1978_span : frame572.space ≤ frame298.space :=
  frame572.inclusion frame298 witness1978 (by decide)
def edge1978 : CertifiedEdge catalog where
  old := 572
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1978_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1979 : Fin frame572.rank → ℕ := ![35,4,24]
theorem edge1979_span : frame572.space ≤ frame582.space :=
  frame572.inclusion frame582 witness1979 (by decide)
def edge1979 : CertifiedEdge catalog where
  old := 572
  next := 582
  rank := 3
  good := by
    constructor
    · exact edge1979_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1980 : Fin frame572.rank → ℕ := ![1,2,12]
theorem edge1980_span : frame572.space ≤ frame594.space :=
  frame572.inclusion frame594 witness1980 (by decide)
def edge1980 : CertifiedEdge catalog where
  old := 572
  next := 594
  rank := 1
  good := by
    constructor
    · exact edge1980_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1981 : Fin frame573.rank → ℕ := ![3,4,8]
theorem edge1981_span : frame573.space ≤ frame298.space :=
  frame573.inclusion frame298 witness1981 (by decide)
def edge1981 : CertifiedEdge catalog where
  old := 573
  next := 298
  rank := 1
  good := by
    constructor
    · exact edge1981_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1982 : Fin frame573.rank → ℕ := ![39,8,16]
theorem edge1982_span : frame573.space ≤ frame584.space :=
  frame573.inclusion frame584 witness1982 (by decide)
def edge1982 : CertifiedEdge catalog where
  old := 573
  next := 584
  rank := 3
  good := by
    constructor
    · exact edge1982_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1983 : Fin frame573.rank → ℕ := ![1,10,12]
theorem edge1983_span : frame573.space ≤ frame595.space :=
  frame573.inclusion frame595 witness1983 (by decide)
def edge1983 : CertifiedEdge catalog where
  old := 573
  next := 595
  rank := 1
  good := by
    constructor
    · exact edge1983_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
