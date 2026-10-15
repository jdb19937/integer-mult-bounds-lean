module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness960 : Fin frame223.rank → ℕ := ![1,4]
theorem edge960_span : frame223.space ≤ frame560.space :=
  frame223.inclusion frame560 witness960 (by decide)
def edge960 : CertifiedEdge catalog where
  old := 223
  next := 560
  rank := 1
  good := by
    constructor
    · exact edge960_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness961 : Fin frame223.rank → ℕ := ![11,16]
theorem edge961_span : frame223.space ≤ frame614.space :=
  frame223.inclusion frame614 witness961 (by decide)
def edge961 : CertifiedEdge catalog where
  old := 223
  next := 614
  rank := 4
  good := by
    constructor
    · exact edge961_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness962 : Fin frame223.rank → ℕ := ![11,112]
theorem edge962_span : frame223.space ≤ frame760.space :=
  frame223.inclusion frame760 witness962 (by decide)
def edge962 : CertifiedEdge catalog where
  old := 223
  next := 760
  rank := 5
  good := by
    constructor
    · exact edge962_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness963 : Fin frame224.rank → ℕ := ![5,2]
theorem edge963_span : frame224.space ≤ frame233.space :=
  frame224.inclusion frame233 witness963 (by decide)
def edge963 : CertifiedEdge catalog where
  old := 224
  next := 233
  rank := 1
  good := by
    constructor
    · exact edge963_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness964 : Fin frame224.rank → ℕ := ![5,6]
theorem edge964_span : frame224.space ≤ frame238.space :=
  frame224.inclusion frame238 witness964 (by decide)
def edge964 : CertifiedEdge catalog where
  old := 224
  next := 238
  rank := 1
  good := by
    constructor
    · exact edge964_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness965 : Fin frame225.rank → ℕ := ![5,2]
theorem edge965_span : frame225.space ≤ frame234.space :=
  frame225.inclusion frame234 witness965 (by decide)
def edge965 : CertifiedEdge catalog where
  old := 225
  next := 234
  rank := 1
  good := by
    constructor
    · exact edge965_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness966 : Fin frame225.rank → ℕ := ![5,6]
theorem edge966_span : frame225.space ≤ frame237.space :=
  frame225.inclusion frame237 witness966 (by decide)
def edge966 : CertifiedEdge catalog where
  old := 225
  next := 237
  rank := 1
  good := by
    constructor
    · exact edge966_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness967 : Fin frame226.rank → ℕ := ![1,6]
theorem edge967_span : frame226.space ≤ frame235.space :=
  frame226.inclusion frame235 witness967 (by decide)
def edge967 : CertifiedEdge catalog where
  old := 226
  next := 235
  rank := 1
  good := by
    constructor
    · exact edge967_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness968 : Fin frame226.rank → ℕ := ![1,2]
theorem edge968_span : frame226.space ≤ frame236.space :=
  frame226.inclusion frame236 witness968 (by decide)
def edge968 : CertifiedEdge catalog where
  old := 226
  next := 236
  rank := 1
  good := by
    constructor
    · exact edge968_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness969 : Fin frame227.rank → ℕ := ![1,6]
theorem edge969_span : frame227.space ≤ frame232.space :=
  frame227.inclusion frame232 witness969 (by decide)
def edge969 : CertifiedEdge catalog where
  old := 227
  next := 232
  rank := 1
  good := by
    constructor
    · exact edge969_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness970 : Fin frame227.rank → ℕ := ![1,2]
theorem edge970_span : frame227.space ≤ frame239.space :=
  frame227.inclusion frame239 witness970 (by decide)
def edge970 : CertifiedEdge catalog where
  old := 227
  next := 239
  rank := 1
  good := by
    constructor
    · exact edge970_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness971 : Fin frame228.rank → ℕ := ![2,4]
theorem edge971_span : frame228.space ≤ frame234.space :=
  frame228.inclusion frame234 witness971 (by decide)
def edge971 : CertifiedEdge catalog where
  old := 228
  next := 234
  rank := 1
  good := by
    constructor
    · exact edge971_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness972 : Fin frame228.rank → ℕ := ![2,4]
theorem edge972_span : frame228.space ≤ frame236.space :=
  frame228.inclusion frame236 witness972 (by decide)
def edge972 : CertifiedEdge catalog where
  old := 228
  next := 236
  rank := 1
  good := by
    constructor
    · exact edge972_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness973 : Fin frame229.rank → ℕ := ![2,4]
theorem edge973_span : frame229.space ≤ frame232.space :=
  frame229.inclusion frame232 witness973 (by decide)
def edge973 : CertifiedEdge catalog where
  old := 229
  next := 232
  rank := 1
  good := by
    constructor
    · exact edge973_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness974 : Fin frame229.rank → ℕ := ![2,4]
theorem edge974_span : frame229.space ≤ frame238.space :=
  frame229.inclusion frame238 witness974 (by decide)
def edge974 : CertifiedEdge catalog where
  old := 229
  next := 238
  rank := 1
  good := by
    constructor
    · exact edge974_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness975 : Fin frame230.rank → ℕ := ![3,4]
theorem edge975_span : frame230.space ≤ frame558.space :=
  frame230.inclusion frame558 witness975 (by decide)
def edge975 : CertifiedEdge catalog where
  old := 230
  next := 558
  rank := 1
  good := by
    constructor
    · exact edge975_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness976 : Fin frame230.rank → ℕ := ![5,6]
theorem edge976_span : frame230.space ≤ frame561.space :=
  frame230.inclusion frame561 witness976 (by decide)
def edge976 : CertifiedEdge catalog where
  old := 230
  next := 561
  rank := 1
  good := by
    constructor
    · exact edge976_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness977 : Fin frame230.rank → ℕ := ![7,8]
theorem edge977_span : frame230.space ≤ frame611.space :=
  frame230.inclusion frame611 witness977 (by decide)
def edge977 : CertifiedEdge catalog where
  old := 230
  next := 611
  rank := 2
  good := by
    constructor
    · exact edge977_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness978 : Fin frame230.rank → ℕ := ![11,12]
theorem edge978_span : frame230.space ≤ frame615.space :=
  frame230.inclusion frame615 witness978 (by decide)
def edge978 : CertifiedEdge catalog where
  old := 230
  next := 615
  rank := 2
  good := by
    constructor
    · exact edge978_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness979 : Fin frame231.rank → ℕ := ![2,4]
theorem edge979_span : frame231.space ≤ frame558.space :=
  frame231.inclusion frame558 witness979 (by decide)
def edge979 : CertifiedEdge catalog where
  old := 231
  next := 558
  rank := 1
  good := by
    constructor
    · exact edge979_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness980 : Fin frame231.rank → ℕ := ![2,4]
theorem edge980_span : frame231.space ≤ frame560.space :=
  frame231.inclusion frame560 witness980 (by decide)
def edge980 : CertifiedEdge catalog where
  old := 231
  next := 560
  rank := 1
  good := by
    constructor
    · exact edge980_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness981 : Fin frame231.rank → ℕ := ![2,12]
theorem edge981_span : frame231.space ≤ frame613.space :=
  frame231.inclusion frame613 witness981 (by decide)
def edge981 : CertifiedEdge catalog where
  old := 231
  next := 613
  rank := 2
  good := by
    constructor
    · exact edge981_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness982 : Fin frame231.rank → ℕ := ![68,112]
theorem edge982_span : frame231.space ≤ frame758.space :=
  frame231.inclusion frame758 witness982 (by decide)
def edge982 : CertifiedEdge catalog where
  old := 231
  next := 758
  rank := 5
  good := by
    constructor
    · exact edge982_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness983 : Fin frame232.rank → ℕ := ![1,2,4]
theorem edge983_span : frame232.space ≤ frame240.space :=
  frame232.inclusion frame240 witness983 (by decide)
def edge983 : CertifiedEdge catalog where
  old := 232
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge983_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness984 : Fin frame232.rank → ℕ := ![5,50,40]
theorem edge984_span : frame232.space ≤ frame642.space :=
  frame232.inclusion frame642 witness984 (by decide)
def edge984 : CertifiedEdge catalog where
  old := 232
  next := 642
  rank := 3
  good := by
    constructor
    · exact edge984_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness985 : Fin frame232.rank → ℕ := ![11,36,16]
theorem edge985_span : frame232.space ≤ frame702.space :=
  frame232.inclusion frame702 witness985 (by decide)
def edge985 : CertifiedEdge catalog where
  old := 232
  next := 702
  rank := 3
  good := by
    constructor
    · exact edge985_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness986 : Fin frame233.rank → ℕ := ![5,6,8]
theorem edge986_span : frame233.space ≤ frame240.space :=
  frame233.inclusion frame240 witness986 (by decide)
def edge986 : CertifiedEdge catalog where
  old := 233
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge986_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness987 : Fin frame233.rank → ℕ := ![37,18,24]
theorem edge987_span : frame233.space ≤ frame643.space :=
  frame233.inclusion frame643 witness987 (by decide)
def edge987 : CertifiedEdge catalog where
  old := 233
  next := 643
  rank := 3
  good := by
    constructor
    · exact edge987_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness988 : Fin frame233.rank → ℕ := ![11,36,48]
theorem edge988_span : frame233.space ≤ frame703.space :=
  frame233.inclusion frame703 witness988 (by decide)
def edge988 : CertifiedEdge catalog where
  old := 233
  next := 703
  rank := 3
  good := by
    constructor
    · exact edge988_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness989 : Fin frame234.rank → ℕ := ![9,10,4]
theorem edge989_span : frame234.space ≤ frame240.space :=
  frame234.inclusion frame240 witness989 (by decide)
def edge989 : CertifiedEdge catalog where
  old := 234
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge989_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness990 : Fin frame234.rank → ℕ := ![43,4,16]
theorem edge990_span : frame234.space ≤ frame652.space :=
  frame234.inclusion frame652 witness990 (by decide)
def edge990 : CertifiedEdge catalog where
  old := 234
  next := 652
  rank := 3
  good := by
    constructor
    · exact edge990_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness991 : Fin frame234.rank → ℕ := ![21,34,40]
theorem edge991_span : frame234.space ≤ frame712.space :=
  frame234.inclusion frame712 witness991 (by decide)
def edge991 : CertifiedEdge catalog where
  old := 234
  next := 712
  rank := 3
  good := by
    constructor
    · exact edge991_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
