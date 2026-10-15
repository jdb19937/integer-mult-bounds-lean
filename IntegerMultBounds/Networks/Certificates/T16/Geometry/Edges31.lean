module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness992 : Fin frame235.rank → ℕ := ![1,2,8]
theorem edge992_span : frame235.space ≤ frame240.space :=
  frame235.inclusion frame240 witness992 (by decide)
def edge992 : CertifiedEdge catalog where
  old := 235
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge992_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness993 : Fin frame235.rank → ℕ := ![11,36,48]
theorem edge993_span : frame235.space ≤ frame653.space :=
  frame235.inclusion frame653 witness993 (by decide)
def edge993 : CertifiedEdge catalog where
  old := 235
  next := 653
  rank := 3
  good := by
    constructor
    · exact edge993_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness994 : Fin frame235.rank → ℕ := ![5,50,24]
theorem edge994_span : frame235.space ≤ frame713.space :=
  frame235.inclusion frame713 witness994 (by decide)
def edge994 : CertifiedEdge catalog where
  old := 235
  next := 713
  rank := 3
  good := by
    constructor
    · exact edge994_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness995 : Fin frame236.rank → ℕ := ![1,10,4]
theorem edge995_span : frame236.space ≤ frame240.space :=
  frame236.inclusion frame240 witness995 (by decide)
def edge995 : CertifiedEdge catalog where
  old := 236
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge995_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness996 : Fin frame236.rank → ℕ := ![11,36,16]
theorem edge996_span : frame236.space ≤ frame658.space :=
  frame236.inclusion frame658 witness996 (by decide)
def edge996 : CertifiedEdge catalog where
  old := 236
  next := 658
  rank := 3
  good := by
    constructor
    · exact edge996_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness997 : Fin frame236.rank → ℕ := ![5,50,40]
theorem edge997_span : frame236.space ≤ frame718.space :=
  frame236.inclusion frame718 witness997 (by decide)
def edge997 : CertifiedEdge catalog where
  old := 236
  next := 718
  rank := 3
  good := by
    constructor
    · exact edge997_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness998 : Fin frame237.rank → ℕ := ![5,2,8]
theorem edge998_span : frame237.space ≤ frame240.space :=
  frame237.inclusion frame240 witness998 (by decide)
def edge998 : CertifiedEdge catalog where
  old := 237
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge998_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness999 : Fin frame237.rank → ℕ := ![27,4,32]
theorem edge999_span : frame237.space ≤ frame659.space :=
  frame237.inclusion frame659 witness999 (by decide)
def edge999 : CertifiedEdge catalog where
  old := 237
  next := 659
  rank := 3
  good := by
    constructor
    · exact edge999_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1000 : Fin frame237.rank → ℕ := ![13,34,48]
theorem edge1000_span : frame237.space ≤ frame719.space :=
  frame237.inclusion frame719 witness1000 (by decide)
def edge1000 : CertifiedEdge catalog where
  old := 237
  next := 719
  rank := 3
  good := by
    constructor
    · exact edge1000_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1001 : Fin frame238.rank → ℕ := ![9,2,4]
theorem edge1001_span : frame238.space ≤ frame240.space :=
  frame238.inclusion frame240 witness1001 (by decide)
def edge1001 : CertifiedEdge catalog where
  old := 238
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge1001_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1002 : Fin frame238.rank → ℕ := ![21,34,40]
theorem edge1002_span : frame238.space ≤ frame668.space :=
  frame238.inclusion frame668 witness1002 (by decide)
def edge1002 : CertifiedEdge catalog where
  old := 238
  next := 668
  rank := 3
  good := by
    constructor
    · exact edge1002_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1003 : Fin frame238.rank → ℕ := ![43,4,16]
theorem edge1003_span : frame238.space ≤ frame728.space :=
  frame238.inclusion frame728 witness1003 (by decide)
def edge1003 : CertifiedEdge catalog where
  old := 238
  next := 728
  rank := 3
  good := by
    constructor
    · exact edge1003_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1004 : Fin frame239.rank → ℕ := ![1,6,8]
theorem edge1004_span : frame239.space ≤ frame240.space :=
  frame239.inclusion frame240 witness1004 (by decide)
def edge1004 : CertifiedEdge catalog where
  old := 239
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge1004_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1005 : Fin frame239.rank → ℕ := ![5,42,48]
theorem edge1005_span : frame239.space ≤ frame669.space :=
  frame239.inclusion frame669 witness1005 (by decide)
def edge1005 : CertifiedEdge catalog where
  old := 239
  next := 669
  rank := 3
  good := by
    constructor
    · exact edge1005_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1006 : Fin frame239.rank → ℕ := ![11,20,32]
theorem edge1006_span : frame239.space ≤ frame729.space :=
  frame239.inclusion frame729 witness1006 (by decide)
def edge1006 : CertifiedEdge catalog where
  old := 239
  next := 729
  rank := 3
  good := by
    constructor
    · exact edge1006_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1007 : Fin frame240.rank → ℕ := ![11,196,400,352]
theorem edge1007_span : frame240.space ≤ frame1.space :=
  frame240.inclusion frame1 witness1007 (by decide)
def edge1007 : CertifiedEdge catalog where
  old := 240
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge1007_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1008 : Fin frame240.rank → ℕ := ![11,196,144,96]
theorem edge1008_span : frame240.space ≤ frame416.space :=
  frame240.inclusion frame416 witness1008 (by decide)
def edge1008 : CertifiedEdge catalog where
  old := 240
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge1008_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1009 : Fin frame240.rank → ℕ := ![11,196,144,96]
theorem edge1009_span : frame240.space ≤ frame417.space :=
  frame240.inclusion frame417 witness1009 (by decide)
def edge1009 : CertifiedEdge catalog where
  old := 240
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge1009_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1010 : Fin frame240.rank → ℕ := ![11,68,144,224]
theorem edge1010_span : frame240.space ≤ frame419.space :=
  frame240.inclusion frame419 witness1010 (by decide)
def edge1010 : CertifiedEdge catalog where
  old := 240
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge1010_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1011 : Fin frame240.rank → ℕ := ![11,68,208,160]
theorem edge1011_span : frame240.space ≤ frame422.space :=
  frame240.inclusion frame422 witness1011 (by decide)
def edge1011 : CertifiedEdge catalog where
  old := 240
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge1011_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1012 : Fin frame241.rank → ℕ := ![3]
theorem edge1012_span : frame241.space ≤ frame249.space :=
  frame241.inclusion frame249 witness1012 (by decide)
def edge1012 : CertifiedEdge catalog where
  old := 241
  next := 249
  rank := 1
  good := by
    constructor
    · exact edge1012_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1013 : Fin frame241.rank → ℕ := ![3]
theorem edge1013_span : frame241.space ≤ frame250.space :=
  frame241.inclusion frame250 witness1013 (by decide)
def edge1013 : CertifiedEdge catalog where
  old := 241
  next := 250
  rank := 1
  good := by
    constructor
    · exact edge1013_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1014 : Fin frame241.rank → ℕ := ![3]
theorem edge1014_span : frame241.space ≤ frame251.space :=
  frame241.inclusion frame251 witness1014 (by decide)
def edge1014 : CertifiedEdge catalog where
  old := 241
  next := 251
  rank := 1
  good := by
    constructor
    · exact edge1014_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1015 : Fin frame242.rank → ℕ := ![1]
theorem edge1015_span : frame242.space ≤ frame252.space :=
  frame242.inclusion frame252 witness1015 (by decide)
def edge1015 : CertifiedEdge catalog where
  old := 242
  next := 252
  rank := 1
  good := by
    constructor
    · exact edge1015_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1016 : Fin frame242.rank → ℕ := ![3]
theorem edge1016_span : frame242.space ≤ frame253.space :=
  frame242.inclusion frame253 witness1016 (by decide)
def edge1016 : CertifiedEdge catalog where
  old := 242
  next := 253
  rank := 1
  good := by
    constructor
    · exact edge1016_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1017 : Fin frame242.rank → ℕ := ![3]
theorem edge1017_span : frame242.space ≤ frame254.space :=
  frame242.inclusion frame254 witness1017 (by decide)
def edge1017 : CertifiedEdge catalog where
  old := 242
  next := 254
  rank := 1
  good := by
    constructor
    · exact edge1017_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1018 : Fin frame243.rank → ℕ := ![3]
theorem edge1018_span : frame243.space ≤ frame252.space :=
  frame243.inclusion frame252 witness1018 (by decide)
def edge1018 : CertifiedEdge catalog where
  old := 243
  next := 252
  rank := 1
  good := by
    constructor
    · exact edge1018_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1019 : Fin frame243.rank → ℕ := ![3]
theorem edge1019_span : frame243.space ≤ frame255.space :=
  frame243.inclusion frame255 witness1019 (by decide)
def edge1019 : CertifiedEdge catalog where
  old := 243
  next := 255
  rank := 1
  good := by
    constructor
    · exact edge1019_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1020 : Fin frame243.rank → ℕ := ![3]
theorem edge1020_span : frame243.space ≤ frame256.space :=
  frame243.inclusion frame256 witness1020 (by decide)
def edge1020 : CertifiedEdge catalog where
  old := 243
  next := 256
  rank := 1
  good := by
    constructor
    · exact edge1020_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1021 : Fin frame244.rank → ℕ := ![1]
theorem edge1021_span : frame244.space ≤ frame249.space :=
  frame244.inclusion frame249 witness1021 (by decide)
def edge1021 : CertifiedEdge catalog where
  old := 244
  next := 249
  rank := 1
  good := by
    constructor
    · exact edge1021_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1022 : Fin frame244.rank → ℕ := ![3]
theorem edge1022_span : frame244.space ≤ frame257.space :=
  frame244.inclusion frame257 witness1022 (by decide)
def edge1022 : CertifiedEdge catalog where
  old := 244
  next := 257
  rank := 1
  good := by
    constructor
    · exact edge1022_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1023 : Fin frame244.rank → ℕ := ![3]
theorem edge1023_span : frame244.space ≤ frame258.space :=
  frame244.inclusion frame258 witness1023 (by decide)
def edge1023 : CertifiedEdge catalog where
  old := 244
  next := 258
  rank := 1
  good := by
    constructor
    · exact edge1023_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
