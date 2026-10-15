module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2880 : Fin frame997.rank → ℕ := ![65,6,8,80,32,128]
theorem edge2880_span : frame997.space ≤ frame991.space :=
  frame997.inclusion frame991 witness2880 (by decide)
def edge2880 : CertifiedEdge catalog where
  old := 997
  next := 991
  rank := 2
  good := by
    constructor
    · exact edge2880_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2881 : Fin frame997.rank → ℕ := ![65,6,8,16,96,128]
theorem edge2881_span : frame997.space ≤ frame995.space :=
  frame997.inclusion frame995 witness2881 (by decide)
def edge2881 : CertifiedEdge catalog where
  old := 997
  next := 995
  rank := 2
  good := by
    constructor
    · exact edge2881_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2882 : Fin frame998.rank → ℕ := ![1,2,4,264,272,32,64,384]
theorem edge2882_span : frame998.space ≤ frame1.space :=
  frame998.inclusion frame1 witness2882 (by decide)
def edge2882 : CertifiedEdge catalog where
  old := 998
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2882_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2883 : Fin frame999.rank → ℕ := ![1,2,4,8,144,160,192,256]
theorem edge2883_span : frame999.space ≤ frame1.space :=
  frame999.inclusion frame1 witness2883 (by decide)
def edge2883 : CertifiedEdge catalog where
  old := 999
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2883_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2884 : Fin frame1000.rank → ℕ := ![1,2,260,8,16,288,64,384]
theorem edge2884_span : frame1000.space ≤ frame1.space :=
  frame1000.inclusion frame1 witness2884 (by decide)
def edge2884 : CertifiedEdge catalog where
  old := 1000
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2884_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2885 : Fin frame1001.rank → ℕ := ![1,2,132,136,16,32,192,256]
theorem edge2885_span : frame1001.space ≤ frame1.space :=
  frame1001.inclusion frame1 witness2885 (by decide)
def edge2885 : CertifiedEdge catalog where
  old := 1001
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2885_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2886 : Fin frame1002.rank → ℕ := ![1,2,260,8,272,32,320,128]
theorem edge2886_span : frame1002.space ≤ frame1.space :=
  frame1002.inclusion frame1 witness2886 (by decide)
def edge2886 : CertifiedEdge catalog where
  old := 1002
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2886_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2887 : Fin frame1003.rank → ℕ := ![1,2,36,40,48,64,128,256]
theorem edge2887_span : frame1003.space ≤ frame1.space :=
  frame1003.inclusion frame1 witness2887 (by decide)
def edge2887 : CertifiedEdge catalog where
  old := 1003
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2887_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
