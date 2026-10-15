module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1984 : Fin frame574.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1984_span : frame574.space ≤ frame770.space :=
  frame574.inclusion frame770 witness1984 (by decide)
def edge1984 : CertifiedEdge catalog where
  old := 574
  next := 770
  rank := 1
  good := by
    constructor
    · exact edge1984_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1985 : Fin frame574.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1985_span : frame574.space ≤ frame771.space :=
  frame574.inclusion frame771 witness1985 (by decide)
def edge1985 : CertifiedEdge catalog where
  old := 574
  next := 771
  rank := 1
  good := by
    constructor
    · exact edge1985_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1986 : Fin frame575.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1986_span : frame575.space ≤ frame772.space :=
  frame575.inclusion frame772 witness1986 (by decide)
def edge1986 : CertifiedEdge catalog where
  old := 575
  next := 772
  rank := 1
  good := by
    constructor
    · exact edge1986_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1987 : Fin frame575.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1987_span : frame575.space ≤ frame773.space :=
  frame575.inclusion frame773 witness1987 (by decide)
def edge1987 : CertifiedEdge catalog where
  old := 575
  next := 773
  rank := 1
  good := by
    constructor
    · exact edge1987_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1988 : Fin frame576.rank → ℕ := ![5,6,8]
theorem edge1988_span : frame576.space ≤ frame327.space :=
  frame576.inclusion frame327 witness1988 (by decide)
def edge1988 : CertifiedEdge catalog where
  old := 576
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1988_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1989 : Fin frame576.rank → ℕ := ![5,6,24]
theorem edge1989_span : frame576.space ≤ frame580.space :=
  frame576.inclusion frame580 witness1989 (by decide)
def edge1989 : CertifiedEdge catalog where
  old := 576
  next := 580
  rank := 3
  good := by
    constructor
    · exact edge1989_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1990 : Fin frame576.rank → ℕ := ![1,2,12]
theorem edge1990_span : frame576.space ≤ frame622.space :=
  frame576.inclusion frame622 witness1990 (by decide)
def edge1990 : CertifiedEdge catalog where
  old := 576
  next := 622
  rank := 1
  good := by
    constructor
    · exact edge1990_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1991 : Fin frame577.rank → ℕ := ![1,2,8]
theorem edge1991_span : frame577.space ≤ frame327.space :=
  frame577.inclusion frame327 witness1991 (by decide)
def edge1991 : CertifiedEdge catalog where
  old := 577
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1991_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1992 : Fin frame577.rank → ℕ := ![1,2,8]
theorem edge1992_span : frame577.space ≤ frame581.space :=
  frame577.inclusion frame581 witness1992 (by decide)
def edge1992 : CertifiedEdge catalog where
  old := 577
  next := 581
  rank := 3
  good := by
    constructor
    · exact edge1992_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1993 : Fin frame577.rank → ℕ := ![1,2,8]
theorem edge1993_span : frame577.space ≤ frame623.space :=
  frame577.inclusion frame623 witness1993 (by decide)
def edge1993 : CertifiedEdge catalog where
  old := 577
  next := 623
  rank := 1
  good := by
    constructor
    · exact edge1993_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1994 : Fin frame578.rank → ℕ := ![1,6,8]
theorem edge1994_span : frame578.space ≤ frame327.space :=
  frame578.inclusion frame327 witness1994 (by decide)
def edge1994 : CertifiedEdge catalog where
  old := 578
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1994_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1995 : Fin frame578.rank → ℕ := ![1,38,24]
theorem edge1995_span : frame578.space ≤ frame588.space :=
  frame578.inclusion frame588 witness1995 (by decide)
def edge1995 : CertifiedEdge catalog where
  old := 578
  next := 588
  rank := 3
  good := by
    constructor
    · exact edge1995_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1996 : Fin frame578.rank → ℕ := ![1,2,12]
theorem edge1996_span : frame578.space ≤ frame598.space :=
  frame578.inclusion frame598 witness1996 (by decide)
def edge1996 : CertifiedEdge catalog where
  old := 578
  next := 598
  rank := 1
  good := by
    constructor
    · exact edge1996_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1997 : Fin frame579.rank → ℕ := ![5,2,8]
theorem edge1997_span : frame579.space ≤ frame327.space :=
  frame579.inclusion frame327 witness1997 (by decide)
def edge1997 : CertifiedEdge catalog where
  old := 579
  next := 327
  rank := 1
  good := by
    constructor
    · exact edge1997_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1998 : Fin frame579.rank → ℕ := ![37,2,24]
theorem edge1998_span : frame579.space ≤ frame590.space :=
  frame579.inclusion frame590 witness1998 (by decide)
def edge1998 : CertifiedEdge catalog where
  old := 579
  next := 590
  rank := 3
  good := by
    constructor
    · exact edge1998_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1999 : Fin frame579.rank → ℕ := ![1,2,12]
theorem edge1999_span : frame579.space ≤ frame599.space :=
  frame579.inclusion frame599 witness1999 (by decide)
def edge1999 : CertifiedEdge catalog where
  old := 579
  next := 599
  rank := 1
  good := by
    constructor
    · exact edge1999_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2000 : Fin frame580.rank → ℕ := ![33,34,4,8,16,64]
theorem edge2000_span : frame580.space ≤ frame766.space :=
  frame580.inclusion frame766 witness2000 (by decide)
def edge2000 : CertifiedEdge catalog where
  old := 580
  next := 766
  rank := 1
  good := by
    constructor
    · exact edge2000_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2001 : Fin frame580.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2001_span : frame580.space ≤ frame767.space :=
  frame580.inclusion frame767 witness2001 (by decide)
def edge2001 : CertifiedEdge catalog where
  old := 580
  next := 767
  rank := 1
  good := by
    constructor
    · exact edge2001_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2002 : Fin frame581.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2002_span : frame581.space ≤ frame768.space :=
  frame581.inclusion frame768 witness2002 (by decide)
def edge2002 : CertifiedEdge catalog where
  old := 581
  next := 768
  rank := 1
  good := by
    constructor
    · exact edge2002_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2003 : Fin frame581.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2003_span : frame581.space ≤ frame769.space :=
  frame581.inclusion frame769 witness2003 (by decide)
def edge2003 : CertifiedEdge catalog where
  old := 581
  next := 769
  rank := 1
  good := by
    constructor
    · exact edge2003_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2004 : Fin frame582.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2004_span : frame582.space ≤ frame743.space :=
  frame582.inclusion frame743 witness2004 (by decide)
def edge2004 : CertifiedEdge catalog where
  old := 582
  next := 743
  rank := 1
  good := by
    constructor
    · exact edge2004_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2005 : Fin frame582.rank → ℕ := ![1,2,68,72,16,32]
theorem edge2005_span : frame582.space ≤ frame745.space :=
  frame582.inclusion frame745 witness2005 (by decide)
def edge2005 : CertifiedEdge catalog where
  old := 582
  next := 745
  rank := 1
  good := by
    constructor
    · exact edge2005_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2006 : Fin frame583.rank → ℕ := ![1,2,20,24,32,64]
theorem edge2006_span : frame583.space ≤ frame767.space :=
  frame583.inclusion frame767 witness2006 (by decide)
def edge2006 : CertifiedEdge catalog where
  old := 583
  next := 767
  rank := 1
  good := by
    constructor
    · exact edge2006_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2007 : Fin frame583.rank → ℕ := ![17,18,4,8,32,64]
theorem edge2007_span : frame583.space ≤ frame769.space :=
  frame583.inclusion frame769 witness2007 (by decide)
def edge2007 : CertifiedEdge catalog where
  old := 583
  next := 769
  rank := 1
  good := by
    constructor
    · exact edge2007_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2008 : Fin frame584.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2008_span : frame584.space ≤ frame742.space :=
  frame584.inclusion frame742 witness2008 (by decide)
def edge2008 : CertifiedEdge catalog where
  old := 584
  next := 742
  rank := 1
  good := by
    constructor
    · exact edge2008_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2009 : Fin frame584.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2009_span : frame584.space ≤ frame744.space :=
  frame584.inclusion frame744 witness2009 (by decide)
def edge2009 : CertifiedEdge catalog where
  old := 584
  next := 744
  rank := 1
  good := by
    constructor
    · exact edge2009_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2010 : Fin frame585.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2010_span : frame585.space ≤ frame766.space :=
  frame585.inclusion frame766 witness2010 (by decide)
def edge2010 : CertifiedEdge catalog where
  old := 585
  next := 766
  rank := 1
  good := by
    constructor
    · exact edge2010_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2011 : Fin frame585.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2011_span : frame585.space ≤ frame768.space :=
  frame585.inclusion frame768 witness2011 (by decide)
def edge2011 : CertifiedEdge catalog where
  old := 585
  next := 768
  rank := 1
  good := by
    constructor
    · exact edge2011_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2012 : Fin frame586.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2012_span : frame586.space ≤ frame750.space :=
  frame586.inclusion frame750 witness2012 (by decide)
def edge2012 : CertifiedEdge catalog where
  old := 586
  next := 750
  rank := 1
  good := by
    constructor
    · exact edge2012_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2013 : Fin frame586.rank → ℕ := ![1,2,4,72,16,96]
theorem edge2013_span : frame586.space ≤ frame752.space :=
  frame586.inclusion frame752 witness2013 (by decide)
def edge2013 : CertifiedEdge catalog where
  old := 586
  next := 752
  rank := 1
  good := by
    constructor
    · exact edge2013_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2014 : Fin frame587.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2014_span : frame587.space ≤ frame758.space :=
  frame587.inclusion frame758 witness2014 (by decide)
def edge2014 : CertifiedEdge catalog where
  old := 587
  next := 758
  rank := 1
  good := by
    constructor
    · exact edge2014_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2015 : Fin frame587.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2015_span : frame587.space ≤ frame760.space :=
  frame587.inclusion frame760 witness2015 (by decide)
def edge2015 : CertifiedEdge catalog where
  old := 587
  next := 760
  rank := 1
  good := by
    constructor
    · exact edge2015_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
