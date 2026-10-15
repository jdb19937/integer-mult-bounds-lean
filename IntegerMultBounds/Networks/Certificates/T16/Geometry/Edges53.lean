module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1696 : Fin frame453.rank → ℕ := ![1,10,12]
theorem edge1696_span : frame453.space ≤ frame457.space :=
  frame453.inclusion frame457 witness1696 (by decide)
def edge1696 : CertifiedEdge catalog where
  old := 453
  next := 457
  rank := 1
  good := by
    constructor
    · exact edge1696_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1697 : Fin frame453.rank → ℕ := ![87,72,32]
theorem edge1697_span : frame453.space ≤ frame465.space :=
  frame453.inclusion frame465 witness1697 (by decide)
def edge1697 : CertifiedEdge catalog where
  old := 453
  next := 465
  rank := 4
  good := by
    constructor
    · exact edge1697_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1698 : Fin frame454.rank → ℕ := ![2,4,8]
theorem edge1698_span : frame454.space ≤ frame456.space :=
  frame454.inclusion frame456 witness1698 (by decide)
def edge1698 : CertifiedEdge catalog where
  old := 454
  next := 456
  rank := 2
  good := by
    constructor
    · exact edge1698_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1699 : Fin frame454.rank → ℕ := ![34,36,104]
theorem edge1699_span : frame454.space ≤ frame462.space :=
  frame454.inclusion frame462 witness1699 (by decide)
def edge1699 : CertifiedEdge catalog where
  old := 454
  next := 462
  rank := 4
  good := by
    constructor
    · exact edge1699_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1700 : Fin frame455.rank → ℕ := ![1,22,8]
theorem edge1700_span : frame455.space ≤ frame458.space :=
  frame455.inclusion frame458 witness1700 (by decide)
def edge1700 : CertifiedEdge catalog where
  old := 455
  next := 458
  rank := 2
  good := by
    constructor
    · exact edge1700_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1701 : Fin frame455.rank → ℕ := ![33,118,40]
theorem edge1701_span : frame455.space ≤ frame463.space :=
  frame455.inclusion frame463 witness1701 (by decide)
def edge1701 : CertifiedEdge catalog where
  old := 455
  next := 463
  rank := 4
  good := by
    constructor
    · exact edge1701_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1702 : Fin frame456.rank → ℕ := ![1,34,36,40,48]
theorem edge1702_span : frame456.space ≤ frame461.space :=
  frame456.inclusion frame461 witness1702 (by decide)
def edge1702 : CertifiedEdge catalog where
  old := 456
  next := 461
  rank := 1
  good := by
    constructor
    · exact edge1702_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1703 : Fin frame456.rank → ℕ := ![65,34,36,40,48]
theorem edge1703_span : frame456.space ≤ frame464.space :=
  frame456.inclusion frame464 witness1703 (by decide)
def edge1703 : CertifiedEdge catalog where
  old := 456
  next := 464
  rank := 2
  good := by
    constructor
    · exact edge1703_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1704 : Fin frame457.rank → ℕ := ![11,4,16,32]
theorem edge1704_span : frame457.space ≤ frame460.space :=
  frame457.inclusion frame460 witness1704 (by decide)
def edge1704 : CertifiedEdge catalog where
  old := 457
  next := 460
  rank := 2
  good := by
    constructor
    · exact edge1704_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1705 : Fin frame457.rank → ℕ := ![23,8,32,64]
theorem edge1705_span : frame457.space ≤ frame466.space :=
  frame457.inclusion frame466 witness1705 (by decide)
def edge1705 : CertifiedEdge catalog where
  old := 457
  next := 466
  rank := 3
  good := by
    constructor
    · exact edge1705_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1706 : Fin frame458.rank → ℕ := ![33,34,100,104,48]
theorem edge1706_span : frame458.space ≤ frame447.space :=
  frame458.inclusion frame447 witness1706 (by decide)
def edge1706 : CertifiedEdge catalog where
  old := 458
  next := 447
  rank := 2
  good := by
    constructor
    · exact edge1706_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1707 : Fin frame458.rank → ℕ := ![33,34,36,40,48]
theorem edge1707_span : frame458.space ≤ frame459.space :=
  frame458.inclusion frame459 witness1707 (by decide)
def edge1707 : CertifiedEdge catalog where
  old := 458
  next := 459
  rank := 1
  good := by
    constructor
    · exact edge1707_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1708 : Fin frame459.rank → ℕ := ![1,2,68,72,16,32]
theorem edge1708_span : frame459.space ≤ frame462.space :=
  frame459.inclusion frame462 witness1708 (by decide)
def edge1708 : CertifiedEdge catalog where
  old := 459
  next := 462
  rank := 1
  good := by
    constructor
    · exact edge1708_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1709 : Fin frame459.rank → ℕ := ![65,66,4,72,80,96]
theorem edge1709_span : frame459.space ≤ frame466.space :=
  frame459.inclusion frame466 witness1709 (by decide)
def edge1709 : CertifiedEdge catalog where
  old := 459
  next := 466
  rank := 1
  good := by
    constructor
    · exact edge1709_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1710 : Fin frame460.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1710_span : frame460.space ≤ frame463.space :=
  frame460.inclusion frame463 witness1710 (by decide)
def edge1710 : CertifiedEdge catalog where
  old := 460
  next := 463
  rank := 1
  good := by
    constructor
    · exact edge1710_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1711 : Fin frame460.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1711_span : frame460.space ≤ frame464.space :=
  frame460.inclusion frame464 witness1711 (by decide)
def edge1711 : CertifiedEdge catalog where
  old := 460
  next := 464
  rank := 1
  good := by
    constructor
    · exact edge1711_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1712 : Fin frame461.rank → ℕ := ![65,66,68,8,80,96]
theorem edge1712_span : frame461.space ≤ frame447.space :=
  frame461.inclusion frame447 witness1712 (by decide)
def edge1712 : CertifiedEdge catalog where
  old := 461
  next := 447
  rank := 1
  good := by
    constructor
    · exact edge1712_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1713 : Fin frame461.rank → ℕ := ![65,66,68,8,80,96]
theorem edge1713_span : frame461.space ≤ frame465.space :=
  frame461.inclusion frame465 witness1713 (by decide)
def edge1713 : CertifiedEdge catalog where
  old := 461
  next := 465
  rank := 1
  good := by
    constructor
    · exact edge1713_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1714 : Fin frame462.rank → ℕ := ![129,130,132,264,144,416,448]
theorem edge1714_span : frame462.space ≤ frame1.space :=
  frame462.inclusion frame1 witness1714 (by decide)
def edge1714 : CertifiedEdge catalog where
  old := 462
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1714_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1715 : Fin frame462.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1715_span : frame462.space ≤ frame784.space :=
  frame462.inclusion frame784 witness1715 (by decide)
def edge1715 : CertifiedEdge catalog where
  old := 462
  next := 784
  rank := 1
  good := by
    constructor
    · exact edge1715_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1716 : Fin frame462.rank → ℕ := ![129,130,132,8,144,160,192]
theorem edge1716_span : frame462.space ≤ frame787.space :=
  frame462.inclusion frame787 witness1716 (by decide)
def edge1716 : CertifiedEdge catalog where
  old := 462
  next := 787
  rank := 1
  good := by
    constructor
    · exact edge1716_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1717 : Fin frame463.rank → ℕ := ![1,322,4,72,16,288,128]
theorem edge1717_span : frame463.space ≤ frame1.space :=
  frame463.inclusion frame1 witness1717 (by decide)
def edge1717 : CertifiedEdge catalog where
  old := 463
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1717_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1718 : Fin frame463.rank → ℕ := ![1,130,4,8,16,160,64]
theorem edge1718_span : frame463.space ≤ frame959.space :=
  frame463.inclusion frame959 witness1718 (by decide)
def edge1718 : CertifiedEdge catalog where
  old := 463
  next := 959
  rank := 1
  good := by
    constructor
    · exact edge1718_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1719 : Fin frame463.rank → ℕ := ![1,66,4,72,16,32,128]
theorem edge1719_span : frame463.space ≤ frame962.space :=
  frame463.inclusion frame962 witness1719 (by decide)
def edge1719 : CertifiedEdge catalog where
  old := 463
  next := 962
  rank := 1
  good := by
    constructor
    · exact edge1719_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1720 : Fin frame464.rank → ℕ := ![321,2,4,72,16,288,128]
theorem edge1720_span : frame464.space ≤ frame1.space :=
  frame464.inclusion frame1 witness1720 (by decide)
def edge1720 : CertifiedEdge catalog where
  old := 464
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1720_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1721 : Fin frame464.rank → ℕ := ![129,2,4,8,16,160,64]
theorem edge1721_span : frame464.space ≤ frame951.space :=
  frame464.inclusion frame951 witness1721 (by decide)
def edge1721 : CertifiedEdge catalog where
  old := 464
  next := 951
  rank := 1
  good := by
    constructor
    · exact edge1721_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1722 : Fin frame464.rank → ℕ := ![65,2,4,72,16,32,128]
theorem edge1722_span : frame464.space ≤ frame954.space :=
  frame464.inclusion frame954 witness1722 (by decide)
def edge1722 : CertifiedEdge catalog where
  old := 464
  next := 954
  rank := 1
  good := by
    constructor
    · exact edge1722_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1723 : Fin frame465.rank → ℕ := ![129,130,132,392,144,416,320]
theorem edge1723_span : frame465.space ≤ frame1.space :=
  frame465.inclusion frame1 witness1723 (by decide)
def edge1723 : CertifiedEdge catalog where
  old := 465
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1723_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1724 : Fin frame465.rank → ℕ := ![129,130,132,136,144,160,64]
theorem edge1724_span : frame465.space ≤ frame975.space :=
  frame465.inclusion frame975 witness1724 (by decide)
def edge1724 : CertifiedEdge catalog where
  old := 465
  next := 975
  rank := 1
  good := by
    constructor
    · exact edge1724_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1725 : Fin frame465.rank → ℕ := ![1,2,4,136,16,160,192]
theorem edge1725_span : frame465.space ≤ frame978.space :=
  frame465.inclusion frame978 witness1725 (by decide)
def edge1725 : CertifiedEdge catalog where
  old := 465
  next := 978
  rank := 1
  good := by
    constructor
    · exact edge1725_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1726 : Fin frame466.rank → ℕ := ![1,2,324,72,16,288,128]
theorem edge1726_span : frame466.space ≤ frame1.space :=
  frame466.inclusion frame1 witness1726 (by decide)
def edge1726 : CertifiedEdge catalog where
  old := 466
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge1726_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1727 : Fin frame466.rank → ℕ := ![1,2,132,8,16,160,64]
theorem edge1727_span : frame466.space ≤ frame967.space :=
  frame466.inclusion frame967 witness1727 (by decide)
def edge1727 : CertifiedEdge catalog where
  old := 466
  next := 967
  rank := 1
  good := by
    constructor
    · exact edge1727_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
