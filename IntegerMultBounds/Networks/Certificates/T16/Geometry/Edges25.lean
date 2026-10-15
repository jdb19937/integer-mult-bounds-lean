module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness800 : Fin frame169.rank → ℕ := ![2,4]
theorem edge800_span : frame169.space ≤ frame181.space :=
  frame169.inclusion frame181 witness800 (by decide)
def edge800 : CertifiedEdge catalog where
  old := 169
  next := 181
  rank := 1
  good := by
    constructor
    · exact edge800_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness801 : Fin frame170.rank → ℕ := ![1,6]
theorem edge801_span : frame170.space ≤ frame176.space :=
  frame170.inclusion frame176 witness801 (by decide)
def edge801 : CertifiedEdge catalog where
  old := 170
  next := 176
  rank := 1
  good := by
    constructor
    · exact edge801_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness802 : Fin frame170.rank → ℕ := ![1,6]
theorem edge802_span : frame170.space ≤ frame178.space :=
  frame170.inclusion frame178 witness802 (by decide)
def edge802 : CertifiedEdge catalog where
  old := 170
  next := 178
  rank := 1
  good := by
    constructor
    · exact edge802_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness803 : Fin frame171.rank → ℕ := ![1,6]
theorem edge803_span : frame171.space ≤ frame174.space :=
  frame171.inclusion frame174 witness803 (by decide)
def edge803 : CertifiedEdge catalog where
  old := 171
  next := 174
  rank := 1
  good := by
    constructor
    · exact edge803_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness804 : Fin frame171.rank → ℕ := ![1,6]
theorem edge804_span : frame171.space ≤ frame180.space :=
  frame171.inclusion frame180 witness804 (by decide)
def edge804 : CertifiedEdge catalog where
  old := 171
  next := 180
  rank := 1
  good := by
    constructor
    · exact edge804_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness805 : Fin frame172.rank → ℕ := ![2,4]
theorem edge805_span : frame172.space ≤ frame546.space :=
  frame172.inclusion frame546 witness805 (by decide)
def edge805 : CertifiedEdge catalog where
  old := 172
  next := 546
  rank := 1
  good := by
    constructor
    · exact edge805_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness806 : Fin frame172.rank → ℕ := ![2,4]
theorem edge806_span : frame172.space ≤ frame549.space :=
  frame172.inclusion frame549 witness806 (by decide)
def edge806 : CertifiedEdge catalog where
  old := 172
  next := 549
  rank := 1
  good := by
    constructor
    · exact edge806_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness807 : Fin frame172.rank → ℕ := ![4,8]
theorem edge807_span : frame172.space ≤ frame600.space :=
  frame172.inclusion frame600 witness807 (by decide)
def edge807 : CertifiedEdge catalog where
  old := 172
  next := 600
  rank := 2
  good := by
    constructor
    · exact edge807_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness808 : Fin frame172.rank → ℕ := ![10,12]
theorem edge808_span : frame172.space ≤ frame604.space :=
  frame172.inclusion frame604 witness808 (by decide)
def edge808 : CertifiedEdge catalog where
  old := 172
  next := 604
  rank := 2
  good := by
    constructor
    · exact edge808_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness809 : Fin frame173.rank → ℕ := ![1,4]
theorem edge809_span : frame173.space ≤ frame546.space :=
  frame173.inclusion frame546 witness809 (by decide)
def edge809 : CertifiedEdge catalog where
  old := 173
  next := 546
  rank := 1
  good := by
    constructor
    · exact edge809_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness810 : Fin frame173.rank → ℕ := ![1,4]
theorem edge810_span : frame173.space ≤ frame548.space :=
  frame173.inclusion frame548 witness810 (by decide)
def edge810 : CertifiedEdge catalog where
  old := 173
  next := 548
  rank := 1
  good := by
    constructor
    · exact edge810_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness811 : Fin frame173.rank → ℕ := ![1,8]
theorem edge811_span : frame173.space ≤ frame602.space :=
  frame173.inclusion frame602 witness811 (by decide)
def edge811 : CertifiedEdge catalog where
  old := 173
  next := 602
  rank := 2
  good := by
    constructor
    · exact edge811_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness812 : Fin frame173.rank → ℕ := ![67,48]
theorem edge812_span : frame173.space ≤ frame750.space :=
  frame173.inclusion frame750 witness812 (by decide)
def edge812 : CertifiedEdge catalog where
  old := 173
  next := 750
  rank := 5
  good := by
    constructor
    · exact edge812_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness813 : Fin frame174.rank → ℕ := ![1,2,12]
theorem edge813_span : frame174.space ≤ frame182.space :=
  frame174.inclusion frame182 witness813 (by decide)
def edge813 : CertifiedEdge catalog where
  old := 174
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge813_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness814 : Fin frame174.rank → ℕ := ![1,34,44]
theorem edge814_span : frame174.space ≤ frame638.space :=
  frame174.inclusion frame638 witness814 (by decide)
def edge814 : CertifiedEdge catalog where
  old := 174
  next := 638
  rank := 3
  good := by
    constructor
    · exact edge814_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness815 : Fin frame174.rank → ℕ := ![35,4,24]
theorem edge815_span : frame174.space ≤ frame654.space :=
  frame174.inclusion frame654 witness815 (by decide)
def edge815 : CertifiedEdge catalog where
  old := 174
  next := 654
  rank := 3
  good := by
    constructor
    · exact edge815_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness816 : Fin frame175.rank → ℕ := ![9,10,4]
theorem edge816_span : frame175.space ≤ frame182.space :=
  frame175.inclusion frame182 witness816 (by decide)
def edge816 : CertifiedEdge catalog where
  old := 175
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge816_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness817 : Fin frame175.rank → ℕ := ![57,10,12]
theorem edge817_span : frame175.space ≤ frame639.space :=
  frame175.inclusion frame639 witness817 (by decide)
def edge817 : CertifiedEdge catalog where
  old := 175
  next := 639
  rank := 3
  good := by
    constructor
    · exact edge817_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness818 : Fin frame175.rank → ℕ := ![51,52,40]
theorem edge818_span : frame175.space ≤ frame655.space :=
  frame175.inclusion frame655 witness818 (by decide)
def edge818 : CertifiedEdge catalog where
  old := 175
  next := 655
  rank := 3
  good := by
    constructor
    · exact edge818_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness819 : Fin frame176.rank → ℕ := ![9,10,12]
theorem edge819_span : frame176.space ≤ frame182.space :=
  frame176.inclusion frame182 witness819 (by decide)
def edge819 : CertifiedEdge catalog where
  old := 176
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge819_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness820 : Fin frame176.rank → ℕ := ![51,52,24]
theorem edge820_span : frame176.space ≤ frame648.space :=
  frame176.inclusion frame648 witness820 (by decide)
def edge820 : CertifiedEdge catalog where
  old := 176
  next := 648
  rank := 3
  good := by
    constructor
    · exact edge820_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness821 : Fin frame176.rank → ℕ := ![57,10,12]
theorem edge821_span : frame176.space ≤ frame664.space :=
  frame176.inclusion frame664 witness821 (by decide)
def edge821 : CertifiedEdge catalog where
  old := 176
  next := 664
  rank := 3
  good := by
    constructor
    · exact edge821_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness822 : Fin frame177.rank → ℕ := ![1,2,4]
theorem edge822_span : frame177.space ≤ frame182.space :=
  frame177.inclusion frame182 witness822 (by decide)
def edge822 : CertifiedEdge catalog where
  old := 177
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge822_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness823 : Fin frame177.rank → ℕ := ![35,4,24]
theorem edge823_span : frame177.space ≤ frame649.space :=
  frame177.inclusion frame649 witness823 (by decide)
def edge823 : CertifiedEdge catalog where
  old := 177
  next := 649
  rank := 3
  good := by
    constructor
    · exact edge823_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness824 : Fin frame177.rank → ℕ := ![1,18,52]
theorem edge824_span : frame177.space ≤ frame665.space :=
  frame177.inclusion frame665 witness824 (by decide)
def edge824 : CertifiedEdge catalog where
  old := 177
  next := 665
  rank := 3
  good := by
    constructor
    · exact edge824_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness825 : Fin frame178.rank → ℕ := ![9,2,4]
theorem edge825_span : frame178.space ≤ frame182.space :=
  frame178.inclusion frame182 witness825 (by decide)
def edge825 : CertifiedEdge catalog where
  old := 178
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge825_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness826 : Fin frame178.rank → ℕ := ![51,4,40]
theorem edge826_span : frame178.space ≤ frame706.space :=
  frame178.inclusion frame706 witness826 (by decide)
def edge826 : CertifiedEdge catalog where
  old := 178
  next := 706
  rank := 3
  good := by
    constructor
    · exact edge826_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness827 : Fin frame178.rank → ℕ := ![57,18,20]
theorem edge827_span : frame178.space ≤ frame722.space :=
  frame178.inclusion frame722 witness827 (by decide)
def edge827 : CertifiedEdge catalog where
  old := 178
  next := 722
  rank := 3
  good := by
    constructor
    · exact edge827_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness828 : Fin frame179.rank → ℕ := ![1,10,12]
theorem edge828_span : frame179.space ≤ frame182.space :=
  frame179.inclusion frame182 witness828 (by decide)
def edge828 : CertifiedEdge catalog where
  old := 179
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge828_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness829 : Fin frame179.rank → ℕ := ![35,20,8]
theorem edge829_span : frame179.space ≤ frame707.space :=
  frame179.inclusion frame707 witness829 (by decide)
def edge829 : CertifiedEdge catalog where
  old := 179
  next := 707
  rank := 3
  good := by
    constructor
    · exact edge829_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness830 : Fin frame179.rank → ℕ := ![1,42,12]
theorem edge830_span : frame179.space ≤ frame723.space :=
  frame179.inclusion frame723 witness830 (by decide)
def edge830 : CertifiedEdge catalog where
  old := 179
  next := 723
  rank := 3
  good := by
    constructor
    · exact edge830_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness831 : Fin frame180.rank → ℕ := ![1,10,4]
theorem edge831_span : frame180.space ≤ frame182.space :=
  frame180.inclusion frame182 witness831 (by decide)
def edge831 : CertifiedEdge catalog where
  old := 180
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge831_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
