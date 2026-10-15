module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness768 : Fin frame157.rank → ℕ := ![3]
theorem edge768_span : frame157.space ≤ frame171.space :=
  frame157.inclusion frame171 witness768 (by decide)
def edge768 : CertifiedEdge catalog where
  old := 157
  next := 171
  rank := 1
  good := by
    constructor
    · exact edge768_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness769 : Fin frame158.rank → ℕ := ![2]
theorem edge769_span : frame158.space ≤ frame166.space :=
  frame158.inclusion frame166 witness769 (by decide)
def edge769 : CertifiedEdge catalog where
  old := 158
  next := 166
  rank := 1
  good := by
    constructor
    · exact edge769_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness770 : Fin frame158.rank → ℕ := ![2]
theorem edge770_span : frame158.space ≤ frame168.space :=
  frame158.inclusion frame168 witness770 (by decide)
def edge770 : CertifiedEdge catalog where
  old := 158
  next := 168
  rank := 1
  good := by
    constructor
    · exact edge770_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness771 : Fin frame158.rank → ℕ := ![1]
theorem edge771_span : frame158.space ≤ frame172.space :=
  frame158.inclusion frame172 witness771 (by decide)
def edge771 : CertifiedEdge catalog where
  old := 158
  next := 172
  rank := 1
  good := by
    constructor
    · exact edge771_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness772 : Fin frame159.rank → ℕ := ![1]
theorem edge772_span : frame159.space ≤ frame163.space :=
  frame159.inclusion frame163 witness772 (by decide)
def edge772 : CertifiedEdge catalog where
  old := 159
  next := 163
  rank := 1
  good := by
    constructor
    · exact edge772_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness773 : Fin frame159.rank → ℕ := ![1]
theorem edge773_span : frame159.space ≤ frame170.space :=
  frame159.inclusion frame170 witness773 (by decide)
def edge773 : CertifiedEdge catalog where
  old := 159
  next := 170
  rank := 1
  good := by
    constructor
    · exact edge773_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness774 : Fin frame159.rank → ℕ := ![3]
theorem edge774_span : frame159.space ≤ frame173.space :=
  frame159.inclusion frame173 witness774 (by decide)
def edge774 : CertifiedEdge catalog where
  old := 159
  next := 173
  rank := 1
  good := by
    constructor
    · exact edge774_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness775 : Fin frame160.rank → ℕ := ![1]
theorem edge775_span : frame160.space ≤ frame164.space :=
  frame160.inclusion frame164 witness775 (by decide)
def edge775 : CertifiedEdge catalog where
  old := 160
  next := 164
  rank := 1
  good := by
    constructor
    · exact edge775_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness776 : Fin frame160.rank → ℕ := ![1]
theorem edge776_span : frame160.space ≤ frame171.space :=
  frame160.inclusion frame171 witness776 (by decide)
def edge776 : CertifiedEdge catalog where
  old := 160
  next := 171
  rank := 1
  good := by
    constructor
    · exact edge776_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness777 : Fin frame160.rank → ℕ := ![1]
theorem edge777_span : frame160.space ≤ frame173.space :=
  frame160.inclusion frame173 witness777 (by decide)
def edge777 : CertifiedEdge catalog where
  old := 160
  next := 173
  rank := 1
  good := by
    constructor
    · exact edge777_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness778 : Fin frame161.rank → ℕ := ![2]
theorem edge778_span : frame161.space ≤ frame167.space :=
  frame161.inclusion frame167 witness778 (by decide)
def edge778 : CertifiedEdge catalog where
  old := 161
  next := 167
  rank := 1
  good := by
    constructor
    · exact edge778_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness779 : Fin frame161.rank → ℕ := ![2]
theorem edge779_span : frame161.space ≤ frame169.space :=
  frame161.inclusion frame169 witness779 (by decide)
def edge779 : CertifiedEdge catalog where
  old := 161
  next := 169
  rank := 1
  good := by
    constructor
    · exact edge779_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness780 : Fin frame161.rank → ℕ := ![3]
theorem edge780_span : frame161.space ≤ frame172.space :=
  frame161.inclusion frame172 witness780 (by decide)
def edge780 : CertifiedEdge catalog where
  old := 161
  next := 172
  rank := 1
  good := by
    constructor
    · exact edge780_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness781 : Fin frame162.rank → ℕ := ![3,4]
theorem edge781_span : frame162.space ≤ frame547.space :=
  frame162.inclusion frame547 witness781 (by decide)
def edge781 : CertifiedEdge catalog where
  old := 162
  next := 547
  rank := 1
  good := by
    constructor
    · exact edge781_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness782 : Fin frame162.rank → ℕ := ![3,4]
theorem edge782_span : frame162.space ≤ frame549.space :=
  frame162.inclusion frame549 witness782 (by decide)
def edge782 : CertifiedEdge catalog where
  old := 162
  next := 549
  rank := 1
  good := by
    constructor
    · exact edge782_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness783 : Fin frame162.rank → ℕ := ![7,8]
theorem edge783_span : frame162.space ≤ frame601.space :=
  frame162.inclusion frame601 witness783 (by decide)
def edge783 : CertifiedEdge catalog where
  old := 162
  next := 601
  rank := 2
  good := by
    constructor
    · exact edge783_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness784 : Fin frame162.rank → ℕ := ![79,48]
theorem edge784_span : frame162.space ≤ frame750.space :=
  frame162.inclusion frame750 witness784 (by decide)
def edge784 : CertifiedEdge catalog where
  old := 162
  next := 750
  rank := 5
  good := by
    constructor
    · exact edge784_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness785 : Fin frame163.rank → ℕ := ![1,6]
theorem edge785_span : frame163.space ≤ frame175.space :=
  frame163.inclusion frame175 witness785 (by decide)
def edge785 : CertifiedEdge catalog where
  old := 163
  next := 175
  rank := 1
  good := by
    constructor
    · exact edge785_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness786 : Fin frame163.rank → ℕ := ![1,6]
theorem edge786_span : frame163.space ≤ frame181.space :=
  frame163.inclusion frame181 witness786 (by decide)
def edge786 : CertifiedEdge catalog where
  old := 163
  next := 181
  rank := 1
  good := by
    constructor
    · exact edge786_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness787 : Fin frame164.rank → ℕ := ![1,6]
theorem edge787_span : frame164.space ≤ frame177.space :=
  frame164.inclusion frame177 witness787 (by decide)
def edge787 : CertifiedEdge catalog where
  old := 164
  next := 177
  rank := 1
  good := by
    constructor
    · exact edge787_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness788 : Fin frame164.rank → ℕ := ![1,6]
theorem edge788_span : frame164.space ≤ frame179.space :=
  frame164.inclusion frame179 witness788 (by decide)
def edge788 : CertifiedEdge catalog where
  old := 164
  next := 179
  rank := 1
  good := by
    constructor
    · exact edge788_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness789 : Fin frame165.rank → ℕ := ![2,4]
theorem edge789_span : frame165.space ≤ frame547.space :=
  frame165.inclusion frame547 witness789 (by decide)
def edge789 : CertifiedEdge catalog where
  old := 165
  next := 547
  rank := 1
  good := by
    constructor
    · exact edge789_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness790 : Fin frame165.rank → ℕ := ![2,4]
theorem edge790_span : frame165.space ≤ frame548.space :=
  frame165.inclusion frame548 witness790 (by decide)
def edge790 : CertifiedEdge catalog where
  old := 165
  next := 548
  rank := 1
  good := by
    constructor
    · exact edge790_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness791 : Fin frame165.rank → ℕ := ![20,56]
theorem edge791_span : frame165.space ≤ frame603.space :=
  frame165.inclusion frame603 witness791 (by decide)
def edge791 : CertifiedEdge catalog where
  old := 165
  next := 603
  rank := 4
  good := by
    constructor
    · exact edge791_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness792 : Fin frame165.rank → ℕ := ![36,112]
theorem edge792_span : frame165.space ≤ frame752.space :=
  frame165.inclusion frame752 witness792 (by decide)
def edge792 : CertifiedEdge catalog where
  old := 165
  next := 752
  rank := 5
  good := by
    constructor
    · exact edge792_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness793 : Fin frame166.rank → ℕ := ![2,4]
theorem edge793_span : frame166.space ≤ frame175.space :=
  frame166.inclusion frame175 witness793 (by decide)
def edge793 : CertifiedEdge catalog where
  old := 166
  next := 175
  rank := 1
  good := by
    constructor
    · exact edge793_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness794 : Fin frame166.rank → ℕ := ![2,4]
theorem edge794_span : frame166.space ≤ frame180.space :=
  frame166.inclusion frame180 witness794 (by decide)
def edge794 : CertifiedEdge catalog where
  old := 166
  next := 180
  rank := 1
  good := by
    constructor
    · exact edge794_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness795 : Fin frame167.rank → ℕ := ![2,4]
theorem edge795_span : frame167.space ≤ frame176.space :=
  frame167.inclusion frame176 witness795 (by decide)
def edge795 : CertifiedEdge catalog where
  old := 167
  next := 176
  rank := 1
  good := by
    constructor
    · exact edge795_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness796 : Fin frame167.rank → ℕ := ![2,4]
theorem edge796_span : frame167.space ≤ frame179.space :=
  frame167.inclusion frame179 witness796 (by decide)
def edge796 : CertifiedEdge catalog where
  old := 167
  next := 179
  rank := 1
  good := by
    constructor
    · exact edge796_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness797 : Fin frame168.rank → ℕ := ![2,4]
theorem edge797_span : frame168.space ≤ frame177.space :=
  frame168.inclusion frame177 witness797 (by decide)
def edge797 : CertifiedEdge catalog where
  old := 168
  next := 177
  rank := 1
  good := by
    constructor
    · exact edge797_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness798 : Fin frame168.rank → ℕ := ![2,4]
theorem edge798_span : frame168.space ≤ frame178.space :=
  frame168.inclusion frame178 witness798 (by decide)
def edge798 : CertifiedEdge catalog where
  old := 168
  next := 178
  rank := 1
  good := by
    constructor
    · exact edge798_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness799 : Fin frame169.rank → ℕ := ![2,4]
theorem edge799_span : frame169.space ≤ frame174.space :=
  frame169.inclusion frame174 witness799 (by decide)
def edge799 : CertifiedEdge catalog where
  old := 169
  next := 174
  rank := 1
  good := by
    constructor
    · exact edge799_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
