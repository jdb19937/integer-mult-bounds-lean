module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness832 : Fin frame180.rank → ℕ := ![1,26,20]
theorem edge832_span : frame180.space ≤ frame716.space :=
  frame180.inclusion frame716 witness832 (by decide)
def edge832 : CertifiedEdge catalog where
  old := 180
  next := 716
  rank := 3
  good := by
    constructor
    · exact edge832_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness833 : Fin frame180.rank → ℕ := ![35,20,8]
theorem edge833_span : frame180.space ≤ frame732.space :=
  frame180.inclusion frame732 witness833 (by decide)
def edge833 : CertifiedEdge catalog where
  old := 180
  next := 732
  rank := 3
  good := by
    constructor
    · exact edge833_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness834 : Fin frame181.rank → ℕ := ![9,2,12]
theorem edge834_span : frame181.space ≤ frame182.space :=
  frame181.inclusion frame182 witness834 (by decide)
def edge834 : CertifiedEdge catalog where
  old := 181
  next := 182
  rank := 1
  good := by
    constructor
    · exact edge834_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness835 : Fin frame181.rank → ℕ := ![57,18,20]
theorem edge835_span : frame181.space ≤ frame717.space :=
  frame181.inclusion frame717 witness835 (by decide)
def edge835 : CertifiedEdge catalog where
  old := 181
  next := 717
  rank := 3
  good := by
    constructor
    · exact edge835_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness836 : Fin frame181.rank → ℕ := ![51,4,24]
theorem edge836_span : frame181.space ≤ frame733.space :=
  frame181.inclusion frame733 witness836 (by decide)
def edge836 : CertifiedEdge catalog where
  old := 181
  next := 733
  rank := 3
  good := by
    constructor
    · exact edge836_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness837 : Fin frame182.rank → ℕ := ![259,164,104,240]
theorem edge837_span : frame182.space ≤ frame1.space :=
  frame182.inclusion frame1 witness837 (by decide)
def edge837 : CertifiedEdge catalog where
  old := 182
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge837_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness838 : Fin frame182.rank → ℕ := ![131,36,104,112]
theorem edge838_span : frame182.space ≤ frame415.space :=
  frame182.inclusion frame415 witness838 (by decide)
def edge838 : CertifiedEdge catalog where
  old := 182
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge838_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness839 : Fin frame182.rank → ℕ := ![131,100,40,112]
theorem edge839_span : frame182.space ≤ frame418.space :=
  frame182.inclusion frame418 witness839 (by decide)
def edge839 : CertifiedEdge catalog where
  old := 182
  next := 418
  rank := 4
  good := by
    constructor
    · exact edge839_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness840 : Fin frame182.rank → ℕ := ![131,36,104,112]
theorem edge840_span : frame182.space ≤ frame419.space :=
  frame182.inclusion frame419 witness840 (by decide)
def edge840 : CertifiedEdge catalog where
  old := 182
  next := 419
  rank := 4
  good := by
    constructor
    · exact edge840_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness841 : Fin frame182.rank → ℕ := ![131,100,40,112]
theorem edge841_span : frame182.space ≤ frame422.space :=
  frame182.inclusion frame422 witness841 (by decide)
def edge841 : CertifiedEdge catalog where
  old := 182
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge841_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness842 : Fin frame183.rank → ℕ := ![3]
theorem edge842_span : frame183.space ≤ frame191.space :=
  frame183.inclusion frame191 witness842 (by decide)
def edge842 : CertifiedEdge catalog where
  old := 183
  next := 191
  rank := 1
  good := by
    constructor
    · exact edge842_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness843 : Fin frame183.rank → ℕ := ![1]
theorem edge843_span : frame183.space ≤ frame192.space :=
  frame183.inclusion frame192 witness843 (by decide)
def edge843 : CertifiedEdge catalog where
  old := 183
  next := 192
  rank := 1
  good := by
    constructor
    · exact edge843_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness844 : Fin frame183.rank → ℕ := ![1]
theorem edge844_span : frame183.space ≤ frame193.space :=
  frame183.inclusion frame193 witness844 (by decide)
def edge844 : CertifiedEdge catalog where
  old := 183
  next := 193
  rank := 1
  good := by
    constructor
    · exact edge844_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness845 : Fin frame184.rank → ℕ := ![1]
theorem edge845_span : frame184.space ≤ frame194.space :=
  frame184.inclusion frame194 witness845 (by decide)
def edge845 : CertifiedEdge catalog where
  old := 184
  next := 194
  rank := 1
  good := by
    constructor
    · exact edge845_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness846 : Fin frame184.rank → ℕ := ![1]
theorem edge846_span : frame184.space ≤ frame195.space :=
  frame184.inclusion frame195 witness846 (by decide)
def edge846 : CertifiedEdge catalog where
  old := 184
  next := 195
  rank := 1
  good := by
    constructor
    · exact edge846_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness847 : Fin frame184.rank → ℕ := ![1]
theorem edge847_span : frame184.space ≤ frame196.space :=
  frame184.inclusion frame196 witness847 (by decide)
def edge847 : CertifiedEdge catalog where
  old := 184
  next := 196
  rank := 1
  good := by
    constructor
    · exact edge847_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness848 : Fin frame185.rank → ℕ := ![3]
theorem edge848_span : frame185.space ≤ frame194.space :=
  frame185.inclusion frame194 witness848 (by decide)
def edge848 : CertifiedEdge catalog where
  old := 185
  next := 194
  rank := 1
  good := by
    constructor
    · exact edge848_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness849 : Fin frame185.rank → ℕ := ![1]
theorem edge849_span : frame185.space ≤ frame197.space :=
  frame185.inclusion frame197 witness849 (by decide)
def edge849 : CertifiedEdge catalog where
  old := 185
  next := 197
  rank := 1
  good := by
    constructor
    · exact edge849_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness850 : Fin frame185.rank → ℕ := ![1]
theorem edge850_span : frame185.space ≤ frame198.space :=
  frame185.inclusion frame198 witness850 (by decide)
def edge850 : CertifiedEdge catalog where
  old := 185
  next := 198
  rank := 1
  good := by
    constructor
    · exact edge850_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness851 : Fin frame186.rank → ℕ := ![1]
theorem edge851_span : frame186.space ≤ frame191.space :=
  frame186.inclusion frame191 witness851 (by decide)
def edge851 : CertifiedEdge catalog where
  old := 186
  next := 191
  rank := 1
  good := by
    constructor
    · exact edge851_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness852 : Fin frame186.rank → ℕ := ![1]
theorem edge852_span : frame186.space ≤ frame199.space :=
  frame186.inclusion frame199 witness852 (by decide)
def edge852 : CertifiedEdge catalog where
  old := 186
  next := 199
  rank := 1
  good := by
    constructor
    · exact edge852_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness853 : Fin frame186.rank → ℕ := ![1]
theorem edge853_span : frame186.space ≤ frame200.space :=
  frame186.inclusion frame200 witness853 (by decide)
def edge853 : CertifiedEdge catalog where
  old := 186
  next := 200
  rank := 1
  good := by
    constructor
    · exact edge853_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness854 : Fin frame187.rank → ℕ := ![3]
theorem edge854_span : frame187.space ≤ frame195.space :=
  frame187.inclusion frame195 witness854 (by decide)
def edge854 : CertifiedEdge catalog where
  old := 187
  next := 195
  rank := 1
  good := by
    constructor
    · exact edge854_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness855 : Fin frame187.rank → ℕ := ![3]
theorem edge855_span : frame187.space ≤ frame197.space :=
  frame187.inclusion frame197 witness855 (by decide)
def edge855 : CertifiedEdge catalog where
  old := 187
  next := 197
  rank := 1
  good := by
    constructor
    · exact edge855_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness856 : Fin frame187.rank → ℕ := ![3]
theorem edge856_span : frame187.space ≤ frame201.space :=
  frame187.inclusion frame201 witness856 (by decide)
def edge856 : CertifiedEdge catalog where
  old := 187
  next := 201
  rank := 1
  good := by
    constructor
    · exact edge856_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness857 : Fin frame188.rank → ℕ := ![3]
theorem edge857_span : frame188.space ≤ frame192.space :=
  frame188.inclusion frame192 witness857 (by decide)
def edge857 : CertifiedEdge catalog where
  old := 188
  next := 192
  rank := 1
  good := by
    constructor
    · exact edge857_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness858 : Fin frame188.rank → ℕ := ![3]
theorem edge858_span : frame188.space ≤ frame199.space :=
  frame188.inclusion frame199 witness858 (by decide)
def edge858 : CertifiedEdge catalog where
  old := 188
  next := 199
  rank := 1
  good := by
    constructor
    · exact edge858_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness859 : Fin frame188.rank → ℕ := ![1]
theorem edge859_span : frame188.space ≤ frame202.space :=
  frame188.inclusion frame202 witness859 (by decide)
def edge859 : CertifiedEdge catalog where
  old := 188
  next := 202
  rank := 1
  good := by
    constructor
    · exact edge859_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness860 : Fin frame189.rank → ℕ := ![3]
theorem edge860_span : frame189.space ≤ frame193.space :=
  frame189.inclusion frame193 witness860 (by decide)
def edge860 : CertifiedEdge catalog where
  old := 189
  next := 193
  rank := 1
  good := by
    constructor
    · exact edge860_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness861 : Fin frame189.rank → ℕ := ![3]
theorem edge861_span : frame189.space ≤ frame200.space :=
  frame189.inclusion frame200 witness861 (by decide)
def edge861 : CertifiedEdge catalog where
  old := 189
  next := 200
  rank := 1
  good := by
    constructor
    · exact edge861_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness862 : Fin frame189.rank → ℕ := ![3]
theorem edge862_span : frame189.space ≤ frame202.space :=
  frame189.inclusion frame202 witness862 (by decide)
def edge862 : CertifiedEdge catalog where
  old := 189
  next := 202
  rank := 1
  good := by
    constructor
    · exact edge862_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness863 : Fin frame190.rank → ℕ := ![3]
theorem edge863_span : frame190.space ≤ frame196.space :=
  frame190.inclusion frame196 witness863 (by decide)
def edge863 : CertifiedEdge catalog where
  old := 190
  next := 196
  rank := 1
  good := by
    constructor
    · exact edge863_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
