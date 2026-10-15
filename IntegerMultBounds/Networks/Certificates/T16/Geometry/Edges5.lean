module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness160 : Fin frame0.rank → ℕ := ![]
theorem edge160_span : frame0.space ≤ frame420.space :=
  frame0.inclusion frame420 witness160 (by decide)
def edge160 : CertifiedEdge catalog where
  old := 0
  next := 420
  rank := 8
  good := by
    constructor
    · exact edge160_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness161 : Fin frame0.rank → ℕ := ![]
theorem edge161_span : frame0.space ≤ frame421.space :=
  frame0.inclusion frame421 witness161 (by decide)
def edge161 : CertifiedEdge catalog where
  old := 0
  next := 421
  rank := 8
  good := by
    constructor
    · exact edge161_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness162 : Fin frame0.rank → ℕ := ![]
theorem edge162_span : frame0.space ≤ frame422.space :=
  frame0.inclusion frame422 witness162 (by decide)
def edge162 : CertifiedEdge catalog where
  old := 0
  next := 422
  rank := 8
  good := by
    constructor
    · exact edge162_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness163 : Fin frame0.rank → ℕ := ![]
theorem edge163_span : frame0.space ≤ frame423.space :=
  frame0.inclusion frame423 witness163 (by decide)
def edge163 : CertifiedEdge catalog where
  old := 0
  next := 423
  rank := 1
  good := by
    constructor
    · exact edge163_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness164 : Fin frame2.rank → ℕ := ![4]
theorem edge164_span : frame2.space ≤ frame31.space :=
  frame2.inclusion frame31 witness164 (by decide)
def edge164 : CertifiedEdge catalog where
  old := 2
  next := 31
  rank := 2
  good := by
    constructor
    · exact edge164_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness165 : Fin frame2.rank → ℕ := ![6]
theorem edge165_span : frame2.space ≤ frame32.space :=
  frame2.inclusion frame32 witness165 (by decide)
def edge165 : CertifiedEdge catalog where
  old := 2
  next := 32
  rank := 2
  good := by
    constructor
    · exact edge165_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness166 : Fin frame2.rank → ℕ := ![4]
theorem edge166_span : frame2.space ≤ frame33.space :=
  frame2.inclusion frame33 witness166 (by decide)
def edge166 : CertifiedEdge catalog where
  old := 2
  next := 33
  rank := 2
  good := by
    constructor
    · exact edge166_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness167 : Fin frame2.rank → ℕ := ![6]
theorem edge167_span : frame2.space ≤ frame34.space :=
  frame2.inclusion frame34 witness167 (by decide)
def edge167 : CertifiedEdge catalog where
  old := 2
  next := 34
  rank := 2
  good := by
    constructor
    · exact edge167_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness168 : Fin frame2.rank → ℕ := ![2]
theorem edge168_span : frame2.space ≤ frame162.space :=
  frame2.inclusion frame162 witness168 (by decide)
def edge168 : CertifiedEdge catalog where
  old := 2
  next := 162
  rank := 1
  good := by
    constructor
    · exact edge168_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness169 : Fin frame2.rank → ℕ := ![2]
theorem edge169_span : frame2.space ≤ frame165.space :=
  frame2.inclusion frame165 witness169 (by decide)
def edge169 : CertifiedEdge catalog where
  old := 2
  next := 165
  rank := 1
  good := by
    constructor
    · exact edge169_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness170 : Fin frame2.rank → ℕ := ![2]
theorem edge170_span : frame2.space ≤ frame172.space :=
  frame2.inclusion frame172 witness170 (by decide)
def edge170 : CertifiedEdge catalog where
  old := 2
  next := 172
  rank := 1
  good := by
    constructor
    · exact edge170_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness171 : Fin frame2.rank → ℕ := ![2]
theorem edge171_span : frame2.space ≤ frame173.space :=
  frame2.inclusion frame173 witness171 (by decide)
def edge171 : CertifiedEdge catalog where
  old := 2
  next := 173
  rank := 1
  good := by
    constructor
    · exact edge171_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness172 : Fin frame2.rank → ℕ := ![2]
theorem edge172_span : frame2.space ≤ frame191.space :=
  frame2.inclusion frame191 witness172 (by decide)
def edge172 : CertifiedEdge catalog where
  old := 2
  next := 191
  rank := 1
  good := by
    constructor
    · exact edge172_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness173 : Fin frame2.rank → ℕ := ![2]
theorem edge173_span : frame2.space ≤ frame194.space :=
  frame2.inclusion frame194 witness173 (by decide)
def edge173 : CertifiedEdge catalog where
  old := 2
  next := 194
  rank := 1
  good := by
    constructor
    · exact edge173_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness174 : Fin frame2.rank → ℕ := ![2]
theorem edge174_span : frame2.space ≤ frame201.space :=
  frame2.inclusion frame201 witness174 (by decide)
def edge174 : CertifiedEdge catalog where
  old := 2
  next := 201
  rank := 1
  good := by
    constructor
    · exact edge174_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness175 : Fin frame2.rank → ℕ := ![2]
theorem edge175_span : frame2.space ≤ frame202.space :=
  frame2.inclusion frame202 witness175 (by decide)
def edge175 : CertifiedEdge catalog where
  old := 2
  next := 202
  rank := 1
  good := by
    constructor
    · exact edge175_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness176 : Fin frame2.rank → ℕ := ![3]
theorem edge176_span : frame2.space ≤ frame220.space :=
  frame2.inclusion frame220 witness176 (by decide)
def edge176 : CertifiedEdge catalog where
  old := 2
  next := 220
  rank := 1
  good := by
    constructor
    · exact edge176_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness177 : Fin frame2.rank → ℕ := ![2]
theorem edge177_span : frame2.space ≤ frame223.space :=
  frame2.inclusion frame223 witness177 (by decide)
def edge177 : CertifiedEdge catalog where
  old := 2
  next := 223
  rank := 1
  good := by
    constructor
    · exact edge177_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness178 : Fin frame2.rank → ℕ := ![2]
theorem edge178_span : frame2.space ≤ frame230.space :=
  frame2.inclusion frame230 witness178 (by decide)
def edge178 : CertifiedEdge catalog where
  old := 2
  next := 230
  rank := 1
  good := by
    constructor
    · exact edge178_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness179 : Fin frame2.rank → ℕ := ![2]
theorem edge179_span : frame2.space ≤ frame231.space :=
  frame2.inclusion frame231 witness179 (by decide)
def edge179 : CertifiedEdge catalog where
  old := 2
  next := 231
  rank := 1
  good := by
    constructor
    · exact edge179_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness180 : Fin frame2.rank → ℕ := ![2]
theorem edge180_span : frame2.space ≤ frame249.space :=
  frame2.inclusion frame249 witness180 (by decide)
def edge180 : CertifiedEdge catalog where
  old := 2
  next := 249
  rank := 1
  good := by
    constructor
    · exact edge180_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness181 : Fin frame2.rank → ℕ := ![2]
theorem edge181_span : frame2.space ≤ frame252.space :=
  frame2.inclusion frame252 witness181 (by decide)
def edge181 : CertifiedEdge catalog where
  old := 2
  next := 252
  rank := 1
  good := by
    constructor
    · exact edge181_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness182 : Fin frame2.rank → ℕ := ![2]
theorem edge182_span : frame2.space ≤ frame259.space :=
  frame2.inclusion frame259 witness182 (by decide)
def edge182 : CertifiedEdge catalog where
  old := 2
  next := 259
  rank := 1
  good := by
    constructor
    · exact edge182_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness183 : Fin frame2.rank → ℕ := ![2]
theorem edge183_span : frame2.space ≤ frame260.space :=
  frame2.inclusion frame260 witness183 (by decide)
def edge183 : CertifiedEdge catalog where
  old := 2
  next := 260
  rank := 1
  good := by
    constructor
    · exact edge183_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness184 : Fin frame2.rank → ℕ := ![4]
theorem edge184_span : frame2.space ≤ frame408.space :=
  frame2.inclusion frame408 witness184 (by decide)
def edge184 : CertifiedEdge catalog where
  old := 2
  next := 408
  rank := 2
  good := by
    constructor
    · exact edge184_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness185 : Fin frame2.rank → ℕ := ![4]
theorem edge185_span : frame2.space ≤ frame409.space :=
  frame2.inclusion frame409 witness185 (by decide)
def edge185 : CertifiedEdge catalog where
  old := 2
  next := 409
  rank := 2
  good := by
    constructor
    · exact edge185_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness186 : Fin frame2.rank → ℕ := ![4]
theorem edge186_span : frame2.space ≤ frame410.space :=
  frame2.inclusion frame410 witness186 (by decide)
def edge186 : CertifiedEdge catalog where
  old := 2
  next := 410
  rank := 2
  good := by
    constructor
    · exact edge186_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness187 : Fin frame2.rank → ℕ := ![4]
theorem edge187_span : frame2.space ≤ frame411.space :=
  frame2.inclusion frame411 witness187 (by decide)
def edge187 : CertifiedEdge catalog where
  old := 2
  next := 411
  rank := 2
  good := by
    constructor
    · exact edge187_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness188 : Fin frame2.rank → ℕ := ![12]
theorem edge188_span : frame2.space ≤ frame429.space :=
  frame2.inclusion frame429 witness188 (by decide)
def edge188 : CertifiedEdge catalog where
  old := 2
  next := 429
  rank := 3
  good := by
    constructor
    · exact edge188_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness189 : Fin frame2.rank → ℕ := ![12]
theorem edge189_span : frame2.space ≤ frame430.space :=
  frame2.inclusion frame430 witness189 (by decide)
def edge189 : CertifiedEdge catalog where
  old := 2
  next := 430
  rank := 3
  good := by
    constructor
    · exact edge189_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness190 : Fin frame2.rank → ℕ := ![16]
theorem edge190_span : frame2.space ≤ frame431.space :=
  frame2.inclusion frame431 witness190 (by decide)
def edge190 : CertifiedEdge catalog where
  old := 2
  next := 431
  rank := 4
  good := by
    constructor
    · exact edge190_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness191 : Fin frame2.rank → ℕ := ![24]
theorem edge191_span : frame2.space ≤ frame436.space :=
  frame2.inclusion frame436 witness191 (by decide)
def edge191 : CertifiedEdge catalog where
  old := 2
  next := 436
  rank := 4
  good := by
    constructor
    · exact edge191_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
