module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness224 : Fin frame3.rank → ℕ := ![2]
theorem edge224_span : frame3.space ≤ frame307.space :=
  frame3.inclusion frame307 witness224 (by decide)
def edge224 : CertifiedEdge catalog where
  old := 3
  next := 307
  rank := 1
  good := by
    constructor
    · exact edge224_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness225 : Fin frame3.rank → ℕ := ![2]
theorem edge225_span : frame3.space ≤ frame310.space :=
  frame3.inclusion frame310 witness225 (by decide)
def edge225 : CertifiedEdge catalog where
  old := 3
  next := 310
  rank := 1
  good := by
    constructor
    · exact edge225_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness226 : Fin frame3.rank → ℕ := ![2]
theorem edge226_span : frame3.space ≤ frame317.space :=
  frame3.inclusion frame317 witness226 (by decide)
def edge226 : CertifiedEdge catalog where
  old := 3
  next := 317
  rank := 1
  good := by
    constructor
    · exact edge226_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness227 : Fin frame3.rank → ℕ := ![2]
theorem edge227_span : frame3.space ≤ frame318.space :=
  frame3.inclusion frame318 witness227 (by decide)
def edge227 : CertifiedEdge catalog where
  old := 3
  next := 318
  rank := 1
  good := by
    constructor
    · exact edge227_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness228 : Fin frame3.rank → ℕ := ![4]
theorem edge228_span : frame3.space ≤ frame406.space :=
  frame3.inclusion frame406 witness228 (by decide)
def edge228 : CertifiedEdge catalog where
  old := 3
  next := 406
  rank := 2
  good := by
    constructor
    · exact edge228_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness229 : Fin frame3.rank → ℕ := ![4]
theorem edge229_span : frame3.space ≤ frame407.space :=
  frame3.inclusion frame407 witness229 (by decide)
def edge229 : CertifiedEdge catalog where
  old := 3
  next := 407
  rank := 2
  good := by
    constructor
    · exact edge229_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness230 : Fin frame3.rank → ℕ := ![4]
theorem edge230_span : frame3.space ≤ frame412.space :=
  frame3.inclusion frame412 witness230 (by decide)
def edge230 : CertifiedEdge catalog where
  old := 3
  next := 412
  rank := 2
  good := by
    constructor
    · exact edge230_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness231 : Fin frame3.rank → ℕ := ![4]
theorem edge231_span : frame3.space ≤ frame413.space :=
  frame3.inclusion frame413 witness231 (by decide)
def edge231 : CertifiedEdge catalog where
  old := 3
  next := 413
  rank := 2
  good := by
    constructor
    · exact edge231_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness232 : Fin frame3.rank → ℕ := ![12]
theorem edge232_span : frame3.space ≤ frame424.space :=
  frame3.inclusion frame424 witness232 (by decide)
def edge232 : CertifiedEdge catalog where
  old := 3
  next := 424
  rank := 3
  good := by
    constructor
    · exact edge232_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness233 : Fin frame3.rank → ℕ := ![8]
theorem edge233_span : frame3.space ≤ frame428.space :=
  frame3.inclusion frame428 witness233 (by decide)
def edge233 : CertifiedEdge catalog where
  old := 3
  next := 428
  rank := 3
  good := by
    constructor
    · exact edge233_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness234 : Fin frame3.rank → ℕ := ![12]
theorem edge234_span : frame3.space ≤ frame432.space :=
  frame3.inclusion frame432 witness234 (by decide)
def edge234 : CertifiedEdge catalog where
  old := 3
  next := 432
  rank := 4
  good := by
    constructor
    · exact edge234_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness235 : Fin frame3.rank → ℕ := ![24]
theorem edge235_span : frame3.space ≤ frame437.space :=
  frame3.inclusion frame437 witness235 (by decide)
def edge235 : CertifiedEdge catalog where
  old := 3
  next := 437
  rank := 4
  good := by
    constructor
    · exact edge235_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness236 : Fin frame3.rank → ℕ := ![4]
theorem edge236_span : frame3.space ≤ frame534.space :=
  frame3.inclusion frame534 witness236 (by decide)
def edge236 : CertifiedEdge catalog where
  old := 3
  next := 534
  rank := 2
  good := by
    constructor
    · exact edge236_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness237 : Fin frame3.rank → ℕ := ![6]
theorem edge237_span : frame3.space ≤ frame535.space :=
  frame3.inclusion frame535 witness237 (by decide)
def edge237 : CertifiedEdge catalog where
  old := 3
  next := 535
  rank := 2
  good := by
    constructor
    · exact edge237_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness238 : Fin frame3.rank → ℕ := ![4]
theorem edge238_span : frame3.space ≤ frame536.space :=
  frame3.inclusion frame536 witness238 (by decide)
def edge238 : CertifiedEdge catalog where
  old := 3
  next := 536
  rank := 2
  good := by
    constructor
    · exact edge238_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness239 : Fin frame3.rank → ℕ := ![6]
theorem edge239_span : frame3.space ≤ frame537.space :=
  frame3.inclusion frame537 witness239 (by decide)
def edge239 : CertifiedEdge catalog where
  old := 3
  next := 537
  rank := 2
  good := by
    constructor
    · exact edge239_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness240 : Fin frame3.rank → ℕ := ![4]
theorem edge240_span : frame3.space ≤ frame540.space :=
  frame3.inclusion frame540 witness240 (by decide)
def edge240 : CertifiedEdge catalog where
  old := 3
  next := 540
  rank := 2
  good := by
    constructor
    · exact edge240_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness241 : Fin frame3.rank → ℕ := ![4]
theorem edge241_span : frame3.space ≤ frame541.space :=
  frame3.inclusion frame541 witness241 (by decide)
def edge241 : CertifiedEdge catalog where
  old := 3
  next := 541
  rank := 2
  good := by
    constructor
    · exact edge241_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness242 : Fin frame3.rank → ℕ := ![4]
theorem edge242_span : frame3.space ≤ frame542.space :=
  frame3.inclusion frame542 witness242 (by decide)
def edge242 : CertifiedEdge catalog where
  old := 3
  next := 542
  rank := 2
  good := by
    constructor
    · exact edge242_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness243 : Fin frame3.rank → ℕ := ![4]
theorem edge243_span : frame3.space ≤ frame543.space :=
  frame3.inclusion frame543 witness243 (by decide)
def edge243 : CertifiedEdge catalog where
  old := 3
  next := 543
  rank := 2
  good := by
    constructor
    · exact edge243_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness244 : Fin frame3.rank → ℕ := ![6]
theorem edge244_span : frame3.space ≤ frame570.space :=
  frame3.inclusion frame570 witness244 (by decide)
def edge244 : CertifiedEdge catalog where
  old := 3
  next := 570
  rank := 2
  good := by
    constructor
    · exact edge244_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness245 : Fin frame3.rank → ℕ := ![4]
theorem edge245_span : frame3.space ≤ frame571.space :=
  frame3.inclusion frame571 witness245 (by decide)
def edge245 : CertifiedEdge catalog where
  old := 3
  next := 571
  rank := 2
  good := by
    constructor
    · exact edge245_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness246 : Fin frame3.rank → ℕ := ![4]
theorem edge246_span : frame3.space ≤ frame572.space :=
  frame3.inclusion frame572 witness246 (by decide)
def edge246 : CertifiedEdge catalog where
  old := 3
  next := 572
  rank := 2
  good := by
    constructor
    · exact edge246_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness247 : Fin frame3.rank → ℕ := ![6]
theorem edge247_span : frame3.space ≤ frame573.space :=
  frame3.inclusion frame573 witness247 (by decide)
def edge247 : CertifiedEdge catalog where
  old := 3
  next := 573
  rank := 2
  good := by
    constructor
    · exact edge247_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness248 : Fin frame3.rank → ℕ := ![4]
theorem edge248_span : frame3.space ≤ frame576.space :=
  frame3.inclusion frame576 witness248 (by decide)
def edge248 : CertifiedEdge catalog where
  old := 3
  next := 576
  rank := 2
  good := by
    constructor
    · exact edge248_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness249 : Fin frame3.rank → ℕ := ![4]
theorem edge249_span : frame3.space ≤ frame577.space :=
  frame3.inclusion frame577 witness249 (by decide)
def edge249 : CertifiedEdge catalog where
  old := 3
  next := 577
  rank := 2
  good := by
    constructor
    · exact edge249_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness250 : Fin frame3.rank → ℕ := ![4]
theorem edge250_span : frame3.space ≤ frame578.space :=
  frame3.inclusion frame578 witness250 (by decide)
def edge250 : CertifiedEdge catalog where
  old := 3
  next := 578
  rank := 2
  good := by
    constructor
    · exact edge250_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness251 : Fin frame3.rank → ℕ := ![4]
theorem edge251_span : frame3.space ≤ frame579.space :=
  frame3.inclusion frame579 witness251 (by decide)
def edge251 : CertifiedEdge catalog where
  old := 3
  next := 579
  rank := 2
  good := by
    constructor
    · exact edge251_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness252 : Fin frame4.rank → ℕ := ![3]
theorem edge252_span : frame4.space ≤ frame290.space :=
  frame4.inclusion frame290 witness252 (by decide)
def edge252 : CertifiedEdge catalog where
  old := 4
  next := 290
  rank := 2
  good := by
    constructor
    · exact edge252_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness253 : Fin frame4.rank → ℕ := ![3]
theorem edge253_span : frame4.space ≤ frame291.space :=
  frame4.inclusion frame291 witness253 (by decide)
def edge253 : CertifiedEdge catalog where
  old := 4
  next := 291
  rank := 2
  good := by
    constructor
    · exact edge253_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness254 : Fin frame4.rank → ℕ := ![3]
theorem edge254_span : frame4.space ≤ frame292.space :=
  frame4.inclusion frame292 witness254 (by decide)
def edge254 : CertifiedEdge catalog where
  old := 4
  next := 292
  rank := 2
  good := by
    constructor
    · exact edge254_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness255 : Fin frame4.rank → ℕ := ![3]
theorem edge255_span : frame4.space ≤ frame293.space :=
  frame4.inclusion frame293 witness255 (by decide)
def edge255 : CertifiedEdge catalog where
  old := 4
  next := 293
  rank := 2
  good := by
    constructor
    · exact edge255_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
