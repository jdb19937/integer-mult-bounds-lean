module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness256 : Fin frame4.rank → ℕ := ![7]
theorem edge256_span : frame4.space ≤ frame319.space :=
  frame4.inclusion frame319 witness256 (by decide)
def edge256 : CertifiedEdge catalog where
  old := 4
  next := 319
  rank := 2
  good := by
    constructor
    · exact edge256_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness257 : Fin frame4.rank → ℕ := ![7]
theorem edge257_span : frame4.space ≤ frame320.space :=
  frame4.inclusion frame320 witness257 (by decide)
def edge257 : CertifiedEdge catalog where
  old := 4
  next := 320
  rank := 2
  good := by
    constructor
    · exact edge257_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness258 : Fin frame4.rank → ℕ := ![7]
theorem edge258_span : frame4.space ≤ frame321.space :=
  frame4.inclusion frame321 witness258 (by decide)
def edge258 : CertifiedEdge catalog where
  old := 4
  next := 321
  rank := 2
  good := by
    constructor
    · exact edge258_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness259 : Fin frame4.rank → ℕ := ![7]
theorem edge259_span : frame4.space ≤ frame322.space :=
  frame4.inclusion frame322 witness259 (by decide)
def edge259 : CertifiedEdge catalog where
  old := 4
  next := 322
  rank := 2
  good := by
    constructor
    · exact edge259_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness260 : Fin frame4.rank → ℕ := ![7]
theorem edge260_span : frame4.space ≤ frame348.space :=
  frame4.inclusion frame348 witness260 (by decide)
def edge260 : CertifiedEdge catalog where
  old := 4
  next := 348
  rank := 2
  good := by
    constructor
    · exact edge260_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness261 : Fin frame4.rank → ℕ := ![7]
theorem edge261_span : frame4.space ≤ frame349.space :=
  frame4.inclusion frame349 witness261 (by decide)
def edge261 : CertifiedEdge catalog where
  old := 4
  next := 349
  rank := 2
  good := by
    constructor
    · exact edge261_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness262 : Fin frame4.rank → ℕ := ![7]
theorem edge262_span : frame4.space ≤ frame350.space :=
  frame4.inclusion frame350 witness262 (by decide)
def edge262 : CertifiedEdge catalog where
  old := 4
  next := 350
  rank := 2
  good := by
    constructor
    · exact edge262_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness263 : Fin frame4.rank → ℕ := ![7]
theorem edge263_span : frame4.space ≤ frame351.space :=
  frame4.inclusion frame351 witness263 (by decide)
def edge263 : CertifiedEdge catalog where
  old := 4
  next := 351
  rank := 2
  good := by
    constructor
    · exact edge263_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness264 : Fin frame4.rank → ℕ := ![3]
theorem edge264_span : frame4.space ≤ frame377.space :=
  frame4.inclusion frame377 witness264 (by decide)
def edge264 : CertifiedEdge catalog where
  old := 4
  next := 377
  rank := 2
  good := by
    constructor
    · exact edge264_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness265 : Fin frame4.rank → ℕ := ![3]
theorem edge265_span : frame4.space ≤ frame378.space :=
  frame4.inclusion frame378 witness265 (by decide)
def edge265 : CertifiedEdge catalog where
  old := 4
  next := 378
  rank := 2
  good := by
    constructor
    · exact edge265_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness266 : Fin frame4.rank → ℕ := ![3]
theorem edge266_span : frame4.space ≤ frame379.space :=
  frame4.inclusion frame379 witness266 (by decide)
def edge266 : CertifiedEdge catalog where
  old := 4
  next := 379
  rank := 2
  good := by
    constructor
    · exact edge266_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness267 : Fin frame4.rank → ℕ := ![3]
theorem edge267_span : frame4.space ≤ frame380.space :=
  frame4.inclusion frame380 witness267 (by decide)
def edge267 : CertifiedEdge catalog where
  old := 4
  next := 380
  rank := 2
  good := by
    constructor
    · exact edge267_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness268 : Fin frame5.rank → ℕ := ![6]
theorem edge268_span : frame5.space ≤ frame87.space :=
  frame5.inclusion frame87 witness268 (by decide)
def edge268 : CertifiedEdge catalog where
  old := 5
  next := 87
  rank := 2
  good := by
    constructor
    · exact edge268_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness269 : Fin frame5.rank → ℕ := ![2]
theorem edge269_span : frame5.space ≤ frame88.space :=
  frame5.inclusion frame88 witness269 (by decide)
def edge269 : CertifiedEdge catalog where
  old := 5
  next := 88
  rank := 2
  good := by
    constructor
    · exact edge269_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness270 : Fin frame5.rank → ℕ := ![2]
theorem edge270_span : frame5.space ≤ frame93.space :=
  frame5.inclusion frame93 witness270 (by decide)
def edge270 : CertifiedEdge catalog where
  old := 5
  next := 93
  rank := 2
  good := by
    constructor
    · exact edge270_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness271 : Fin frame5.rank → ℕ := ![6]
theorem edge271_span : frame5.space ≤ frame94.space :=
  frame5.inclusion frame94 witness271 (by decide)
def edge271 : CertifiedEdge catalog where
  old := 5
  next := 94
  rank := 2
  good := by
    constructor
    · exact edge271_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness272 : Fin frame5.rank → ℕ := ![2]
theorem edge272_span : frame5.space ≤ frame118.space :=
  frame5.inclusion frame118 witness272 (by decide)
def edge272 : CertifiedEdge catalog where
  old := 5
  next := 118
  rank := 2
  good := by
    constructor
    · exact edge272_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness273 : Fin frame5.rank → ℕ := ![2]
theorem edge273_span : frame5.space ≤ frame119.space :=
  frame5.inclusion frame119 witness273 (by decide)
def edge273 : CertifiedEdge catalog where
  old := 5
  next := 119
  rank := 2
  good := by
    constructor
    · exact edge273_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness274 : Fin frame5.rank → ℕ := ![2]
theorem edge274_span : frame5.space ≤ frame120.space :=
  frame5.inclusion frame120 witness274 (by decide)
def edge274 : CertifiedEdge catalog where
  old := 5
  next := 120
  rank := 2
  good := by
    constructor
    · exact edge274_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness275 : Fin frame5.rank → ℕ := ![2]
theorem edge275_span : frame5.space ≤ frame121.space :=
  frame5.inclusion frame121 witness275 (by decide)
def edge275 : CertifiedEdge catalog where
  old := 5
  next := 121
  rank := 2
  good := by
    constructor
    · exact edge275_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness276 : Fin frame5.rank → ℕ := ![4]
theorem edge276_span : frame5.space ≤ frame207.space :=
  frame5.inclusion frame207 witness276 (by decide)
def edge276 : CertifiedEdge catalog where
  old := 5
  next := 207
  rank := 2
  good := by
    constructor
    · exact edge276_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness277 : Fin frame5.rank → ℕ := ![4]
theorem edge277_span : frame5.space ≤ frame208.space :=
  frame5.inclusion frame208 witness277 (by decide)
def edge277 : CertifiedEdge catalog where
  old := 5
  next := 208
  rank := 2
  good := by
    constructor
    · exact edge277_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness278 : Fin frame5.rank → ℕ := ![2]
theorem edge278_span : frame5.space ≤ frame234.space :=
  frame5.inclusion frame234 witness278 (by decide)
def edge278 : CertifiedEdge catalog where
  old := 5
  next := 234
  rank := 2
  good := by
    constructor
    · exact edge278_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness279 : Fin frame5.rank → ℕ := ![6]
theorem edge279_span : frame5.space ≤ frame235.space :=
  frame5.inclusion frame235 witness279 (by decide)
def edge279 : CertifiedEdge catalog where
  old := 5
  next := 235
  rank := 2
  good := by
    constructor
    · exact edge279_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness280 : Fin frame5.rank → ℕ := ![2]
theorem edge280_span : frame5.space ≤ frame236.space :=
  frame5.inclusion frame236 witness280 (by decide)
def edge280 : CertifiedEdge catalog where
  old := 5
  next := 236
  rank := 2
  good := by
    constructor
    · exact edge280_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness281 : Fin frame5.rank → ℕ := ![6]
theorem edge281_span : frame5.space ≤ frame237.space :=
  frame5.inclusion frame237 witness281 (by decide)
def edge281 : CertifiedEdge catalog where
  old := 5
  next := 237
  rank := 2
  good := by
    constructor
    · exact edge281_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness282 : Fin frame5.rank → ℕ := ![4]
theorem edge282_span : frame5.space ≤ frame323.space :=
  frame5.inclusion frame323 witness282 (by decide)
def edge282 : CertifiedEdge catalog where
  old := 5
  next := 323
  rank := 2
  good := by
    constructor
    · exact edge282_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness283 : Fin frame5.rank → ℕ := ![4]
theorem edge283_span : frame5.space ≤ frame324.space :=
  frame5.inclusion frame324 witness283 (by decide)
def edge283 : CertifiedEdge catalog where
  old := 5
  next := 324
  rank := 2
  good := by
    constructor
    · exact edge283_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness284 : Fin frame6.rank → ℕ := ![6]
theorem edge284_span : frame6.space ≤ frame89.space :=
  frame6.inclusion frame89 witness284 (by decide)
def edge284 : CertifiedEdge catalog where
  old := 6
  next := 89
  rank := 2
  good := by
    constructor
    · exact edge284_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness285 : Fin frame6.rank → ℕ := ![2]
theorem edge285_span : frame6.space ≤ frame90.space :=
  frame6.inclusion frame90 witness285 (by decide)
def edge285 : CertifiedEdge catalog where
  old := 6
  next := 90
  rank := 2
  good := by
    constructor
    · exact edge285_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness286 : Fin frame6.rank → ℕ := ![2]
theorem edge286_span : frame6.space ≤ frame91.space :=
  frame6.inclusion frame91 witness286 (by decide)
def edge286 : CertifiedEdge catalog where
  old := 6
  next := 91
  rank := 2
  good := by
    constructor
    · exact edge286_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness287 : Fin frame6.rank → ℕ := ![6]
theorem edge287_span : frame6.space ≤ frame92.space :=
  frame6.inclusion frame92 witness287 (by decide)
def edge287 : CertifiedEdge catalog where
  old := 6
  next := 92
  rank := 2
  good := by
    constructor
    · exact edge287_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
