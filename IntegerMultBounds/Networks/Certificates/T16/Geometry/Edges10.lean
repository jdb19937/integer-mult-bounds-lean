module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness320 : Fin frame8.rank → ℕ := ![4]
theorem edge320_span : frame8.space ≤ frame145.space :=
  frame8.inclusion frame145 witness320 (by decide)
def edge320 : CertifiedEdge catalog where
  old := 8
  next := 145
  rank := 2
  good := by
    constructor
    · exact edge320_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness321 : Fin frame8.rank → ℕ := ![4]
theorem edge321_span : frame8.space ≤ frame146.space :=
  frame8.inclusion frame146 witness321 (by decide)
def edge321 : CertifiedEdge catalog where
  old := 8
  next := 146
  rank := 2
  good := by
    constructor
    · exact edge321_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness322 : Fin frame8.rank → ℕ := ![4]
theorem edge322_span : frame8.space ≤ frame151.space :=
  frame8.inclusion frame151 witness322 (by decide)
def edge322 : CertifiedEdge catalog where
  old := 8
  next := 151
  rank := 2
  good := by
    constructor
    · exact edge322_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness323 : Fin frame8.rank → ℕ := ![4]
theorem edge323_span : frame8.space ≤ frame152.space :=
  frame8.inclusion frame152 witness323 (by decide)
def edge323 : CertifiedEdge catalog where
  old := 8
  next := 152
  rank := 2
  good := by
    constructor
    · exact edge323_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness324 : Fin frame8.rank → ℕ := ![4]
theorem edge324_span : frame8.space ≤ frame209.space :=
  frame8.inclusion frame209 witness324 (by decide)
def edge324 : CertifiedEdge catalog where
  old := 8
  next := 209
  rank := 2
  good := by
    constructor
    · exact edge324_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness325 : Fin frame8.rank → ℕ := ![4]
theorem edge325_span : frame8.space ≤ frame210.space :=
  frame8.inclusion frame210 witness325 (by decide)
def edge325 : CertifiedEdge catalog where
  old := 8
  next := 210
  rank := 2
  good := by
    constructor
    · exact edge325_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness326 : Fin frame8.rank → ℕ := ![6]
theorem edge326_span : frame8.space ≤ frame232.space :=
  frame8.inclusion frame232 witness326 (by decide)
def edge326 : CertifiedEdge catalog where
  old := 8
  next := 232
  rank := 2
  good := by
    constructor
    · exact edge326_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness327 : Fin frame8.rank → ℕ := ![2]
theorem edge327_span : frame8.space ≤ frame233.space :=
  frame8.inclusion frame233 witness327 (by decide)
def edge327 : CertifiedEdge catalog where
  old := 8
  next := 233
  rank := 2
  good := by
    constructor
    · exact edge327_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness328 : Fin frame8.rank → ℕ := ![6]
theorem edge328_span : frame8.space ≤ frame238.space :=
  frame8.inclusion frame238 witness328 (by decide)
def edge328 : CertifiedEdge catalog where
  old := 8
  next := 238
  rank := 2
  good := by
    constructor
    · exact edge328_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness329 : Fin frame8.rank → ℕ := ![2]
theorem edge329_span : frame8.space ≤ frame239.space :=
  frame8.inclusion frame239 witness329 (by decide)
def edge329 : CertifiedEdge catalog where
  old := 8
  next := 239
  rank := 2
  good := by
    constructor
    · exact edge329_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness330 : Fin frame8.rank → ℕ := ![2]
theorem edge330_span : frame8.space ≤ frame296.space :=
  frame8.inclusion frame296 witness330 (by decide)
def edge330 : CertifiedEdge catalog where
  old := 8
  next := 296
  rank := 2
  good := by
    constructor
    · exact edge330_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness331 : Fin frame8.rank → ℕ := ![6]
theorem edge331_span : frame8.space ≤ frame297.space :=
  frame8.inclusion frame297 witness331 (by decide)
def edge331 : CertifiedEdge catalog where
  old := 8
  next := 297
  rank := 2
  good := by
    constructor
    · exact edge331_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness332 : Fin frame9.rank → ℕ := ![2]
theorem edge332_span : frame9.space ≤ frame17.space :=
  frame9.inclusion frame17 witness332 (by decide)
def edge332 : CertifiedEdge catalog where
  old := 9
  next := 17
  rank := 1
  good := by
    constructor
    · exact edge332_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness333 : Fin frame9.rank → ℕ := ![2]
theorem edge333_span : frame9.space ≤ frame18.space :=
  frame9.inclusion frame18 witness333 (by decide)
def edge333 : CertifiedEdge catalog where
  old := 9
  next := 18
  rank := 1
  good := by
    constructor
    · exact edge333_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness334 : Fin frame9.rank → ℕ := ![2]
theorem edge334_span : frame9.space ≤ frame19.space :=
  frame9.inclusion frame19 witness334 (by decide)
def edge334 : CertifiedEdge catalog where
  old := 9
  next := 19
  rank := 1
  good := by
    constructor
    · exact edge334_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness335 : Fin frame10.rank → ℕ := ![1]
theorem edge335_span : frame10.space ≤ frame20.space :=
  frame10.inclusion frame20 witness335 (by decide)
def edge335 : CertifiedEdge catalog where
  old := 10
  next := 20
  rank := 1
  good := by
    constructor
    · exact edge335_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness336 : Fin frame10.rank → ℕ := ![1]
theorem edge336_span : frame10.space ≤ frame21.space :=
  frame10.inclusion frame21 witness336 (by decide)
def edge336 : CertifiedEdge catalog where
  old := 10
  next := 21
  rank := 1
  good := by
    constructor
    · exact edge336_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness337 : Fin frame10.rank → ℕ := ![1]
theorem edge337_span : frame10.space ≤ frame22.space :=
  frame10.inclusion frame22 witness337 (by decide)
def edge337 : CertifiedEdge catalog where
  old := 10
  next := 22
  rank := 1
  good := by
    constructor
    · exact edge337_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness338 : Fin frame11.rank → ℕ := ![3]
theorem edge338_span : frame11.space ≤ frame20.space :=
  frame11.inclusion frame20 witness338 (by decide)
def edge338 : CertifiedEdge catalog where
  old := 11
  next := 20
  rank := 1
  good := by
    constructor
    · exact edge338_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness339 : Fin frame11.rank → ℕ := ![1]
theorem edge339_span : frame11.space ≤ frame23.space :=
  frame11.inclusion frame23 witness339 (by decide)
def edge339 : CertifiedEdge catalog where
  old := 11
  next := 23
  rank := 1
  good := by
    constructor
    · exact edge339_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness340 : Fin frame11.rank → ℕ := ![3]
theorem edge340_span : frame11.space ≤ frame24.space :=
  frame11.inclusion frame24 witness340 (by decide)
def edge340 : CertifiedEdge catalog where
  old := 11
  next := 24
  rank := 1
  good := by
    constructor
    · exact edge340_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness341 : Fin frame12.rank → ℕ := ![1]
theorem edge341_span : frame12.space ≤ frame17.space :=
  frame12.inclusion frame17 witness341 (by decide)
def edge341 : CertifiedEdge catalog where
  old := 12
  next := 17
  rank := 1
  good := by
    constructor
    · exact edge341_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness342 : Fin frame12.rank → ℕ := ![1]
theorem edge342_span : frame12.space ≤ frame25.space :=
  frame12.inclusion frame25 witness342 (by decide)
def edge342 : CertifiedEdge catalog where
  old := 12
  next := 25
  rank := 1
  good := by
    constructor
    · exact edge342_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness343 : Fin frame12.rank → ℕ := ![1]
theorem edge343_span : frame12.space ≤ frame26.space :=
  frame12.inclusion frame26 witness343 (by decide)
def edge343 : CertifiedEdge catalog where
  old := 12
  next := 26
  rank := 1
  good := by
    constructor
    · exact edge343_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness344 : Fin frame13.rank → ℕ := ![3]
theorem edge344_span : frame13.space ≤ frame21.space :=
  frame13.inclusion frame21 witness344 (by decide)
def edge344 : CertifiedEdge catalog where
  old := 13
  next := 21
  rank := 1
  good := by
    constructor
    · exact edge344_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness345 : Fin frame13.rank → ℕ := ![3]
theorem edge345_span : frame13.space ≤ frame23.space :=
  frame13.inclusion frame23 witness345 (by decide)
def edge345 : CertifiedEdge catalog where
  old := 13
  next := 23
  rank := 1
  good := by
    constructor
    · exact edge345_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness346 : Fin frame13.rank → ℕ := ![3]
theorem edge346_span : frame13.space ≤ frame27.space :=
  frame13.inclusion frame27 witness346 (by decide)
def edge346 : CertifiedEdge catalog where
  old := 13
  next := 27
  rank := 1
  good := by
    constructor
    · exact edge346_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness347 : Fin frame14.rank → ℕ := ![3]
theorem edge347_span : frame14.space ≤ frame18.space :=
  frame14.inclusion frame18 witness347 (by decide)
def edge347 : CertifiedEdge catalog where
  old := 14
  next := 18
  rank := 1
  good := by
    constructor
    · exact edge347_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness348 : Fin frame14.rank → ℕ := ![3]
theorem edge348_span : frame14.space ≤ frame25.space :=
  frame14.inclusion frame25 witness348 (by decide)
def edge348 : CertifiedEdge catalog where
  old := 14
  next := 25
  rank := 1
  good := by
    constructor
    · exact edge348_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness349 : Fin frame14.rank → ℕ := ![3]
theorem edge349_span : frame14.space ≤ frame28.space :=
  frame14.inclusion frame28 witness349 (by decide)
def edge349 : CertifiedEdge catalog where
  old := 14
  next := 28
  rank := 1
  good := by
    constructor
    · exact edge349_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness350 : Fin frame15.rank → ℕ := ![1]
theorem edge350_span : frame15.space ≤ frame19.space :=
  frame15.inclusion frame19 witness350 (by decide)
def edge350 : CertifiedEdge catalog where
  old := 15
  next := 19
  rank := 1
  good := by
    constructor
    · exact edge350_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness351 : Fin frame15.rank → ℕ := ![2]
theorem edge351_span : frame15.space ≤ frame26.space :=
  frame15.inclusion frame26 witness351 (by decide)
def edge351 : CertifiedEdge catalog where
  old := 15
  next := 26
  rank := 1
  good := by
    constructor
    · exact edge351_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
