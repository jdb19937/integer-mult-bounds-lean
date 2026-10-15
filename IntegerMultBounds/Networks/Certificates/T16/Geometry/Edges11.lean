module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness352 : Fin frame15.rank → ℕ := ![2]
theorem edge352_span : frame15.space ≤ frame28.space :=
  frame15.inclusion frame28 witness352 (by decide)
def edge352 : CertifiedEdge catalog where
  old := 15
  next := 28
  rank := 1
  good := by
    constructor
    · exact edge352_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness353 : Fin frame16.rank → ℕ := ![3]
theorem edge353_span : frame16.space ≤ frame22.space :=
  frame16.inclusion frame22 witness353 (by decide)
def edge353 : CertifiedEdge catalog where
  old := 16
  next := 22
  rank := 1
  good := by
    constructor
    · exact edge353_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness354 : Fin frame16.rank → ℕ := ![1]
theorem edge354_span : frame16.space ≤ frame24.space :=
  frame16.inclusion frame24 witness354 (by decide)
def edge354 : CertifiedEdge catalog where
  old := 16
  next := 24
  rank := 1
  good := by
    constructor
    · exact edge354_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness355 : Fin frame16.rank → ℕ := ![1]
theorem edge355_span : frame16.space ≤ frame27.space :=
  frame16.inclusion frame27 witness355 (by decide)
def edge355 : CertifiedEdge catalog where
  old := 16
  next := 27
  rank := 1
  good := by
    constructor
    · exact edge355_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness356 : Fin frame17.rank → ℕ := ![2,4]
theorem edge356_span : frame17.space ≤ frame438.space :=
  frame17.inclusion frame438 witness356 (by decide)
def edge356 : CertifiedEdge catalog where
  old := 17
  next := 438
  rank := 1
  good := by
    constructor
    · exact edge356_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness357 : Fin frame17.rank → ℕ := ![52,40]
theorem edge357_span : frame17.space ≤ frame444.space :=
  frame17.inclusion frame444 witness357 (by decide)
def edge357 : CertifiedEdge catalog where
  old := 17
  next := 444
  rank := 4
  good := by
    constructor
    · exact edge357_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness358 : Fin frame17.rank → ℕ := ![2,4]
theorem edge358_span : frame17.space ≤ frame453.space :=
  frame17.inclusion frame453 witness358 (by decide)
def edge358 : CertifiedEdge catalog where
  old := 17
  next := 453
  rank := 1
  good := by
    constructor
    · exact edge358_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness359 : Fin frame17.rank → ℕ := ![8,32]
theorem edge359_span : frame17.space ≤ frame459.space :=
  frame17.inclusion frame459 witness359 (by decide)
def edge359 : CertifiedEdge catalog where
  old := 17
  next := 459
  rank := 4
  good := by
    constructor
    · exact edge359_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness360 : Fin frame18.rank → ℕ := ![2,4]
theorem edge360_span : frame18.space ≤ frame30.space :=
  frame18.inclusion frame30 witness360 (by decide)
def edge360 : CertifiedEdge catalog where
  old := 18
  next := 30
  rank := 1
  good := by
    constructor
    · exact edge360_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness361 : Fin frame18.rank → ℕ := ![2,4]
theorem edge361_span : frame18.space ≤ frame36.space :=
  frame18.inclusion frame36 witness361 (by decide)
def edge361 : CertifiedEdge catalog where
  old := 18
  next := 36
  rank := 1
  good := by
    constructor
    · exact edge361_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness362 : Fin frame19.rank → ℕ := ![2,4]
theorem edge362_span : frame19.space ≤ frame32.space :=
  frame19.inclusion frame32 witness362 (by decide)
def edge362 : CertifiedEdge catalog where
  old := 19
  next := 32
  rank := 1
  good := by
    constructor
    · exact edge362_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness363 : Fin frame19.rank → ℕ := ![2,4]
theorem edge363_span : frame19.space ≤ frame34.space :=
  frame19.inclusion frame34 witness363 (by decide)
def edge363 : CertifiedEdge catalog where
  old := 19
  next := 34
  rank := 1
  good := by
    constructor
    · exact edge363_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness364 : Fin frame20.rank → ℕ := ![1,6]
theorem edge364_span : frame20.space ≤ frame438.space :=
  frame20.inclusion frame438 witness364 (by decide)
def edge364 : CertifiedEdge catalog where
  old := 20
  next := 438
  rank := 1
  good := by
    constructor
    · exact edge364_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness365 : Fin frame20.rank → ℕ := ![7,8]
theorem edge365_span : frame20.space ≤ frame441.space :=
  frame20.inclusion frame441 witness365 (by decide)
def edge365 : CertifiedEdge catalog where
  old := 20
  next := 441
  rank := 2
  good := by
    constructor
    · exact edge365_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness366 : Fin frame20.rank → ℕ := ![1,2]
theorem edge366_span : frame20.space ≤ frame515.space :=
  frame20.inclusion frame515 witness366 (by decide)
def edge366 : CertifiedEdge catalog where
  old := 20
  next := 515
  rank := 1
  good := by
    constructor
    · exact edge366_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness367 : Fin frame20.rank → ℕ := ![3,4]
theorem edge367_span : frame20.space ≤ frame518.space :=
  frame20.inclusion frame518 witness367 (by decide)
def edge367 : CertifiedEdge catalog where
  old := 20
  next := 518
  rank := 2
  good := by
    constructor
    · exact edge367_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness368 : Fin frame21.rank → ℕ := ![1,2]
theorem edge368_span : frame21.space ≤ frame30.space :=
  frame21.inclusion frame30 witness368 (by decide)
def edge368 : CertifiedEdge catalog where
  old := 21
  next := 30
  rank := 1
  good := by
    constructor
    · exact edge368_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness369 : Fin frame21.rank → ℕ := ![1,6]
theorem edge369_span : frame21.space ≤ frame35.space :=
  frame21.inclusion frame35 witness369 (by decide)
def edge369 : CertifiedEdge catalog where
  old := 21
  next := 35
  rank := 1
  good := by
    constructor
    · exact edge369_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness370 : Fin frame22.rank → ℕ := ![1,4]
theorem edge370_span : frame22.space ≤ frame31.space :=
  frame22.inclusion frame31 witness370 (by decide)
def edge370 : CertifiedEdge catalog where
  old := 22
  next := 31
  rank := 1
  good := by
    constructor
    · exact edge370_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness371 : Fin frame22.rank → ℕ := ![1,6]
theorem edge371_span : frame22.space ≤ frame34.space :=
  frame22.inclusion frame34 witness371 (by decide)
def edge371 : CertifiedEdge catalog where
  old := 22
  next := 34
  rank := 1
  good := by
    constructor
    · exact edge371_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness372 : Fin frame23.rank → ℕ := ![5,6]
theorem edge372_span : frame23.space ≤ frame32.space :=
  frame23.inclusion frame32 witness372 (by decide)
def edge372 : CertifiedEdge catalog where
  old := 23
  next := 32
  rank := 1
  good := by
    constructor
    · exact edge372_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness373 : Fin frame23.rank → ℕ := ![3,4]
theorem edge373_span : frame23.space ≤ frame33.space :=
  frame23.inclusion frame33 witness373 (by decide)
def edge373 : CertifiedEdge catalog where
  old := 23
  next := 33
  rank := 1
  good := by
    constructor
    · exact edge373_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness374 : Fin frame24.rank → ℕ := ![5,6]
theorem edge374_span : frame24.space ≤ frame29.space :=
  frame24.inclusion frame29 witness374 (by decide)
def edge374 : CertifiedEdge catalog where
  old := 24
  next := 29
  rank := 1
  good := by
    constructor
    · exact edge374_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness375 : Fin frame24.rank → ℕ := ![5,2]
theorem edge375_span : frame24.space ≤ frame36.space :=
  frame24.inclusion frame36 witness375 (by decide)
def edge375 : CertifiedEdge catalog where
  old := 24
  next := 36
  rank := 1
  good := by
    constructor
    · exact edge375_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness376 : Fin frame25.rank → ℕ := ![2,4]
theorem edge376_span : frame25.space ≤ frame31.space :=
  frame25.inclusion frame31 witness376 (by decide)
def edge376 : CertifiedEdge catalog where
  old := 25
  next := 31
  rank := 1
  good := by
    constructor
    · exact edge376_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness377 : Fin frame25.rank → ℕ := ![2,4]
theorem edge377_span : frame25.space ≤ frame33.space :=
  frame25.inclusion frame33 witness377 (by decide)
def edge377 : CertifiedEdge catalog where
  old := 25
  next := 33
  rank := 1
  good := by
    constructor
    · exact edge377_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness378 : Fin frame26.rank → ℕ := ![2,4]
theorem edge378_span : frame26.space ≤ frame29.space :=
  frame26.inclusion frame29 witness378 (by decide)
def edge378 : CertifiedEdge catalog where
  old := 26
  next := 29
  rank := 1
  good := by
    constructor
    · exact edge378_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness379 : Fin frame26.rank → ℕ := ![2,4]
theorem edge379_span : frame26.space ≤ frame35.space :=
  frame26.inclusion frame35 witness379 (by decide)
def edge379 : CertifiedEdge catalog where
  old := 26
  next := 35
  rank := 1
  good := by
    constructor
    · exact edge379_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness380 : Fin frame27.rank → ℕ := ![5,6]
theorem edge380_span : frame27.space ≤ frame453.space :=
  frame27.inclusion frame453 witness380 (by decide)
def edge380 : CertifiedEdge catalog where
  old := 27
  next := 453
  rank := 1
  good := by
    constructor
    · exact edge380_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness381 : Fin frame27.rank → ℕ := ![23,8]
theorem edge381_span : frame27.space ≤ frame456.space :=
  frame27.inclusion frame456 witness381 (by decide)
def edge381 : CertifiedEdge catalog where
  old := 27
  next := 456
  rank := 3
  good := by
    constructor
    · exact edge381_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness382 : Fin frame27.rank → ℕ := ![5,2]
theorem edge382_span : frame27.space ≤ frame504.space :=
  frame27.inclusion frame504 witness382 (by decide)
def edge382 : CertifiedEdge catalog where
  old := 27
  next := 504
  rank := 1
  good := by
    constructor
    · exact edge382_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness383 : Fin frame27.rank → ℕ := ![27,12]
theorem edge383_span : frame27.space ≤ frame507.space :=
  frame27.inclusion frame507 witness383 (by decide)
def edge383 : CertifiedEdge catalog where
  old := 27
  next := 507
  rank := 3
  good := by
    constructor
    · exact edge383_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
