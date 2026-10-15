module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness384 : Fin frame28.rank → ℕ := ![2,4]
theorem edge384_span : frame28.space ≤ frame504.space :=
  frame28.inclusion frame504 witness384 (by decide)
def edge384 : CertifiedEdge catalog where
  old := 28
  next := 504
  rank := 1
  good := by
    constructor
    · exact edge384_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness385 : Fin frame28.rank → ℕ := ![40,48]
theorem edge385_span : frame28.space ≤ frame510.space :=
  frame28.inclusion frame510 witness385 (by decide)
def edge385 : CertifiedEdge catalog where
  old := 28
  next := 510
  rank := 4
  good := by
    constructor
    · exact edge385_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness386 : Fin frame28.rank → ℕ := ![2,4]
theorem edge386_span : frame28.space ≤ frame515.space :=
  frame28.inclusion frame515 witness386 (by decide)
def edge386 : CertifiedEdge catalog where
  old := 28
  next := 515
  rank := 1
  good := by
    constructor
    · exact edge386_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness387 : Fin frame28.rank → ℕ := ![20,8]
theorem edge387_span : frame28.space ≤ frame521.space :=
  frame28.inclusion frame521 witness387 (by decide)
def edge387 : CertifiedEdge catalog where
  old := 28
  next := 521
  rank := 4
  good := by
    constructor
    · exact edge387_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness388 : Fin frame29.rank → ℕ := ![9,2,4]
theorem edge388_span : frame29.space ≤ frame37.space :=
  frame29.inclusion frame37 witness388 (by decide)
def edge388 : CertifiedEdge catalog where
  old := 29
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge388_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness389 : Fin frame29.rank → ℕ := ![19,36,40]
theorem edge389_span : frame29.space ≤ frame538.space :=
  frame29.inclusion frame538 witness389 (by decide)
def edge389 : CertifiedEdge catalog where
  old := 29
  next := 538
  rank := 3
  good := by
    constructor
    · exact edge389_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness390 : Fin frame29.rank → ℕ := ![39,8,16]
theorem edge390_span : frame29.space ≤ frame544.space :=
  frame29.inclusion frame544 witness390 (by decide)
def edge390 : CertifiedEdge catalog where
  old := 29
  next := 544
  rank := 3
  good := by
    constructor
    · exact edge390_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness391 : Fin frame30.rank → ℕ := ![1,6,8]
theorem edge391_span : frame30.space ≤ frame37.space :=
  frame30.inclusion frame37 witness391 (by decide)
def edge391 : CertifiedEdge catalog where
  old := 30
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge391_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness392 : Fin frame30.rank → ℕ := ![3,44,48]
theorem edge392_span : frame30.space ≤ frame539.space :=
  frame30.inclusion frame539 witness392 (by decide)
def edge392 : CertifiedEdge catalog where
  old := 30
  next := 539
  rank := 3
  good := by
    constructor
    · exact edge392_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness393 : Fin frame30.rank → ℕ := ![7,24,32]
theorem edge393_span : frame30.space ≤ frame545.space :=
  frame30.inclusion frame545 witness393 (by decide)
def edge393 : CertifiedEdge catalog where
  old := 30
  next := 545
  rank := 3
  good := by
    constructor
    · exact edge393_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness394 : Fin frame31.rank → ℕ := ![1,2,12]
theorem edge394_span : frame31.space ≤ frame37.space :=
  frame31.inclusion frame37 witness394 (by decide)
def edge394 : CertifiedEdge catalog where
  old := 31
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge394_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness395 : Fin frame31.rank → ℕ := ![3,36,56]
theorem edge395_span : frame31.space ≤ frame550.space :=
  frame31.inclusion frame550 witness395 (by decide)
def edge395 : CertifiedEdge catalog where
  old := 31
  next := 550
  rank := 3
  good := by
    constructor
    · exact edge395_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness396 : Fin frame31.rank → ℕ := ![7,8,48]
theorem edge396_span : frame31.space ≤ frame556.space :=
  frame31.inclusion frame556 witness396 (by decide)
def edge396 : CertifiedEdge catalog where
  old := 31
  next := 556
  rank := 3
  good := by
    constructor
    · exact edge396_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness397 : Fin frame32.rank → ℕ := ![3,4,8]
theorem edge397_span : frame32.space ≤ frame37.space :=
  frame32.inclusion frame37 witness397 (by decide)
def edge397 : CertifiedEdge catalog where
  old := 32
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge397_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness398 : Fin frame32.rank → ℕ := ![7,40,48]
theorem edge398_span : frame32.space ≤ frame551.space :=
  frame32.inclusion frame551 witness398 (by decide)
def edge398 : CertifiedEdge catalog where
  old := 32
  next := 551
  rank := 3
  good := by
    constructor
    · exact edge398_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness399 : Fin frame32.rank → ℕ := ![15,16,32]
theorem edge399_span : frame32.space ≤ frame557.space :=
  frame32.inclusion frame557 witness399 (by decide)
def edge399 : CertifiedEdge catalog where
  old := 32
  next := 557
  rank := 3
  good := by
    constructor
    · exact edge399_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness400 : Fin frame33.rank → ℕ := ![9,2,12]
theorem edge400_span : frame33.space ≤ frame37.space :=
  frame33.inclusion frame37 witness400 (by decide)
def edge400 : CertifiedEdge catalog where
  old := 33
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge400_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness401 : Fin frame33.rank → ℕ := ![35,20,24]
theorem edge401_span : frame33.space ≤ frame562.space :=
  frame33.inclusion frame562 witness401 (by decide)
def edge401 : CertifiedEdge catalog where
  old := 33
  next := 562
  rank := 3
  good := by
    constructor
    · exact edge401_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness402 : Fin frame33.rank → ℕ := ![7,40,48]
theorem edge402_span : frame33.space ≤ frame568.space :=
  frame33.inclusion frame568 witness402 (by decide)
def edge402 : CertifiedEdge catalog where
  old := 33
  next := 568
  rank := 3
  good := by
    constructor
    · exact edge402_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness403 : Fin frame34.rank → ℕ := ![1,4,8]
theorem edge403_span : frame34.space ≤ frame37.space :=
  frame34.inclusion frame37 witness403 (by decide)
def edge403 : CertifiedEdge catalog where
  old := 34
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge403_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness404 : Fin frame34.rank → ℕ := ![3,52,40]
theorem edge404_span : frame34.space ≤ frame563.space :=
  frame34.inclusion frame563 witness404 (by decide)
def edge404 : CertifiedEdge catalog where
  old := 34
  next := 563
  rank := 3
  good := by
    constructor
    · exact edge404_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness405 : Fin frame34.rank → ℕ := ![7,40,16]
theorem edge405_span : frame34.space ≤ frame569.space :=
  frame34.inclusion frame569 witness405 (by decide)
def edge405 : CertifiedEdge catalog where
  old := 34
  next := 569
  rank := 3
  good := by
    constructor
    · exact edge405_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness406 : Fin frame35.rank → ℕ := ![1,2,4]
theorem edge406_span : frame35.space ≤ frame37.space :=
  frame35.inclusion frame37 witness406 (by decide)
def edge406 : CertifiedEdge catalog where
  old := 35
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge406_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness407 : Fin frame35.rank → ℕ := ![3,52,24]
theorem edge407_span : frame35.space ≤ frame574.space :=
  frame35.inclusion frame574 witness407 (by decide)
def edge407 : CertifiedEdge catalog where
  old := 35
  next := 574
  rank := 3
  good := by
    constructor
    · exact edge407_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness408 : Fin frame35.rank → ℕ := ![7,40,48]
theorem edge408_span : frame35.space ≤ frame580.space :=
  frame35.inclusion frame580 witness408 (by decide)
def edge408 : CertifiedEdge catalog where
  old := 35
  next := 580
  rank := 3
  good := by
    constructor
    · exact edge408_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness409 : Fin frame36.rank → ℕ := ![5,6,8]
theorem edge409_span : frame36.space ≤ frame37.space :=
  frame36.inclusion frame37 witness409 (by decide)
def edge409 : CertifiedEdge catalog where
  old := 36
  next := 37
  rank := 1
  good := by
    constructor
    · exact edge409_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness410 : Fin frame36.rank → ℕ := ![19,36,40]
theorem edge410_span : frame36.space ≤ frame575.space :=
  frame36.inclusion frame575 witness410 (by decide)
def edge410 : CertifiedEdge catalog where
  old := 36
  next := 575
  rank := 3
  good := by
    constructor
    · exact edge410_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness411 : Fin frame36.rank → ℕ := ![39,8,16]
theorem edge411_span : frame36.space ≤ frame581.space :=
  frame36.inclusion frame581 witness411 (by decide)
def edge411 : CertifiedEdge catalog where
  old := 36
  next := 581
  rank := 3
  good := by
    constructor
    · exact edge411_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness412 : Fin frame37.rank → ℕ := ![7,200,336,416]
theorem edge412_span : frame37.space ≤ frame1.space :=
  frame37.inclusion frame1 witness412 (by decide)
def edge412 : CertifiedEdge catalog where
  old := 37
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge412_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness413 : Fin frame37.rank → ℕ := ![7,72,208,160]
theorem edge413_span : frame37.space ≤ frame415.space :=
  frame37.inclusion frame415 witness413 (by decide)
def edge413 : CertifiedEdge catalog where
  old := 37
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge413_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness414 : Fin frame37.rank → ℕ := ![7,200,80,160]
theorem edge414_span : frame37.space ≤ frame416.space :=
  frame37.inclusion frame416 witness414 (by decide)
def edge414 : CertifiedEdge catalog where
  old := 37
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge414_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness415 : Fin frame37.rank → ℕ := ![7,200,80,160]
theorem edge415_span : frame37.space ≤ frame417.space :=
  frame37.inclusion frame417 witness415 (by decide)
def edge415 : CertifiedEdge catalog where
  old := 37
  next := 417
  rank := 4
  good := by
    constructor
    · exact edge415_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
