module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1376 : Fin frame365.rank → ℕ := ![2,4]
theorem edge1376_span : frame365.space ≤ frame454.space :=
  frame365.inclusion frame454 witness1376 (by decide)
def edge1376 : CertifiedEdge catalog where
  old := 365
  next := 454
  rank := 1
  good := by
    constructor
    · exact edge1376_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1377 : Fin frame365.rank → ℕ := ![18,20]
theorem edge1377_span : frame365.space ≤ frame460.space :=
  frame365.inclusion frame460 witness1377 (by decide)
def edge1377 : CertifiedEdge catalog where
  old := 365
  next := 460
  rank := 4
  good := by
    constructor
    · exact edge1377_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1378 : Fin frame365.rank → ℕ := ![2,4]
theorem edge1378_span : frame365.space ≤ frame482.space :=
  frame365.inclusion frame482 witness1378 (by decide)
def edge1378 : CertifiedEdge catalog where
  old := 365
  next := 482
  rank := 1
  good := by
    constructor
    · exact edge1378_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1379 : Fin frame365.rank → ℕ := ![20,56]
theorem edge1379_span : frame365.space ≤ frame488.space :=
  frame365.inclusion frame488 witness1379 (by decide)
def edge1379 : CertifiedEdge catalog where
  old := 365
  next := 488
  rank := 4
  good := by
    constructor
    · exact edge1379_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1380 : Fin frame366.rank → ℕ := ![2,4]
theorem edge1380_span : frame366.space ≤ frame378.space :=
  frame366.inclusion frame378 witness1380 (by decide)
def edge1380 : CertifiedEdge catalog where
  old := 366
  next := 378
  rank := 1
  good := by
    constructor
    · exact edge1380_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1381 : Fin frame366.rank → ℕ := ![2,4]
theorem edge1381_span : frame366.space ≤ frame384.space :=
  frame366.inclusion frame384 witness1381 (by decide)
def edge1381 : CertifiedEdge catalog where
  old := 366
  next := 384
  rank := 1
  good := by
    constructor
    · exact edge1381_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1382 : Fin frame367.rank → ℕ := ![2,4]
theorem edge1382_span : frame367.space ≤ frame380.space :=
  frame367.inclusion frame380 witness1382 (by decide)
def edge1382 : CertifiedEdge catalog where
  old := 367
  next := 380
  rank := 1
  good := by
    constructor
    · exact edge1382_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1383 : Fin frame367.rank → ℕ := ![2,4]
theorem edge1383_span : frame367.space ≤ frame382.space :=
  frame367.inclusion frame382 witness1383 (by decide)
def edge1383 : CertifiedEdge catalog where
  old := 367
  next := 382
  rank := 1
  good := by
    constructor
    · exact edge1383_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1384 : Fin frame368.rank → ℕ := ![3,4]
theorem edge1384_span : frame368.space ≤ frame455.space :=
  frame368.inclusion frame455 witness1384 (by decide)
def edge1384 : CertifiedEdge catalog where
  old := 368
  next := 455
  rank := 1
  good := by
    constructor
    · exact edge1384_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1385 : Fin frame368.rank → ℕ := ![9,6]
theorem edge1385_span : frame368.space ≤ frame457.space :=
  frame368.inclusion frame457 witness1385 (by decide)
def edge1385 : CertifiedEdge catalog where
  old := 368
  next := 457
  rank := 2
  good := by
    constructor
    · exact edge1385_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1386 : Fin frame368.rank → ℕ := ![3,4]
theorem edge1386_span : frame368.space ≤ frame493.space :=
  frame368.inclusion frame493 witness1386 (by decide)
def edge1386 : CertifiedEdge catalog where
  old := 368
  next := 493
  rank := 1
  good := by
    constructor
    · exact edge1386_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1387 : Fin frame368.rank → ℕ := ![11,4]
theorem edge1387_span : frame368.space ≤ frame497.space :=
  frame368.inclusion frame497 witness1387 (by decide)
def edge1387 : CertifiedEdge catalog where
  old := 368
  next := 497
  rank := 2
  good := by
    constructor
    · exact edge1387_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1388 : Fin frame369.rank → ℕ := ![1,6]
theorem edge1388_span : frame369.space ≤ frame378.space :=
  frame369.inclusion frame378 witness1388 (by decide)
def edge1388 : CertifiedEdge catalog where
  old := 369
  next := 378
  rank := 1
  good := by
    constructor
    · exact edge1388_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1389 : Fin frame369.rank → ℕ := ![1,6]
theorem edge1389_span : frame369.space ≤ frame383.space :=
  frame369.inclusion frame383 witness1389 (by decide)
def edge1389 : CertifiedEdge catalog where
  old := 369
  next := 383
  rank := 1
  good := by
    constructor
    · exact edge1389_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1390 : Fin frame370.rank → ℕ := ![5,2]
theorem edge1390_span : frame370.space ≤ frame379.space :=
  frame370.inclusion frame379 witness1390 (by decide)
def edge1390 : CertifiedEdge catalog where
  old := 370
  next := 379
  rank := 1
  good := by
    constructor
    · exact edge1390_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1391 : Fin frame370.rank → ℕ := ![1,6]
theorem edge1391_span : frame370.space ≤ frame382.space :=
  frame370.inclusion frame382 witness1391 (by decide)
def edge1391 : CertifiedEdge catalog where
  old := 370
  next := 382
  rank := 1
  good := by
    constructor
    · exact edge1391_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1392 : Fin frame371.rank → ℕ := ![1,6]
theorem edge1392_span : frame371.space ≤ frame380.space :=
  frame371.inclusion frame380 witness1392 (by decide)
def edge1392 : CertifiedEdge catalog where
  old := 371
  next := 380
  rank := 1
  good := by
    constructor
    · exact edge1392_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1393 : Fin frame371.rank → ℕ := ![1,2]
theorem edge1393_span : frame371.space ≤ frame381.space :=
  frame371.inclusion frame381 witness1393 (by decide)
def edge1393 : CertifiedEdge catalog where
  old := 371
  next := 381
  rank := 1
  good := by
    constructor
    · exact edge1393_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1394 : Fin frame372.rank → ℕ := ![1,6]
theorem edge1394_span : frame372.space ≤ frame377.space :=
  frame372.inclusion frame377 witness1394 (by decide)
def edge1394 : CertifiedEdge catalog where
  old := 372
  next := 377
  rank := 1
  good := by
    constructor
    · exact edge1394_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1395 : Fin frame372.rank → ℕ := ![5,6]
theorem edge1395_span : frame372.space ≤ frame384.space :=
  frame372.inclusion frame384 witness1395 (by decide)
def edge1395 : CertifiedEdge catalog where
  old := 372
  next := 384
  rank := 1
  good := by
    constructor
    · exact edge1395_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1396 : Fin frame373.rank → ℕ := ![2,4]
theorem edge1396_span : frame373.space ≤ frame379.space :=
  frame373.inclusion frame379 witness1396 (by decide)
def edge1396 : CertifiedEdge catalog where
  old := 373
  next := 379
  rank := 1
  good := by
    constructor
    · exact edge1396_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1397 : Fin frame373.rank → ℕ := ![2,4]
theorem edge1397_span : frame373.space ≤ frame381.space :=
  frame373.inclusion frame381 witness1397 (by decide)
def edge1397 : CertifiedEdge catalog where
  old := 373
  next := 381
  rank := 1
  good := by
    constructor
    · exact edge1397_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1398 : Fin frame374.rank → ℕ := ![2,4]
theorem edge1398_span : frame374.space ≤ frame377.space :=
  frame374.inclusion frame377 witness1398 (by decide)
def edge1398 : CertifiedEdge catalog where
  old := 374
  next := 377
  rank := 1
  good := by
    constructor
    · exact edge1398_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1399 : Fin frame374.rank → ℕ := ![2,4]
theorem edge1399_span : frame374.space ≤ frame383.space :=
  frame374.inclusion frame383 witness1399 (by decide)
def edge1399 : CertifiedEdge catalog where
  old := 374
  next := 383
  rank := 1
  good := by
    constructor
    · exact edge1399_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1400 : Fin frame375.rank → ℕ := ![3,4]
theorem edge1400_span : frame375.space ≤ frame481.space :=
  frame375.inclusion frame481 witness1400 (by decide)
def edge1400 : CertifiedEdge catalog where
  old := 375
  next := 481
  rank := 1
  good := by
    constructor
    · exact edge1400_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1401 : Fin frame375.rank → ℕ := ![3,8]
theorem edge1401_span : frame375.space ≤ frame485.space :=
  frame375.inclusion frame485 witness1401 (by decide)
def edge1401 : CertifiedEdge catalog where
  old := 375
  next := 485
  rank := 2
  good := by
    constructor
    · exact edge1401_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1402 : Fin frame375.rank → ℕ := ![3,4]
theorem edge1402_span : frame375.space ≤ frame517.space :=
  frame375.inclusion frame517 witness1402 (by decide)
def edge1402 : CertifiedEdge catalog where
  old := 375
  next := 517
  rank := 1
  good := by
    constructor
    · exact edge1402_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1403 : Fin frame375.rank → ℕ := ![1,4]
theorem edge1403_span : frame375.space ≤ frame519.space :=
  frame375.inclusion frame519 witness1403 (by decide)
def edge1403 : CertifiedEdge catalog where
  old := 375
  next := 519
  rank := 2
  good := by
    constructor
    · exact edge1403_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1404 : Fin frame376.rank → ℕ := ![2,4]
theorem edge1404_span : frame376.space ≤ frame494.space :=
  frame376.inclusion frame494 witness1404 (by decide)
def edge1404 : CertifiedEdge catalog where
  old := 376
  next := 494
  rank := 1
  good := by
    constructor
    · exact edge1404_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1405 : Fin frame376.rank → ℕ := ![40,48]
theorem edge1405_span : frame376.space ≤ frame500.space :=
  frame376.inclusion frame500 witness1405 (by decide)
def edge1405 : CertifiedEdge catalog where
  old := 376
  next := 500
  rank := 4
  good := by
    constructor
    · exact edge1405_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1406 : Fin frame376.rank → ℕ := ![2,4]
theorem edge1406_span : frame376.space ≤ frame516.space :=
  frame376.inclusion frame516 witness1406 (by decide)
def edge1406 : CertifiedEdge catalog where
  old := 376
  next := 516
  rank := 1
  good := by
    constructor
    · exact edge1406_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1407 : Fin frame376.rank → ℕ := ![52,56]
theorem edge1407_span : frame376.space ≤ frame522.space :=
  frame376.inclusion frame522 witness1407 (by decide)
def edge1407 : CertifiedEdge catalog where
  old := 376
  next := 522
  rank := 4
  good := by
    constructor
    · exact edge1407_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
