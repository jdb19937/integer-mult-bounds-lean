module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1312 : Fin frame344.rank → ℕ := ![1,4]
theorem edge1312_span : frame344.space ≤ frame352.space :=
  frame344.inclusion frame352 witness1312 (by decide)
def edge1312 : CertifiedEdge catalog where
  old := 344
  next := 352
  rank := 1
  good := by
    constructor
    · exact edge1312_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1313 : Fin frame345.rank → ℕ := ![1,4]
theorem edge1313_span : frame345.space ≤ frame348.space :=
  frame345.inclusion frame348 witness1313 (by decide)
def edge1313 : CertifiedEdge catalog where
  old := 345
  next := 348
  rank := 1
  good := by
    constructor
    · exact edge1313_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1314 : Fin frame345.rank → ℕ := ![1,4]
theorem edge1314_span : frame345.space ≤ frame354.space :=
  frame345.inclusion frame354 witness1314 (by decide)
def edge1314 : CertifiedEdge catalog where
  old := 345
  next := 354
  rank := 1
  good := by
    constructor
    · exact edge1314_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1315 : Fin frame346.rank → ℕ := ![3,4]
theorem edge1315_span : frame346.space ≤ frame468.space :=
  frame346.inclusion frame468 witness1315 (by decide)
def edge1315 : CertifiedEdge catalog where
  old := 346
  next := 468
  rank := 1
  good := by
    constructor
    · exact edge1315_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1316 : Fin frame346.rank → ℕ := ![6,24]
theorem edge1316_span : frame346.space ≤ frame472.space :=
  frame346.inclusion frame472 witness1316 (by decide)
def edge1316 : CertifiedEdge catalog where
  old := 346
  next := 472
  rank := 3
  good := by
    constructor
    · exact edge1316_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1317 : Fin frame346.rank → ℕ := ![1,2]
theorem edge1317_span : frame346.space ≤ frame516.space :=
  frame346.inclusion frame516 witness1317 (by decide)
def edge1317 : CertifiedEdge catalog where
  old := 346
  next := 516
  rank := 1
  good := by
    constructor
    · exact edge1317_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1318 : Fin frame346.rank → ℕ := ![10,4]
theorem edge1318_span : frame346.space ≤ frame520.space :=
  frame346.inclusion frame520 witness1318 (by decide)
def edge1318 : CertifiedEdge catalog where
  old := 346
  next := 520
  rank := 2
  good := by
    constructor
    · exact edge1318_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1319 : Fin frame347.rank → ℕ := ![1,4]
theorem edge1319_span : frame347.space ≤ frame517.space :=
  frame347.inclusion frame517 witness1319 (by decide)
def edge1319 : CertifiedEdge catalog where
  old := 347
  next := 517
  rank := 1
  good := by
    constructor
    · exact edge1319_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1320 : Fin frame347.rank → ℕ := ![5,40]
theorem edge1320_span : frame347.space ≤ frame523.space :=
  frame347.inclusion frame523 witness1320 (by decide)
def edge1320 : CertifiedEdge catalog where
  old := 347
  next := 523
  rank := 4
  good := by
    constructor
    · exact edge1320_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1321 : Fin frame347.rank → ℕ := ![3,4]
theorem edge1321_span : frame347.space ≤ frame527.space :=
  frame347.inclusion frame527 witness1321 (by decide)
def edge1321 : CertifiedEdge catalog where
  old := 347
  next := 527
  rank := 1
  good := by
    constructor
    · exact edge1321_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1322 : Fin frame347.rank → ℕ := ![5,40]
theorem edge1322_span : frame347.space ≤ frame533.space :=
  frame347.inclusion frame533 witness1322 (by decide)
def edge1322 : CertifiedEdge catalog where
  old := 347
  next := 533
  rank := 4
  good := by
    constructor
    · exact edge1322_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1323 : Fin frame348.rank → ℕ := ![9,10,4]
theorem edge1323_span : frame348.space ≤ frame356.space :=
  frame348.inclusion frame356 witness1323 (by decide)
def edge1323 : CertifiedEdge catalog where
  old := 348
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1323_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1324 : Fin frame348.rank → ℕ := ![9,10,36]
theorem edge1324_span : frame348.space ≤ frame658.space :=
  frame348.inclusion frame658 witness1324 (by decide)
def edge1324 : CertifiedEdge catalog where
  old := 348
  next := 658
  rank := 3
  good := by
    constructor
    · exact edge1324_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1325 : Fin frame348.rank → ℕ := ![17,18,36]
theorem edge1325_span : frame348.space ≤ frame690.space :=
  frame348.inclusion frame690 witness1325 (by decide)
def edge1325 : CertifiedEdge catalog where
  old := 348
  next := 690
  rank := 3
  good := by
    constructor
    · exact edge1325_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1326 : Fin frame349.rank → ℕ := ![1,2,4]
theorem edge1326_span : frame349.space ≤ frame356.space :=
  frame349.inclusion frame356 witness1326 (by decide)
def edge1326 : CertifiedEdge catalog where
  old := 349
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1326_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1327 : Fin frame349.rank → ℕ := ![33,34,36]
theorem edge1327_span : frame349.space ≤ frame659.space :=
  frame349.inclusion frame659 witness1327 (by decide)
def edge1327 : CertifiedEdge catalog where
  old := 349
  next := 659
  rank := 3
  good := by
    constructor
    · exact edge1327_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1328 : Fin frame349.rank → ℕ := ![1,2,4]
theorem edge1328_span : frame349.space ≤ frame691.space :=
  frame349.inclusion frame691 witness1328 (by decide)
def edge1328 : CertifiedEdge catalog where
  old := 349
  next := 691
  rank := 3
  good := by
    constructor
    · exact edge1328_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1329 : Fin frame350.rank → ℕ := ![9,2,12]
theorem edge1329_span : frame350.space ≤ frame356.space :=
  frame350.inclusion frame356 witness1329 (by decide)
def edge1329 : CertifiedEdge catalog where
  old := 350
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1329_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1330 : Fin frame350.rank → ℕ := ![9,34,12]
theorem edge1330_span : frame350.space ≤ frame666.space :=
  frame350.inclusion frame666 witness1330 (by decide)
def edge1330 : CertifiedEdge catalog where
  old := 350
  next := 666
  rank := 3
  good := by
    constructor
    · exact edge1330_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1331 : Fin frame350.rank → ℕ := ![17,34,20]
theorem edge1331_span : frame350.space ≤ frame698.space :=
  frame350.inclusion frame698 witness1331 (by decide)
def edge1331 : CertifiedEdge catalog where
  old := 350
  next := 698
  rank := 3
  good := by
    constructor
    · exact edge1331_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1332 : Fin frame351.rank → ℕ := ![1,10,12]
theorem edge1332_span : frame351.space ≤ frame356.space :=
  frame351.inclusion frame356 witness1332 (by decide)
def edge1332 : CertifiedEdge catalog where
  old := 351
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1332_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1333 : Fin frame351.rank → ℕ := ![33,10,12]
theorem edge1333_span : frame351.space ≤ frame667.space :=
  frame351.inclusion frame667 witness1333 (by decide)
def edge1333 : CertifiedEdge catalog where
  old := 351
  next := 667
  rank := 3
  good := by
    constructor
    · exact edge1333_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1334 : Fin frame351.rank → ℕ := ![33,18,20]
theorem edge1334_span : frame351.space ≤ frame699.space :=
  frame351.inclusion frame699 witness1334 (by decide)
def edge1334 : CertifiedEdge catalog where
  old := 351
  next := 699
  rank := 3
  good := by
    constructor
    · exact edge1334_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1335 : Fin frame352.rank → ℕ := ![9,10,12]
theorem edge1335_span : frame352.space ≤ frame356.space :=
  frame352.inclusion frame356 witness1335 (by decide)
def edge1335 : CertifiedEdge catalog where
  old := 352
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1335_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1336 : Fin frame352.rank → ℕ := ![9,10,12]
theorem edge1336_span : frame352.space ≤ frame674.space :=
  frame352.inclusion frame674 witness1336 (by decide)
def edge1336 : CertifiedEdge catalog where
  old := 352
  next := 674
  rank := 3
  good := by
    constructor
    · exact edge1336_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1337 : Fin frame352.rank → ℕ := ![41,42,44]
theorem edge1337_span : frame352.space ≤ frame706.space :=
  frame352.inclusion frame706 witness1337 (by decide)
def edge1337 : CertifiedEdge catalog where
  old := 352
  next := 706
  rank := 3
  good := by
    constructor
    · exact edge1337_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1338 : Fin frame353.rank → ℕ := ![1,2,12]
theorem edge1338_span : frame353.space ≤ frame356.space :=
  frame353.inclusion frame356 witness1338 (by decide)
def edge1338 : CertifiedEdge catalog where
  old := 353
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1338_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1339 : Fin frame353.rank → ℕ := ![33,34,12]
theorem edge1339_span : frame353.space ≤ frame675.space :=
  frame353.inclusion frame675 witness1339 (by decide)
def edge1339 : CertifiedEdge catalog where
  old := 353
  next := 675
  rank := 3
  good := by
    constructor
    · exact edge1339_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1340 : Fin frame353.rank → ℕ := ![33,34,28]
theorem edge1340_span : frame353.space ≤ frame707.space :=
  frame353.inclusion frame707 witness1340 (by decide)
def edge1340 : CertifiedEdge catalog where
  old := 353
  next := 707
  rank := 3
  good := by
    constructor
    · exact edge1340_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1341 : Fin frame354.rank → ℕ := ![9,2,4]
theorem edge1341_span : frame354.space ≤ frame356.space :=
  frame354.inclusion frame356 witness1341 (by decide)
def edge1341 : CertifiedEdge catalog where
  old := 354
  next := 356
  rank := 1
  good := by
    constructor
    · exact edge1341_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1342 : Fin frame354.rank → ℕ := ![9,34,36]
theorem edge1342_span : frame354.space ≤ frame682.space :=
  frame354.inclusion frame682 witness1342 (by decide)
def edge1342 : CertifiedEdge catalog where
  old := 354
  next := 682
  rank := 3
  good := by
    constructor
    · exact edge1342_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1343 : Fin frame354.rank → ℕ := ![25,2,36]
theorem edge1343_span : frame354.space ≤ frame714.space :=
  frame354.inclusion frame714 witness1343 (by decide)
def edge1343 : CertifiedEdge catalog where
  old := 354
  next := 714
  rank := 3
  good := by
    constructor
    · exact edge1343_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
