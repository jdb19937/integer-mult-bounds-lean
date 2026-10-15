module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2496 : Fin frame759.rank → ℕ := ![1,2,68,8,16,96,128]
theorem edge2496_span : frame759.space ≤ frame891.space :=
  frame759.inclusion frame891 witness2496 (by decide)
def edge2496 : CertifiedEdge catalog where
  old := 759
  next := 891
  rank := 1
  good := by
    constructor
    · exact edge2496_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2497 : Fin frame759.rank → ℕ := ![1,2,36,8,48,64,128]
theorem edge2497_span : frame759.space ≤ frame999.space :=
  frame759.inclusion frame999 witness2497 (by decide)
def edge2497 : CertifiedEdge catalog where
  old := 759
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2497_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2498 : Fin frame760.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2498_span : frame760.space ≤ frame887.space :=
  frame760.inclusion frame887 witness2498 (by decide)
def edge2498 : CertifiedEdge catalog where
  old := 760
  next := 887
  rank := 1
  good := by
    constructor
    · exact edge2498_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2499 : Fin frame760.rank → ℕ := ![1,2,4,8,144,160,192]
theorem edge2499_span : frame760.space ≤ frame890.space :=
  frame760.inclusion frame890 witness2499 (by decide)
def edge2499 : CertifiedEdge catalog where
  old := 760
  next := 890
  rank := 1
  good := by
    constructor
    · exact edge2499_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2500 : Fin frame760.rank → ℕ := ![1,2,4,8,16,160,192]
theorem edge2500_span : frame760.space ≤ frame999.space :=
  frame760.inclusion frame999 witness2500 (by decide)
def edge2500 : CertifiedEdge catalog where
  old := 760
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2500_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2501 : Fin frame761.rank → ℕ := ![1,2,4,72,80,96,128]
theorem edge2501_span : frame761.space ≤ frame895.space :=
  frame761.inclusion frame895 witness2501 (by decide)
def edge2501 : CertifiedEdge catalog where
  old := 761
  next := 895
  rank := 1
  good := by
    constructor
    · exact edge2501_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2502 : Fin frame761.rank → ℕ := ![9,10,4,16,32,64,128]
theorem edge2502_span : frame761.space ≤ frame898.space :=
  frame761.inclusion frame898 witness2502 (by decide)
def edge2502 : CertifiedEdge catalog where
  old := 761
  next := 898
  rank := 1
  good := by
    constructor
    · exact edge2502_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2503 : Fin frame761.rank → ℕ := ![9,10,4,16,32,64,128]
theorem edge2503_span : frame761.space ≤ frame999.space :=
  frame761.inclusion frame999 witness2503 (by decide)
def edge2503 : CertifiedEdge catalog where
  old := 761
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2503_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2504 : Fin frame762.rank → ℕ := ![1,162,4,8,48,192,256]
theorem edge2504_span : frame762.space ≤ frame1.space :=
  frame762.inclusion frame1 witness2504 (by decide)
def edge2504 : CertifiedEdge catalog where
  old := 762
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2504_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2505 : Fin frame762.rank → ℕ := ![1,34,4,8,48,64,128]
theorem edge2505_span : frame762.space ≤ frame912.space :=
  frame762.inclusion frame912 witness2505 (by decide)
def edge2505 : CertifiedEdge catalog where
  old := 762
  next := 912
  rank := 1
  good := by
    constructor
    · exact edge2505_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2506 : Fin frame762.rank → ℕ := ![1,66,4,8,16,96,128]
theorem edge2506_span : frame762.space ≤ frame915.space :=
  frame762.inclusion frame915 witness2506 (by decide)
def edge2506 : CertifiedEdge catalog where
  old := 762
  next := 915
  rank := 1
  good := by
    constructor
    · exact edge2506_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2507 : Fin frame763.rank → ℕ := ![161,2,4,8,48,192,256]
theorem edge2507_span : frame763.space ≤ frame1.space :=
  frame763.inclusion frame1 witness2507 (by decide)
def edge2507 : CertifiedEdge catalog where
  old := 763
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2507_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2508 : Fin frame763.rank → ℕ := ![65,2,4,8,16,96,128]
theorem edge2508_span : frame763.space ≤ frame904.space :=
  frame763.inclusion frame904 witness2508 (by decide)
def edge2508 : CertifiedEdge catalog where
  old := 763
  next := 904
  rank := 1
  good := by
    constructor
    · exact edge2508_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2509 : Fin frame763.rank → ℕ := ![33,2,4,8,48,64,128]
theorem edge2509_span : frame763.space ≤ frame907.space :=
  frame763.inclusion frame907 witness2509 (by decide)
def edge2509 : CertifiedEdge catalog where
  old := 763
  next := 907
  rank := 1
  good := by
    constructor
    · exact edge2509_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2510 : Fin frame763.rank → ℕ := ![33,2,4,8,48,64,128]
theorem edge2510_span : frame763.space ≤ frame999.space :=
  frame763.inclusion frame999 witness2510 (by decide)
def edge2510 : CertifiedEdge catalog where
  old := 763
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2510_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2511 : Fin frame764.rank → ℕ := ![9,2,12,144,160,192,256]
theorem edge2511_span : frame764.space ≤ frame1.space :=
  frame764.inclusion frame1 witness2511 (by decide)
def edge2511 : CertifiedEdge catalog where
  old := 764
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2511_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2512 : Fin frame764.rank → ℕ := ![1,2,4,72,80,96,128]
theorem edge2512_span : frame764.space ≤ frame903.space :=
  frame764.inclusion frame903 witness2512 (by decide)
def edge2512 : CertifiedEdge catalog where
  old := 764
  next := 903
  rank := 1
  good := by
    constructor
    · exact edge2512_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2513 : Fin frame764.rank → ℕ := ![9,2,12,16,32,64,128]
theorem edge2513_span : frame764.space ≤ frame906.space :=
  frame764.inclusion frame906 witness2513 (by decide)
def edge2513 : CertifiedEdge catalog where
  old := 764
  next := 906
  rank := 1
  good := by
    constructor
    · exact edge2513_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2514 : Fin frame764.rank → ℕ := ![9,2,12,16,32,64,128]
theorem edge2514_span : frame764.space ≤ frame999.space :=
  frame764.inclusion frame999 witness2514 (by decide)
def edge2514 : CertifiedEdge catalog where
  old := 764
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2514_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2515 : Fin frame765.rank → ℕ := ![1,10,12,16,32,64,128]
theorem edge2515_span : frame765.space ≤ frame911.space :=
  frame765.inclusion frame911 witness2515 (by decide)
def edge2515 : CertifiedEdge catalog where
  old := 765
  next := 911
  rank := 1
  good := by
    constructor
    · exact edge2515_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2516 : Fin frame765.rank → ℕ := ![1,2,4,72,80,96,128]
theorem edge2516_span : frame765.space ≤ frame914.space :=
  frame765.inclusion frame914 witness2516 (by decide)
def edge2516 : CertifiedEdge catalog where
  old := 765
  next := 914
  rank := 1
  good := by
    constructor
    · exact edge2516_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2517 : Fin frame765.rank → ℕ := ![1,10,12,16,32,64,128]
theorem edge2517_span : frame765.space ≤ frame999.space :=
  frame765.inclusion frame999 witness2517 (by decide)
def edge2517 : CertifiedEdge catalog where
  old := 765
  next := 999
  rank := 1
  good := by
    constructor
    · exact edge2517_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2518 : Fin frame766.rank → ℕ := ![1,2,4,264,144,32,448]
theorem edge2518_span : frame766.space ≤ frame1.space :=
  frame766.inclusion frame1 witness2518 (by decide)
def edge2518 : CertifiedEdge catalog where
  old := 766
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2518_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2519 : Fin frame766.rank → ℕ := ![1,2,4,136,16,32,192]
theorem edge2519_span : frame766.space ≤ frame928.space :=
  frame766.inclusion frame928 witness2519 (by decide)
def edge2519 : CertifiedEdge catalog where
  old := 766
  next := 928
  rank := 1
  good := by
    constructor
    · exact edge2519_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2520 : Fin frame766.rank → ℕ := ![1,2,4,8,144,32,192]
theorem edge2520_span : frame766.space ≤ frame931.space :=
  frame766.inclusion frame931 witness2520 (by decide)
def edge2520 : CertifiedEdge catalog where
  old := 766
  next := 931
  rank := 1
  good := by
    constructor
    · exact edge2520_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2521 : Fin frame766.rank → ℕ := ![1,2,4,8,144,32,192]
theorem edge2521_span : frame766.space ≤ frame998.space :=
  frame766.inclusion frame998 witness2521 (by decide)
def edge2521 : CertifiedEdge catalog where
  old := 766
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2521_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2522 : Fin frame767.rank → ℕ := ![33,34,4,264,272,64,384]
theorem edge2522_span : frame767.space ≤ frame1.space :=
  frame767.inclusion frame1 witness2522 (by decide)
def edge2522 : CertifiedEdge catalog where
  old := 767
  next := 1
  rank := 2
  good := by
    constructor
    · exact edge2522_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2523 : Fin frame767.rank → ℕ := ![1,2,4,136,144,32,192]
theorem edge2523_span : frame767.space ≤ frame920.space :=
  frame767.inclusion frame920 witness2523 (by decide)
def edge2523 : CertifiedEdge catalog where
  old := 767
  next := 920
  rank := 1
  good := by
    constructor
    · exact edge2523_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2524 : Fin frame767.rank → ℕ := ![33,34,4,8,16,64,128]
theorem edge2524_span : frame767.space ≤ frame923.space :=
  frame767.inclusion frame923 witness2524 (by decide)
def edge2524 : CertifiedEdge catalog where
  old := 767
  next := 923
  rank := 1
  good := by
    constructor
    · exact edge2524_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2525 : Fin frame767.rank → ℕ := ![33,34,4,8,16,64,128]
theorem edge2525_span : frame767.space ≤ frame998.space :=
  frame767.inclusion frame998 witness2525 (by decide)
def edge2525 : CertifiedEdge catalog where
  old := 767
  next := 998
  rank := 1
  good := by
    constructor
    · exact edge2525_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2526 : Fin frame768.rank → ℕ := ![129,130,132,136,16,160,192]
theorem edge2526_span : frame768.space ≤ frame919.space :=
  frame768.inclusion frame919 witness2526 (by decide)
def edge2526 : CertifiedEdge catalog where
  old := 768
  next := 919
  rank := 1
  good := by
    constructor
    · exact edge2526_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2527 : Fin frame768.rank → ℕ := ![129,130,132,8,144,160,192]
theorem edge2527_span : frame768.space ≤ frame922.space :=
  frame768.inclusion frame922 witness2527 (by decide)
def edge2527 : CertifiedEdge catalog where
  old := 768
  next := 922
  rank := 1
  good := by
    constructor
    · exact edge2527_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
