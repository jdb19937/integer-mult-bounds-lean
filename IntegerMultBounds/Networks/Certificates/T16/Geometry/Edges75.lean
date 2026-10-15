module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2400 : Fin frame730.rank → ℕ := ![129,130,68,328,272,32]
theorem edge2400_span : frame730.space ≤ frame1.space :=
  frame730.inclusion frame1 witness2400 (by decide)
def edge2400 : CertifiedEdge catalog where
  old := 730
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2400_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2401 : Fin frame730.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2401_span : frame730.space ≤ frame972.space :=
  frame730.inclusion frame972 witness2401 (by decide)
def edge2401 : CertifiedEdge catalog where
  old := 730
  next := 972
  rank := 1
  good := by
    constructor
    · exact edge2401_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2402 : Fin frame730.rank → ℕ := ![1,2,68,72,16,32]
theorem edge2402_span : frame730.space ≤ frame981.space :=
  frame730.inclusion frame981 witness2402 (by decide)
def edge2402 : CertifiedEdge catalog where
  old := 730
  next := 981
  rank := 1
  good := by
    constructor
    · exact edge2402_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2403 : Fin frame731.rank → ℕ := ![129,130,388,136,208,480]
theorem edge2403_span : frame731.space ≤ frame1.space :=
  frame731.inclusion frame1 witness2403 (by decide)
def edge2403 : CertifiedEdge catalog where
  old := 731
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2403_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2404 : Fin frame731.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2404_span : frame731.space ≤ frame973.space :=
  frame731.inclusion frame973 witness2404 (by decide)
def edge2404 : CertifiedEdge catalog where
  old := 731
  next := 973
  rank := 1
  good := by
    constructor
    · exact edge2404_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2405 : Fin frame731.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2405_span : frame731.space ≤ frame980.space :=
  frame731.inclusion frame980 witness2405 (by decide)
def edge2405 : CertifiedEdge catalog where
  old := 731
  next := 980
  rank := 1
  good := by
    constructor
    · exact edge2405_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2406 : Fin frame732.rank → ℕ := ![129,130,100,104,48,256]
theorem edge2406_span : frame732.space ≤ frame1.space :=
  frame732.inclusion frame1 witness2406 (by decide)
def edge2406 : CertifiedEdge catalog where
  old := 732
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2406_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2407 : Fin frame732.rank → ℕ := ![33,34,4,8,16,64]
theorem edge2407_span : frame732.space ≤ frame966.space :=
  frame732.inclusion frame966 witness2407 (by decide)
def edge2407 : CertifiedEdge catalog where
  old := 732
  next := 966
  rank := 1
  good := by
    constructor
    · exact edge2407_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2408 : Fin frame732.rank → ℕ := ![1,2,36,40,16,64]
theorem edge2408_span : frame732.space ≤ frame977.space :=
  frame732.inclusion frame977 witness2408 (by decide)
def edge2408 : CertifiedEdge catalog where
  old := 732
  next := 977
  rank := 1
  good := by
    constructor
    · exact edge2408_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2409 : Fin frame733.rank → ℕ := ![129,130,164,424,304,192]
theorem edge2409_span : frame733.space ≤ frame1.space :=
  frame733.inclusion frame1 witness2409 (by decide)
def edge2409 : CertifiedEdge catalog where
  old := 733
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2409_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2410 : Fin frame733.rank → ℕ := ![65,66,68,72,16,96]
theorem edge2410_span : frame733.space ≤ frame969.space :=
  frame733.inclusion frame969 witness2410 (by decide)
def edge2410 : CertifiedEdge catalog where
  old := 733
  next := 969
  rank := 1
  good := by
    constructor
    · exact edge2410_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2411 : Fin frame733.rank → ℕ := ![65,66,68,72,16,96]
theorem edge2411_span : frame733.space ≤ frame974.space :=
  frame733.inclusion frame974 witness2411 (by decide)
def edge2411 : CertifiedEdge catalog where
  old := 733
  next := 974
  rank := 1
  good := by
    constructor
    · exact edge2411_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2412 : Fin frame734.rank → ℕ := ![3,4,8,16,32]
theorem edge2412_span : frame734.space ≤ frame982.space :=
  frame734.inclusion frame982 witness2412 (by decide)
def edge2412 : CertifiedEdge catalog where
  old := 734
  next := 982
  rank := 1
  good := by
    constructor
    · exact edge2412_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2413 : Fin frame734.rank → ℕ := ![3,4,8,16,32]
theorem edge2413_span : frame734.space ≤ frame990.space :=
  frame734.inclusion frame990 witness2413 (by decide)
def edge2413 : CertifiedEdge catalog where
  old := 734
  next := 990
  rank := 1
  good := by
    constructor
    · exact edge2413_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2414 : Fin frame734.rank → ℕ := ![67,132,8,144,96]
theorem edge2414_span : frame734.space ≤ frame998.space :=
  frame734.inclusion frame998 witness2414 (by decide)
def edge2414 : CertifiedEdge catalog where
  old := 734
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2414_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2415 : Fin frame735.rank → ℕ := ![3,4,8,16,32]
theorem edge2415_span : frame735.space ≤ frame985.space :=
  frame735.inclusion frame985 witness2415 (by decide)
def edge2415 : CertifiedEdge catalog where
  old := 735
  next := 985
  rank := 1
  good := by
    constructor
    · exact edge2415_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2416 : Fin frame735.rank → ℕ := ![3,4,8,16,32]
theorem edge2416_span : frame735.space ≤ frame993.space :=
  frame735.inclusion frame993 witness2416 (by decide)
def edge2416 : CertifiedEdge catalog where
  old := 735
  next := 993
  rank := 1
  good := by
    constructor
    · exact edge2416_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2417 : Fin frame735.rank → ℕ := ![135,8,144,32,64]
theorem edge2417_span : frame735.space ≤ frame998.space :=
  frame735.inclusion frame998 witness2417 (by decide)
def edge2417 : CertifiedEdge catalog where
  old := 735
  next := 998
  rank := 3
  good := by
    constructor
    · exact edge2417_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2418 : Fin frame736.rank → ℕ := ![259,196,264,144,96]
theorem edge2418_span : frame736.space ≤ frame1.space :=
  frame736.inclusion frame1 witness2418 (by decide)
def edge2418 : CertifiedEdge catalog where
  old := 736
  next := 1
  rank := 4
  good := by
    constructor
    · exact edge2418_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2419 : Fin frame736.rank → ℕ := ![3,4,8,16,32]
theorem edge2419_span : frame736.space ≤ frame988.space :=
  frame736.inclusion frame988 witness2419 (by decide)
def edge2419 : CertifiedEdge catalog where
  old := 736
  next := 988
  rank := 1
  good := by
    constructor
    · exact edge2419_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2420 : Fin frame736.rank → ℕ := ![3,4,8,16,32]
theorem edge2420_span : frame736.space ≤ frame996.space :=
  frame736.inclusion frame996 witness2420 (by decide)
def edge2420 : CertifiedEdge catalog where
  old := 736
  next := 996
  rank := 1
  good := by
    constructor
    · exact edge2420_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2421 : Fin frame737.rank → ℕ := ![3,4,8,16,32]
theorem edge2421_span : frame737.space ≤ frame989.space :=
  frame737.inclusion frame989 witness2421 (by decide)
def edge2421 : CertifiedEdge catalog where
  old := 737
  next := 989
  rank := 1
  good := by
    constructor
    · exact edge2421_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2422 : Fin frame737.rank → ℕ := ![3,4,8,16,32]
theorem edge2422_span : frame737.space ≤ frame997.space :=
  frame737.inclusion frame997 witness2422 (by decide)
def edge2422 : CertifiedEdge catalog where
  old := 737
  next := 997
  rank := 1
  good := by
    constructor
    · exact edge2422_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2423 : Fin frame737.rank → ℕ := ![71,8,16,96,128]
theorem edge2423_span : frame737.space ≤ frame999.space :=
  frame737.inclusion frame999 witness2423 (by decide)
def edge2423 : CertifiedEdge catalog where
  old := 737
  next := 999
  rank := 3
  good := by
    constructor
    · exact edge2423_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2424 : Fin frame738.rank → ℕ := ![193,262,264,144,96]
theorem edge2424_span : frame738.space ≤ frame1.space :=
  frame738.inclusion frame1 witness2424 (by decide)
def edge2424 : CertifiedEdge catalog where
  old := 738
  next := 1
  rank := 4
  good := by
    constructor
    · exact edge2424_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2425 : Fin frame738.rank → ℕ := ![1,6,8,16,32]
theorem edge2425_span : frame738.space ≤ frame988.space :=
  frame738.inclusion frame988 witness2425 (by decide)
def edge2425 : CertifiedEdge catalog where
  old := 738
  next := 988
  rank := 1
  good := by
    constructor
    · exact edge2425_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2426 : Fin frame738.rank → ℕ := ![1,34,36,8,16]
theorem edge2426_span : frame738.space ≤ frame997.space :=
  frame738.inclusion frame997 witness2426 (by decide)
def edge2426 : CertifiedEdge catalog where
  old := 738
  next := 997
  rank := 1
  good := by
    constructor
    · exact edge2426_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2427 : Fin frame739.rank → ℕ := ![33,2,36,8,16]
theorem edge2427_span : frame739.space ≤ frame989.space :=
  frame739.inclusion frame989 witness2427 (by decide)
def edge2427 : CertifiedEdge catalog where
  old := 739
  next := 989
  rank := 1
  good := by
    constructor
    · exact edge2427_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2428 : Fin frame739.rank → ℕ := ![5,2,8,16,32]
theorem edge2428_span : frame739.space ≤ frame996.space :=
  frame739.inclusion frame996 witness2428 (by decide)
def edge2428 : CertifiedEdge catalog where
  old := 739
  next := 996
  rank := 1
  good := by
    constructor
    · exact edge2428_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2429 : Fin frame739.rank → ℕ := ![133,66,136,16,96]
theorem edge2429_span : frame739.space ≤ frame999.space :=
  frame739.inclusion frame999 witness2429 (by decide)
def edge2429 : CertifiedEdge catalog where
  old := 739
  next := 999
  rank := 3
  good := by
    constructor
    · exact edge2429_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2430 : Fin frame740.rank → ℕ := ![1,6,8,16,32]
theorem edge2430_span : frame740.space ≤ frame982.space :=
  frame740.inclusion frame982 witness2430 (by decide)
def edge2430 : CertifiedEdge catalog where
  old := 740
  next := 982
  rank := 1
  good := by
    constructor
    · exact edge2430_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2431 : Fin frame740.rank → ℕ := ![1,34,4,8,48]
theorem edge2431_span : frame740.space ≤ frame993.space :=
  frame740.inclusion frame993 witness2431 (by decide)
def edge2431 : CertifiedEdge catalog where
  old := 740
  next := 993
  rank := 1
  good := by
    constructor
    · exact edge2431_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
