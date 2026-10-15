module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2560 : Fin frame783.rank → ℕ := ![257,258,260,264,16,288,320,128]
theorem edge2560_span : frame783.space ≤ frame1.space :=
  frame783.inclusion frame1 witness2560 (by decide)
def edge2560 : CertifiedEdge catalog where
  old := 783
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2560_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2561 : Fin frame784.rank → ℕ := ![129,130,132,8,144,160,192,256]
theorem edge2561_span : frame784.space ≤ frame1.space :=
  frame784.inclusion frame1 witness2561 (by decide)
def edge2561 : CertifiedEdge catalog where
  old := 784
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2561_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2562 : Fin frame785.rank → ℕ := ![1,2,132,72,16,32]
theorem edge2562_span : frame785.space ≤ frame786.space :=
  frame785.inclusion frame786 witness2562 (by decide)
def edge2562 : CertifiedEdge catalog where
  old := 785
  next := 786
  rank := 2
  good := by
    constructor
    · exact edge2562_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2563 : Fin frame785.rank → ℕ := ![5,6,8,144,32,64]
theorem edge2563_span : frame785.space ≤ frame787.space :=
  frame785.inclusion frame787 witness2563 (by decide)
def edge2563 : CertifiedEdge catalog where
  old := 785
  next := 787
  rank := 2
  good := by
    constructor
    · exact edge2563_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2564 : Fin frame786.rank → ℕ := ![5,6,8,16,32,64,128,256]
theorem edge2564_span : frame786.space ≤ frame1.space :=
  frame786.inclusion frame1 witness2564 (by decide)
def edge2564 : CertifiedEdge catalog where
  old := 786
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2564_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2565 : Fin frame787.rank → ℕ := ![257,258,260,264,272,32,64,384]
theorem edge2565_span : frame787.space ≤ frame1.space :=
  frame787.inclusion frame1 witness2565 (by decide)
def edge2565 : CertifiedEdge catalog where
  old := 787
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2565_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2566 : Fin frame788.rank → ℕ := ![5,6,8,16,96,128]
theorem edge2566_span : frame788.space ≤ frame784.space :=
  frame788.inclusion frame784 witness2566 (by decide)
def edge2566 : CertifiedEdge catalog where
  old := 788
  next := 784
  rank := 2
  good := by
    constructor
    · exact edge2566_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2567 : Fin frame788.rank → ℕ := ![1,2,4,72,48,128]
theorem edge2567_span : frame788.space ≤ frame786.space :=
  frame788.inclusion frame786 witness2567 (by decide)
def edge2567 : CertifiedEdge catalog where
  old := 788
  next := 786
  rank := 2
  good := by
    constructor
    · exact edge2567_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2568 : Fin frame789.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2568_span : frame789.space ≤ frame783.space :=
  frame789.inclusion frame783 witness2568 (by decide)
def edge2568 : CertifiedEdge catalog where
  old := 789
  next := 783
  rank := 2
  good := by
    constructor
    · exact edge2568_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2569 : Fin frame789.rank → ℕ := ![193,194,196,8,144,96]
theorem edge2569_span : frame789.space ≤ frame787.space :=
  frame789.inclusion frame787 witness2569 (by decide)
def edge2569 : CertifiedEdge catalog where
  old := 789
  next := 787
  rank := 2
  good := by
    constructor
    · exact edge2569_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2570 : Fin frame790.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2570_span : frame790.space ≤ frame791.space :=
  frame790.inclusion frame791 witness2570 (by decide)
def edge2570 : CertifiedEdge catalog where
  old := 790
  next := 791
  rank := 1
  good := by
    constructor
    · exact edge2570_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2571 : Fin frame790.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2571_span : frame790.space ≤ frame792.space :=
  frame790.inclusion frame792 witness2571 (by decide)
def edge2571 : CertifiedEdge catalog where
  old := 790
  next := 792
  rank := 1
  good := by
    constructor
    · exact edge2571_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2572 : Fin frame791.rank → ℕ := ![1,258,260,264,272,288,320,128]
theorem edge2572_span : frame791.space ≤ frame1.space :=
  frame791.inclusion frame1 witness2572 (by decide)
def edge2572 : CertifiedEdge catalog where
  old := 791
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2572_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2573 : Fin frame792.rank → ℕ := ![1,258,4,8,16,32,320,128]
theorem edge2573_span : frame792.space ≤ frame1.space :=
  frame792.inclusion frame1 witness2573 (by decide)
def edge2573 : CertifiedEdge catalog where
  old := 792
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2573_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2574 : Fin frame793.rank → ℕ := ![1,18,4,24,32,64,128]
theorem edge2574_span : frame793.space ≤ frame794.space :=
  frame793.inclusion frame794 witness2574 (by decide)
def edge2574 : CertifiedEdge catalog where
  old := 793
  next := 794
  rank := 1
  good := by
    constructor
    · exact edge2574_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2575 : Fin frame793.rank → ℕ := ![1,18,20,8,32,64,128]
theorem edge2575_span : frame793.space ≤ frame795.space :=
  frame793.inclusion frame795 witness2575 (by decide)
def edge2575 : CertifiedEdge catalog where
  old := 793
  next := 795
  rank := 1
  good := by
    constructor
    · exact edge2575_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2576 : Fin frame794.rank → ℕ := ![1,18,20,8,32,64,128,256]
theorem edge2576_span : frame794.space ≤ frame1.space :=
  frame794.inclusion frame1 witness2576 (by decide)
def edge2576 : CertifiedEdge catalog where
  old := 794
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2576_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2577 : Fin frame795.rank → ℕ := ![1,34,4,40,16,64,128,256]
theorem edge2577_span : frame795.space ≤ frame1.space :=
  frame795.inclusion frame1 witness2577 (by decide)
def edge2577 : CertifiedEdge catalog where
  old := 795
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2577_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2578 : Fin frame796.rank → ℕ := ![1,34,4,40,16,64,128]
theorem edge2578_span : frame796.space ≤ frame791.space :=
  frame796.inclusion frame791 witness2578 (by decide)
def edge2578 : CertifiedEdge catalog where
  old := 796
  next := 791
  rank := 1
  good := by
    constructor
    · exact edge2578_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2579 : Fin frame796.rank → ℕ := ![1,2,132,8,144,160,64]
theorem edge2579_span : frame796.space ≤ frame795.space :=
  frame796.inclusion frame795 witness2579 (by decide)
def edge2579 : CertifiedEdge catalog where
  old := 796
  next := 795
  rank := 1
  good := by
    constructor
    · exact edge2579_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2580 : Fin frame797.rank → ℕ := ![1,18,20,8,32,64,128]
theorem edge2580_span : frame797.space ≤ frame792.space :=
  frame797.inclusion frame792 witness2580 (by decide)
def edge2580 : CertifiedEdge catalog where
  old := 797
  next := 792
  rank := 1
  good := by
    constructor
    · exact edge2580_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2581 : Fin frame797.rank → ℕ := ![1,130,4,8,16,160,64]
theorem edge2581_span : frame797.space ≤ frame794.space :=
  frame797.inclusion frame794 witness2581 (by decide)
def edge2581 : CertifiedEdge catalog where
  old := 797
  next := 794
  rank := 1
  good := by
    constructor
    · exact edge2581_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2582 : Fin frame798.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2582_span : frame798.space ≤ frame799.space :=
  frame798.inclusion frame799 witness2582 (by decide)
def edge2582 : CertifiedEdge catalog where
  old := 798
  next := 799
  rank := 1
  good := by
    constructor
    · exact edge2582_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2583 : Fin frame798.rank → ℕ := ![1,2,36,40,48,64,128]
theorem edge2583_span : frame798.space ≤ frame800.space :=
  frame798.inclusion frame800 witness2583 (by decide)
def edge2583 : CertifiedEdge catalog where
  old := 798
  next := 800
  rank := 1
  good := by
    constructor
    · exact edge2583_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2584 : Fin frame799.rank → ℕ := ![257,2,260,264,272,288,320,128]
theorem edge2584_span : frame799.space ≤ frame1.space :=
  frame799.inclusion frame1 witness2584 (by decide)
def edge2584 : CertifiedEdge catalog where
  old := 799
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2584_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2585 : Fin frame800.rank → ℕ := ![257,2,4,8,16,32,320,128]
theorem edge2585_span : frame800.space ≤ frame1.space :=
  frame800.inclusion frame1 witness2585 (by decide)
def edge2585 : CertifiedEdge catalog where
  old := 800
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2585_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2586 : Fin frame801.rank → ℕ := ![17,2,4,24,32,64,128]
theorem edge2586_span : frame801.space ≤ frame802.space :=
  frame801.inclusion frame802 witness2586 (by decide)
def edge2586 : CertifiedEdge catalog where
  old := 801
  next := 802
  rank := 1
  good := by
    constructor
    · exact edge2586_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2587 : Fin frame801.rank → ℕ := ![17,2,20,8,32,64,128]
theorem edge2587_span : frame801.space ≤ frame803.space :=
  frame801.inclusion frame803 witness2587 (by decide)
def edge2587 : CertifiedEdge catalog where
  old := 801
  next := 803
  rank := 1
  good := by
    constructor
    · exact edge2587_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2588 : Fin frame802.rank → ℕ := ![17,2,20,8,32,64,128,256]
theorem edge2588_span : frame802.space ≤ frame1.space :=
  frame802.inclusion frame1 witness2588 (by decide)
def edge2588 : CertifiedEdge catalog where
  old := 802
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2588_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2589 : Fin frame803.rank → ℕ := ![33,2,4,40,16,64,128,256]
theorem edge2589_span : frame803.space ≤ frame1.space :=
  frame803.inclusion frame1 witness2589 (by decide)
def edge2589 : CertifiedEdge catalog where
  old := 803
  next := 1
  rank := 1
  good := by
    constructor
    · exact edge2589_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2590 : Fin frame804.rank → ℕ := ![17,2,20,8,32,64,128]
theorem edge2590_span : frame804.space ≤ frame800.space :=
  frame804.inclusion frame800 witness2590 (by decide)
def edge2590 : CertifiedEdge catalog where
  old := 804
  next := 800
  rank := 1
  good := by
    constructor
    · exact edge2590_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2591 : Fin frame804.rank → ℕ := ![129,2,4,8,16,160,64]
theorem edge2591_span : frame804.space ≤ frame802.space :=
  frame804.inclusion frame802 witness2591 (by decide)
def edge2591 : CertifiedEdge catalog where
  old := 804
  next := 802
  rank := 1
  good := by
    constructor
    · exact edge2591_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
