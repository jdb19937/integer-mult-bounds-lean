module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness576 : Fin frame93.rank → ℕ := ![9,10,4]
theorem edge576_span : frame93.space ≤ frame95.space :=
  frame93.inclusion frame95 witness576 (by decide)
def edge576 : CertifiedEdge catalog where
  old := 93
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge576_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness577 : Fin frame93.rank → ℕ := ![51,4,8]
theorem edge577_span : frame93.space ≤ frame688.space :=
  frame93.inclusion frame688 witness577 (by decide)
def edge577 : CertifiedEdge catalog where
  old := 93
  next := 688
  rank := 3
  good := by
    constructor
    · exact edge577_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness578 : Fin frame93.rank → ℕ := ![57,34,36]
theorem edge578_span : frame93.space ≤ frame712.space :=
  frame93.inclusion frame712 witness578 (by decide)
def edge578 : CertifiedEdge catalog where
  old := 93
  next := 712
  rank := 3
  good := by
    constructor
    · exact edge578_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness579 : Fin frame94.rank → ℕ := ![1,2,8]
theorem edge579_span : frame94.space ≤ frame95.space :=
  frame94.inclusion frame95 witness579 (by decide)
def edge579 : CertifiedEdge catalog where
  old := 94
  next := 95
  rank := 1
  good := by
    constructor
    · exact edge579_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness580 : Fin frame94.rank → ℕ := ![11,36,48]
theorem edge580_span : frame94.space ≤ frame689.space :=
  frame94.inclusion frame689 witness580 (by decide)
def edge580 : CertifiedEdge catalog where
  old := 94
  next := 689
  rank := 3
  good := by
    constructor
    · exact edge580_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness581 : Fin frame94.rank → ℕ := ![1,18,56]
theorem edge581_span : frame94.space ≤ frame713.space :=
  frame94.inclusion frame713 witness581 (by decide)
def edge581 : CertifiedEdge catalog where
  old := 94
  next := 713
  rank := 3
  good := by
    constructor
    · exact edge581_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness582 : Fin frame95.rank → ℕ := ![19,324,392,224]
theorem edge582_span : frame95.space ≤ frame1.space :=
  frame95.inclusion frame1 witness582 (by decide)
def edge582 : CertifiedEdge catalog where
  old := 95
  next := 1
  rank := 5
  good := by
    constructor
    · exact edge582_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness583 : Fin frame95.rank → ℕ := ![19,196,136,96]
theorem edge583_span : frame95.space ≤ frame415.space :=
  frame95.inclusion frame415 witness583 (by decide)
def edge583 : CertifiedEdge catalog where
  old := 95
  next := 415
  rank := 4
  good := by
    constructor
    · exact edge583_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness584 : Fin frame95.rank → ℕ := ![19,68,136,224]
theorem edge584_span : frame95.space ≤ frame416.space :=
  frame95.inclusion frame416 witness584 (by decide)
def edge584 : CertifiedEdge catalog where
  old := 95
  next := 416
  rank := 4
  good := by
    constructor
    · exact edge584_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness585 : Fin frame95.rank → ℕ := ![19,68,136,224]
theorem edge585_span : frame95.space ≤ frame421.space :=
  frame95.inclusion frame421 witness585 (by decide)
def edge585 : CertifiedEdge catalog where
  old := 95
  next := 421
  rank := 4
  good := by
    constructor
    · exact edge585_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness586 : Fin frame95.rank → ℕ := ![19,132,200,96]
theorem edge586_span : frame95.space ≤ frame422.space :=
  frame95.inclusion frame422 witness586 (by decide)
def edge586 : CertifiedEdge catalog where
  old := 95
  next := 422
  rank := 4
  good := by
    constructor
    · exact edge586_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness587 : Fin frame96.rank → ℕ := ![1]
theorem edge587_span : frame96.space ≤ frame104.space :=
  frame96.inclusion frame104 witness587 (by decide)
def edge587 : CertifiedEdge catalog where
  old := 96
  next := 104
  rank := 1
  good := by
    constructor
    · exact edge587_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness588 : Fin frame96.rank → ℕ := ![2]
theorem edge588_span : frame96.space ≤ frame105.space :=
  frame96.inclusion frame105 witness588 (by decide)
def edge588 : CertifiedEdge catalog where
  old := 96
  next := 105
  rank := 1
  good := by
    constructor
    · exact edge588_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness589 : Fin frame96.rank → ℕ := ![2]
theorem edge589_span : frame96.space ≤ frame106.space :=
  frame96.inclusion frame106 witness589 (by decide)
def edge589 : CertifiedEdge catalog where
  old := 96
  next := 106
  rank := 1
  good := by
    constructor
    · exact edge589_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness590 : Fin frame97.rank → ℕ := ![3]
theorem edge590_span : frame97.space ≤ frame107.space :=
  frame97.inclusion frame107 witness590 (by decide)
def edge590 : CertifiedEdge catalog where
  old := 97
  next := 107
  rank := 1
  good := by
    constructor
    · exact edge590_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness591 : Fin frame97.rank → ℕ := ![1]
theorem edge591_span : frame97.space ≤ frame108.space :=
  frame97.inclusion frame108 witness591 (by decide)
def edge591 : CertifiedEdge catalog where
  old := 97
  next := 108
  rank := 1
  good := by
    constructor
    · exact edge591_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness592 : Fin frame97.rank → ℕ := ![1]
theorem edge592_span : frame97.space ≤ frame109.space :=
  frame97.inclusion frame109 witness592 (by decide)
def edge592 : CertifiedEdge catalog where
  old := 97
  next := 109
  rank := 1
  good := by
    constructor
    · exact edge592_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness593 : Fin frame98.rank → ℕ := ![1]
theorem edge593_span : frame98.space ≤ frame107.space :=
  frame98.inclusion frame107 witness593 (by decide)
def edge593 : CertifiedEdge catalog where
  old := 98
  next := 107
  rank := 1
  good := by
    constructor
    · exact edge593_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness594 : Fin frame98.rank → ℕ := ![1]
theorem edge594_span : frame98.space ≤ frame110.space :=
  frame98.inclusion frame110 witness594 (by decide)
def edge594 : CertifiedEdge catalog where
  old := 98
  next := 110
  rank := 1
  good := by
    constructor
    · exact edge594_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness595 : Fin frame98.rank → ℕ := ![1]
theorem edge595_span : frame98.space ≤ frame111.space :=
  frame98.inclusion frame111 witness595 (by decide)
def edge595 : CertifiedEdge catalog where
  old := 98
  next := 111
  rank := 1
  good := by
    constructor
    · exact edge595_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness596 : Fin frame99.rank → ℕ := ![2]
theorem edge596_span : frame99.space ≤ frame104.space :=
  frame99.inclusion frame104 witness596 (by decide)
def edge596 : CertifiedEdge catalog where
  old := 99
  next := 104
  rank := 1
  good := by
    constructor
    · exact edge596_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness597 : Fin frame99.rank → ℕ := ![2]
theorem edge597_span : frame99.space ≤ frame112.space :=
  frame99.inclusion frame112 witness597 (by decide)
def edge597 : CertifiedEdge catalog where
  old := 99
  next := 112
  rank := 1
  good := by
    constructor
    · exact edge597_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness598 : Fin frame99.rank → ℕ := ![2]
theorem edge598_span : frame99.space ≤ frame113.space :=
  frame99.inclusion frame113 witness598 (by decide)
def edge598 : CertifiedEdge catalog where
  old := 99
  next := 113
  rank := 1
  good := by
    constructor
    · exact edge598_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness599 : Fin frame100.rank → ℕ := ![3]
theorem edge599_span : frame100.space ≤ frame108.space :=
  frame100.inclusion frame108 witness599 (by decide)
def edge599 : CertifiedEdge catalog where
  old := 100
  next := 108
  rank := 1
  good := by
    constructor
    · exact edge599_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness600 : Fin frame100.rank → ℕ := ![3]
theorem edge600_span : frame100.space ≤ frame110.space :=
  frame100.inclusion frame110 witness600 (by decide)
def edge600 : CertifiedEdge catalog where
  old := 100
  next := 110
  rank := 1
  good := by
    constructor
    · exact edge600_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness601 : Fin frame100.rank → ℕ := ![1]
theorem edge601_span : frame100.space ≤ frame114.space :=
  frame100.inclusion frame114 witness601 (by decide)
def edge601 : CertifiedEdge catalog where
  old := 100
  next := 114
  rank := 1
  good := by
    constructor
    · exact edge601_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness602 : Fin frame101.rank → ℕ := ![1]
theorem edge602_span : frame101.space ≤ frame105.space :=
  frame101.inclusion frame105 witness602 (by decide)
def edge602 : CertifiedEdge catalog where
  old := 101
  next := 105
  rank := 1
  good := by
    constructor
    · exact edge602_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness603 : Fin frame101.rank → ℕ := ![3]
theorem edge603_span : frame101.space ≤ frame112.space :=
  frame101.inclusion frame112 witness603 (by decide)
def edge603 : CertifiedEdge catalog where
  old := 101
  next := 112
  rank := 1
  good := by
    constructor
    · exact edge603_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness604 : Fin frame101.rank → ℕ := ![1]
theorem edge604_span : frame101.space ≤ frame115.space :=
  frame101.inclusion frame115 witness604 (by decide)
def edge604 : CertifiedEdge catalog where
  old := 101
  next := 115
  rank := 1
  good := by
    constructor
    · exact edge604_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness605 : Fin frame102.rank → ℕ := ![3]
theorem edge605_span : frame102.space ≤ frame106.space :=
  frame102.inclusion frame106 witness605 (by decide)
def edge605 : CertifiedEdge catalog where
  old := 102
  next := 106
  rank := 1
  good := by
    constructor
    · exact edge605_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness606 : Fin frame102.rank → ℕ := ![1]
theorem edge606_span : frame102.space ≤ frame113.space :=
  frame102.inclusion frame113 witness606 (by decide)
def edge606 : CertifiedEdge catalog where
  old := 102
  next := 113
  rank := 1
  good := by
    constructor
    · exact edge606_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness607 : Fin frame102.rank → ℕ := ![3]
theorem edge607_span : frame102.space ≤ frame115.space :=
  frame102.inclusion frame115 witness607 (by decide)
def edge607 : CertifiedEdge catalog where
  old := 102
  next := 115
  rank := 1
  good := by
    constructor
    · exact edge607_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
