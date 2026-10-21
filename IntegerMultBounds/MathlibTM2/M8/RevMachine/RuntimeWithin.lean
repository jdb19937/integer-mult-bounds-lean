module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimeCross
public import IntegerMultBounds.Machine.RecursiveAffineDimensionsClean

/-!
# Within-field views at runtime atom positions

The ordered shifts inside one field (`RecursiveAffineViews.withinH`, `withinD`: an earlier control
atom `j` and a later target atom `i` of the same field) need the views' headers at runtime
positions, as `RuntimeCross` does for cross views. The four powers `q^(j b)`, `q^((i-j-1) b)`,
`q^((m-1-i) b)`, `q^(m b)` come from `RuntimePower` with counters, and four products give the
new spectators; every result is written directly to its handoff slot, the temporary powers and
products are erased, and stage 1's handoff installs the view's six headers (`handoff_hoare`).

`prepares`: from the parent headers and the counters of `w`, `j`, `i - j - 1`, `m - 1 - i`, `m`,
the canonical headers of the view, counters restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimeWithin

open IntegerMultBounds.Machine
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open RuntimeCross (extras big big_setTape stage_power extra_setTape active_setTape slot erase_hoare
  copies copies_hoare)
open RecursiveChildDimensions (bank)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

/-! ### Generic stages -/

theorem bank_fill (hs : Fin 6 → List Bool) (bs rs : List Bool) (ds : Fin 8 → Option (List Bool))
    (k : Fin 8) (xs : List Bool) : bank (q := q) hs bs rs (Function.update ds k (some xs)) =
      setTape (bank hs bs rs ds) (⟨11+k.val, by omega⟩ : Fin 19) (RadixZeroFill.encodedBinary xs) 1 := by
  unfold bank setTape
  fin_cases k <;> apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

private theorem placed_exact {t u n r a cost : ℕ} {M : Program t r a}
    (e : Fin (t+u) ≃ Fin n) (v w : Tapes n a) (small small' : Tapes t a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem product_output (ws ns : List Bool) (N W : ℕ) :
    setTape (DimensionProductDescriptor.input (q := q) ws ns) 1
      (RadixZeroFill.encodedBinary (DimensionProductDescriptor.bits N W)) 1 =
      DimensionProductDescriptor.output ws ns N W := by
  unfold DimensionProductDescriptor.input DimensionProductDescriptor.output setTape
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [Function.update]

/-- One product placed so that its output slot is `e 1`. -/
theorem stage_product (e : Fin (6+41) ≃ Fin 47) (v : Tapes 47 q) (ws ns : List Bool) (N W : ℕ)
    (hW : 0 < W) (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns)
    (ha : Placement.active e v = DimensionProductDescriptor.input ws ns) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) e) (fun x => x = v)
      (fun x => x = setTape v (e (Fin.castAdd 41 1))
        (RadixZeroFill.encodedBinary (DimensionProductDescriptor.bits N W)) 1) (53*(N*W)+28) :=
  placed_exact e _ _ _ _ ha
    (by rw [active_setTape, ha, product_output])
    (extra_setTape e v 1 _ _).symm
    (DimensionProductDescriptor.construct_hoare ws ns N W hW hw hn cw cn)

/-- The handoff from final spectators in slots 15, 17, 18 to the six canonical view headers. -/
theorem handoff_hoare (hs : Fin 6 → List Bool) (bs rs x4 x6 x7 : List Bool) :
    HoareTime (RecursiveChildHeaderHandoff.program q)
      (fun x => x = (bank hs bs rs ![none,none,none,none,some x4,none,some x6,some x7]).append
        (SharedBank.empty 19 q))
      (fun x => x = RecursiveChildHeaderHandoff.canonical ![hs 0,rs,x4,bs,x6,x7])
      (RecursiveChildHeaderHandoff.cost hs ![hs 0,rs,x4,bs,x6,x7]) := by
  have h := RecursiveChildHeaderHandoff.hands_off hs ![hs 0,rs,x4,bs,x6,x7]
    ((bank hs bs rs ![none,none,none,none,some x4,none,some x6,some x7]).append (SharedBank.empty 19 q))
    (by intro z; fin_cases z <;> exact ⟨rfl, rfl⟩) (by intro z; fin_cases z <;> exact ⟨rfl, rfl⟩)
  refine h.consequence (fun _ h => h) (fun x hx => hx.trans ?_) le_rfl
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl

/-! ### Placements and states -/

def powerPlace1 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,11,39,43,44,45,46,2,3,4,5,6,7,8,10,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,40,41,42]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,3,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,4,44,45,46,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def powerPlace2 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,17,40,43,44,45,46,2,3,4,5,6,7,8,10,11,12,13,14,15,16,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,41,42]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,17,18,19,20,21,22,3,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,4,45,46,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def powerPlace3 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,12,41,43,44,45,46,2,3,4,5,6,7,8,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,42]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,17,3,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,4,46,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def powerPlace4 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,13,42,43,44,45,46,2,3,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,17,18,3,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,4,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaceh1 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,15,1,11,2,5,3,4,6,7,8,9,10,12,13,14,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,5,8,9,10,11,12,3,13,14,15,1,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaceh2 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,14,1,7,2,12,3,4,5,6,8,9,10,11,13,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,13,5,14,1,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaceh3 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,16,1,13,2,14,3,4,5,6,7,8,9,10,11,12,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,14,15,3,5,16,1,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaceh4 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,18,1,8,2,16,3,4,5,6,7,9,10,11,12,13,14,15,17,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,8,9,10,3,11,12,13,14,15,16,17,5,18,1,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaced1 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,14,1,13,2,5,3,4,6,7,8,9,10,11,12,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,5,8,9,10,11,12,13,14,3,1,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaced2 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,16,1,7,2,14,3,4,5,6,8,9,10,11,12,13,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,13,14,15,5,16,1,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaced3 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,15,1,11,2,16,3,4,5,6,7,8,9,10,12,13,14,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,3,14,15,16,1,5,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def productPlaced4 : Fin (6+41) ≃ Fin 47 where
  toFun := ![0,18,1,8,2,12,3,4,5,6,7,9,10,11,13,14,15,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  invFun := ![0,2,4,6,7,8,9,10,3,11,12,13,5,14,15,16,17,18,1,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sth1 (_v : Descriptor) (b : ℕ) {m : ℕ} (j _i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),none,none,none,none,none,none,none]

def sth2 (_v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),none,none,none,none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def sth3 (_v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),none,none,none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def sth4 (_v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),none,none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def sth5 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),none,some (DimensionProductDescriptor.bits (v.beforeH) (q^(j.val*b))),none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def sth6 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.between)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(j.val*b))),none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def sth7 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.between)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(j.val*b))),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b))),some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def sth8 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.between)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(j.val*b))),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b))),some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between*q^(m*b)) (v.afterD))]

def std1 (_v : Descriptor) (b : ℕ) {m : ℕ} (j _i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),none,none,none,none,none,none,none]

def std2 (_v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),none,none,none,none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def std3 (_v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),none,none,none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def std4 (_v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),none,none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def std5 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(m*b))),none,none,some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def std6 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(m*b))),none,some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) (v.between)),some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def std7 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(m*b))),some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)*v.between) (q^(j.val*b))),some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) (v.between)),some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),none]

def std8 (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (RadixPowerDescriptor.bits hq (j.val*b)),some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)),some (RadixPowerDescriptor.bits hq (m*b)),some (DimensionProductDescriptor.bits (v.beforeH) (q^(m*b))),some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)*v.between) (q^(j.val*b))),some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) (v.between)),some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b)),some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.afterD))]


/-! ### The construction stages -/

section Stages

variable (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool) (ws : Fin 5 → List Bool)
  (b : ℕ) {m : ℕ} (j i : Fin m)
variable (hb0 : 0 < b) (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
  (hc : ∀ z, GrowingCounterData.Canonical (ws z))
  (h1 : Counter.value (ws 1) = j.val) (h2 : Counter.value (ws 2) = i.val-j.val-1)
  (h3 : Counter.value (ws 3) = m-1-i.val) (h4 : Counter.value (ws 4) = m)
include hb0 hb cb hc


include h1 in
theorem stageh1 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace1)
    (fun x => x = big (bank hs bs rs (RecursiveChildDimensions.ds0)) ws) (fun x => x = big (bank hs bs rs (sth1 hq v b j i)) ws)
    (RuntimePower.cost (q := q) j.val b) := by
  rw [show sth1 hq v b j i = Function.update (RecursiveChildDimensions.ds0) 0 (some (RadixPowerDescriptor.bits hq (j.val*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace1 _ (ws 1) bs j.val b hb0 h1 hb (hc 1) cb (by
    unfold Placement.active powerPlace1 big extras RuntimePower.input RuntimePower.bank bank RecursiveChildDimensions.ds0
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h2 in
theorem stageh2 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace2)
    (fun x => x = big (bank hs bs rs (sth1 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth2 hq v b j i)) ws)
    (RuntimePower.cost (q := q) (i.val-j.val-1) b) := by
  rw [show sth2 hq v b j i = Function.update (sth1 hq v b j i) 6 (some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace2 _ (ws 2) bs (i.val-j.val-1) b hb0 h2 hb (hc 2) cb (by
    unfold Placement.active powerPlace2 big extras RuntimePower.input RuntimePower.bank bank sth1
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h3 in
theorem stageh3 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace3)
    (fun x => x = big (bank hs bs rs (sth2 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth3 hq v b j i)) ws)
    (RuntimePower.cost (q := q) (m-1-i.val) b) := by
  rw [show sth3 hq v b j i = Function.update (sth2 hq v b j i) 1 (some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace3 _ (ws 3) bs (m-1-i.val) b hb0 h3 hb (hc 3) cb (by
    unfold Placement.active powerPlace3 big extras RuntimePower.input RuntimePower.bank bank sth2
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h4 in
theorem stageh4 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace4)
    (fun x => x = big (bank hs bs rs (sth3 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth4 hq v b j i)) ws)
    (RuntimePower.cost (q := q) m b) := by
  rw [show sth4 hq v b j i = Function.update (sth3 hq v b j i) 2 (some (RadixPowerDescriptor.bits hq (m*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace4 _ (ws 4) bs m b hb0 h4 hb (hc 4) cb (by
    unfold Placement.active powerPlace4 big extras RuntimePower.input RuntimePower.bank bank sth3
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem stageh5 (hv : RecursiveDimensionBank.Headers v hs) (_hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh1)
    (fun x => x = big (bank hs bs rs (sth4 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth5 hq v b j i)) ws)
    (53*((v.beforeH)*(q^(j.val*b)))+28) := by
  rw [show sth5 hq v b j i = Function.update (sth4 hq v b j i) 4 (some (DimensionProductDescriptor.bits (v.beforeH) (q^(j.val*b)))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaceh1 _ (RadixPowerDescriptor.bits hq (j.val*b)) (hs 2) (v.beforeH) (q^(j.val*b))
    (pow_pos (by omega) _) (RadixPowerDescriptor.bits_value _ _) (hv.1 2) (RadixPowerDescriptor.bits_canonical _ _) (hv.2 2) (by
    unfold Placement.active productPlaceh1 big extras DimensionProductDescriptor.input bank sth4
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem stageh6 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh2)
    (fun x => x = big (bank hs bs rs (sth5 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth6 hq v b j i)) ws)
    (53*((q^((m-1-i.val)*b))*(v.between))+28) := by
  rw [show sth6 hq v b j i = Function.update (sth5 hq v b j i) 3 (some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.between))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaceh2 _ (hs 4) (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)) (q^((m-1-i.val)*b)) (v.between)
    hvpos.2.2.2.1 (hv.1 4) (RadixPowerDescriptor.bits_value _ _) (hv.2 4) (RadixPowerDescriptor.bits_canonical _ _) (by
    unfold Placement.active productPlaceh2 big extras DimensionProductDescriptor.input bank sth5
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem stageh7 (_hv : RecursiveDimensionBank.Headers v hs) (_hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh3)
    (fun x => x = big (bank hs bs rs (sth6 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth7 hq v b j i)) ws)
    (53*((q^((m-1-i.val)*b)*v.between)*(q^(m*b)))+28) := by
  rw [show sth7 hq v b j i = Function.update (sth6 hq v b j i) 5 (some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b)))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaceh3 _ (RadixPowerDescriptor.bits hq (m*b)) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.between)) (q^((m-1-i.val)*b)*v.between) (q^(m*b))
    (pow_pos (by omega) _) (RadixPowerDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _) (RadixPowerDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _) (by
    unfold Placement.active productPlaceh3 big extras DimensionProductDescriptor.input bank sth6
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem stageh8 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh4)
    (fun x => x = big (bank hs bs rs (sth7 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (sth8 hq v b j i)) ws)
    (53*((q^((m-1-i.val)*b)*v.between*q^(m*b))*(v.afterD))+28) := by
  rw [show sth8 hq v b j i = Function.update (sth7 hq v b j i) 7 (some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between*q^(m*b)) (v.afterD))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaceh4 _ (hs 5) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b))) (q^((m-1-i.val)*b)*v.between*q^(m*b)) (v.afterD)
    hvpos.2.2.2.2 (hv.1 5) (DimensionProductDescriptor.bits_value _ _) (hv.2 5) (DimensionProductDescriptor.bits_canonical _ _) (by
    unfold Placement.active productPlaceh4 big extras DimensionProductDescriptor.input bank sth7
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h1 in
theorem staged1 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace1)
    (fun x => x = big (bank hs bs rs (RecursiveChildDimensions.ds0)) ws) (fun x => x = big (bank hs bs rs (std1 hq v b j i)) ws)
    (RuntimePower.cost (q := q) j.val b) := by
  rw [show std1 hq v b j i = Function.update (RecursiveChildDimensions.ds0) 0 (some (RadixPowerDescriptor.bits hq (j.val*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace1 _ (ws 1) bs j.val b hb0 h1 hb (hc 1) cb (by
    unfold Placement.active powerPlace1 big extras RuntimePower.input RuntimePower.bank bank RecursiveChildDimensions.ds0
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h2 in
theorem staged2 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace2)
    (fun x => x = big (bank hs bs rs (std1 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std2 hq v b j i)) ws)
    (RuntimePower.cost (q := q) (i.val-j.val-1) b) := by
  rw [show std2 hq v b j i = Function.update (std1 hq v b j i) 6 (some (RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace2 _ (ws 2) bs (i.val-j.val-1) b hb0 h2 hb (hc 2) cb (by
    unfold Placement.active powerPlace2 big extras RuntimePower.input RuntimePower.bank bank std1
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h3 in
theorem staged3 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace3)
    (fun x => x = big (bank hs bs rs (std2 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std3 hq v b j i)) ws)
    (RuntimePower.cost (q := q) (m-1-i.val) b) := by
  rw [show std3 hq v b j i = Function.update (std2 hq v b j i) 1 (some (RadixPowerDescriptor.bits hq ((m-1-i.val)*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace3 _ (ws 3) bs (m-1-i.val) b hb0 h3 hb (hc 3) cb (by
    unfold Placement.active powerPlace3 big extras RuntimePower.input RuntimePower.bank bank std2
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h4 in
theorem staged4 : HoareTime (Placement.placed (RuntimePower.program hq) powerPlace4)
    (fun x => x = big (bank hs bs rs (std3 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std4 hq v b j i)) ws)
    (RuntimePower.cost (q := q) m b) := by
  rw [show std4 hq v b j i = Function.update (std3 hq v b j i) 2 (some (RadixPowerDescriptor.bits hq (m*b))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_power hq powerPlace4 _ (ws 4) bs m b hb0 h4 hb (hc 4) cb (by
    unfold Placement.active powerPlace4 big extras RuntimePower.input RuntimePower.bank bank std3
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem staged5 (hv : RecursiveDimensionBank.Headers v hs) (_hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced1)
    (fun x => x = big (bank hs bs rs (std4 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std5 hq v b j i)) ws)
    (53*((v.beforeH)*(q^(m*b)))+28) := by
  rw [show std5 hq v b j i = Function.update (std4 hq v b j i) 3 (some (DimensionProductDescriptor.bits (v.beforeH) (q^(m*b)))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaced1 _ (RadixPowerDescriptor.bits hq (m*b)) (hs 2) (v.beforeH) (q^(m*b))
    (pow_pos (by omega) _) (RadixPowerDescriptor.bits_value _ _) (hv.1 2) (RadixPowerDescriptor.bits_canonical _ _) (hv.2 2) (by
    unfold Placement.active productPlaced1 big extras DimensionProductDescriptor.input bank std4
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem staged6 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced2)
    (fun x => x = big (bank hs bs rs (std5 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std6 hq v b j i)) ws)
    (53*((v.beforeH*q^(m*b))*(v.between))+28) := by
  rw [show std6 hq v b j i = Function.update (std5 hq v b j i) 5 (some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) (v.between))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaced2 _ (hs 4) (DimensionProductDescriptor.bits (v.beforeH) (q^(m*b))) (v.beforeH*q^(m*b)) (v.between)
    hvpos.2.2.2.1 (hv.1 4) (DimensionProductDescriptor.bits_value _ _) (hv.2 4) (DimensionProductDescriptor.bits_canonical _ _) (by
    unfold Placement.active productPlaced2 big extras DimensionProductDescriptor.input bank std5
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem staged7 (_hv : RecursiveDimensionBank.Headers v hs) (_hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced3)
    (fun x => x = big (bank hs bs rs (std6 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std7 hq v b j i)) ws)
    (53*((v.beforeH*q^(m*b)*v.between)*(q^(j.val*b)))+28) := by
  rw [show std7 hq v b j i = Function.update (std6 hq v b j i) 4 (some (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)*v.between) (q^(j.val*b)))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaced3 _ (RadixPowerDescriptor.bits hq (j.val*b)) (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) (v.between)) (v.beforeH*q^(m*b)*v.between) (q^(j.val*b))
    (pow_pos (by omega) _) (RadixPowerDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _) (RadixPowerDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _) (by
    unfold Placement.active productPlaced3 big extras DimensionProductDescriptor.input bank std6
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem staged8 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced4)
    (fun x => x = big (bank hs bs rs (std7 hq v b j i)) ws) (fun x => x = big (bank hs bs rs (std8 hq v b j i)) ws)
    (53*((q^((m-1-i.val)*b))*(v.afterD))+28) := by
  rw [show std8 hq v b j i = Function.update (std7 hq v b j i) 7 (some (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) (v.afterD))) by
    funext z; fin_cases z <;> rfl, bank_fill, big_setTape]
  exact stage_product productPlaced4 _ (hs 5) (RadixPowerDescriptor.bits hq ((m-1-i.val)*b)) (q^((m-1-i.val)*b)) (v.afterD)
    hvpos.2.2.2.2 (hv.1 5) (RadixPowerDescriptor.bits_value _ _) (hv.2 5) (RadixPowerDescriptor.bits_canonical _ _) (by
    unfold Placement.active productPlaced4 big extras DimensionProductDescriptor.input bank std7
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])


end Stages

/-! ### Construction, clean-up and handoff -/

def constructH :=
  seq (seq (seq (seq (seq (seq (seq
    (Placement.placed (RuntimePower.program hq) powerPlace1) (Placement.placed (RuntimePower.program hq) powerPlace2))
      (Placement.placed (RuntimePower.program hq) powerPlace3)) (Placement.placed (RuntimePower.program hq) powerPlace4))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh1))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh2))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh3))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaceh4)

def constructD :=
  seq (seq (seq (seq (seq (seq (seq
    (Placement.placed (RuntimePower.program hq) powerPlace1) (Placement.placed (RuntimePower.program hq) powerPlace2))
      (Placement.placed (RuntimePower.program hq) powerPlace3)) (Placement.placed (RuntimePower.program hq) powerPlace4))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced1))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced2))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced3))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlaced4)

section Composite

variable (v : Descriptor) (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool)
  (b : ℕ) {m : ℕ} (j i : Fin m)

/-- The four power costs. -/
def powerCost : ℕ :=
  RuntimePower.cost (q := q) j.val b+1+RuntimePower.cost (q := q) (i.val-j.val-1) b+1+
    RuntimePower.cost (q := q) (m-1-i.val) b+1+RuntimePower.cost (q := q) m b

/-- The words erased after the construction. -/
def erased (g : RecursiveAffineDimensions.Group) : Fin 5 → List Bool :=
  ![RadixPowerDescriptor.bits hq (j.val*b),RadixPowerDescriptor.bits hq ((m-1-i.val)*b),
    RadixPowerDescriptor.bits hq (m*b),
    match g with
    | .h => DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) v.between
    | .d => DimensionProductDescriptor.bits v.beforeH (q^(m*b)),
    match g with
    | .h => DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b))
    | .d => DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) v.between]

def cleanCost (g : RecursiveAffineDimensions.Group) : ℕ :=
  (2*(erased hq v b j i g 0).length+4)+1+(2*(erased hq v b j i g 1).length+4)+1+
    (2*(erased hq v b j i g 2).length+4)+1+(2*(erased hq v b j i g 3).length+4)+1+
    (2*(erased hq v b j i g 4).length+4)

/-- The view's new beforeH, between and afterD words. -/
def spectators : RecursiveAffineDimensions.Group → Fin 3 → List Bool
  | .h => ![DimensionProductDescriptor.bits v.beforeH (q^(j.val*b)),
      RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b),
      DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between*q^(m*b)) v.afterD]
  | .d => ![DimensionProductDescriptor.bits (v.beforeH*q^(m*b)*v.between) (q^(j.val*b)),
      RadixPowerDescriptor.bits hq ((i.val-j.val-1)*b),
      DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) v.afterD]

/-- The six headers of the view. -/
def headers (g : RecursiveAffineDimensions.Group) : Fin 6 → List Bool :=
  ![hs 0,hs 1,spectators hq v b j i g 0,ws 0,spectators hq v b j i g 1,spectators hq v b j i g 2]

/-- The eight descriptors after the construction. -/
def full (g : RecursiveAffineDimensions.Group) : Fin 8 → Option (List Bool) :=
  ![some (erased hq v b j i g 0),some (erased hq v b j i g 1),some (erased hq v b j i g 2),
    some (erased hq v b j i g 3),some (spectators hq v b j i g 0),some (erased hq v b j i g 4),
    some (spectators hq v b j i g 1),some (spectators hq v b j i g 2)]

/-- The three descriptors handed off. -/
def final (g : RecursiveAffineDimensions.Group) : Fin 8 → Option (List Bool) :=
  ![none,none,none,none,some (spectators hq v b j i g 0),none,
    some (spectators hq v b j i g 1),some (spectators hq v b j i g 2)]

theorem clean_hoare (bs rs : List Bool) (g : RecursiveAffineDimensions.Group) :
    HoareTime (RuntimeCross.clean (q := q)) (fun x => x = big (bank hs bs rs (full hq v b j i g)) ws)
      (fun x => x = big (bank hs bs rs (final hq v b j i g)) ws) (cleanCost hq v b j i g) := by
  let f0 := full hq v b j i g
  let f1 := Function.update f0 0 none
  let f2 := Function.update f1 1 none
  let f3 := Function.update f2 2 none
  let f4 := Function.update f3 3 none
  have e1 := erase_hoare (q := q) hs bs rs f0 ws 0 (erased hq v b j i g 0) rfl
  have e2 := erase_hoare (q := q) hs bs rs f1 ws 1 (erased hq v b j i g 1) rfl
  have e3 := erase_hoare (q := q) hs bs rs f2 ws 2 (erased hq v b j i g 2) rfl
  have e4 := erase_hoare (q := q) hs bs rs f3 ws 3 (erased hq v b j i g 3) rfl
  have e5 := erase_hoare (q := q) hs bs rs f4 ws 5 (erased hq v b j i g 4) rfl
  have he : Function.update f4 5 none = final hq v b j i g := by
    funext z; fin_cases z <;> rfl
  rw [he] at e5
  exact (((e1.seq e2).seq e3).seq e4).seq e5

end Composite

theorem constructH_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ws : Fin 5 → List Bool) (b : ℕ) {m : ℕ} (j i : Fin m) (hb0 : 0 < b)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hc : ∀ z, GrowingCounterData.Canonical (ws z))
    (h1 : Counter.value (ws 1) = j.val) (h2 : Counter.value (ws 2) = i.val-j.val-1)
    (h3 : Counter.value (ws 3) = m-1-i.val) (h4 : Counter.value (ws 4) = m)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    ∃ c, HoareTime (constructH hq) (fun x => x = big (bank hs bs rs RecursiveChildDimensions.ds0) ws)
      (fun x => x = big (bank hs bs rs (full hq v b j i .h)) ws) c ∧
      c = powerCost (q := q) b j i+1+(53*(((v.beforeH)*(q^(j.val*b)))+((q^((m-1-i.val)*b))*(v.between))+((q^((m-1-i.val)*b)*v.between)*(q^(m*b)))+((q^((m-1-i.val)*b)*v.between*q^(m*b))*(v.afterD)))+(28+1+28+1+28+1+28)) := by
  have hf : sth8 hq v b j i = full hq v b j i .h := by funext z; fin_cases z <;> rfl
  have hh := (((((((stageh1 hq v hs bs rs ws b j i hb0 hb cb hc h1).seq (stageh2 hq v hs bs rs ws b j i hb0 hb cb hc h2)).seq (stageh3 hq v hs bs rs ws b j i hb0 hb cb hc h3)).seq (stageh4 hq v hs bs rs ws b j i hb0 hb cb hc h4)).seq
    (stageh5 hq v hs bs rs ws b j i hv hvpos)).seq (stageh6 hq v hs bs rs ws b j i hv hvpos)).seq (stageh7 hq v hs bs rs ws b j i hv hvpos)).seq (stageh8 hq v hs bs rs ws b j i hv hvpos)
  rw [hf] at hh
  exact ⟨_, hh, by unfold powerCost; ring⟩

theorem constructD_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ws : Fin 5 → List Bool) (b : ℕ) {m : ℕ} (j i : Fin m) (hb0 : 0 < b)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hc : ∀ z, GrowingCounterData.Canonical (ws z))
    (h1 : Counter.value (ws 1) = j.val) (h2 : Counter.value (ws 2) = i.val-j.val-1)
    (h3 : Counter.value (ws 3) = m-1-i.val) (h4 : Counter.value (ws 4) = m)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    ∃ c, HoareTime (constructD hq) (fun x => x = big (bank hs bs rs RecursiveChildDimensions.ds0) ws)
      (fun x => x = big (bank hs bs rs (full hq v b j i .d)) ws) c ∧
      c = powerCost (q := q) b j i+1+(53*(((v.beforeH)*(q^(m*b)))+((v.beforeH*q^(m*b))*(v.between))+((v.beforeH*q^(m*b)*v.between)*(q^(j.val*b)))+((q^((m-1-i.val)*b))*(v.afterD)))+(28+1+28+1+28+1+28)) := by
  have hf : std8 hq v b j i = full hq v b j i .d := by funext z; fin_cases z <;> rfl
  have hh := (((((((staged1 hq v hs bs rs ws b j i hb0 hb cb hc h1).seq (staged2 hq v hs bs rs ws b j i hb0 hb cb hc h2)).seq (staged3 hq v hs bs rs ws b j i hb0 hb cb hc h3)).seq (staged4 hq v hs bs rs ws b j i hb0 hb cb hc h4)).seq
    (staged5 hq v hs bs rs ws b j i hv hvpos)).seq (staged6 hq v hs bs rs ws b j i hv hvpos)).seq (staged7 hq v hs bs rs ws b j i hv hvpos)).seq (staged8 hq v hs bs rs ws b j i hv hvpos)
  rw [hf] at hh
  exact ⟨_, hh, by unfold powerCost; ring⟩

/-- The construction of either group. -/
def construct (g : RecursiveAffineDimensions.Group) : type_of% (constructH hq) :=
  match g with
  | .h => constructH hq
  | .d => constructD hq

/-- **The runtime within-field view.** -/
def program (g : RecursiveAffineDimensions.Group) :=
  seq (seq (seq (RuntimeCross.copies (q := q)) (construct hq g)) (RuntimeCross.clean (q := q)))
    (extend (RecursiveChildHeaderHandoff.program q) 9)

theorem headers_spec (v : Descriptor) (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) (b : ℕ)
    {m : ℕ} (j i : Fin m) (g : RecursiveAffineDimensions.Group)
    (hv : RecursiveDimensionBank.Headers v hs) (hb : Counter.value (ws 0) = b)
    (hc : ∀ z, GrowingCounterData.Canonical (ws z)) :
    RecursiveDimensionBank.Headers (RecursiveAffineDimensionsClean.view (q := q) b v j i g)
      (headers hq v hs ws b j i g) := by
  constructor
  · intro z
    cases g <;> fin_cases z <;>
      simp only [headers, spectators, RecursiveAffineDimensionsClean.view, RecursiveDimensionBank.values,
        RecursiveAffineViews.withinH, RecursiveAffineViews.withinD, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue]
    all_goals first | exact hv.1 0 | exact hv.1 1 | exact hb |
      exact DimensionProductDescriptor.bits_value _ _ | exact RadixPowerDescriptor.bits_value _ _
  · intro z
    cases g <;> fin_cases z <;>
      simp only [headers, spectators, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue]
    all_goals first | exact hv.2 0 | exact hv.2 1 | exact hc 0 |
      exact DimensionProductDescriptor.bits_canonical _ _ | exact RadixPowerDescriptor.bits_canonical _ _

/-- **Runtime within-field view preparation.** From the parent headers and the counters of the
atom width `b` and of `j`, `i - j - 1`, `m - 1 - i`, `m` (control `j` before target `i`), the
canonical headers of the within-field view are installed; the counters are restored and every
work tape is blank. -/
theorem prepares (v : Descriptor) (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) (b : ℕ)
    {m : ℕ} (j i : Fin m) (g : RecursiveAffineDimensions.Group) (hb0 : 0 < b)
    (hb : Counter.value (ws 0) = b) (hc : ∀ z, GrowingCounterData.Canonical (ws z))
    (h1 : Counter.value (ws 1) = j.val) (h2 : Counter.value (ws 2) = i.val-j.val-1)
    (h3 : Counter.value (ws 3) = m-1-i.val) (h4 : Counter.value (ws 4) = m)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    RecursiveDimensionBank.Headers (RecursiveAffineDimensionsClean.view (q := q) b v j i g)
        (headers hq v hs ws b j i g) ∧
      ∃ c, HoareTime (program hq g)
        (fun x => x = (RecursiveChildHeaderHandoff.canonical hs).append (RuntimeCross.extras ws))
        (fun x => x = (RecursiveChildHeaderHandoff.canonical (headers hq v hs ws b j i g)).append
          (RuntimeCross.extras ws)) c ∧
        c = (2*(ws 0).length+5+1+(2*(hs 1).length+5))+1+
          (powerCost (q := q) b j i+1+(53*(match g with
            | .h => (v.beforeH*q^(j.val*b))+(q^((m-1-i.val)*b)*v.between)+
                (q^((m-1-i.val)*b)*v.between*q^(m*b))+(q^((m-1-i.val)*b)*v.between*q^(m*b)*v.afterD)
            | .d => (v.beforeH*q^(m*b))+(v.beforeH*q^(m*b)*v.between)+
                (v.beforeH*q^(m*b)*v.between*q^(j.val*b))+(q^((m-1-i.val)*b)*v.afterD))+
            (28+1+28+1+28+1+28)))+1+cleanCost hq v b j i g+1+
          RecursiveChildHeaderHandoff.cost hs (headers hq v hs ws b j i g) := by
  refine ⟨headers_spec hq v hs ws b j i g hv hb hc, ?_⟩
  have hk := FamilyPlacementAlphabet.extend_hoare (handoff_hoare (q := q) hs (ws 0) (hs 1)
    (spectators hq v b j i g 0) (spectators hq v b j i g 1) (spectators hq v b j i g 2)) (RuntimeCross.extras ws)
  have hcl := clean_hoare hq v hs ws b j i (ws 0) (hs 1) g
  cases g with
  | h =>
    obtain ⟨c, hcon, hceq⟩ := constructH_hoare hq v hs (ws 0) (hs 1) ws b j i hb0 hb (hc 0) hc h1 h2 h3 h4 hv hvpos
    refine ⟨_, (((RuntimeCross.copies_hoare hs ws).seq hcon).seq hcl).seq hk, ?_⟩
    rw [hceq]
    rfl
  | d =>
    obtain ⟨c, hcon, hceq⟩ := constructD_hoare hq v hs (ws 0) (hs 1) ws b j i hb0 hb (hc 0) hc h1 h2 h3 h4 hv hvpos
    refine ⟨_, (((RuntimeCross.copies_hoare hs ws).seq hcon).seq hcl).seq hk, ?_⟩
    rw [hceq]
    rfl

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimeWithin
