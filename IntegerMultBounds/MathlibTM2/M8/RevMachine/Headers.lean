module

public import IntegerMultBounds.Machine.CounterDimensions
public import IntegerMultBounds.Machine.RecursiveDimensionBank
public import IntegerMultBounds.Machine.RecursiveAffinePrepare
public import IntegerMultBounds.Machine.BinaryDescriptorInstall
public import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
public import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Views

/-!
# The headers of a sub-view from runtime counters

A call of the reversed family enters the view `RevMachine.sub q w n s c v`: head atoms `[s, s+c)`
against tail atoms `[n-s-c, n-s)`. Its six headers are the parent's `beforeRows` and `rows`,
`beforeH · q^(s w)`, `c w`, `q^(e w) · between · q^(e w)` and `q^(s w) · afterD`, with
`e = n - s - c`. One fixed program (`program`), independent of `n`, `s`, `c` and the atom width
`w`, computes them from the parent headers and the runtime descriptors `w, s, c, e` with placed
power and product routines, installs them over the parent headers and erases every intermediate
(`prepares`). The bank (`bank`) is `22` optional descriptors: three scratch tapes, the six
headers, the four counters and nine outputs. The cost is linear in the parent volume
(`prepares_volume`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Headers

noncomputable section
open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.CounterDimensions (descriptorHead descriptorTape)
open IntegerMultBounds.Machine.RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.Machine.SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.RevMachine

variable {q : ℕ} (hq : 2 ≤ q)

/-- A bank of `22` optional descriptors. -/
def bank (d : Fin 22 → Option (List Bool)) : Tapes 22 q :=
  ⟨fun i => descriptorHead (d i), fun i => descriptorTape q (d i)⟩

theorem bank_update (d : Fin 22 → Option (List Bool)) (j : Fin 22) (x : Option (List Bool)) :
    bank (q := q) (Function.update d j x) =
      setTape (bank d) j (descriptorTape q x) (descriptorHead x) := by
  unfold bank setTape
  congr 1 <;> funext i <;> by_cases h : i = j <;> simp [h, Function.update_of_ne]

/-- A placed routine on the bank changes only its own slots. -/
theorem placed_bank {k r c : ℕ} {M : Program k r q} (slot : Fin k → Fin 22)
    (hinj : Function.Injective slot) (hk : k + (22 - k) = 22)
    {small small' : Tapes k q} {d d' : Fin 22 → Option (List Bool)}
    (hin : (⟨fun i => descriptorHead (d (slot i)), fun i => descriptorTape q (d (slot i))⟩ : Tapes k q) = small)
    (hout : (⟨fun i => descriptorHead (d' (slot i)), fun i => descriptorTape q (d' (slot i))⟩ : Tapes k q) = small')
    (hframe : ∀ j, (∀ i, slot i ≠ j) → d' j = d j)
    (hM : HoareTime M (fun v => v = small) (fun v => v = small') c) :
    HoareTime (Placement.placed M (InjectivePlacement.placement slot hinj hk))
      (fun v => v = bank d) (fun v => v = bank d') c := by
  set e := InjectivePlacement.placement slot hinj hk
  have ha : Placement.active e (bank d) = small := by
    rw [InjectivePlacement.active_bank]; exact hin
  apply (Placement.hoare_at hM e (bank d) ha).consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨w', rfl, rfl⟩
  rw [← hout]
  have hslot (i : Fin k) : e (Fin.castAdd (22 - k) i) = slot i := InjectivePlacement.active_slot _ _ _ i
  have hrest (i : Fin (22 - k)) : d' (e (Fin.natAdd k i)) = d (e (Fin.natAdd k i)) := by
    apply hframe
    intro i₀ h
    rw [← hslot i₀] at h
    have := e.injective h
    have hv := congrArg Fin.val this
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  unfold Placement.replace
  have key (j : Fin 22) :
      (Placement.combine e (⟨fun i => descriptorHead (d' (slot i)),
        fun i => descriptorTape q (d' (slot i))⟩ : Tapes k q) (Placement.extra e (bank d))).head j =
        (bank (q := q) d').head j ∧
      (Placement.combine e (⟨fun i => descriptorHead (d' (slot i)),
        fun i => descriptorTape q (d' (slot i))⟩ : Tapes k q) (Placement.extra e (bank d))).tape j =
        (bank (q := q) d').tape j := by
    obtain ⟨i, rfl⟩ := e.surjective j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Placement.combine_head_active, Placement.combine_tape_active]
      simp [bank, hslot]
    · rw [Placement.combine_head_extra, Placement.combine_tape_extra]
      simp [Placement.extra, bank, hrest]
  exact congrArg₂ Tapes.mk (funext fun j => (key j).1) (funext fun j => (key j).2)

/-! ### The steps -/

/-- The power slots: radix scratch, clock scratch, exponent, output. -/
def powerSlots (e o : Fin 22) : Fin 4 → Fin 22 := ![0, 1, e, o]

/-- The product slots: spare, output, inner clock, inner count, outer clock, outer count. -/
def productSlots (w o m : Fin 22) : Fin 6 → Fin 22 := ![0, o, 1, w, 2, m]

theorem powerSlots_inj (e o : Fin 22) (he : 2 ≤ e.val) (ho : 2 ≤ o.val) (h : e.val ≠ o.val) :
    Function.Injective (powerSlots e o) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> first | rfl | ((simp [powerSlots] at hv) <;> omega)

theorem productSlots_inj (w o m : Fin 22) (hw : 3 ≤ w.val) (ho : 3 ≤ o.val) (hm : 3 ≤ m.val)
    (h₁ : w.val ≠ o.val) (h₂ : w.val ≠ m.val) (h₃ : o.val ≠ m.val) :
    Function.Injective (productSlots w o m) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> first | rfl | ((simp [productSlots] at hv) <;> omega)

def powerAt (e o : Fin 22) (h : Function.Injective (powerSlots e o)) :=
  Placement.placed (RadixPowerDescriptor.program hq)
    (InjectivePlacement.placement (u := 18) (powerSlots e o) h (by norm_num))

def productAt (w o m : Fin 22) (h : Function.Injective (productSlots w o m)) :=
  Placement.placed (DimensionProductDescriptor.program (q := q))
    (InjectivePlacement.placement (u := 16) (productSlots w o m) h (by norm_num))

theorem power_step {d : Fin 22 → Option (List Bool)} {e o : Fin 22} {xs : List Bool} {x : ℕ}
    (hinj : Function.Injective (powerSlots e o))
    (hx : Counter.value xs = x) (cx : GrowingCounterData.Canonical xs)
    (hd : d e = some xs) (h0 : d 0 = none) (h1 : d 1 = none) (ho : d o = none) :
    HoareTime (powerAt hq e o hinj) (fun v => v = bank d)
      (fun v => v = bank (Function.update d o (some (RadixPowerDescriptor.bits hq x)))) (99*q^x) := by
  have he : e ≠ o := fun h => by have := hinj.ne (show (2 : Fin 4) ≠ 3 by decide); simp [powerSlots, h] at this
  have he0 : e ≠ 0 := fun h => by have := hinj.ne (show (2 : Fin 4) ≠ 0 by decide); simp [powerSlots, h] at this
  have he1 : e ≠ 1 := fun h => by have := hinj.ne (show (2 : Fin 4) ≠ 1 by decide); simp [powerSlots, h] at this
  have ho0 : o ≠ 0 := fun h => by have := hinj.ne (show (3 : Fin 4) ≠ 0 by decide); simp [powerSlots, h] at this
  have ho1 : o ≠ 1 := fun h => by have := hinj.ne (show (3 : Fin 4) ≠ 1 by decide); simp [powerSlots, h] at this
  refine placed_bank _ _ _ ?_ ?_ ?_ (RadixPowerDescriptor.construct_hoare_linear hq xs x hx cx)
  · rw [CounterDimensions.power_input]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powerSlots, h0, h1, hd, ho, descriptorHead, descriptorTape]
  · unfold RadixPowerDescriptor.output
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powerSlots, h0, h1, hd, Function.update_of_ne he, Function.update_of_ne ho0.symm,
        Function.update_of_ne ho1.symm, descriptorHead, descriptorTape]
  · intro j hj
    exact Function.update_of_ne (fun h => hj 3 (by simp [powerSlots, h])) _ _

theorem product_step {d : Fin 22 → Option (List Bool)} {w o m : Fin 22} {xs ys : List Bool}
    {x y : ℕ} (hinj : Function.Injective (productSlots w o m)) (hy0 : 0 < y)
    (hx : Counter.value xs = x) (cx : GrowingCounterData.Canonical xs)
    (hy : Counter.value ys = y) (cy : GrowingCounterData.Canonical ys)
    (hdw : d w = some ys) (hdm : d m = some xs)
    (h0 : d 0 = none) (h1 : d 1 = none) (h2 : d 2 = none) (ho : d o = none) :
    HoareTime (productAt (q := q) w o m hinj) (fun v => v = bank d)
      (fun v => v = bank (Function.update d o (some (DimensionProductDescriptor.bits x y))))
      (53*(x*y)+28) := by
  have ne (i j : Fin 6) (h : i ≠ j) := hinj.ne h
  have hwo : w ≠ o := by simpa [productSlots] using ne 3 1 (by decide)
  have hmo : m ≠ o := by simpa [productSlots] using ne 5 1 (by decide)
  have ho0 : o ≠ 0 := by simpa [productSlots] using ne 1 0 (by decide)
  have ho1 : o ≠ 1 := by simpa [productSlots] using ne 1 2 (by decide)
  have ho2 : o ≠ 2 := by simpa [productSlots] using ne 1 4 (by decide)
  refine placed_bank _ _ _ ?_ ?_ ?_
    (DimensionProductDescriptor.construct_hoare ys xs x y hy0 hy hx cy cx)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [productSlots, h0, h1, h2, hdw, hdm, ho, descriptorHead, descriptorTape]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [productSlots, h0, h1, h2, hdw, hdm, Function.update_of_ne hwo, Function.update_of_ne hmo,
        Function.update_of_ne ho0.symm, Function.update_of_ne ho1.symm, Function.update_of_ne ho2.symm,
        descriptorHead, descriptorTape]
  · intro j hj
    exact Function.update_of_ne (fun h => hj 1 (by simp [productSlots, h])) _ _

/-- Erase one descriptor. -/
def eraseAt (j : Fin 22) : Program 22 4 q := BinaryDescriptorCleanupList.oneProgram j

theorem erase_step {d : Fin 22 → Option (List Bool)} {j : Fin 22} {xs : List Bool}
    (hd : d j = some xs) :
    HoareTime (eraseAt (q := q) j) (fun v => v = bank d)
      (fun v => v = bank (Function.update d j none)) (2*xs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare j (bank (q := q) d) xs
    (by simp [bank, hd, descriptorTape, BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by simp [bank, hd, descriptorHead])
  rw [bank_update]
  exact h

/-- Copy one descriptor to a blank slot. -/
def copyAt (src dst : Fin 22) (h : src ≠ dst) : Program 22 5 q :=
  BinaryDescriptorInstall.program q src dst h

theorem copy_step {d : Fin 22 → Option (List Bool)} {src dst : Fin 22} (h : src ≠ dst)
    {xs : List Bool} (hs : d src = some xs) (hd : d dst = none) :
    HoareTime (copyAt (q := q) src dst h) (fun v => v = bank d)
      (fun v => v = bank (Function.update d dst (some xs))) (2*xs.length+5) := by
  have hh := BinaryDescriptorInstall.install_hoare src dst h (bank (q := q) d) xs
    (by simp [bank, hs, descriptorTape]) (by simp [bank, hs, descriptorHead])
    (by simp [bank, hd, descriptorTape]) (by simp [bank, hd, descriptorHead])
  rw [bank_update]
  exact hh

/-! ### The construction -/

/-- Slots `3..8` hold the parent headers, `9..12` the counters `w, s, c, e`. -/
def inputs (hs : Fin 6 → List Bool) (ws ss cs es : List Bool) : Fin 22 → Option (List Bool) :=
  ![none, none, none, some (hs 0), some (hs 1), some (hs 2), some (hs 3), some (hs 4), some (hs 5),
    some ws, some ss, some cs, some es, none, none, none, none, none, none, none, none, none]

/-- The child headers of the view at atom width `w`, offset `s`, count `c` and rest `e`. -/
def childHeaders (v : Descriptor) (hs : Fin 6 → List Bool) (w s c e : ℕ) : Fin 6 → List Bool :=
  ![hs 0, hs 1, DimensionProductDescriptor.bits v.beforeH (q^(s*w)), DimensionProductDescriptor.bits c w,
    DimensionProductDescriptor.bits (q^(e*w)*v.between) (q^(e*w)),
    DimensionProductDescriptor.bits (q^(s*w)) v.afterD]

section Run

variable (v : Descriptor) (hs : Fin 6 → List Bool) (ws ss cs es : List Bool) (w s c e : ℕ)

/-- The descriptor of each arithmetic step. -/
def stepVal : ℕ → List Bool
  | 0 => DimensionProductDescriptor.bits s w
  | 1 => RadixPowerDescriptor.bits hq (s*w)
  | 2 => DimensionProductDescriptor.bits e w
  | 3 => RadixPowerDescriptor.bits hq (e*w)
  | 4 => DimensionProductDescriptor.bits v.beforeH (q^(s*w))
  | 5 => DimensionProductDescriptor.bits c w
  | 6 => DimensionProductDescriptor.bits (q^(e*w)) v.between
  | 7 => DimensionProductDescriptor.bits (q^(e*w)*v.between) (q^(e*w))
  | _ => DimensionProductDescriptor.bits (q^(s*w)) v.afterD

/-- The slot each of the `26` steps writes. -/
def slotOf : ℕ → Fin 22
  | 0 => 13 | 1 => 14 | 2 => 15 | 3 => 16 | 4 => 17 | 5 => 18 | 6 => 19 | 7 => 20 | 8 => 21
  | 9 => 5 | 10 => 6 | 11 => 7 | 12 => 8 | 13 => 5 | 14 => 6 | 15 => 7 | 16 => 8
  | 17 => 13 | 18 => 14 | 19 => 15 | 20 => 16 | 21 => 17 | 22 => 18 | 23 => 19 | 24 => 20 | _ => 21

/-- What each step writes there. -/
def valOf : ℕ → Option (List Bool)
  | 0 => some (stepVal hq v w s c e 0) | 1 => some (stepVal hq v w s c e 1)
  | 2 => some (stepVal hq v w s c e 2) | 3 => some (stepVal hq v w s c e 3)
  | 4 => some (stepVal hq v w s c e 4) | 5 => some (stepVal hq v w s c e 5)
  | 6 => some (stepVal hq v w s c e 6) | 7 => some (stepVal hq v w s c e 7)
  | 8 => some (stepVal hq v w s c e 8)
  | 13 => some (stepVal hq v w s c e 4) | 14 => some (stepVal hq v w s c e 5)
  | 15 => some (stepVal hq v w s c e 7) | 16 => some (stepVal hq v w s c e 8)
  | _ => none

/-- The bank `n` steps after step `k`, from `base`. -/
def afterFrom (base : Fin 22 → Option (List Bool)) (k : ℕ) : ℕ → Fin 22 → Option (List Bool)
  | 0 => base
  | n+1 => Function.update (afterFrom base k n) (slotOf (k+n)) (valOf hq v w s c e (k+n))

/-- After the arithmetic. -/
def mid₁ : Fin 22 → Option (List Bool) :=
  ![none, none, none, some (hs 0), some (hs 1), some (hs 2), some (hs 3), some (hs 4), some (hs 5),
    some ws, some ss, some cs, some es,
    some (stepVal hq v w s c e 0), some (stepVal hq v w s c e 1), some (stepVal hq v w s c e 2),
    some (stepVal hq v w s c e 3), some (stepVal hq v w s c e 4), some (stepVal hq v w s c e 5),
    some (stepVal hq v w s c e 6), some (stepVal hq v w s c e 7), some (stepVal hq v w s c e 8)]

/-- After installing the child headers. -/
def mid₂ : Fin 22 → Option (List Bool) :=
  ![none, none, none, some (hs 0), some (hs 1), some (stepVal hq v w s c e 4),
    some (stepVal hq v w s c e 5), some (stepVal hq v w s c e 7), some (stepVal hq v w s c e 8),
    some ws, some ss, some cs, some es,
    some (stepVal hq v w s c e 0), some (stepVal hq v w s c e 1), some (stepVal hq v w s c e 2),
    some (stepVal hq v w s c e 3), some (stepVal hq v w s c e 4), some (stepVal hq v w s c e 5),
    some (stepVal hq v w s c e 6), some (stepVal hq v w s c e 7), some (stepVal hq v w s c e 8)]

end Run

def pw (e o : Fin 22) (h1 : 2 ≤ e.val) (h2 : 2 ≤ o.val) (h3 : e.val ≠ o.val) :=
  powerAt hq e o (powerSlots_inj e o h1 h2 h3)

def pr (w o m : Fin 22) (h1 : 3 ≤ w.val) (h2 : 3 ≤ o.val) (h3 : 3 ≤ m.val) (h4 : w.val ≠ o.val)
    (h5 : w.val ≠ m.val) (h6 : o.val ≠ m.val) :=
  productAt (q := q) w o m (productSlots_inj w o m h1 h2 h3 h4 h5 h6)

/-- The arithmetic: `s w`, `q^(s w)`, `e w`, `q^(e w)` and the four new headers. -/
def program₁ :=
  seq (seq (seq (seq (seq (seq (seq (seq
    (pr (q := q) 9 13 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (pw hq 13 14 (by decide) (by decide) (by decide)))
    (pr (q := q) 9 15 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    (pw hq 15 16 (by decide) (by decide) (by decide)))
    (pr (q := q) 14 17 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    (pr (q := q) 9 18 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    (pr (q := q) 7 19 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    (pr (q := q) 16 20 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    (pr (q := q) 8 21 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

/-- Replace the four parent headers by the child's. -/
def program₂ :=
  seq (seq (seq (seq (seq (seq (seq (eraseAt (q := q) 5) (eraseAt 6)) (eraseAt 7)) (eraseAt 8))
    (copyAt (q := q) 17 5 (by decide))) (copyAt 18 6 (by decide))) (copyAt 20 7 (by decide)))
    (copyAt 21 8 (by decide))

/-- Erase the nine intermediates. -/
def program₃ :=
  seq (seq (seq (seq (seq (seq (seq (seq (eraseAt (q := q) 13) (eraseAt 14)) (eraseAt 15)) (eraseAt 16))
    (eraseAt 17)) (eraseAt 18)) (eraseAt 19)) (eraseAt 20)) (eraseAt 21)

/-- One fixed program: no header or counter value enters it. -/
def program := seq (seq (program₁ hq) (program₂ (q := q))) (program₃ (q := q))

section Proof

variable {v : Descriptor} {hs : Fin 6 → List Bool} {ws ss cs es : List Bool} {w s c e : ℕ}

local macro "aft" : tactic =>
  `(tactic| simp [afterFrom, slotOf, valOf, stepVal, inputs, mid₁, mid₂, Function.update_apply])

local macro "aft'" : tactic =>
  `(tactic| simp only [afterFrom, slotOf, valOf, mid₁, mid₂, Function.update_apply, Nat.reduceAdd,
    Fin.isValue, Fin.reduceEq, ite_true, ite_false, Matrix.cons_val])

theorem phase₁ (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hw0 : 0 < w)
    (hwv : Counter.value ws = w) (hsv : Counter.value ss = s) (hcv : Counter.value cs = c)
    (hev : Counter.value es = e)
    (cwv : GrowingCounterData.Canonical ws) (csv : GrowingCounterData.Canonical ss)
    (ccv : GrowingCounterData.Canonical cs) (cev : GrowingCounterData.Canonical es) :
    HoareTime (program₁ hq) (fun x => x = bank (inputs hs ws ss cs es))
      (fun x => x = bank (mid₁ hq v hs ws ss cs es w s c e))
      ((53*(s*w)+28) + 99*q^(s*w) + (53*(e*w)+28) + 99*q^(e*w) + (53*(v.beforeH*q^(s*w))+28) +
        (53*(c*w)+28) + (53*(q^(e*w)*v.between)+28) + (53*(q^(e*w)*v.between*q^(e*w))+28) +
        (53*(q^(s*w)*v.afterD)+28) + 8) := by
  obtain ⟨hval, hcan⟩ := hv
  have hb : Counter.value (hs 2) = v.beforeH := hval 2
  have hbt : Counter.value (hs 4) = v.between := hval 4
  have ha : Counter.value (hs 5) = v.afterD := hval 5
  obtain ⟨-, -, -, hC, hE⟩ := hpos
  have hq0 : 0 < q := by omega
  have pv := fun x => RadixPowerDescriptor.bits_value hq x
  have pc := fun x => RadixPowerDescriptor.bits_canonical hq x
  have dv := DimensionProductDescriptor.bits_value
  have dc := DimensionProductDescriptor.bits_canonical
  let A := afterFrom hq v w s c e (inputs hs ws ss cs es) 0
  have s1 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 0)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 1)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 0) (w := 9) (o := 13) (m := 10)
    (productSlots_inj 9 13 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hw0 hsv csv hwv cwv (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have s2 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 1)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 2)) _ :=
    power_step hq (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 1) (x := s*w) (e := 13) (o := 14)
    (powerSlots_inj 13 14 (by decide) (by decide) (by decide)) (dv s w) (dc s w)
    (by aft) (by aft) (by aft) (by aft)
  have s3 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 2)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 3)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 2) (w := 9) (o := 15) (m := 12)
    (productSlots_inj 9 15 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hw0 hev cev hwv cwv (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have s4 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 3)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 4)) _ :=
    power_step hq (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 3) (x := e*w) (e := 15) (o := 16)
    (powerSlots_inj 15 16 (by decide) (by decide) (by decide)) (dv e w) (dc e w)
    (by aft) (by aft) (by aft) (by aft)
  have s5 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 4)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 5)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 4) (w := 14) (o := 17) (m := 5)
    (productSlots_inj 14 17 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (pow_pos hq0 _) hb (hcan 2) (pv _) (pc _) (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have s6 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 5)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 6)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 5) (w := 9) (o := 18) (m := 11)
    (productSlots_inj 9 18 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hw0 hcv ccv hwv cwv (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have s7 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 6)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 7)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 6) (w := 7) (o := 19) (m := 16)
    (productSlots_inj 7 19 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hC (pv _) (pc _) hbt (hcan 4) (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have s8 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 7)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 8)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 7) (w := 16) (o := 20) (m := 19)
    (productSlots_inj 16 20 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (pow_pos hq0 _) (dv _ _) (dc _ _) (pv _) (pc _) (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have s9 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 8)) (fun x => x = bank (afterFrom hq v w s c e (inputs hs ws ss cs es) 0 9)) _ :=
    product_step (q := q) (d := afterFrom hq v w s c e (inputs hs ws ss cs es) 0 8) (w := 8) (o := 21) (m := 14)
    (productSlots_inj 8 21 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hE (pv _) (pc _) ha (hcan 5) (by aft) (by aft) (by aft) (by aft) (by aft) (by aft)
  have hend : afterFrom hq v w s c e (inputs hs ws ss cs es) 0 9 = mid₁ hq v hs ws ss cs es w s c e := by
    funext i; fin_cases i <;> aft
  have h := (((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8).seq s9
  rw [hend] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem phase₂ :
    HoareTime (program₂ (q := q)) (fun x => x = bank (mid₁ hq v hs ws ss cs es w s c e))
      (fun x => x = bank (mid₂ hq v hs ws ss cs es w s c e))
      ((2*(hs 2).length+4) + (2*(hs 3).length+4) + (2*(hs 4).length+4) + (2*(hs 5).length+4) +
        (2*(stepVal hq v w s c e 4).length+5) + (2*(stepVal hq v w s c e 5).length+5) +
        (2*(stepVal hq v w s c e 7).length+5) + (2*(stepVal hq v w s c e 8).length+5) + 7) := by
  have e1 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 0)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 1)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 0) (j := 5) (xs := hs 2) (by aft')
  have e2 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 1)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 2)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 1) (j := 6) (xs := hs 3) (by aft')
  have e3 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 2)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 3)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 2) (j := 7) (xs := hs 4) (by aft')
  have e4 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 3)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 4)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 3) (j := 8) (xs := hs 5) (by aft')
  have c1 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 4)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 5)) _ :=
    copy_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 4) (src := 17) (dst := 5) (by decide) (xs := stepVal hq v w s c e 4) (by aft') (by aft')
  have c2 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 5)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 6)) _ :=
    copy_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 5) (src := 18) (dst := 6) (by decide) (xs := stepVal hq v w s c e 5) (by aft') (by aft')
  have c3 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 6)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 7)) _ :=
    copy_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 6) (src := 20) (dst := 7) (by decide) (xs := stepVal hq v w s c e 7) (by aft') (by aft')
  have c4 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 7)) (fun x => x = bank (afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 8)) _ :=
    copy_step (q := q) (d := afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 7) (src := 21) (dst := 8) (by decide) (xs := stepVal hq v w s c e 8) (by aft') (by aft')
  have hend : afterFrom hq v w s c e (mid₁ hq v hs ws ss cs es w s c e) 9 8 =
      mid₂ hq v hs ws ss cs es w s c e := by
    funext i; fin_cases i <;> rfl
  have h := ((((((e1.seq e2).seq e3).seq e4).seq c1).seq c2).seq c3).seq c4
  rw [hend] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem phase₃ :
    HoareTime (program₃ (q := q)) (fun x => x = bank (mid₂ hq v hs ws ss cs es w s c e))
      (fun x => x = bank (inputs (childHeaders (q := q) v hs w s c e) ws ss cs es))
      ((2*(stepVal hq v w s c e 0).length+4) + (2*(stepVal hq v w s c e 1).length+4) +
        (2*(stepVal hq v w s c e 2).length+4) + (2*(stepVal hq v w s c e 3).length+4) +
        (2*(stepVal hq v w s c e 4).length+4) + (2*(stepVal hq v w s c e 5).length+4) +
        (2*(stepVal hq v w s c e 6).length+4) + (2*(stepVal hq v w s c e 7).length+4) +
        (2*(stepVal hq v w s c e 8).length+4) + 8) := by
  have f1 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 0)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 1)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 0) (j := 13) (xs := stepVal hq v w s c e 0) (by aft')
  have f2 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 1)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 2)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 1) (j := 14) (xs := stepVal hq v w s c e 1) (by aft')
  have f3 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 2)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 3)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 2) (j := 15) (xs := stepVal hq v w s c e 2) (by aft')
  have f4 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 3)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 4)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 3) (j := 16) (xs := stepVal hq v w s c e 3) (by aft')
  have f5 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 4)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 5)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 4) (j := 17) (xs := stepVal hq v w s c e 4) (by aft')
  have f6 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 5)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 6)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 5) (j := 18) (xs := stepVal hq v w s c e 5) (by aft')
  have f7 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 6)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 7)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 6) (j := 19) (xs := stepVal hq v w s c e 6) (by aft')
  have f8 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 7)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 8)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 7) (j := 20) (xs := stepVal hq v w s c e 7) (by aft')
  have f9 : HoareTime _ (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 8)) (fun x => x = bank (afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 9)) _ :=
    erase_step (q := q) (d := afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 8) (j := 21) (xs := stepVal hq v w s c e 8) (by aft')
  have hend : afterFrom hq v w s c e (mid₂ hq v hs ws ss cs es w s c e) 17 9 =
      inputs (childHeaders (q := q) v hs w s c e) ws ss cs es := by
    funext i; fin_cases i <;> rfl
  have h := (((((((f1.seq f2).seq f3).seq f4).seq f5).seq f6).seq f7).seq f8).seq f9
  rw [hend] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The child headers describe the sub-view. -/
theorem child_headers (hv : RecursiveDimensionBank.Headers v hs) {n : ℕ} (he : e = n - s - c) :
    RecursiveDimensionBank.Headers (RevMachine.sub q w n s c v) (childHeaders (q := q) v hs w s c e) := by
  obtain ⟨hval, hcan⟩ := hv
  subst he
  constructor
  · intro i
    have h0 := hval 0
    have h1 := hval 1
    simp only [RecursiveDimensionBank.values] at h0 h1
    fin_cases i <;> simp [childHeaders, RecursiveDimensionBank.values, RevMachine.sub,
      DimensionProductDescriptor.bits_value, h0, h1]
  · intro i
    fin_cases i <;> simp [childHeaders, DimensionProductDescriptor.bits_canonical, hcan 0, hcan 1]

theorem length_le (xs : List Bool) (h : GrowingCounterData.Canonical xs) :
    xs.length ≤ Counter.value xs + 1 := by
  have hw := GrowingCounterData.canonical_width xs h
  have hl := Nat.log2_le_self (Counter.value xs)
  omega

/-- **The sub-view headers in linear time.** From the parent headers and the counters
`w, s, c, e = n - s - c`, the fixed program installs the headers of `sub q w n s c v` and erases
everything it wrote, within `1500` times the parent volume. -/
theorem prepares (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hw0 : 0 < w) {n : ℕ} (hwidth : v.width = n * w) (hsc : s + c ≤ n)
    (he : e = n - s - c)
    (hwv : Counter.value ws = w) (hsv : Counter.value ss = s) (hcv : Counter.value cs = c)
    (hev : Counter.value es = e)
    (cwv : GrowingCounterData.Canonical ws) (csv : GrowingCounterData.Canonical ss)
    (ccv : GrowingCounterData.Canonical cs) (cev : GrowingCounterData.Canonical es) :
    HoareTime (program hq) (fun x => x = bank (inputs hs ws ss cs es))
      (fun x => x = bank (inputs (childHeaders (q := q) v hs w s c e) ws ss cs es))
      (1500 * volume q v) := by
  have h := ((phase₁ hq hv hpos hw0 hwv hsv hcv hev cwv csv ccv cev).seq
    (phase₂ hq (v := v) (hs := hs) (ws := ws) (ss := ss) (cs := cs) (es := es) (w := w) (s := s)
      (c := c) (e := e))).seq
    (phase₃ hq (v := v) (hs := hs) (ws := ws) (ss := ss) (cs := cs) (es := es) (w := w) (s := s)
      (c := c) (e := e))
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  obtain ⟨hA, hR, hB, hC, hE⟩ := hpos
  have hq1 : 1 < q := by omega
  set V := volume q v with hVdef
  set Q := q ^ v.width
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hWQ : v.width ≤ Q := (Nat.lt_pow_self (n := v.width) hq1).le
  have hVQ : v.beforeH * Q * v.between * Q * v.afterD ≤ V := by
    have h1 : 1 ≤ v.beforeRows * v.rows := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc v.beforeH * Q * v.between * Q * v.afterD
        ≤ (v.beforeRows * v.rows) * (v.beforeH * Q * v.between * Q * v.afterD) :=
          Nat.le_mul_of_pos_left _ h1
      _ = V := by rw [hVdef, volume]; ring
  have hsw : s * w ≤ v.width := by rw [hwidth]; exact Nat.mul_le_mul_right w (by omega)
  have hew : e * w ≤ v.width := by rw [hwidth]; exact Nat.mul_le_mul_right w (by omega)
  have hcw : c * w ≤ v.width := by rw [hwidth]; exact Nat.mul_le_mul_right w (by omega)
  have hps : q ^ (s * w) ≤ Q := Nat.pow_le_pow_right (by omega) hsw
  have hpe : q ^ (e * w) ≤ Q := Nat.pow_le_pow_right (by omega) hew
  have hBQ : 0 < v.between * Q * v.afterD := by positivity
  have m1 : v.beforeH * Q ≤ V := le_trans (by
      calc v.beforeH * Q ≤ v.beforeH * Q * (v.between * Q * v.afterD) := Nat.le_mul_of_pos_right _ hBQ
        _ = v.beforeH * Q * v.between * Q * v.afterD := by ring) hVQ
  have hBA : 0 < v.beforeH * v.afterD := by positivity
  have m2 : Q * v.between * Q ≤ V := le_trans (by
      calc Q * v.between * Q ≤ (Q * v.between * Q) * (v.beforeH * v.afterD) := Nat.le_mul_of_pos_right _ hBA
        _ = v.beforeH * Q * v.between * Q * v.afterD := by ring) hVQ
  have hBB : 0 < v.beforeH * Q * v.between := by positivity
  have m3 : Q * v.afterD ≤ V := le_trans (by
      calc Q * v.afterD ≤ (Q * v.afterD) * (v.beforeH * Q * v.between) := Nat.le_mul_of_pos_right _ hBB
        _ = v.beforeH * Q * v.between * Q * v.afterD := by ring) hVQ
  have m4 : Q ≤ V := le_trans (Nat.le_mul_of_pos_right _ hE) m3
  have b1 : v.beforeH * q ^ (s * w) ≤ V := le_trans (Nat.mul_le_mul_left _ hps) m1
  have b2 : q ^ (e * w) * v.between ≤ V := le_trans (by
      calc q ^ (e * w) * v.between ≤ Q * v.between := Nat.mul_le_mul_right _ hpe
        _ ≤ Q * v.between * Q := Nat.le_mul_of_pos_right _ hQ) m2
  have b3 : q ^ (e * w) * v.between * q ^ (e * w) ≤ V := le_trans (by
      have := Nat.mul_le_mul (Nat.mul_le_mul_right v.between hpe) hpe
      exact this) m2
  have b4 : q ^ (s * w) * v.afterD ≤ V := le_trans (Nat.mul_le_mul_right _ hps) m3
  have b5 : q ^ (s * w) ≤ V := hps.trans m4
  have b6 : q ^ (e * w) ≤ V := hpe.trans m4
  have b7 : s * w ≤ V := (hsw.trans hWQ).trans m4
  have b8 : e * w ≤ V := (hew.trans hWQ).trans m4
  have b9 : c * w ≤ V := (hcw.trans hWQ).trans m4
  have hL (i : Fin 6) : (hs i).length ≤ V + 1 := by
    have h1 : (hs i).length ≤ Nat.log2 V + 1 :=
      RecursiveAffinePrepare.header_log hq v ⟨hA, hR, hB, hC, hE⟩ hs hv i
    have h2 := Nat.log2_le_self V
    omega
  have dl (x y : ℕ) (hxy : x * y ≤ V) : (DimensionProductDescriptor.bits x y).length ≤ V + 1 :=
    (length_le _ (DimensionProductDescriptor.bits_canonical x y)).trans (by
      rw [DimensionProductDescriptor.bits_value]; omega)
  have pl (x : ℕ) (hx : q ^ x ≤ V) : (RadixPowerDescriptor.bits hq x).length ≤ V + 1 :=
    (length_le _ (RadixPowerDescriptor.bits_canonical hq x)).trans (by
      rw [RadixPowerDescriptor.bits_value]; omega)
  have l0 : (stepVal hq v w s c e 0).length ≤ V + 1 := dl _ _ b7
  have l1 : (stepVal hq v w s c e 1).length ≤ V + 1 := pl _ b5
  have l2 : (stepVal hq v w s c e 2).length ≤ V + 1 := dl _ _ b8
  have l3 : (stepVal hq v w s c e 3).length ≤ V + 1 := pl _ b6
  have l4 : (stepVal hq v w s c e 4).length ≤ V + 1 := dl _ _ b1
  have l5 : (stepVal hq v w s c e 5).length ≤ V + 1 := dl _ _ b9
  have l6 : (stepVal hq v w s c e 6).length ≤ V + 1 := dl _ _ b2
  have l7 : (stepVal hq v w s c e 7).length ≤ V + 1 := dl _ _ b3
  have l8 : (stepVal hq v w s c e 8).length ≤ V + 1 := dl _ _ b4
  have hV1 : 1 ≤ V := m4.trans' hQ
  have := hL 2; have := hL 3; have := hL 4; have := hL 5
  linarith

end Proof

end

end IntegerMultBounds.MathlibTM2.M8.RevMachine.Headers
