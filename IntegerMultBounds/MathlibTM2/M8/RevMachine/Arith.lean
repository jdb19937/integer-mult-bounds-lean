module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Headers
public import IntegerMultBounds.Machine.BinaryDescriptorDivMod
public import IntegerMultBounds.Machine.BinaryDescriptorDifference
public import IntegerMultBounds.Machine.CounterAdvance

/-!
# Runtime arithmetic of a node of the reversed family

A node of `n` atoms on `m` coordinates has `f = n / m` atoms per coordinate and `δ = n % m`
remainder atoms; a block child of rank `r` has `r f` atoms; a sub-view at offset `s` with `c`
atoms leaves `e = n - s - c`. These are placed routines on the optional descriptor bank of
`Headers` (`Headers.bank`, scratch `0..2`):
* `split_hoare`: from `n` and `m`, the quotient and the remainder (`BinaryDescriptorDivMod`);
* `width_hoare`: the child width `r f` (`DimensionProductDescriptor`);
* `difference_hoare`: one difference `x - y` (`BinaryDescriptorDifference`), twice for `e`.
Each leaves its inputs in place and writes one blank slot; the scratch stays blank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Arith

noncomputable section
open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.CounterDimensions (descriptorHead descriptorTape)

variable {q : ℕ}

/-! ### Quotient and remainder -/

/-- The division slots: dividend, divisor, ten scratch tapes with the quotient and remainder at
positions `5, 6`. -/
def divSlots (y d z r : Fin 22) : Fin 14 → Fin 22 :=
  ![y, d, 0, 1, 2, z, r, 13, 14, 15, 16, 17, 18, 19]

def splitAt (y d z r : Fin 22) (h : Function.Injective (divSlots y d z r)) :=
  Placement.placed (BinaryDescriptorDivMod.program q)
    (InjectivePlacement.placement (u := 8) (divSlots y d z r) h (by norm_num))

theorem divmod_input (ys ds : List Bool) :
    (BinaryDescriptorDivMod.input ys ds : Tapes 14 q) =
      ⟨![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![RadixZeroFill.encodedBinary ys, RadixZeroFill.encodedBinary ds, fun _ => blank,
          fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank,
          fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank,
          fun _ => blank]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [BinaryDescriptorDivMod.initial,
      BinaryDescriptorDivisionBoundary.input, BinaryDescriptorDivisionRaw.bank,
      FiniteReturnStack.bank, SharedBank.empty, Tapes.append,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] <;> rfl

theorem divmod_output (ys ds zs rs : List Bool) :
    (BinaryDescriptorDivMod.output ys ds zs rs : Tapes 14 q) =
      ⟨![1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        ![RadixZeroFill.encodedBinary ys, RadixZeroFill.encodedBinary ds, fun _ => blank,
          fun _ => blank, fun _ => blank, RadixZeroFill.encodedBinary zs, RadixZeroFill.encodedBinary rs,
          fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank, fun _ => blank,
          fun _ => blank, fun _ => blank]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [BinaryDescriptorDivMod.retained, BinaryDescriptorDivMod.bank,
      SharedBank.empty, BinaryDescriptorStackRoundtrip.descriptor_encoded] <;> rfl

theorem divSlots_inj : Function.Injective (divSlots 3 4 8 9) := by decide

/-- The node split `f = n / m`, `δ = n % m`: slots `3, 4` to slots `8, 9`. -/
def split := splitAt (q := q) 3 4 8 9 divSlots_inj

/-- **Quotient and remainder.** -/
theorem split_hoare {d : Fin 22 → Option (List Bool)} {ys ds : List Bool}
    (hd0 : 0 < Counter.value ds) (hy : d 3 = some ys) (hdv : d 4 = some ds)
    (hz : d 8 = none) (hr : d 9 = none)
    (hscratch : ∀ i : Fin 22, i ∈ [0, 1, 2, 13, 14, 15, 16, 17, 18, 19] → d i = none) :
    ∃ zs rs : List Bool, GrowingCounterData.Canonical zs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value zs = Counter.value ys / Counter.value ds ∧
      Counter.value rs = Counter.value ys % Counter.value ds ∧
      HoareTime (split (q := q)) (fun v => v = Headers.bank d)
        (fun v => v = Headers.bank (Function.update (Function.update d 8 (some zs)) 9 (some rs)))
        (BinaryDescriptorDivMod.cost ys ds) := by
  obtain ⟨zs, rs, cz, cr, vz, vr, -, -, h⟩ := BinaryDescriptorDivMod.divmod_hoare (a := q) ys ds hd0
  refine ⟨zs, rs, cz, cr, vz, vr, ?_⟩
  have s0 := hscratch 0 (by simp); have s1 := hscratch 1 (by simp); have s2 := hscratch 2 (by simp)
  have s13 := hscratch 13 (by simp); have s14 := hscratch 14 (by simp); have s15 := hscratch 15 (by simp)
  have s16 := hscratch 16 (by simp); have s17 := hscratch 17 (by simp); have s18 := hscratch 18 (by simp)
  have s19 := hscratch 19 (by simp)
  refine Headers.placed_bank _ _ _ ?_ ?_ ?_ h
  · rw [divmod_input]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [divSlots, hy, hdv, hz, hr, s0, s1, s2, s13, s14, s15, s16, s17, s18, s19,
        descriptorHead, descriptorTape]
  · rw [divmod_output]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [divSlots, hy, hdv, s0, s1, s2, s13, s14, s15, s16, s17, s18, s19,
        descriptorHead, descriptorTape]
  · intro j hj
    have h5 : (8 : Fin 22) ≠ j := fun h => hj 5 (by simp [divSlots, h])
    have h6 : (9 : Fin 22) ≠ j := fun h => hj 6 (by simp [divSlots, h])
    rw [Function.update_of_ne h6.symm, Function.update_of_ne h5.symm]

/-! ### The child width -/

/-- The child width `r f`: rank at slot `5`, atoms per coordinate at slot `8`, into slot `10`. -/
def width := Headers.pr (q := q) 8 10 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem width_hoare {d : Fin 22 → Option (List Bool)} {rs fs : List Bool} {r f : ℕ} (hf0 : 0 < f)
    (hrv : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hfv : Counter.value fs = f) (cf : GrowingCounterData.Canonical fs)
    (hr : d 5 = some rs) (hf : d 8 = some fs)
    (h0 : d 0 = none) (h1 : d 1 = none) (h2 : d 2 = none) (ho : d 10 = none) :
    HoareTime (width (q := q)) (fun v => v = Headers.bank d)
      (fun v => v = Headers.bank (Function.update d 10 (some (DimensionProductDescriptor.bits r f))))
      (53*(r*f)+28) :=
  Headers.product_step _ hf0 hrv cr hfv cf hf hr h0 h1 h2 ho

/-! ### Differences -/

def diffSlots (x y o : Fin 22) : Fin 3 → Fin 22 := ![x, y, o]

def diffAt (x y o : Fin 22) (h : Function.Injective (diffSlots x y o)) :=
  Placement.placed (BinaryDescriptorDifference.program (a := q))
    (InjectivePlacement.placement (u := 19) (diffSlots x y o) h (by norm_num))

theorem difference_hoare {d : Fin 22 → Option (List Bool)} {x y o : Fin 22}
    (hinj : Function.Injective (diffSlots x y o)) {xs ys : List Bool}
    (hle : Counter.value ys ≤ Counter.value xs)
    (cx : GrowingCounterData.Canonical xs) (cy : GrowingCounterData.Canonical ys)
    (hx : d x = some xs) (hy : d y = some ys) (ho : d o = none) :
    HoareTime (diffAt (q := q) x y o hinj) (fun v => v = Headers.bank d)
      (fun v => v = Headers.bank (Function.update d o
        (some (RecursiveChildQuotientsConstant.bits (Counter.value xs - Counter.value ys)))))
      (6*Counter.value xs+27) := by
  have ne (i j : Fin 3) (h : i ≠ j) := hinj.ne h
  have hxo : x ≠ o := by simpa [diffSlots] using ne 0 2 (by decide)
  have hyo : y ≠ o := by simpa [diffSlots] using ne 1 2 (by decide)
  refine Headers.placed_bank _ _ _ ?_ ?_ ?_
    (BinaryDescriptorDifference.difference_linear (a := q) xs ys hle cx cy)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [diffSlots, hx, hy, ho, descriptorHead, descriptorTape, CounterAdvance.binary_encoded]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [diffSlots, hx, hy, Function.update_of_ne hxo, Function.update_of_ne hyo, descriptorHead,
        descriptorTape, CounterAdvance.binary_encoded, BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · intro j hj
    exact Function.update_of_ne (fun h => hj 2 (by simp [diffSlots, h])) _ _

/-- The rest `e = n - s - c`: `n` at slot `3`, `s` at `6`, `c` at `7`, `n - s` at `11`, `e` at `12`. -/
def rest :=
  seq (diffAt (q := q) 3 6 11 (by decide)) (diffAt (q := q) 11 7 12 (by decide))

theorem rest_hoare {d : Fin 22 → Option (List Bool)} {ns ss cs : List Bool} {n s c : ℕ}
    (hsc : s + c ≤ n) (hnv : Counter.value ns = n) (hsv : Counter.value ss = s)
    (hcv : Counter.value cs = c) (cn : GrowingCounterData.Canonical ns)
    (csv : GrowingCounterData.Canonical ss) (ccv : GrowingCounterData.Canonical cs)
    (hn : d 3 = some ns) (hs : d 6 = some ss) (hc : d 7 = some cs) (h11 : d 11 = none)
    (h12 : d 12 = none) :
    HoareTime (rest (q := q)) (fun v => v = Headers.bank d)
      (fun v => v = Headers.bank (Function.update (Function.update d 11
        (some (RecursiveChildQuotientsConstant.bits (n - s))))
        12 (some (RecursiveChildQuotientsConstant.bits (n - s - c)))))
      (6*n+27 + 1 + (6*(n-s)+27)) := by
  have h1 := difference_hoare (q := q) (d := d) (x := 3) (y := 6) (o := 11) (by decide)
    (by omega) cn csv hn hs h11
  rw [hnv, hsv] at h1
  have h2 := difference_hoare (q := q) (d := Function.update d 11 (some (RecursiveChildQuotientsConstant.bits (n - s))))
    (x := 11) (y := 7) (o := 12) (by decide) (xs := RecursiveChildQuotientsConstant.bits (n - s)) (ys := cs)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; omega)
    (RecursiveChildQuotientsConstant.bits_canonical _) ccv (by simp)
    (by rw [Function.update_of_ne (by decide)]; exact hc)
    (by rw [Function.update_of_ne (by decide)]; exact h12)
  rw [RecursiveChildQuotientsConstant.bits_value, hcv] at h2
  exact h1.seq h2

end

end IntegerMultBounds.MathlibTM2.M8.RevMachine.Arith
