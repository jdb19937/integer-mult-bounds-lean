module

public import IntegerMultBounds.Machine.RadixPowerDescriptor
public import IntegerMultBounds.Machine.DimensionProductDescriptor
public import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
public import IntegerMultBounds.Machine.RecursiveDimensionBank

/-!
# Powers with a runtime exponent multiple

`RadixPowerMultipleDescriptor.program k` writes `q^(k b)` from the descriptor of `b`, with `k` a
constant of the program. The stage-2 views place atoms at positions known only at run time, so
here `k` is a descriptor on a tape: the product `k b` is formed (`DimensionProductDescriptor`),
raised (`RadixPowerDescriptor`) and erased. The first four tapes are exactly those of
`RadixPowerMultipleDescriptor` (radix scratch, clock scratch, `b`, output), so the program
replaces it inside any bank (`power_hoare`); the counter `k` and four blank work tapes follow.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimePower

open IntegerMultBounds.Machine
open RecursiveDimensionBank (head tape)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

/-- Radix and clock scratch, `b`, output, `k`, product spare, product, two clocks. -/
def bank (ks bs : List Bool) (x out : Option (List Bool)) : Tapes 9 q :=
  ⟨![0,0,1,head out,1,0,head x,0,0],
   ![fun _ => blank,fun _ => blank,RadixZeroFill.encodedBinary bs,tape out,
     RadixZeroFill.encodedBinary ks,fun _ => blank,tape x,fun _ => blank,fun _ => blank]⟩

def input (ks bs : List Bool) : Tapes 9 q := bank ks bs none none

def output (ks bs : List Bool) (n : ℕ) : Tapes 9 q :=
  bank ks bs none (some (RadixPowerDescriptor.bits hq n))

/-- The product sees the spare, product, clock, `b`, clock and `k` tapes. -/
def productPlacement : Fin (6+3) ≃ Fin 9 where
  toFun := ![5,6,7,2,8,4,0,1,3]
  invFun := ![6,7,3,8,5,0,1,2,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The power sees the two scratch tapes, the product as exponent, and the output. -/
def powerPlacement : Fin (4+5) ≃ Fin 9 where
  toFun := ![0,1,6,3,2,4,5,7,8]
  invFun := ![0,1,4,3,5,6,2,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def program :=
  seq (seq (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlacement)
    (Placement.placed (RadixPowerDescriptor.program hq) powerPlacement))
    (BinaryDescriptorCleanupList.oneProgram (a := q) (6 : Fin 9))

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

/-- The cost of one runtime power. -/
def cost (k b : ℕ) : ℕ :=
  53*(k*b)+28+1+99*q^(k*b)+1+(2*(DimensionProductDescriptor.bits k b).length+4)

theorem power_input (xs : List Bool) : RadixPowerDescriptor.input (q := q) xs =
    ⟨![0,0,1,0],![fun _ => blank,fun _ => blank,RadixZeroFill.encodedBinary xs,fun _ => blank]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem product_hoare (ks bs : List Bool) (k b : ℕ) (hb0 : 0 < b)
    (hk : Counter.value ks = k) (hb : Counter.value bs = b)
    (ck : GrowingCounterData.Canonical ks) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlacement)
      (fun v => v = input ks bs)
      (fun v => v = bank ks bs (some (DimensionProductDescriptor.bits k b)) none) (53*(k*b)+28) :=
  placed_exact productPlacement _ _ _ _
    (by
      unfold Placement.active productPlacement input bank DimensionProductDescriptor.input
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
        simp [Fin.castAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape])
    (by
      unfold Placement.active productPlacement bank DimensionProductDescriptor.output
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
        simp [Fin.castAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape])
    (by
      unfold Placement.extra productPlacement input bank
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
        simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
        norm_num)
    (DimensionProductDescriptor.construct_hoare (q := q) bs ks k b hb0 hb hk cb ck)

theorem raise_hoare (ks bs xs : List Bool) (n : ℕ) (hx : Counter.value xs = n)
    (cx : GrowingCounterData.Canonical xs) :
    HoareTime (Placement.placed (RadixPowerDescriptor.program hq) powerPlacement)
      (fun v => v = bank ks bs (some xs) none)
      (fun v => v = bank ks bs (some xs) (some (RadixPowerDescriptor.bits hq n))) (99*q^n) :=
  placed_exact powerPlacement _ _ _ _
    (by
      rw [power_input]
      unfold Placement.active powerPlacement bank
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
        simp [Fin.castAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape])
    (by
      unfold Placement.active powerPlacement bank RadixPowerDescriptor.output
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
        simp [Fin.castAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape])
    (by
      unfold Placement.extra powerPlacement bank
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
        simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
        norm_num)
    (RadixPowerDescriptor.construct_hoare_linear hq xs n hx cx)

theorem erase_hoare (ks bs xs : List Bool) (n : ℕ) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := q) (6 : Fin 9))
      (fun v => v = bank ks bs (some xs) (some (RadixPowerDescriptor.bits hq n)))
      (fun v => v = output hq ks bs n) (2*xs.length+4) := by
  apply (BinaryDescriptorCleanupList.one_hoare (a := q) (6 : Fin 9)
    (bank ks bs (some xs) (some (RadixPowerDescriptor.bits hq n))) xs
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl).consequence
    (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold output bank SharedPlacementAlphabet.setTape
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [RecursiveDimensionBank.head,RecursiveDimensionBank.tape,Function.update]

/-- **The runtime power.** From `k` and `b`, the canonical descriptor of `q^(k b)` is written
on the output tape; `k`, `b` and every work tape are restored. -/
theorem power_hoare (ks bs : List Bool) (k b : ℕ) (hb0 : 0 < b)
    (hk : Counter.value ks = k) (hb : Counter.value bs = b)
    (ck : GrowingCounterData.Canonical ks) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program hq) (fun v => v = input ks bs) (fun v => v = output hq ks bs (k*b))
      (cost (q := q) k b) :=
  ((product_hoare ks bs k b hb0 hk hb ck cb).seq
    (raise_hoare hq ks bs _ (k*b) (DimensionProductDescriptor.bits_value k b)
      (DimensionProductDescriptor.bits_canonical k b))).seq (erase_hoare hq ks bs _ (k*b))

/-- The cost is linear in the power and the exponent. -/
theorem cost_le (k b : ℕ) : cost (q := q) k b ≤ 155*q^(k*b)+55*(k*b)+40 := by
  have hl := GrowingCounterData.canonical_width (DimensionProductDescriptor.bits k b)
    (DimensionProductDescriptor.bits_canonical k b)
  rw [DimensionProductDescriptor.bits_value] at hl
  have hlog := Nat.log2_le_self (k*b)
  unfold cost
  omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimePower
