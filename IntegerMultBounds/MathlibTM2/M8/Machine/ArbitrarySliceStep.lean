module

public import IntegerMultBounds.Machine.SliceOffsetAdvance
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady
public import IntegerMultBounds.MathlibTM2.M8.Machine.RootExecution

/-! One actual piece step executes the selected recursive slice, restores
the parent bank, and physically advances its offset to the next piece. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStep
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (bank data)

def program := seq ArbitrarySliceCall.program
  (SliceOffsetAdvance.program (T := ArbitrarySliceCall.rootCount) (q := prime))

def cost (depth V b : ℕ) (ts bs : List Bool) :=
  RootExecution.rootBudget depth V+1030*V+
    (10*b+2*ts.length+7*bs.length+28)+1

theorem step_hoare (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (ts bs : List Bool) (t b : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) (hw : b = Machine.width^depth)
    (hr : roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun z => z = bank (data x) hs ts bs f p node scalar st frame)
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs
        (GrowingCounterData.advance b ts) bs f p node scalar st frame)
      (cost depth (volume prime v) b ts bs) := by
  have hc := ArbitrarySliceCall.call_hoare depth v hs ts bs t b hp hv ht hb ct cb hfit hw hr
    f p node scalar st ready frame hfree x
  have ha := SliceOffsetAdvance.advances_hoare
    (ArbitrarySliceCall.rootBank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs f p node scalar st)
    ts bs frame b hb
  exact (hc.seq ha).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

omit [Net] in
theorem offset_value (ts : List Bool) (t b : ℕ) (ht : Counter.value ts = t) :
    Counter.value (GrowingCounterData.advance b ts) = t+b := by
  rw [GrowingCounterData.advance_value,ht]

omit [Net] in
theorem offset_canonical (ts : List Bool) (b : ℕ) (ct : GrowingCounterData.Canonical ts) :
    GrowingCounterData.Canonical (GrowingCounterData.advance b ts) :=
  GrowingCounterData.advance_canonical b ts ct

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStep
