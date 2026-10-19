module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceConsume
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPiecePrefix
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthConsumePlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthLevelPlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady

/-! A concrete fixed digit dispatcher: its body executes actual runtime-counted
slice calls and advances the physical depth and width, with no callback trace
supplied as a hypothesis. Initialization and final control erasure are separate. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecution
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitraryWidthPieceLoop (remaining digit count state emitted)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPiecePrefix (offset images)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (bank data)

def payload (v : Descriptor) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) (x : Fin (volume prime v) → ZMod 2) (i : ℕ) :=
  (bank (data (images Machine.width v.width v i le_rfl x)) hs
    (bits (offset Machine.width v.width i)) (FixedBasePowerStep.bits Machine.width i)
    f p node scalar st frame).append (ArbitraryWidthLevelPlacement.extras Machine.width i)

def consumeCost (v : Descriptor) (i : ℕ) :=
  ArbitraryWidthPieceConsume.cost i (volume prime v) (Machine.width^i) (digit Machine.width v.width i)
    (bits (offset Machine.width v.width i)) (FixedBasePowerStep.bits Machine.width i)
    (bits (digit Machine.width v.width i))

def program := ArbitraryWidthPieceLoop.loop Machine.width ArbitraryWidthPieceConsume.program

theorem dispatches (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0))
      (fun z => z = state Machine.width v.width (count Machine.width v.width)
        (payload v hs f p node scalar st frame x (count Machine.width v.width)))
      (ArbitraryWidthPieceLoop.overheadConstant Machine.width*(v.width+1)+
        ∑ i ∈ Finset.range (count Machine.width v.width), consumeCost v i) := by
  apply ArbitraryWidthPieceLoop.loop_linear Machine.width v.width two_le_width
    ArbitraryWidthPieceConsume.program _ (consumeCost v)
  intro i hi
  have hik := ArbitraryWidthPiecePrefix.selected_depth Machine.width v.width i k two_le_width hi hwidth
  have hr : roleCount^i ∣ v.rows :=
    dvd_trans (pow_dvd_pow roleCount hik) hrows
  have h := ArbitraryWidthPieceConsume.consumes i v hs
    (bits (remaining Machine.width v.width (i+1))) (bits (offset Machine.width v.width i))
    (FixedBasePowerStep.bits Machine.width i) (bits (digit Machine.width v.width i))
    (offset Machine.width v.width i) (Machine.width^i) (digit Machine.width v.width i) hp hv
    (RecursiveChildQuotientsConstant.bits_value _) (FixedBasePowerStep.bits_value _ _)
    (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (FixedBasePowerStep.bits_canonical _ _)
    (ArbitraryWidthPiecePrefix.step_fit _ _ _) rfl hr
    f p node scalar st ready frame hfree (images Machine.width v.width v i le_rfl x)
  rw [ArbitraryWidthPieceConsume.advance_bits,← ArbitraryWidthPiecePrefix.offset_succ,
    ← ArbitraryWidthPiecePrefix.images_succ] at h
  exact h

theorem final_payload (v : Descriptor) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) (x : Fin (volume prime v) → ZMod 2) :
    payload v hs f p node scalar st frame x (count Machine.width v.width) =
      (bank (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs
        (bits v.width) (FixedBasePowerStep.bits Machine.width (count Machine.width v.width))
        f p node scalar st frame).append
          (ArbitraryWidthLevelPlacement.extras Machine.width (count Machine.width v.width)) := by
  unfold payload
  rw [ArbitraryWidthPiecePrefix.offset_count _ _ two_le_width,
    ArbitraryWidthPiecePrefix.images_count _ _ _ two_le_width rfl]

theorem dispatches_full (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0))
      (fun z => z = ArbitraryWidthConsumePlacement.parent (bits 0)
        (bank (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs
          (bits v.width) (FixedBasePowerStep.bits Machine.width (count Machine.width v.width))
          f p node scalar st frame)
        (ArbitraryWidthLevelPlacement.extras Machine.width (count Machine.width v.width)))
      (ArbitraryWidthPieceLoop.overheadConstant Machine.width*(v.width+1)+
        ∑ i ∈ Finset.range (count Machine.width v.width), consumeCost v i) := by
  have h := dispatches v hs k hp hv hwidth hrows f p node scalar st ready frame hfree x
  have hin : state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0) =
      ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0) := by
    simp only [state,payload,remaining,pow_zero,Nat.div_one,
      ArbitraryWidthPiecePrefix.images_zero,ArbitraryWidthPiecePrefix.offset_zero]
    rfl
  rw [hin] at h
  unfold state at h
  rw [ArbitraryWidthPieceLoop.exit _ _ two_le_width,final_payload] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecution
