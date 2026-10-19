module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePadding
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady

/-! Physical zero padding, full arbitrary-width dispatch, and cropping back
onto the original source. No execution trace is supplied by the caller. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthConsumePlacement (T)

abbrev tapeCount := 12+T

def program := seq
  (seq (extend (RowPaddingConstructedAlphabet.program (a := prime)) T)
    (ArbitraryWidthPaddedPiecePlacement.program (1 : Fin 12)))
  (extend ArbitraryWidthPaddedPiecePadding.cropProgram T)

def bank {v : Descriptor} (x : Fin (volume prime v) → ZMod 2)
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) : Tapes tapeCount prime :=
  (ArbitraryWidthPaddedPiecePadding.input x paddingHeaders).append
    (ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders f p node scalar st frame)

def cost (v : Descriptor) (R' : ℕ) (hs : Fin 6 → List Bool) : ℕ :=
  826*volume prime (withRows v R')+ArbitraryWidthPieceRun.cost (withRows v R') hs+2

/-- Every retained source bit undergoes exactly the unpadded transpose.
The padded working tape, private control banks and heads return to their
initial state, while supplied immutable descriptor words are retained. -/
theorem runs (v : Descriptor) (R' k : ℕ)
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R')
    (hpadding : ArbitraryWidthPaddedPiecePadding.Headers v R' paddingHeaders)
    (hroot : RecursiveDimensionBank.Headers (withRows v R') rootHeaders)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ R')
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free rootHeaders frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = bank x paddingHeaders rootHeaders f p node scalar st frame)
      (fun z => z = bank (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)
        paddingHeaders rootHeaders f p node scalar st frame) (cost v R' rootHeaders) := by
  have hp' : (withRows v R').Positive :=
    ⟨hp.1,lt_of_lt_of_le hp.2.1 hR,hp.2.2⟩
  have hpad := hoare_extend_eq
    (ArbitraryWidthPaddedPiecePadding.pad_hoare v R' paddingHeaders hp hR hpadding x)
    (ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders f p node scalar st frame)
  have hpiece := ArbitraryWidthPaddedPiecePlacement.runs
    (ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) paddingHeaders) (1 : Fin 12)
    (withRows v R') rootHeaders k hp' hroot hwidth hrows
    f p node scalar st ready frame hfree (padArray R' 0 x) rfl rfl
  rw [ArbitraryWidthPaddedPiecePadding.middle_source] at hpiece
  have hcrop := hoare_extend_eq (ArbitraryWidthPaddedPiecePadding.crop_hoare v R' paddingHeaders
    hp hR hpadding (Shared50RecursiveNodeRows.transpose (one_dvd R') (padArray R' 0 x)))
    (ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders f p node scalar st frame)
  rw [cropArray_transpose_padArray] at hcrop
  exact ((hpad.seq hpiece).seq hcrop).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceRun
