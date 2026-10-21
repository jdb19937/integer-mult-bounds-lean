module

public import IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersShared
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.MetaShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMetadataBudget
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot

/-!
# The stage-2 common preparation

After stage 1's `ArbitraryWidthHighCommonPrepare` and `ArbitraryWidthHighCommonHeaderWiring`, with
the stage-2 row metadata (`MetaShared`) in place of stage 1's: the six shape headers are folded
(`ArbitraryWidthHighFoldHeadersShared`) and the depth, divisor, joined digits `r = Params.r 2 e`,
joined rows and padded rows are built from the width (`constructs`), then erased (`cleans`). The
sources of the high body's banks are read off the output (`exchange_sources`, `dimensions_sources`,
`joined_sources`, `row_cells`, `rounded_cells`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Common
open IntegerMultBounds.Machine
noncomputable section
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources)
variable {a t : ℕ}

def input (caller : Tapes t a) :=
  (caller.append (FixedHeaderBankCopy.empty 16)).append MetaShared.privateInput

def output (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) :=
  (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)).append (MetaShared.privateOutput q d.width)

def program (focus : Fin 6 → Fin t) (q : ℕ) := seq
  (extend (ArbitraryWidthHighFoldHeadersShared.program (a := a) focus) 19)
  (MetaShared.program (Fin.castAdd 16 (focus 3)) q)
def cleanup (focus : Fin 6 → Fin t) := seq
  (MetaShared.cleanup (a := a) (Fin.castAdd 16 (focus 3)))
  (extend (ArbitraryWidthHighFoldHeadersShared.cleanup (a := a) (t := t)) 19)

def setupCost (q : ℕ) (d : Descriptor) :=
  285*volume q d+MetaPrepare.constant q*MetaPrepare.rounded q d.width+1
def cleanupCost (q : ℕ) (d : Descriptor) :=
  45*MetaPrepare.rounded q d.width+109*volume q d+1

theorem constructs (focus : Fin 6 → Fin t) (caller : Tapes t a) (q : ℕ)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hq : 2 ≤ q) (hp : d.Positive)
    (he : 0 < d.width) (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus q) (fun w => w = input caller)
      (fun w => w = output caller d hs q) (setupCost q d) := by
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hfold := hoare_extend_eq
    (ArbitraryWidthHighFoldHeadersShared.constructs focus caller d hs (volume q d) hV hp hv
      (M8.Machine.ArbitraryWidthHighCommonPrepare.prefix_le_volume q d hq hp)
      (RecursiveHeaderBounds.values_le_volume hq d hp) ht hh)
    (MetaShared.privateInput (a := a))
  have hprep := MetaShared.constructs (Fin.castAdd 16 (focus 3))
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)) q d.width hq he (hs 3) (hv.1 3) (hv.2 3)
    (by simpa only [Tapes.append,Fin.addCases_left] using ht 3)
    (by simpa only [Tapes.append,Fin.addCases_left] using hh 3)
  exact (hfold.seq hprep).consequence (fun _ h => h) (fun _ h => h) (by unfold setupCost; omega)

theorem cleans (focus : Fin 6 → Fin t) (caller : Tapes t a) (q : ℕ)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hq : 2 ≤ q) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : caller.tape (focus 3) = RadixZeroFill.encodedBinary (hs 3))
    (hh : caller.head (focus 3) = 1) :
    HoareTime (cleanup focus) (fun w => w = output caller d hs q)
      (fun w => w = input caller) (cleanupCost q d) := by
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hprep := MetaShared.cleans (Fin.castAdd 16 (focus 3))
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)) q d.width hq (hs 3)
    (by simpa only [Tapes.append,Fin.addCases_left] using ht)
    (by simpa only [Tapes.append,Fin.addCases_left] using hh)
  have hfold := hoare_extend_eq
    (ArbitraryWidthHighFoldHeadersShared.cleans caller d hs (volume q d) hV hp hv
      (M8.Machine.ArbitraryWidthHighCommonPrepare.prefix_le_volume q d hq hp)
      (RecursiveHeaderBounds.values_le_volume hq d hp))
    (MetaShared.privateInput (a := a))
  exact (hprep.seq hfold).consequence (fun _ h => h) (fun _ h => h) (by unfold cleanupCost; omega)

/-- The padded rows are at most twice the volume once the joined digits fit the width. -/
theorem rounded_le (d : Descriptor) (hp : d.Positive) (hr : Params.r 2 d.width ≤ d.width) :
    MetaPrepare.rounded prime d.width ≤ 2*volume prime d := by
  rw [MetaPrepare.rounded_eq]
  have h1 := Params.padded_lt 2 d.width
  have h2 : Params.rows 2 d.width ≤ prime^(2*d.width) :=
    Nat.pow_le_pow_right (by have := Params.prime_two; omega) (by omega)
  have h3 := M8.Machine.ArbitraryWidthHighMetadataBudget.volume_lower prime Params.prime_two d hp
  omega

/-- The common preparation and its erasure are linear in the volume. -/
theorem costs_le (d : Descriptor) (hp : d.Positive) (hr : Params.r 2 d.width ≤ d.width) :
    setupCost prime d+cleanupCost prime d ≤ (2*MetaPrepare.constant prime+486)*volume prime d := by
  have h := rounded_le d hp hr
  have hV := RecursiveAffinePrepare.volume_positive Params.prime_two d hp
  have hc := Nat.mul_le_mul_left (MetaPrepare.constant prime) h
  unfold setupCost cleanupCost
  nlinarith

/-! ### The sources of the high body -/

abbrev count (t : ℕ) := (t+16)+19

def originalSlot (i : Fin 6) : Fin (count t) := Fin.castAdd 19 (Fin.natAdd t (Fin.castAdd 10 i))
def foldedSlot (i : Fin 6) : Fin (count t) := Fin.castAdd 19 (Fin.natAdd t (Fin.natAdd 6 (Fin.castAdd 4 i)))
def metadataSlot (i : Fin 5) : Fin (count t) := Fin.natAdd (t+16) (MetaPrepare.slots i)

theorem original_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) (i : Fin 6) :
    (output caller d hs q).head (originalSlot i) = 1 ∧
    (output caller d hs q).tape (originalSlot i) = RadixZeroFill.encodedBinary (hs i) := by
  simpa only [output,originalSlot,Tapes.append,Fin.addCases_left] using
    ArbitraryWidthHighFoldHeadersShared.source_view caller d hs i

theorem folded_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) (i : Fin 6) :
    (output caller d hs q).head (foldedSlot i) = 1 ∧
    (output caller d hs q).tape (foldedSlot i) =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighFoldHeaders.words d hs i) := by
  simpa only [output,foldedSlot,Tapes.append,Fin.addCases_left] using
    ArbitraryWidthHighFoldHeadersShared.target_view caller d hs i

theorem metadata_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) (i : Fin 5) :
    (output caller d hs q).head (metadataSlot i) = 1 ∧
    (output caller d hs q).tape (metadataSlot i) =
      RadixZeroFill.encodedBinary (MetaPrepare.words q d.width i) := by
  simpa only [output,metadataSlot,Tapes.append,Fin.addCases_right] using
    MetaShared.private_output_headers (a := a) q d.width i

def foldedPrefix (d : Descriptor) := d.beforeRows*d.rows*d.beforeH

def rhoWord (d : Descriptor) := MetaPrepare.words prime d.width 2
def rowWord (d : Descriptor) := MetaPrepare.words prime d.width 3
def roundedWord (d : Descriptor) := MetaPrepare.words prime d.width 4

def exchangeFocus : Fin (6+1) → Fin (count t) :=
  Fin.addCases foldedSlot (fun _ => metadataSlot 2)
def dimensionsFocus : Fin 5 → Fin (count t) :=
  ![foldedSlot 0,originalSlot 4,originalSlot 5,originalSlot 3,metadataSlot 2]
def joinedFocus : Fin (5+1) → Fin (count t) :=
  Fin.addCases dimensionsFocus (fun _ => metadataSlot 4)
def rowFocus : Fin (count t) := metadataSlot 3
def roundedFocus : Fin (count t) := metadataSlot 4

def dimensionsWords (d : Descriptor) (hs : Fin 6 → List Bool) : Fin 5 → List Bool :=
  ![ArbitraryWidthHighFoldHeaders.words d hs 0,hs 4,hs 5,hs 3,rhoWord d]
def joinedWords (d : Descriptor) (hs : Fin 6 → List Bool) : Fin (5+1) → List Bool :=
  Fin.addCases (dimensionsWords d hs) (fun _ => roundedWord d)

theorem foldedPrefix_positive (d : Descriptor) (hp : d.Positive) : 0 < foldedPrefix d :=
  Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1

theorem folded_headers (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) :
    RecursiveDimensionBank.Headers
      (ArbitraryWidthHighLayout.originalDescriptor (foldedPrefix d) d.width d.between d.afterD)
      (ArbitraryWidthHighFoldHeaders.words d hs) :=
  ArbitraryWidthHighFoldHeaders.headers d hs hv

theorem exchange_sources (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    Sources (output caller d hs prime) exchangeFocus
      (M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot.exchangeWords
        (ArbitraryWidthHighFoldHeaders.words d hs) (rhoWord d)) := by
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simpa only [exchangeFocus,M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot.exchangeWords,
        Fin.addCases_left] using (folded_view caller d hs prime i).2
    | right i =>
      simpa only [exchangeFocus,M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot.exchangeWords,
        Fin.addCases_right,rhoWord] using (metadata_view caller d hs prime 2).2
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [exchangeFocus,Fin.addCases_left] using (folded_view caller d hs prime i).1
    | right i => simpa only [exchangeFocus,Fin.addCases_right] using (metadata_view caller d hs prime 2).1

theorem dimensions_sources (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    Sources (output caller d hs prime) dimensionsFocus (dimensionsWords d hs) := by
  constructor
  · intro i; fin_cases i
    · exact (folded_view caller d hs prime 0).2
    · exact (original_view caller d hs prime 4).2
    · exact (original_view caller d hs prime 5).2
    · exact (original_view caller d hs prime 3).2
    · exact (metadata_view caller d hs prime 2).2
  · intro i; fin_cases i
    · exact (folded_view caller d hs prime 0).1
    · exact (original_view caller d hs prime 4).1
    · exact (original_view caller d hs prime 5).1
    · exact (original_view caller d hs prime 3).1
    · exact (metadata_view caller d hs prime 2).1

theorem joined_sources (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    Sources (output caller d hs prime) joinedFocus (joinedWords d hs) := by
  have hd := dimensions_sources caller d hs
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [joinedFocus,joinedWords,Fin.addCases_left] using hd.tape i
    | right i =>
      simpa only [joinedFocus,joinedWords,Fin.addCases_right,roundedWord] using
        (metadata_view caller d hs prime 4).2
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [joinedFocus,Fin.addCases_left] using hd.head i
    | right i => simpa only [joinedFocus,Fin.addCases_right] using (metadata_view caller d hs prime 4).1

theorem row_cells (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    (output caller d hs prime).head rowFocus = 1 ∧
    (output caller d hs prime).tape rowFocus = RadixZeroFill.encodedBinary (rowWord d) :=
  metadata_view caller d hs prime 3

theorem rounded_cells (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    (output caller d hs prime).head roundedFocus = 1 ∧
    (output caller d hs prime).tape roundedFocus = RadixZeroFill.encodedBinary (roundedWord d) :=
  metadata_view caller d hs prime 4

theorem rho_value (d : Descriptor) : Counter.value (rhoWord d) = Params.r 2 d.width :=
  (MetaPrepare.words_value prime d.width 2).trans (MetaPrepare.highDepth_eq d.width)

theorem row_value (d : Descriptor) : Counter.value (rowWord d) = prime^(2*Params.r 2 d.width) := by
  rw [← MetaPrepare.highDepth_eq, ArbitraryWidthHighRows.square_power]
  exact MetaPrepare.words_value prime d.width 3

theorem rounded_value (d : Descriptor) : Counter.value (roundedWord d) = Params.padded 2 d.width :=
  (MetaPrepare.words_value prime d.width 4).trans (MetaPrepare.rounded_eq d.width)

theorem rho_canonical (d : Descriptor) : GrowingCounterData.Canonical (rhoWord d) :=
  MetaPrepare.words_canonical prime d.width 2

theorem row_canonical (d : Descriptor) : GrowingCounterData.Canonical (rowWord d) :=
  MetaPrepare.words_canonical prime d.width 3

theorem rounded_canonical (d : Descriptor) : GrowingCounterData.Canonical (roundedWord d) :=
  MetaPrepare.words_canonical prime d.width 4

theorem dimensions_values (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 5) :
    Counter.value (dimensionsWords d hs i) = ArbitraryWidthHighDimensions.originalValues
      (foldedPrefix d) d.between d.afterD d.width (Params.r 2 d.width) i := by
  fin_cases i
  · exact ArbitraryWidthHighPrefix.bits_value d.beforeRows d.rows d.beforeH
  · exact hv.1 4
  · exact hv.1 5
  · exact hv.1 3
  · exact rho_value d

theorem dimensions_canonical (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 5) :
    GrowingCounterData.Canonical (dimensionsWords d hs i) := by
  fin_cases i
  · exact ArbitraryWidthHighPrefix.bits_canonical d.beforeRows d.rows d.beforeH
  · exact hv.2 4
  · exact hv.2 5
  · exact hv.2 3
  · exact rho_canonical d

theorem joined_values (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 6) :
    Counter.value (joinedWords d hs i) = ArbitraryWidthJoinedHeaders.originalValues
      (foldedPrefix d) d.between d.afterD d.width (Params.r 2 d.width) (Params.padded 2 d.width) i := by
  fin_cases i
  · exact ArbitraryWidthHighPrefix.bits_value d.beforeRows d.rows d.beforeH
  · exact hv.1 4
  · exact hv.1 5
  · exact hv.1 3
  · exact rho_value d
  · exact rounded_value d

theorem joined_canonical (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 6) :
    GrowingCounterData.Canonical (joinedWords d hs i) := by
  change Fin (5+1) at i
  induction i using Fin.addCases with
  | left i => simpa only [joinedWords,Fin.addCases_left] using dimensions_canonical d hs hv i
  | right i => simpa only [joinedWords,Fin.addCases_right] using rounded_canonical d

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Common
