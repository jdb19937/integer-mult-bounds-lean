module

public import IntegerMultBounds.Schoenhage.DifOppositeRounds
public import IntegerMultBounds.Schoenhage.PrefixRoundMath
public import IntegerMultBounds.Schoenhage.TwistDescriptors
public import IntegerMultBounds.Spec.SimultaneousLayer

/-! The transform drivers' round script (§6 task 6), the words on named tape 6. Each slot
contributes its Hadamard words (`hadWords`): a prefix or top slot the kind word `[false]`, its
block ruler `ones (2r·2^s)` and its pass count `ones D`; a chunk-group slot the kind word `[true]`
and its layer header. Its twist words (`twistWords`) are a unary count followed by the slot's table
words. The forward script runs the slots from the top down, Hadamard words before twist words
(`fwdScript`); the opposite script runs them from slot 0 up, twist words first (`oppScript`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct TwistDescriptors

/-- The chunk group `c` and the bit `ρ` within it of a chunk-group slot `h`. -/
def chunkOf (ℓ K h : ℕ) : ℕ := (h - (ℓ - 1) % K) / K

def rhoOf (ℓ K h : ℕ) : ℕ := (h - (ℓ - 1) % K) % K

/-- The layer header of chunk-group slot `h`, for a transform of length `2^n` over axes `ts` with `ℓ`
slots in groups of `K`, precision `p`, layer parameter `d`, ring degree `r` and record word width
`w`: `S = 2^(cDK)` and `P = 2^n / (S·2^(KD))` for the slot's chunk group `c`. -/
def chunkHdr (p d r w n : ℕ) (ts : List ℕ) (ℓ K h : ℕ) : List Bool :=
  layerHeader p d r ts.length (2 ^ (n - (chunkOf ℓ K h * ts.length * K + K * ts.length)))
    (2 ^ (chunkOf ℓ K h * ts.length * K)) K (rhoOf ℓ K h) w

/-- A slot's Hadamard words. -/
def hadWords (p d r w n : ℕ) (ts : List ℕ) (ℓ K h : ℕ) : List (List Bool) :=
  if h < (ℓ - 1) % K then [[false], ones (2 * r * 2 ^ prefixBase ts.length ℓ K h), ones ts.length]
  else if h < ℓ - 1 then [[true], chunkHdr p d r w n ts ℓ K h]
  else [[false], ones (2 * r * 2 ^ topBase ts.length ℓ K), ones (longs ts ℓ).length]

/-- A slot's twist words: the table's word count in unary, then its words. -/
def twistWords {n : ℕ} (π : BitPerm n) (r : ℕ) (ts : List ℕ) (h : ℕ) : List (List Bool) :=
  ones (tableWords (slotTable π r ts (slotAxes ts h) h)).length ::
    tableWords (slotTable π r ts (slotAxes ts h) h)

/-- The forward round script: slots `ℓ - 1` down to `0`, each Hadamard then twist. -/
def fwdScript (p d r w : ℕ) {n : ℕ} (π : BitPerm n) (ts : List ℕ) (ℓ K : ℕ) : List (List Bool) :=
  (List.range ℓ).reverse.flatMap fun h => hadWords p d r w n ts ℓ K h ++ twistWords π r ts h

/-- The opposite round script: slots `0` up to `ℓ - 1`, each untwist then Hadamard. -/
def oppScript (p d r w : ℕ) {n : ℕ} (π : BitPerm n) (ts : List ℕ) (ℓ K : ℕ) : List (List Bool) :=
  (List.range ℓ).flatMap fun h => twistWords π r ts h ++ hadWords p d r w n ts ℓ K h

end IntegerMultBounds.Schoenhage
