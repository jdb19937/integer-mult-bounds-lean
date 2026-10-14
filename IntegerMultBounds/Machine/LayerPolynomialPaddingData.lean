module

public import IntegerMultBounds.Machine.NativePolynomialPadding
public import IntegerMultBounds.Machine.LayerPolynomialPaddingHeaders

@[expose] public section
namespace IntegerMultBounds.Machine.LayerPolynomialPaddingData
noncomputable section
open Spec.SignedRingProduct (Rec)
variable {coefficientCount : ℕ}

def widenedPair (width : ℕ) (pair : ChirpPublicArray.Pair) : ChirpConjugateArray.Pair :=
  (NativeSignExtend.extended (ChirpPublicCodec.nativeWord pair.1) width,
    NativeSignExtend.extended (ChirpPublicCodec.nativeWord pair.2) width)
def coefficients (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) :=
  (ChirpPublicArray.publicPairs wordWidth polynomial.1 polynomial.2).map (widenedPair nativeWidth)
def group (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) :=
  ChirpConjugateArray.native (coefficients wordWidth nativeWidth polynomial)
def groups (wordWidth nativeWidth : ℕ) (polynomials : List (Rec coefficientCount)) :=
  polynomials.map (group wordWidth nativeWidth)
def paddedCoefficients (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) :=
  coefficients wordWidth nativeWidth polynomial++
    List.replicate (LayerPolynomialPaddingHeaders.deficit coefficientCount) (NativeZeroRecord.coefficient nativeWidth)

private theorem native_pair_fields (pairs : List ChirpPublicArray.Pair) (nativeWidth : ℕ) :
    NativeSignExtendArray.widened
      (pairs.flatMap fun pair => [ChirpPublicCodec.nativeWord pair.1, ChirpPublicCodec.nativeWord pair.2]) nativeWidth =
      ChirpConjugateArray.native (pairs.map (widenedPair nativeWidth)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
    simpa [NativeSignExtendArray.widened, NativeSignExtendArray.native, ChirpConjugateArray.native,
      widenedPair, DelimitedRadixRecord.complex] using inductionHypothesis

theorem group_widened (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) :
    group wordWidth nativeWidth polynomial =
      NativeSignExtendArray.widened (LayerGuardedInput.fields wordWidth [polynomial]) nativeWidth := by
  simpa [group, coefficients, LayerGuardedInput.fields, LayerNativeInput.publicPairs] using
    (native_pair_fields (ChirpPublicArray.publicPairs wordWidth polynomial.1 polynomial.2) nativeWidth).symm

theorem groups_widened (wordWidth nativeWidth : ℕ) (polynomials : List (Rec coefficientCount)) :
    (groups wordWidth nativeWidth polynomials).flatten =
      NativeSignExtendArray.widened (LayerGuardedInput.fields wordWidth polynomials) nativeWidth := by
  induction polynomials with
  | nil => rfl
  | cons polynomial rest inductionHypothesis =>
    rw [groups, List.map_cons, List.flatten_cons, group_widened]
    change NativeSignExtendArray.widened (LayerGuardedInput.fields wordWidth [polynomial]) nativeWidth++
      (groups wordWidth nativeWidth rest).flatten = _
    rw [inductionHypothesis]
    simp [LayerGuardedInput.fields, LayerNativeInput.publicPairs, NativeSignExtendArray.widened, NativeSignExtendArray.native]

theorem coefficient_widths (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount)
    (widthFits : wordWidth ≤ nativeWidth) :
    ∀ pair ∈ coefficients wordWidth nativeWidth polynomial, pair.1.length = nativeWidth ∧ pair.2.length = nativeWidth := by
  intro pair member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨coordinate, _, rfl⟩ := List.mem_map.mp originalMember
  constructor <;> apply NativeSignExtend.extended_length <;> simpa [ChirpPublicCodec.native_length] using widthFits

theorem coefficient_count (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) :
    (coefficients wordWidth nativeWidth polynomial).length = coefficientCount := by
  simp [coefficients, ChirpPublicArray.publicPairs]

private theorem native_length (pairs : List ChirpConjugateArray.Pair) (nativeWidth : ℕ)
    (pairWidths : ∀ pair ∈ pairs, pair.1.length = nativeWidth ∧ pair.2.length = nativeWidth) :
    (ChirpConjugateArray.native pairs).length = 2*pairs.length*(nativeWidth+1) := by
  induction pairs with
  | nil => simp [ChirpConjugateArray.native]
  | cons pair rest inductionHypothesis =>
    have widths := pairWidths pair (by simp)
    have restLength := inductionHypothesis (fun next member => pairWidths next (List.mem_cons_of_mem pair member))
    simp only [ChirpConjugateArray.native, List.flatMap_cons, List.length_append,
      DelimitedRadixRecord.complex_length _ _ nativeWidth widths.1 widths.2, List.length_cons] at *
    nlinarith

theorem group_length (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) (widthFits : wordWidth ≤ nativeWidth) :
    (group wordWidth nativeWidth polynomial).length = LayerPolynomialPaddingHeaders.span coefficientCount nativeWidth := by
  rw [group, native_length _ nativeWidth (coefficient_widths wordWidth nativeWidth polynomial widthFits), coefficient_count]
  rfl

theorem groups_nonblank (wordWidth nativeWidth : ℕ) (polynomials : List (Rec coefficientCount)) :
    ∀ groupWord ∈ groups wordWidth nativeWidth polynomials, ∀ symbol ∈ groupWord, symbol ≠ (blank : Fin 6) := by
  intro groupWord member symbol symbolMember
  obtain ⟨polynomial, _, rfl⟩ := List.mem_map.mp member
  rw [group_widened] at symbolMember
  exact LayerNativeWidening.native_nonblank _ symbol symbolMember

theorem padded_word (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) :
    ChirpConjugateArray.native (paddedCoefficients wordWidth nativeWidth polynomial) =
      group wordWidth nativeWidth polynomial++
        NativeZeroStream.records nativeWidth (LayerPolynomialPaddingHeaders.deficit coefficientCount) := by
  unfold paddedCoefficients group ChirpConjugateArray.native NativeZeroStream.records NativeZeroRecord.word
  rw [List.flatMap_append]
  congr 1
  generalize LayerPolynomialPaddingHeaders.deficit coefficientCount = deficit
  induction deficit with
  | zero => rfl
  | succ deficit inductionHypothesis =>
    simpa [List.replicate_succ, ButterflyStreamData.encoded] using
      congrArg (fun rest => DelimitedRadixRecord.complex (NativeZeroRecord.coefficient nativeWidth).1
        (NativeZeroRecord.coefficient nativeWidth).2++rest) inductionHypothesis

theorem padded_count (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) (countPositive : 0 < coefficientCount) :
    (paddedCoefficients wordWidth nativeWidth polynomial).length = LayerPolynomialHeaders.paddedCount coefficientCount := by
  have paddingFits := (LayerPolynomialHeaders.padded_bounds coefficientCount countPositive).1
  simp only [paddedCoefficients, List.length_append, coefficient_count, List.length_replicate,
    LayerPolynomialPaddingHeaders.deficit]
  omega

theorem padded_widths (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount) (widthFits : wordWidth ≤ nativeWidth) :
    ∀ pair ∈ paddedCoefficients wordWidth nativeWidth polynomial, pair.1.length = nativeWidth ∧ pair.2.length = nativeWidth := by
  intro pair member
  rcases List.mem_append.mp member with originalMember | zeroMember
  · exact coefficient_widths wordWidth nativeWidth polynomial widthFits pair originalMember
  · have equal := (List.mem_replicate.mp zeroMember).2
    rw [equal]
    simp [NativeZeroRecord.coefficient, NativeZeroRecord.digits]

theorem added_value (nativeWidth precision : ℕ) :
    ChirpConjugateArray.value (nativeWidth-1) precision (NativeZeroRecord.coefficient nativeWidth) = 0 := by
  simp [ChirpConjugateArray.value, NativeZeroRecord.coefficient, NativeZeroRecord.signed, ButterflySigned.complexValue]

theorem padded_values (wordWidth nativeWidth precision : ℕ) (polynomial : Rec coefficientCount) :
    (paddedCoefficients wordWidth nativeWidth polynomial).map (ChirpConjugateArray.value (nativeWidth-1) precision) =
      (coefficients wordWidth nativeWidth polynomial).map (ChirpConjugateArray.value (nativeWidth-1) precision)++
        List.replicate (LayerPolynomialPaddingHeaders.deficit coefficientCount) 0 := by
  simp only [paddedCoefficients, List.map_append, List.map_replicate, added_value]

theorem padded_group_length (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount)
    (widthFits : wordWidth ≤ nativeWidth) (countPositive : 0 < coefficientCount) :
    (group wordWidth nativeWidth polynomial++NativeZeroStream.records nativeWidth
      (LayerPolynomialPaddingHeaders.deficit coefficientCount)).length =
        2*LayerPolynomialHeaders.paddedCount coefficientCount*(nativeWidth+1) := by
  rw [←padded_word, native_length _ nativeWidth (padded_widths wordWidth nativeWidth polynomial widthFits),
    padded_count wordWidth nativeWidth polynomial countPositive]

theorem padded_volume_bound (wordWidth nativeWidth : ℕ) (polynomial : Rec coefficientCount)
    (widthFits : wordWidth ≤ nativeWidth) (countPositive : 0 < coefficientCount) :
    (group wordWidth nativeWidth polynomial++NativeZeroStream.records nativeWidth
      (LayerPolynomialPaddingHeaders.deficit coefficientCount)).length < 2*(group wordWidth nativeWidth polynomial).length := by
  rw [padded_group_length wordWidth nativeWidth polynomial widthFits countPositive,
    group_length wordWidth nativeWidth polynomial widthFits, LayerPolynomialPaddingHeaders.span]
  have paddingBound := (LayerPolynomialHeaders.padded_bounds coefficientCount countPositive).2
  nlinarith

theorem padding_cost_linear (coefficientCount nativeWidth : ℕ) (countPositive : 0 < coefficientCount) :
    NativePolynomialPadding.blockCost (LayerPolynomialPaddingHeaders.span coefficientCount nativeWidth) nativeWidth
      (LayerPolynomialPaddingHeaders.deficit coefficientCount)+2 ≤
        128*LayerPolynomialPaddingHeaders.span coefficientCount nativeWidth := by
  have paddingBound := (LayerPolynomialHeaders.padded_bounds coefficientCount countPositive).2
  have deficitBound : LayerPolynomialPaddingHeaders.deficit coefficientCount ≤ coefficientCount := by
    unfold LayerPolynomialPaddingHeaders.deficit
    omega
  have spanBits := ActiveRepairRankHeadersCommands.bits_length (LayerPolynomialPaddingHeaders.span coefficientCount nativeWidth)
  have widthBits := ActiveRepairRankHeadersCommands.bits_length nativeWidth
  have deficitBits := ActiveRepairRankHeadersCommands.bits_length (LayerPolynomialPaddingHeaders.deficit coefficientCount)
  have innerBound : 14*nativeWidth+22*(RecursiveChildQuotientsConstant.bits nativeWidth).length+81 ≤ 36*nativeWidth+103 := by omega
  have paddingCostBound := (Nat.mul_le_mul_left (LayerPolynomialPaddingHeaders.deficit coefficientCount) innerBound).trans
    (Nat.mul_le_mul_right (36*nativeWidth+103) deficitBound)
  unfold NativePolynomialPadding.blockCost
  unfold LayerPolynomialPaddingHeaders.span at *
  nlinarith

theorem groups_length (wordWidth nativeWidth : ℕ) (polynomials : List (Rec coefficientCount)) (widthFits : wordWidth ≤ nativeWidth) :
    (groups wordWidth nativeWidth polynomials).flatten.length =
      LayerPolynomialPaddingHeaders.span coefficientCount nativeWidth*polynomials.length := by
  induction polynomials with
  | nil => simp [groups]
  | cons polynomial rest inductionHypothesis =>
    change (group wordWidth nativeWidth polynomial++(groups wordWidth nativeWidth rest).flatten).length = _
    rw [List.length_append, group_length wordWidth nativeWidth polynomial widthFits, inductionHypothesis, List.length_cons]
    ring

theorem padded_groups_volume (wordWidth nativeWidth : ℕ) (polynomials : List (Rec coefficientCount))
    (widthFits : wordWidth ≤ nativeWidth) (countPositive : 0 < coefficientCount) :
    (NativePolynomialPadding.padded (groups wordWidth nativeWidth polynomials) nativeWidth
      (LayerPolynomialPaddingHeaders.deficit coefficientCount)).flatten.length ≤
        2*(groups wordWidth nativeWidth polynomials).flatten.length := by
  induction polynomials with
  | nil => simp [groups, NativePolynomialPadding.padded]
  | cons polynomial rest inductionHypothesis =>
    have polynomialBound := padded_volume_bound wordWidth nativeWidth polynomial widthFits countPositive
    change ((group wordWidth nativeWidth polynomial++NativeZeroStream.records nativeWidth
      (LayerPolynomialPaddingHeaders.deficit coefficientCount))++
      (NativePolynomialPadding.padded (groups wordWidth nativeWidth rest) nativeWidth
        (LayerPolynomialPaddingHeaders.deficit coefficientCount)).flatten).length ≤
          2*(group wordWidth nativeWidth polynomial++(groups wordWidth nativeWidth rest).flatten).length
    simp only [List.length_append] at *
    omega

end
end IntegerMultBounds.Machine.LayerPolynomialPaddingData
