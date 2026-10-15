module

public import IntegerMultBounds.Machine.GaussianStreamBridge
public import IntegerMultBounds.Machine.CompactNativeTensorPhaseCoordinates

/-! Exact semantics of whole native complex streams, including their relation
to the Gaussian carry automata. Butterfly guards follow from the inherited
prefix grid. Integer linear combinations derive their output guard from the
expression's coefficient budget; phases retain the input grid and width.
These are arithmetic semantics, not a recursive machine execution theorem. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ButterflyPhaseRecordSemantics
noncomputable section

open ButterflyStreamData ButterflyStreamSemantics
open Networks.GaussianPrecision
open RadixLinearCombinationRefresh (Expr)
open IntegerMultBounds.MathlibTM2.Layer

/-- Both physical output streams have the required widths, exact butterfly
values, next-prefix grids, and the same bits as the new Gaussian automaton. -/
def ButterflyExact {n : ℕ} (p D j : ℕ) (xs : Fin 2 → Fin n → Coefficient) : Prop :=
  ∀ i,
    (∀ k, (result (xs 0 i) (xs 1 i) k).1.length = ButterflyGuard.width p D ∧
      (result (xs 0 i) (xs 1 i) k).2.length = ButterflyGuard.width p D ∧
      BoundedGrid (p + (j + 1)) ((2 ^ p) * 4 ^ (j + 1))
        (decode (ButterflyGuard.halfWidth p D) (p + (j + 1)) (result (xs 0 i) (xs 1 i) k))) ∧
    (decode (ButterflyGuard.halfWidth p D) (p + j + 1) (result (xs 0 i) (xs 1 i) 0) =
      (decode (ButterflyGuard.halfWidth p D) (p + j) (xs 0 i) +
       decode (ButterflyGuard.halfWidth p D) (p + j) (xs 1 i) +
       Complex.I * (decode (ButterflyGuard.halfWidth p D) (p + j) (xs 0 i) -
         decode (ButterflyGuard.halfWidth p D) (p + j) (xs 1 i))) / 2) ∧
    (decode (ButterflyGuard.halfWidth p D) (p + j + 1) (result (xs 0 i) (xs 1 i) 1) =
      (decode (ButterflyGuard.halfWidth p D) (p + j) (xs 0 i) +
       decode (ButterflyGuard.halfWidth p D) (p + j) (xs 1 i) -
       Complex.I * (decode (ButterflyGuard.halfWidth p D) (p + j) (xs 0 i) -
         decode (ButterflyGuard.halfWidth p D) (p + j) (xs 1 i))) / 2) ∧
    grun gKernel2 (fun _ => (0, 0))
        (gcols ![GaussianStreamBridge.residue (ButterflyGuard.width p D) (xs 0 i),
          GaussianStreamBridge.residue (ButterflyGuard.width p D) (xs 1 i)]) =
      gcols ![GaussianStreamBridge.residue (ButterflyGuard.width p D) (result (xs 0 i) (xs 1 i) 0),
        GaussianStreamBridge.residue (ButterflyGuard.width p D) (result (xs 0 i) (xs 1 i) 1)]

theorem butterfly_stream_exact {n : ℕ} (p D j : ℕ) (hj : j ≤ D)
    (xs : Fin 2 → Fin n → Coefficient)
    (hw : ∀ k i, (xs k i).1.length = ButterflyGuard.width p D ∧
      (xs k i).2.length = ButterflyGuard.width p D)
    (hg : ∀ k i, BoundedGrid (p + j) ((2 ^ p) * 4 ^ j)
      (decode (ButterflyGuard.halfWidth p D) (p + j) (xs k i))) :
    ButterflyExact p D j xs := by
  intro i
  obtain ⟨h0, h1⟩ := result_exact (xs 0 i) (xs 1 i) p D j hj (hw 0 i) (hw 1 i) (hg 0 i) (hg 1 i)
  refine ⟨fun k => ?_, h0, h1,
    GaussianStreamBridge.butterfly_columns _ _ _ (hw 0 i) (hw 1 i)⟩
  have hwidth := ButterflyStreamEndpoint.result_width _ _ _ (hw 0 i) (hw 1 i) k
  exact ⟨hwidth.1, hwidth.2, result_grid _ _ p D j hj (hw 0 i) (hw 1 i) (hg 0 i) (hg 1 i) k⟩

/-! ### Raw integer linear combinations -/

/-- Integer coefficients are exactly the denominator-one leaves used by the
raw radix-two arithmetic, before a common denominator is advanced. -/
def IntegerCoefficients {c : ℕ} : Expr c → Prop
  | .term _ r => r.den = 1
  | .add e f => IntegerCoefficients e ∧ IntegerCoefficients f

def integerValue {c : ℕ} : Expr c → (ℕ → ℤ) → ℤ
  | .term i r, xs => r.num * xs i.val
  | .add e f, xs => integerValue e xs + integerValue f xs

/-- A budget derived from the literal expression, not from its desired output. -/
def integerBound {c : ℕ} : Expr c → ℕ → ℕ
  | .term _ r, M => r.num.natAbs * M
  | .add e f, M => integerBound e M + integerBound f M

theorem integer_bound {c : ℕ} (e : Expr c) (xs : ℕ → ℤ) (M : ℕ)
    (hx : ∀ i, |xs i| ≤ (M : ℤ)) : |integerValue e xs| ≤ (integerBound e M : ℤ) := by
  induction e with
  | term i r =>
    simpa [integerValue, integerBound, abs_mul] using
      mul_le_mul_of_nonneg_left (hx i.val) (abs_nonneg r.num)
  | add e f he hf =>
    exact (abs_add_le _ _).trans (by simpa [integerValue, integerBound] using add_le_add he hf)

theorem integer_residue {c : ℕ} (e : Expr c) (he : IntegerCoefficients e)
    (b : ℕ) (xs : ℕ → List (Fin 2)) :
    RadixLinearCombination.valueMod (b + 1) e.erase xs =
      (integerValue e (fun i => ButterflySigned.signedValue b (xs i)) : ZMod (2 ^ (b + 1))) := by
  induction e with
  | term i r =>
    simp only [IntegerCoefficients] at he
    simp [Expr.erase, RadixLinearCombination.valueMod, Swap.Modular.ratMod, he,
      integerValue, ButterflySigned.signed_cast]
  | add e f ihE ihF =>
    simp only [IntegerCoefficients] at he
    simp [Expr.erase, RadixLinearCombination.valueMod, integerValue, ihE he.1, ihF he.2]

theorem raw_signed {c : ℕ} (e : Expr c) (he : IntegerCoefficients e) (b M : ℕ)
    (xs : ℕ → List (Fin 2)) (hw : ∀ i, (xs i).length = b + 1)
    (hx : ∀ i, |ButterflySigned.signedValue b (xs i)| ≤ (M : ℤ))
    (hfit : integerBound e M < 2 ^ b) :
    ButterflySigned.signedValue b (RadixLinearCombination.result e.erase xs) =
      integerValue e (fun i => ButterflySigned.signedValue b (xs i)) := by
  have hv : RadixLinearCombination.Valid (q := 2) e.erase := by
    clear hfit
    induction e with
    | term i r => simp_all [IntegerCoefficients, Expr.erase, RadixLinearCombination.Valid]
    | add e f ihE ihF => exact ⟨ihE he.1, ihF he.2⟩
  apply ButterflySigned.signed_unique b _ (RadixLinearCombination.result_length _ _ _ hw)
  · have hb := abs_le.mp (integer_bound e _ M hx)
    have hf : (integerBound e M : ℤ) < (2 ^ b : ℕ) := by exact_mod_cast hfit
    constructor <;> omega
  · rw [RadixLinearCombination.result_value _ hv _ _ hw, integer_residue e he]

def rawOutput {c : ℕ} (e : Expr c) (xs : ℕ → Coefficient) : Coefficient :=
  (RadixLinearCombination.result e.erase (fun i => (xs i).1),
    RadixLinearCombination.result e.erase (fun i => (xs i).2))

/-- The literal raw-expression outputs have exact integer component sums and
lie on the next common-denominator grid with the derived coefficient budget. -/
def LinearExact {c n : ℕ} (e : Expr c) (b p M : ℕ) (xs : ℕ → Fin n → Coefficient) : Prop :=
  ∀ i,
    (rawOutput e (fun k => xs k i)).1.length = b + 1 ∧
    (rawOutput e (fun k => xs k i)).2.length = b + 1 ∧
    GaussianStreamBridge.numerator b (rawOutput e (fun k => xs k i)) =
      ⟨integerValue e (fun k => ButterflySigned.signedValue b (xs k i).1),
        integerValue e (fun k => ButterflySigned.signedValue b (xs k i).2)⟩ ∧
    BoundedGrid (p + 1) (integerBound e M) (decode b (p + 1) (rawOutput e (fun k => xs k i)))

theorem linear_stream_exact {c n : ℕ} (e : Expr c) (he : IntegerCoefficients e) (b p M : ℕ)
    (xs : ℕ → Fin n → Coefficient)
    (hw : ∀ k i, (xs k i).1.length = b + 1 ∧ (xs k i).2.length = b + 1)
    (hg : ∀ k i, BoundedGrid p M (decode b p (xs k i)))
    (hfit : integerBound e M < 2 ^ b) : LinearExact e b p M xs := by
  intro i
  have hb := fun k => ButterflyGuard.represented_bound _ _ p M (hg k i)
  have hre := raw_signed e he b M (fun k => (xs k i).1) (fun k => (hw k i).1)
    (fun k => (hb k).1) hfit
  have him := raw_signed e he b M (fun k => (xs k i).2) (fun k => (hw k i).2)
    (fun k => (hb k).2) hfit
  refine ⟨RadixLinearCombination.result_length _ _ _ (fun k => (hw k i).1),
    RadixLinearCombination.result_length _ _ _ (fun k => (hw k i).2), ?_, ?_⟩
  · exact congrArg₂ (fun x y => (⟨x, y⟩ : GaussianInt)) hre him
  · refine ⟨_, _, ?_, integer_bound e _ M (fun k => (hb k).1),
      integer_bound e _ M (fun k => (hb k).2)⟩
    change ButterflySigned.complexValue _ _ (p + 1) * (2 : ℂ) ^ (p + 1) = _
    dsimp only [rawOutput]
    rw [hre, him]
    exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))

/-! ### Sparse and all-axis unit phases -/

def component (x : Coefficient) : ℕ → List (Fin 2)
  | 0 => x.1
  | _ => x.2

def phaseOutput (q : Fin 4) (x : Coefficient) : Coefficient :=
  (UnitPhaseNumerator.words q 0 (component x), UnitPhaseNumerator.words q 1 (component x))

theorem component_width (x : Coefficient) (b : ℕ)
    (hw : x.1.length = b + 1 ∧ x.2.length = b + 1) :
    ∀ i, (component x i).length = b + 1 := by
  intro i
  cases i with
  | zero => exact hw.1
  | succ i => exact hw.2

theorem phase_guard (x : Coefficient) (b p M : ℕ)
    (hg : BoundedGrid p M (decode b p x)) (hfit : M < 2 ^ b) :
    ∀ k : Fin 2, |ButterflySigned.signedValue b (component x k.val)| < (2 ^ b : ℕ) := by
  have hb := ButterflyGuard.represented_bound _ _ p M hg
  have hf : (M : ℤ) < (2 ^ b : ℕ) := by exact_mod_cast hfit
  intro k
  fin_cases k
  · exact hb.1.trans_lt hf
  · exact hb.2.trans_lt hf

def PhaseExact {n : ℕ} (b p M : ℕ) (q : Fin n → Fin 4) (xs : Fin n → Coefficient) : Prop :=
  ∀ i, (phaseOutput (q i) (xs i)).1.length = b + 1 ∧
    (phaseOutput (q i) (xs i)).2.length = b + 1 ∧
    decode b p (phaseOutput (q i) (xs i)) =
      Networks.BinaryPhase.phase ((q i).val : ZMod 4) * decode b p (xs i) ∧
    BoundedGrid p M (decode b p (phaseOutput (q i) (xs i)))

theorem phase_stream_exact {n : ℕ} (b p M : ℕ) (q : Fin n → Fin 4) (xs : Fin n → Coefficient)
    (hw : ∀ i, (xs i).1.length = b + 1 ∧ (xs i).2.length = b + 1)
    (hg : ∀ i, BoundedGrid p M (decode b p (xs i))) (hfit : M < 2 ^ b) :
    PhaseExact b p M q xs := by
  intro i
  have he := UnitPhaseSigned.words_phase (q i) (component (xs i)) b p
    (component_width _ b (hw i)) (phase_guard _ b p M (hg i) hfit)
  refine ⟨UnitPhaseNumerator.words_length _ _ _ _ (component_width _ b (hw i)),
    UnitPhaseNumerator.words_length _ _ _ _ (component_width _ b (hw i)), he, ?_⟩
  rw [show decode b p (phaseOutput (q i) (xs i)) = _ from he]
  exact bounded_phase_mul _ (hg i)

open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open Networks.ComplexPhaseRowSchedule

def reachedPhase {s : Shape} (d : Inputs s) (hs : d.stage.slots = 25 ^ 3) (edge : Edge)
    (hm : 0 < dimension edge) (r : Fin (count d)) : Fin 4 :=
  CompactNativeTensorPhaseCoordinates.phase d hs edge hm
    (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hs edge) r)

/-- The phase read at the actual reached row is the complete original tensor
phase, for every coefficient in every polynomial spectator stream. -/
def TensorPhaseExact {s : Shape} (d : Inputs s) (hs : d.stage.slots = 25 ^ 3) (edge : Edge)
    (hm : 0 < dimension edge) {n : ℕ} (b p : ℕ) (xs : Fin (count d) → Fin n → Coefficient) : Prop :=
  ∀ r i, decode b p (phaseOutput (reachedPhase d hs edge hm r) (xs r i)) =
    (∏ axis : Fin d.stage.f, Networks.BinaryPhase.phase
      (CompactAllAxisPhaseReadout.delta d hs edge
        (ActivePrefixStageNativePairCoordinates.start d r) axis)) * decode b p (xs r i)

theorem tensor_phase_stream_exact {s : Shape} (d : Inputs s) (hs : d.stage.slots = 25 ^ 3)
    (edge : Edge) (hm : 0 < dimension edge) {n : ℕ} (b p M : ℕ)
    (xs : Fin (count d) → Fin n → Coefficient)
    (hw : ∀ r i, (xs r i).1.length = b + 1 ∧ (xs r i).2.length = b + 1)
    (hg : ∀ r i, BoundedGrid p M (decode b p (xs r i))) (hfit : M < 2 ^ b) :
    TensorPhaseExact d hs edge hm b p xs := by
  intro r i
  exact CompactNativeTensorPhaseCoordinates.coefficient_phase d hs edge hm r
    (component (xs r i)) b p (component_width _ b (hw r i)) (phase_guard _ b p M (hg r i) hfit)

/-- Complete whole-stream arithmetic milestone: exact physical butterfly
outputs and their Gaussian-automaton bridge, raw integer linear combinations,
and sparse or all-axis unit phases under input-derived signed guards. -/
theorem stream_exact :
    (∀ {n} p D j, j ≤ D → ∀ xs : Fin 2 → Fin n → Coefficient,
      (∀ k i, (xs k i).1.length = ButterflyGuard.width p D ∧
        (xs k i).2.length = ButterflyGuard.width p D) →
      (∀ k i, BoundedGrid (p + j) ((2 ^ p) * 4 ^ j)
        (decode (ButterflyGuard.halfWidth p D) (p + j) (xs k i))) → ButterflyExact p D j xs) ∧
    (∀ {c n} (e : Expr c), IntegerCoefficients e → ∀ b p M (xs : ℕ → Fin n → Coefficient),
      (∀ k i, (xs k i).1.length = b + 1 ∧ (xs k i).2.length = b + 1) →
      (∀ k i, BoundedGrid p M (decode b p (xs k i))) → integerBound e M < 2 ^ b →
      LinearExact e b p M xs) ∧
    (∀ {n} b p M (q : Fin n → Fin 4) (xs : Fin n → Coefficient),
      (∀ i, (xs i).1.length = b + 1 ∧ (xs i).2.length = b + 1) →
      (∀ i, BoundedGrid p M (decode b p (xs i))) → M < 2 ^ b → PhaseExact b p M q xs) ∧
    (∀ {s : Shape} (d : Inputs s) (hs : d.stage.slots = 25 ^ 3) (edge : Edge)
      (hm : 0 < dimension edge) {n} b p M (xs : Fin (count d) → Fin n → Coefficient),
      (∀ r i, (xs r i).1.length = b + 1 ∧ (xs r i).2.length = b + 1) →
      (∀ r i, BoundedGrid p M (decode b p (xs r i))) → M < 2 ^ b →
      TensorPhaseExact d hs edge hm b p xs) :=
  ⟨butterfly_stream_exact, linear_stream_exact, phase_stream_exact, tensor_phase_stream_exact⟩

end
end IntegerMultBounds.Machine.ButterflyPhaseRecordSemantics
