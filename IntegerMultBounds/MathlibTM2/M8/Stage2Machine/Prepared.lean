module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Init
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchPrepare
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighHeaderBounds

/-!
# The stage-2 high body with its metadata prepared

After stage 1's `ArbitraryWidthHighPreparedRun`: stage 1's `ArbitraryWidthHighBranchPrepare` builds the
dimension, joined-header and zero banks from words on a caller (`base`), the atom width program
(`Width.shared`) builds `w = atomWidth 1000 (e - r)` and `529` from the joined width header, and the
high body runs with its banks filled and erased (`Init.program`); then the width and the metadata
banks are erased. The nineteen padding sources are read off these banks (`padding_sources`): the
four padding headers, the six joined headers (which are the padded view's headers,
`joined_hdr`), its width, `w`, five zero words, `529` and a joined header of value `1`.
Every private bank starts and finishes blank (`runs`), within a constant times `V e^τ₂` plus a
constant times `V`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Prepared

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighLayout (originalDescriptor joinedDescriptor)
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources Bounded)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement (movementWords)
open M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring (bank baseSlot dimensionSlot joinedSlot zeroSlot
  exchangeFocus movementFocus paddingWords)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ padCount)
open Params (r padded view threshold)

variable {t : ℕ}

/-! ### Sources on a longer bank -/

theorem sources_append {n u : ℕ} {x : Tapes t prime} {f : Fin n → Fin t} {ws : Fin n → List Bool}
    (h : Sources x f ws) (y : Tapes u prime) : Sources (x.append y) (fun i => Fin.castAdd u (f i)) ws :=
  ⟨fun i => by simpa only [Tapes.append, Fin.addCases_left] using h.tape i,
    fun i => by simpa only [Tapes.append, Fin.addCases_left] using h.head i⟩

theorem bounded_left {m n : ℕ} {ws : Fin m → List Bool} {vs : Fin n → List Bool} {V : ℕ}
    (h : Bounded (Fin.addCases ws vs) V) : Bounded ws V :=
  ⟨fun i => by simpa only [Fin.addCases_left] using h.canonical (Fin.castAdd n i),
    fun i => by simpa only [Fin.addCases_left] using h.value (Fin.castAdd n i)⟩

theorem bounded_append {m n : ℕ} {ws : Fin m → List Bool} {vs : Fin n → List Bool} {V : ℕ}
    (h : Bounded ws V) (h' : Bounded vs V) : Bounded (Fin.addCases ws vs) V :=
  ⟨fun i => by
      induction i using Fin.addCases with
      | left i => simpa only [Fin.addCases_left] using h.canonical i
      | right i => simpa only [Fin.addCases_right] using h'.canonical i,
    fun i => by
      induction i using Fin.addCases with
      | left i => simpa only [Fin.addCases_left] using h.value i
      | right i => simpa only [Fin.addCases_right] using h'.value i⟩

/-! ### The padded view's headers -/

/-- The joined headers are the padded view's headers. -/
theorem joined_hdr (P G B e r R : ℕ) (jh : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (jh i) = ArbitraryWidthJoinedHeaders.originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (jh i)) :
    ArbitraryWidthJoinedHeaders.words jh e r =
      Routines.hdr (RecursiveRowPadding.withRows (joinedDescriptor prime P e r G B) R) := by
  have hh := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.lowroot_headers P G B e r R jh hv hc
  funext i
  rw [Routines.canon (hh.2 i), hh.1 i]
  rfl

theorem hdr_headers (v : Descriptor) : RecursiveDimensionBank.Headers v (Routines.hdr v) :=
  ⟨fun _ => FlatCoordinateSchedule.bits_value _, fun _ => FlatCoordinateSchedule.bits_canonical _⟩

/-! ### The padding sources -/

/-- The joined width header, read by the atom width program. -/
def wslot : Fin (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.count t) := joinedSlot (Fin.natAdd 6 (3 : Fin 6))

/-- A slot of the bank below the atom width program's own. -/
abbrev low (j : Fin (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.count t)) :
    Fin (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.count t + 22) := Fin.castAdd 22 j

/-- A slot of the atom width program's own bank. -/
abbrev high (j : Fin 22) : Fin (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.count t + 22) :=
  Fin.natAdd _ j

/-- The core's fifteen sources. -/
def coreFocus : Fin 15 → Fin (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.count t + 22) :=
  ![low (joinedSlot (Fin.natAdd 6 (0 : Fin 6))), low (joinedSlot (Fin.natAdd 6 (1 : Fin 6))), low (joinedSlot (Fin.natAdd 6 (2 : Fin 6))),
    low (joinedSlot (Fin.natAdd 6 (3 : Fin 6))), low (joinedSlot (Fin.natAdd 6 (4 : Fin 6))), low (joinedSlot (Fin.natAdd 6 (5 : Fin 6))),
    low (joinedSlot (Fin.natAdd 6 (3 : Fin 6))), high 12, low zeroSlot, low zeroSlot, low zeroSlot, low zeroSlot,
    low zeroSlot, high 4, low (joinedSlot (Fin.natAdd 6 (2 : Fin 6)))]

/-- The nineteen padding sources. -/
def padFocus (rows rounded : Fin t) : Fin (4+15) → Fin (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.count t + 22) :=
  Fin.addCases (fun i => low (![dimensionSlot 0, baseSlot rows, baseSlot rounded, dimensionSlot 12] i)) coreFocus

theorem padding_sources (base : Tapes t prime) (P G B e : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (rows rounded : Fin t) (rs rps : List Bool)
    (jhv : ∀ i, Counter.value (jh i) = ArbitraryWidthJoinedHeaders.originalValues P G B e (r 2 e) (padded 2 e) i)
    (jhc : ∀ i, GrowingCounterData.Canonical (jh i))
    (hrows : base.tape rows = RadixZeroFill.encodedBinary rs) (hrowhead : base.head rows = 1)
    (hrounded : base.tape rounded = RadixZeroFill.encodedBinary rps) (hroundedhead : base.head rounded = 1) :
    Sources ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (e - r 2 e))) (padFocus rows rounded)
      (Init.coreWords 2 (paddingWords dh rs rps e (r 2 e) G B) P e G B) := by
  set b := bank base P G B e (r 2 e) dh jh
  have hj := joined_hdr P G B e (r 2 e) (padded 2 e) jh jhv jhc
  have jc : ∀ i : Fin 6, b.head (joinedSlot (Fin.natAdd 6 i)) = 1 ∧
      b.tape (joinedSlot (Fin.natAdd 6 i)) = RadixZeroFill.encodedBinary (Routines.hdr (view 2 P e G B) i) := by
    intro i
    have h := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.joined_cells base P G B e (r 2 e) dh jh i
    rw [hj] at h
    exact h
  have zc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.zero_cells base P G B e (r 2 e) dh jh
  have wc := Width.out_cells (q := prime) (e - r 2 e)
  have lc : ∀ j, ((b.append (Width.privateOut (e - r 2 e))).head (low j) = b.head j) ∧
      ((b.append (Width.privateOut (e - r 2 e))).tape (low j) = b.tape j) := fun j =>
    ⟨by simp only [Tapes.append, Fin.addCases_left], by simp only [Tapes.append, Fin.addCases_left]⟩
  have hc : ∀ j, ((b.append (Width.privateOut (e - r 2 e))).head (high j) = (Width.privateOut (q := prime) (e - r 2 e)).head j) ∧
      ((b.append (Width.privateOut (e - r 2 e))).tape (high j) = (Width.privateOut (q := prime) (e - r 2 e)).tape j) := fun j =>
    ⟨by simp only [Tapes.append, Fin.addCases_right], by simp only [Tapes.append, Fin.addCases_right]⟩
  have hrc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.base_cells base P G B e (r 2 e) dh jh rows
  have hpc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.base_cells base P G B e (r 2 e) dh jh rounded
  have hdo := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.dimension_original base P G B e (r 2 e) dh jh 0
  have hsc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.suffix_cells base P G B e (r 2 e) dh jh
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [padFocus, Init.coreWords, CoreSparse.paddedWords, Fin.addCases_left]
      fin_cases i
      · exact (lc _).2.trans hdo.2
      · exact (lc _).2.trans (hrc.2.trans hrows)
      · exact (lc _).2.trans (hpc.2.trans hrounded)
      · exact (lc _).2.trans hsc.2
    | right i =>
      simp only [padFocus, Init.coreWords, CoreSparse.paddedWords, Fin.addCases_right]
      fin_cases i <;> simp only [coreFocus, CoreSparse.words, Matrix.cons_val_succ', Matrix.cons_val_zero']
      · exact (lc _).2.trans (jc 0).2
      · exact (lc _).2.trans (jc 1).2
      · exact (lc _).2.trans (jc 2).2
      · exact (lc _).2.trans (jc 3).2
      · exact (lc _).2.trans (jc 4).2
      · exact (lc _).2.trans (jc 5).2
      · exact (lc _).2.trans (jc 3).2
      · exact (hc _).2.trans wc.2.1
      · exact (lc _).2.trans zc.2
      · exact (lc _).2.trans zc.2
      · exact (lc _).2.trans zc.2
      · exact (lc _).2.trans zc.2
      · exact (lc _).2.trans zc.2
      · exact (hc _).2.trans wc.2.2.2
      · exact (lc _).2.trans (jc 2).2
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [padFocus, Fin.addCases_left]
      fin_cases i
      · exact (lc _).1.trans hdo.1
      · exact (lc _).1.trans (hrc.1.trans hrowhead)
      · exact (lc _).1.trans (hpc.1.trans hroundedhead)
      · exact (lc _).1.trans hsc.1
    | right i =>
      simp only [padFocus, Fin.addCases_right]
      fin_cases i <;> simp only [coreFocus, Matrix.cons_val_succ', Matrix.cons_val_zero']
      · exact (lc _).1.trans (jc 0).1
      · exact (lc _).1.trans (jc 1).1
      · exact (lc _).1.trans (jc 2).1
      · exact (lc _).1.trans (jc 3).1
      · exact (lc _).1.trans (jc 4).1
      · exact (lc _).1.trans (jc 5).1
      · exact (lc _).1.trans (jc 3).1
      · exact (hc _).1.trans wc.1
      · exact (lc _).1.trans zc.1
      · exact (lc _).1.trans zc.1
      · exact (lc _).1.trans zc.1
      · exact (lc _).1.trans zc.1
      · exact (lc _).1.trans zc.1
      · exact (hc _).1.trans wc.2.2.1
      · exact (lc _).1.trans (jc 2).1

/-- The width is at least five past the threshold. -/
theorem five_le_threshold : 5 ≤ threshold 2 := by
  unfold threshold
  exact (show 5 ≤ 3^2 by norm_num).trans (Nat.pow_le_pow_left (by omega) 2)

theorem bits_le (n V : ℕ) (h : n ≤ V) : Counter.value (bits n) ≤ V := by
  rw [FlatCoordinateSchedule.bits_value]; exact h

/-- The padding words are bounded by twice the volume. -/
theorem padding_bounded (P e G B : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (he : threshold 2 ≤ e)
    (ph : Fin 4 → List Bool)
    (hph : M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers (joinedDescriptor prime P e (r 2 e) G B) (padded 2 e) ph) :
    Bounded (Init.coreWords 2 ph P e G B) (2*volume prime (originalDescriptor P e G B)) := by
  have hr := Params.fit_of_threshold (le_refl 2) he
  have hp : (joinedDescriptor prime P e (r 2 e) G B).Positive :=
    ⟨hP, pow_pos Networks.Shared50ModularControl.prime_prime.pos _, by change 0 < 1; decide, hG, hB⟩
  have hR : (joinedDescriptor prime P e (r 2 e) G B).rows ≤ padded 2 e := Params.rows_le 2 e
  have hvol := Params.volume_le (b := 2) (P := P) (G := G) (B := B) (by omega : r 2 e ≤ e)
  have hb := M8.Machine.ArbitraryWidthHighHeaderBounds.padding_root_bounded _ (padded 2 e) _ hp hR ph
    (Routines.hdr (view 2 P e G B)) hph (hdr_headers _) hvol
  have hl := bounded_left hb
  have hhdr : Bounded (Routines.hdr (view 2 P e G B)) (2*volume prime (originalDescriptor P e G B)) :=
    ⟨fun i => by simpa only [M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding.paddedWords,
        Fin.addCases_right] using hb.canonical (Fin.natAdd 4 i),
      fun i => by simpa only [M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding.paddedWords,
        Fin.addCases_right] using hb.value (Fin.natAdd 4 i)⟩
  have hpo : (originalDescriptor P e G B).Positive :=
    ⟨hP, by change 0 < 1; decide, by change 0 < 1; decide, hG, hB⟩
  have hlow := M8.Machine.ArbitraryWidthHighMetadataBudget.volume_lower prime Params.prime_two _ hpo
  have h5 := five_le_threshold
  have h529 : 529 ≤ 2*volume prime (originalDescriptor P e G B) := by
    have h1 : 2^(2*5) ≤ 2^(2*e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2^(2*e) ≤ prime^(2*e) := Nat.pow_le_pow_left Params.prime_two _
    change 529 ≤ 2*volume prime (originalDescriptor P e G B)
    have : prime^(2*(originalDescriptor P e G B).width) = prime^(2*e) := rfl
    norm_num at h1
    omega
  have he' : e ≤ 2*volume prime (originalDescriptor P e G B) := by
    have := Nat.lt_two_pow_self (n := 2*e)
    have h2 : 2^(2*e) ≤ prime^(2*e) := Nat.pow_le_pow_left Params.prime_two _
    have : prime^(2*(originalDescriptor P e G B).width) = prime^(2*e) := rfl
    omega
  have hw : Stage2Width.atomWidth HighCost.K (e - r 2 e) ≤ e :=
    (Stage2Width.atomWidth_le_self (by norm_num) (by omega)).trans (Nat.sub_le _ _)
  refine bounded_append hl ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i <;> simp only [CoreSparse.words, Matrix.cons_val_succ', Matrix.cons_val_zero']
    all_goals exact FlatCoordinateSchedule.bits_canonical _
  · fin_cases i <;> simp only [CoreSparse.words, Matrix.cons_val_succ', Matrix.cons_val_zero']
    · exact hhdr.value 0
    · exact hhdr.value 1
    · exact hhdr.value 2
    · exact hhdr.value 3
    · exact hhdr.value 4
    · exact hhdr.value 5
    · exact hhdr.value 3
    · exact bits_le _ _ (hw.trans he')
    all_goals first
      | exact bits_le _ _ (Nat.zero_le _)
      | exact bits_le _ _ h529
      | exact hhdr.value 2

/-! ### The run after the metadata -/

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- The atom width, the high body with its banks, and the width's erasure. -/
def runProgram (focus : Fin t) (exchange : Fin 7 → Fin t) (rows rounded : Fin t) :=
  seq (seq (extend (extend (extend (Width.shared Params.prime_two (wslot (t := t))) exchangeCount) movementCount)
      (padCount capacity))
    (Init.program capacity (low (baseSlot focus)) (fun i => low (exchangeFocus exchange i))
      (fun i => low (movementFocus exchange i)) (padFocus rows rounded)))
    (extend (extend (extend (Width.sharedCleanup Params.prime_two (wslot (t := t))) exchangeCount) movementCount)
      (padCount capacity))

/-- **The prepared high body.** -/
def program (focus : Fin t) (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t)
    (exchange : Fin 7 → Fin t) (rows rounded : Fin t) :=
  seq (seq (extend (extend (extend (extend
      (M8.Machine.ArbitraryWidthHighBranchPrepare.program (a := prime) dimensions joined prime) 22)
      exchangeCount) movementCount) (padCount capacity))
    (runProgram capacity focus exchange rows rounded))
    (extend (extend (extend (extend (M8.Machine.ArbitraryWidthHighBranchPrepare.cleanup (a := prime) (t := t)) 22)
      exchangeCount) movementCount) (padCount capacity))

/-- The blank private banks. -/
def input (base : Tapes t prime) :=
  Init.input capacity ((M8.Machine.ArbitraryWidthHighBranchPrepare.input base).append (Width.privateIn (q := prime)))

omit [M8.Machine.Net] in
theorem changed_bank (base : Tapes t prime) (focus : Fin t)
    (P G B e r : ℕ) (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (word : ℤ → Fin (prime+4)) :
    setTape (bank base P G B e r dh jh) (baseSlot focus) word 0 = bank (setTape base focus word 0) P G B e r dh jh := by
  unfold bank baseSlot
  rw [SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]

omit [M8.Machine.Net] in
theorem cost_arith {s cl c U V e ρ A L K : ℕ} {X : ℝ} (hs1 : s ≤ (L + 429) * U) (hs2 : cl ≤ 333 * U)
    (hV : V = 2 * U) (he : e ≤ U) (hU : 0 < U) (hc : (c : ℝ) ≤ X + 802 * V)
    (hK : K = L + 429 + 333 + 200 * A + 20000 * 533 + 1604 + 6) :
    ((s + 1 + (100 * A * (e - ρ + 1) + 1 + c + 1 + (20000 * (e - ρ + 2) + 20000 * 530 + 1)) + 1 + cl : ℕ) : ℝ) ≤
      X + (K : ℝ) * U := by
  subst hK
  have h1 : e - ρ + 1 ≤ 2 * U := by omega
  have h2 : e - ρ + 2 ≤ 3 * U := by omega
  have h3 := Nat.mul_le_mul_left (100 * A) h1
  have hlin : s + 1 + (100 * A * (e - ρ + 1) + 1 + 1 + (20000 * (e - ρ + 2) + 20000 * 530 + 1)) + 1 + cl +
      802 * V ≤ (L + 429 + 333 + 200 * A + 20000 * 533 + 1604 + 6) * U := by
    subst hV; nlinarith
  have hlin' : ((s + 1 + (100 * A * (e - ρ + 1) + 1 + 1 + (20000 * (e - ρ + 2) + 20000 * 530 + 1)) + 1 + cl : ℕ) : ℝ) +
      802 * (V : ℝ) ≤ ((L + 429 + 333 + 200 * A + 20000 * 533 + 1604 + 6 : ℕ) : ℝ) * U := by exact_mod_cast hlin
  have hseq : s + 1 + (100 * A * (e - ρ + 1) + 1 + c + 1 + (20000 * (e - ρ + 2) + 20000 * 530 + 1)) + 1 + cl =
      (s + 1 + (100 * A * (e - ρ + 1) + 1 + 1 + (20000 * (e - ρ + 2) + 20000 * 530 + 1)) + 1 + cl) + c := by ring
  rw [hseq, Nat.cast_add]
  linarith

theorem runs (hspec : FamilySpec capacity) (hτ : Exponents HighCost.K) :
    ∃ C D : ℝ, ∀ {t : ℕ} (base : Tapes t prime) (focus : Fin t)
      (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t) (exchange : Fin 7 → Fin t)
      (rowsSlot roundedSlot : Fin t) (P e G B : ℕ), threshold 2 ≤ e →
      0 < P → 0 < G → 0 < B →
      ∀ (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (hs : Fin 6 → List Bool)
        (rs rowBits roundedBits : List Bool),
      (∀ i, Counter.value (dh i) = ArbitraryWidthHighDimensions.originalValues P G B e (r 2 e) i) →
      (∀ i, GrowingCounterData.Canonical (dh i)) →
      (∀ i, Counter.value (jh i) =
        ArbitraryWidthJoinedHeaders.originalValues P G B e (r 2 e) (padded 2 e) i) →
      (∀ i, GrowingCounterData.Canonical (jh i)) →
      Sources base dimensions dh → Sources base joined jh → Sources base exchange (exchangeWords hs rs) →
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs →
      Counter.value rs = r 2 e → GrowingCounterData.Canonical rs →
      Counter.value rowBits = prime^(2*r 2 e) → GrowingCounterData.Canonical rowBits →
      Counter.value roundedBits = padded 2 e → GrowingCounterData.Canonical roundedBits →
      base.tape rowsSlot = RadixZeroFill.encodedBinary rowBits → base.head rowsSlot = 1 →
      base.tape roundedSlot = RadixZeroFill.encodedBinary roundedBits → base.head roundedSlot = 1 →
      ∀ x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2,
      base.tape focus = sourceWord x → base.head focus = 0 → ∃ c : ℕ,
        (c : ℝ) ≤ C * volume prime (originalDescriptor P e G B) * (e : ℝ) ^ tau₂ HighCost.K +
          D * volume prime (originalDescriptor P e G B) ∧
        HoareTime (program capacity focus dimensions joined exchange rowsSlot roundedSlot)
          (fun z => z = input capacity base)
          (fun z => z = input capacity (setTape base focus
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c := by
  obtain ⟨C, hC⟩ := Init.runs capacity hspec hτ (le_refl 2)
  refine ⟨C, ((ArbitraryWidthHighDimensions.linearConstant prime + 429 + 333 + 200 * Width.constant +
    20000 * 533 + 1604 + 6 : ℕ) : ℝ), fun {t} base focus dimensions joined exchange rowsSlot roundedSlot P e G B he hP hG hB
    dh jh hs rs rowBits roundedBits dhv dhc jhv jhc sd sj sx hh hr cr hrows crows hrounded crounded
    rowsTape rowsHead roundedTape roundedHead x hf hhead => ?_⟩
  have hfit := Params.fit_of_threshold (le_refl 2) he
  have hdvol := ArbitraryWidthHighPaddingSuffix.original_volume prime P e G B
  obtain ⟨V, hVdef⟩ : ∃ V, V = 2*volume prime (originalDescriptor P e G B) := ⟨_, rfl⟩
  have ho := ArbitraryWidthHighDimensionsShared.original_bounds prime P G B e (r 2 e) Params.prime_two
    (by omega) hP hG hB
  have hU : 0 < volume prime (originalDescriptor P e G B) := by rw [hdvol]; exact ho.1
  have hV : 0 < V := by omega
  have bP : P ≤ V := by have := ho.2 0; change P ≤ _ at this; rw [← hdvol] at this; omega
  have bG : G ≤ V := by have := ho.2 1; change G ≤ _ at this; rw [← hdvol] at this; omega
  have bB : B ≤ V := by have := ho.2 2; change B ≤ _ at this; rw [← hdvol] at this; omega
  have be : e ≤ V := by have := ho.2 3; change e ≤ _ at this; rw [← hdvol] at this; omega
  have hviewpos : (view 2 P e G B).Positive :=
    ⟨hP, (Params.rows_pos 2 e).trans_le (Params.rows_le 2 e), by change 0 < 1; decide, hG, hB⟩
  have bR : padded 2 e ≤ V := by
    have h1 := RecursiveHeaderBounds.values_le_volume Params.prime_two _ hviewpos 1
    have h2 := Params.volume_le (b := 2) (P := P) (G := G) (B := B) (by omega : r 2 e ≤ e)
    change padded 2 e ≤ _ at h1
    omega
  -- the metadata banks
  have hp := M8.Machine.ArbitraryWidthHighBranchPrepare.constructs dimensions joined base
    prime P G B e (r 2 e) (padded 2 e) V Params.prime_two (by omega) hP hG hB hV dh jh dhv dhc jhv jhc
    bP bG bB be bR sd.tape sd.head sj.tape sj.head
  have hp' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hp
    (Width.privateIn (q := prime))) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty (padCount capacity) prime)
  -- the atom width
  have hj := joined_hdr P G B e (r 2 e) (padded 2 e) jh jhv jhc
  have hwc : ∀ base' : Tapes t prime, (bank base' P G B e (r 2 e) dh jh).tape wslot =
      RadixZeroFill.encodedBinary (bits (e - r 2 e)) ∧ (bank base' P G B e (r 2 e) dh jh).head wslot = 1 := by
    intro base'
    have h := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.joined_cells base' P G B e (r 2 e) dh jh 3
    rw [hj] at h
    exact ⟨h.2, h.1⟩
  have hw := Width.shared_runs Params.prime_two (bank base P G B e (r 2 e) dh jh) wslot (by omega)
    (hwc base).1 (hwc base).2
  have hw' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hw
    (SharedBank.empty exchangeCount prime)) (SharedBank.empty movementCount prime))
    (SharedBank.empty (padCount capacity) prime)
  -- the high body
  have mv := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.movement_values P G B e (r 2 e) rs hr
  have mc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.movement_canonical P G B e (r 2 e) rs cr
  have hjc : HighBody.JoinCounters P e (r 2 e) G B rs (ArbitraryWidthHighDimensions.words prime P G B e (r 2 e) 4)
      (ArbitraryWidthHighDimensions.words prime P G B e (r 2 e) 3)
      (ArbitraryWidthHighDimensions.words prime P G B e (r 2 e) 5) :=
    ⟨hr, cr, mv 0, mc 0, mv 1, mc 1, mv 2, mc 2⟩
  have hph := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.padding_headers P G B e (r 2 e) (padded 2 e) dh
    rowBits roundedBits (dhv 0) hrows hrounded (dhc 0) crows crounded
  have bex := M8.Machine.ArbitraryWidthHighHeaderBounds.exchange_bounded P e G B (r 2 e) hP hG hB (by omega)
    hs rs hh hr cr
  have bmv := M8.Machine.ArbitraryWidthHighHeaderBounds.movement_bounded P e G B (r 2 e) hP hG hB (by omega)
    _ _ _ rs (mv 0) (mc 0) (mv 1) (mc 1) (mv 2) (mc 2) hr cr
  have bpd := padding_bounded P e G B hP hG hB he _ hph
  rw [← hVdef] at bex bmv bpd
  have sxb := sources_append (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.exchange_sources base P G B e (r 2 e)
    dh jh exchange hs rs sx) (Width.privateOut (q := prime) (e - r 2 e))
  have smb := sources_append (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.movement_sources base P G B e (r 2 e)
    dh jh exchange hs rs sx) (Width.privateOut (q := prime) (e - r 2 e))
  have spb := padding_sources base P G B e dh jh rowsSlot roundedSlot rowBits roundedBits jhv jhc
    rowsTape rowsHead roundedTape roundedHead
  have hbc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.base_cells base P G B e (r 2 e) dh jh focus
  have hft : ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e - r 2 e))).tape
      (low (baseSlot focus)) = sourceWord x := by
    simp only [low, Tapes.append, Fin.addCases_left]
    exact hbc.2.trans hf
  have hfh : ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e - r 2 e))).head
      (low (baseSlot focus)) = 0 := by
    simp only [low, Tapes.append, Fin.addCases_left]
    exact hbc.1.trans hhead
  obtain ⟨c, hc, hi⟩ := hC P e G B he hP hG hB hs rs _ _ _ hh hjc _ hph
    ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e - r 2 e))) (low (baseSlot focus))
    (fun i => low (exchangeFocus exchange i)) (fun i => low (movementFocus exchange i))
    (padFocus rowsSlot roundedSlot) V hV sxb smb spb bex bmv bpd x hft hfh
  rw [SharedPlacementAlphabet.setTape_append_left, changed_bank] at hi
  -- the width's erasure
  have hwe := Width.shared_cleans Params.prime_two
    (bank (setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0) P G B e (r 2 e) dh jh)
    wslot (hwc _).1 (hwc _).2
  have hwe' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hwe
    (SharedBank.empty exchangeCount prime)) (SharedBank.empty movementCount prime))
    (SharedBank.empty (padCount capacity) prime)
  -- the metadata's erasure
  have hcl := M8.Machine.ArbitraryWidthHighBranchPrepare.cleans dimensions
    (setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)
    prime P G B e (r 2 e) (padded 2 e) V Params.prime_two (by omega) hP hG hB hV dh jh dhv dhc jhv jhc bP bG bB be bR
  have hcl' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hcl
    (Width.privateIn (q := prime))) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty (padCount capacity) prime)
  have hrun := (hp'.seq ((hw'.seq hi).seq hwe')).seq hcl'
  refine ⟨_, ?_, hrun.consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
  -- the cost
  have hD : 0 < ArbitraryWidthHighDimensions.dataVolume prime P G B e := by rw [← hdvol]; exact hU
  have hs1 := M8.Machine.ArbitraryWidthHighBranchPrepare.setup_cost_bound prime P G B e hD
  have hs2 := M8.Machine.ArbitraryWidthHighBranchPrepare.cleanup_cost_bound prime P G B e hD
  rw [← hdvol, ← hVdef] at hs1 hs2
  have heU : e ≤ volume prime (originalDescriptor P e G B) := by rw [hdvol]; exact ho.2 3
  exact cost_arith hs1 hs2 hVdef heU hU hc rfl

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Prepared
