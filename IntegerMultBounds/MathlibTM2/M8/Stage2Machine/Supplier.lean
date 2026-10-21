module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.High
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Lift
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchComposition
public import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
public import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
public import IntegerMultBounds.Machine.FiniteReturnStackAt

/-!
# The stage-2 supplier on a caller's six headers

One fixed program for every descriptor. It writes the constant `threshold 2 - 1` on a guard tape,
compares it with the width header (stage 1's `ArbitraryWidthHighBranchComposition`), and runs the
stage-2 high path (`High.program`) past the threshold, stage 1's whole original-descriptor machine
(`ArbitraryWidthOriginalTotalRun.program`) below it; then it erases the constant. Both branches
share one bank: stage 1's private banks outside the high path's (`Lift`). Every private bank starts
and finishes blank, and the caller's source is transposed within `C V max(1,e)^τ₂` (`runs`): past
the threshold by the high path's bound, below it by stage 1's bound at `τ₁ ≥ τ₂` on bounded widths
(`HighCost.small_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Supplier

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthHighCommonFallback (elementaryCount)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ padCount)
open Params (threshold)

/-! ### A constant on one tape -/

/-- Write the descriptor of `n` on a blank tape. -/
def constProgram {N : ℕ} (n : ℕ) (slot : Fin N) :=
  Placement.placed (RecursiveChildQuotientsConstant.program (a := prime) n) (FiniteReturnStackAt.placement slot)

theorem const_hoare {N : ℕ} (n : ℕ) (slot : Fin N) (v : Tapes N prime)
    (ht : v.tape slot = fun _ => blank) (hh : v.head slot = 0) :
    HoareTime (constProgram n slot) (fun w => w = v)
      (fun w => w = setTape v slot (BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits n)) 1)
      (RecursiveChildQuotientsConstant.cost n) := by
  have hi : Placement.active (FiniteReturnStackAt.placement slot) v = FiniteReturnStack.bank (fun _ => blank) 0 := by
    rw [FiniteReturnStackAt.active_bank, ht, hh]
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := prime) n)
    (FiniteReturnStackAt.placement slot) v hi
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z, rfl, rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

/-! ### The banks -/

/-- The guard's two tapes: the constant and the selector's flag. -/
def guard : Tapes 2 prime := SharedBank.empty 2 prime

/-- The guard with the constant written. -/
def guardWith (n : ℕ) : Tapes 2 prime :=
  setTape guard 0 (BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits n)) 1

/-- Stage 1's private banks around a caller. -/
abbrev outer {t : ℕ} [M8.Machine.Net] (x : Tapes t prime) := M8.Machine.ArbitraryWidthOriginalZeroBranch.input x

/-- The slot of a caller tape among stage 1's private banks. -/
def outerSlot [M8.Machine.Net] {t : ℕ} (j : Fin t) : Fin (M8.Machine.ArbitraryWidthOriginalZeroBranch.count t) :=
  Fin.castAdd elementaryCount (Fin.castAdd M8.Machine.ArbitraryWidthHighRun.paddingCount
    (Fin.castAdd movementCount (Fin.castAdd exchangeCount (Fin.castAdd 1 (Fin.castAdd 12
      (Fin.castAdd 17 (Fin.castAdd 19 (Fin.castAdd 16 j))))))))

theorem outer_lift [M8.Machine.Net] {t : ℕ} : Lift (outer (t := t)) outerSlot where
  inj := by
    intro i j h
    unfold outerSlot at h
    simpa only [Fin.castAdd_inj] using h
  tape c j := by
    simp only [outer, M8.Machine.ArbitraryWidthOriginalZeroBranch.input, M8.Machine.ArbitraryWidthHighPreparedRun.input,
      M8.Machine.ArbitraryWidthHighExecutionInitialize.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input,
      M8.Machine.ArbitraryWidthHighCommonPrepare.input, outerSlot, Tapes.append, Fin.addCases_left]
  head c j := by
    simp only [outer, M8.Machine.ArbitraryWidthOriginalZeroBranch.input, M8.Machine.ArbitraryWidthHighPreparedRun.input,
      M8.Machine.ArbitraryWidthHighExecutionInitialize.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input,
      M8.Machine.ArbitraryWidthHighCommonPrepare.input, outerSlot, Tapes.append, Fin.addCases_left]
  set c j f p := by
    simp only [outer, M8.Machine.ArbitraryWidthOriginalZeroBranch.input, M8.Machine.ArbitraryWidthHighPreparedRun.input,
      M8.Machine.ArbitraryWidthHighExecutionInitialize.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input,
      M8.Machine.ArbitraryWidthHighCommonPrepare.input, outerSlot, SharedPlacementAlphabet.setTape_append_left]

/-- Stage 1's private banks around a program. -/
def extendOuter [M8.Machine.Net] {t states : ℕ} (M : Program t states prime) :=
  extend (extend (extend (extend (extend (extend (extend (extend (extend M 16) 19) 17) 12) 1) exchangeCount)
    movementCount) M8.Machine.ArbitraryWidthHighRun.paddingCount) elementaryCount

theorem extend_outer [M8.Machine.Net] {t states budget : ℕ} {M : Program t states prime} {v w : Tapes t prime}
    (h : HoareTime M (fun z => z = v) (fun z => z = w) budget) :
    HoareTime (extendOuter M) (fun z => z = outer v) (fun z => z = outer w) budget :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h (FixedHeaderBankCopy.empty 16))
    M8.Machine.ArbitraryWidthHighPrepareShared.privateInput) (FixedHeaderBankCopy.empty 17))
    (FixedHeaderBankCopy.empty 12)) ArbitraryWidthZeroHeaderShared.empty) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty M8.Machine.ArbitraryWidthHighRun.paddingCount prime))
    (FixedHeaderBankCopy.empty elementaryCount)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)
variable {t : ℕ}

/-- The high path's tape count. -/
abbrev innerCount (t : ℕ) :=
  ((((((Common.count t + 17) + 12) + 1) + 22) + exchangeCount) + movementCount) + padCount capacity

/-- The slot of a caller tape among the high path's private banks. -/
def innerSlot (j : Fin t) : Fin (innerCount capacity t) :=
  Fin.castAdd (padCount capacity) (Fin.castAdd movementCount (Fin.castAdd exchangeCount (Fin.castAdd 22
    (Fin.castAdd 1 (Fin.castAdd 12 (Fin.castAdd 17 (Fin.castAdd 19 (Fin.castAdd 16 j))))))))

theorem inner_lift : Lift (High.input capacity (t := t)) (innerSlot capacity) where
  inj := by
    intro i j h
    unfold innerSlot at h
    simpa only [Fin.castAdd_inj] using h
  tape c j := by
    simp only [High.input, Prepared.input, Init.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input, Common.input,
      innerSlot, Tapes.append, Fin.addCases_left]
  head c j := by
    simp only [High.input, Prepared.input, Init.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input, Common.input,
      innerSlot, Tapes.append, Fin.addCases_left]
  set c j f p := by
    simp only [High.input, Prepared.input, Init.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input, Common.input,
      innerSlot, SharedPlacementAlphabet.setTape_append_left]

/-- The tape count of the supplier. -/
abbrev count (t : ℕ) := M8.Machine.ArbitraryWidthOriginalZeroBranch.count (innerCount capacity (t+2))

/-- A caller or guard tape on the supplier's bank. -/
def slot (j : Fin (t+2)) : Fin (count capacity t) := outerSlot (innerSlot capacity j)

theorem slot_injective : Function.Injective (slot capacity (t := t)) :=
  (outer_lift (t := innerCount capacity (t+2))).inj.comp (inner_lift capacity).inj

def rho : Fin (count capacity t) := slot capacity (Fin.natAdd t 0)
def flag : Fin (count capacity t) := slot capacity (Fin.natAdd t 1)
def width (headers : Fin 6 → Fin t) : Fin (count capacity t) := slot capacity (Fin.castAdd 2 (headers 3))

theorem rho_ne_width (headers : Fin 6 → Fin t) : rho capacity ≠ width capacity headers := by
  intro h
  have := congrArg Fin.val (slot_injective capacity h)
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  have := (headers 3).isLt
  omega

theorem rho_ne_flag : rho capacity (t := t) ≠ flag capacity := by
  intro h
  have := congrArg Fin.val (slot_injective capacity h)
  simp only [Fin.val_natAdd] at this
  omega

theorem width_ne_flag (headers : Fin 6 → Fin t) : width capacity headers ≠ flag capacity := by
  intro h
  have := congrArg Fin.val (slot_injective capacity h)
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  have := (headers 3).isLt
  omega

/-- The guard constant. -/
abbrev bound : ℕ := threshold 2 - 1

/-- **The stage-2 supplier.** -/
def program (headers : Fin 6 → Fin t) (source : Fin t) :=
  seq (seq (constProgram bound (rho capacity))
    (M8.Machine.ArbitraryWidthHighBranchComposition.program (rho capacity) (width capacity headers) (flag capacity)
      (rho_ne_width capacity headers) (rho_ne_flag capacity) (width_ne_flag capacity headers)
      (extendOuter (High.program capacity (fun i => Fin.castAdd 2 (headers i)) (Fin.castAdd 2 source)))
      (M8.Machine.ArbitraryWidthOriginalTotalRun.program (fun i => innerSlot capacity (Fin.castAdd 2 (headers i)))
        (innerSlot capacity (Fin.castAdd 2 source)))))
    (BinaryDescriptorCleanupList.oneProgram (rho capacity))

/-- The blank private banks. -/
def input (caller : Tapes t prime) := outer (High.input capacity (caller.append guard))

omit [M8.Machine.Net] in
theorem cost_arith {w er Vb V n hc : ℕ} {B : ℝ} (hV : 1 ≤ V) (hVb : Vb = V + n) (hB : (hc : ℝ) ≤ B) :
    ((w + 1 + (21 * Vb + 1 + hc) + 1 + er : ℕ) : ℝ) ≤ ((w + er + 21 + 21 * n + 3 : ℕ) : ℝ) * V + B := by
  have h : w + 1 + (21 * Vb + 1 + 0) + 1 + er ≤ (w + er + 21 + 21 * n + 3) * V := by subst hVb; nlinarith
  have h' : ((w + 1 + (21 * Vb + 1 + 0) + 1 + er : ℕ) : ℝ) ≤ ((w + er + 21 + 21 * n + 3 : ℕ) : ℝ) * V := by
    exact_mod_cast h
  have hseq : w + 1 + (21 * Vb + 1 + hc) + 1 + er = (w + 1 + (21 * Vb + 1 + 0) + 1 + er) + hc := by ring
  rw [hseq, Nat.cast_add]
  linarith

omit [M8.Machine.Net] in
theorem final_arith {L V P B A : ℝ} (hP : 1 ≤ P) (hV : 0 ≤ V) (hL : 0 ≤ L) (hB : B ≤ A * V * P) :
    L * V + B ≤ (L + A) * V * P := by
  have : L * V ≤ L * V * P := le_mul_of_one_le_right (mul_nonneg hL hV) hP
  nlinarith

omit [M8.Machine.Net] in
theorem bound_le {T L V P B A : ℝ} (hT : T ≤ L * V + B) (hB : B ≤ A * V * P) (hP : 1 ≤ P) (hV : 0 ≤ V)
    (hL : 0 ≤ L) : T ≤ (L + A + 1) * V * P := by
  have h1 := final_arith hP hV hL hB
  have h2 : 0 ≤ V * P := mul_nonneg hV (by linarith)
  nlinarith

omit [M8.Machine.Net] in
theorem high_B {C D X V P : ℝ} (hP : 1 ≤ P) (hV : 0 ≤ V) (hX : 0 ≤ X) :
    C * V * P + D * V ≤ (|C| + |D| + X) * V * P := by
  have hVP : 0 ≤ V * P := mul_nonneg hV (by linarith)
  have h1 : C * (V * P) ≤ |C| * (V * P) := mul_le_mul_of_nonneg_right (le_abs_self C) hVP
  have h2 : D * V ≤ |D| * V := mul_le_mul_of_nonneg_right (le_abs_self D) hV
  have h3 : |D| * V ≤ |D| * (V * P) := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg D)
  have h4 : 0 ≤ X * (V * P) := mul_nonneg hX hVP
  nlinarith

omit [M8.Machine.Net] in
theorem low_B {C D X V P : ℝ} (hP : 1 ≤ P) (hV : 0 ≤ V) : X * V * P ≤ (|C| + |D| + X) * V * P := by
  have hVP : 0 ≤ V * P := mul_nonneg hV (by linarith)
  have : 0 ≤ (|C| + |D|) * (V * P) := mul_nonneg (by positivity) hVP
  nlinarith

theorem tau₂_le (hτ : Exponents HighCost.K) : tau₂ HighCost.K ≤ M8.Machine.BudgetBound.tau := by
  have h := hτ.s1
  simp only [tau₂, Stage2Width.tau2]
  have hK : (0 : ℝ) ≤ ((HighCost.K : ℕ) : ℝ)⁻¹ := by positivity
  have hK1 : ((HighCost.K : ℕ) : ℝ)⁻¹ ≤ 1 := by norm_num
  nlinarith

/-- **The stage-2 supplier**: from blank private banks to blank private banks, the caller's source
is transposed within a constant times `V max(1,e)^τ₂`. -/
theorem runs (hspec : FamilySpec capacity) (hτ : Exponents HighCost.K) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : ℕ} (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
      (d : Descriptor) (hs : Fin 6 → List Bool), d.Positive → RecursiveDimensionBank.Headers d hs →
      (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) → (∀ i, caller.head (headers i) = 1) →
      ∀ x : Fin (volume prime d) → ZMod 2, caller.tape source = sourceWord x → caller.head source = 0 →
      ∃ c : ℕ, (c : ℝ) ≤ C * volume prime d * ((max 1 d.width : ℕ) : ℝ) ^ tau₂ HighCost.K ∧
        HoareTime (program capacity headers source) (fun z => z = input capacity caller)
          (fun z => z = input capacity (setTape caller source
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c := by
  obtain ⟨C, D, hCD⟩ := High.runs capacity hspec hτ
  obtain ⟨C₁, hC₁, hb₁⟩ := M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound
  have hτ₂ := tau₂_le hτ
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = RecursiveChildQuotientsConstant.cost bound +
      (2 * (RecursiveChildQuotientsConstant.bits bound).length + 4) + 21 + 21 * bound + 3 := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = ((threshold 2 : ℕ) : ℝ) ^ (M8.Machine.BudgetBound.tau - tau₂ HighCost.K) :=
    ⟨_, rfl⟩
  have hE : 0 ≤ E := hEdef ▸ Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |C| + |D| + C₁ * E := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨(L : ℝ) + A + 1, by positivity, fun {t} caller headers source d hs hp hv ht hh x hf hhead => ?_⟩
  have h5 := Prepared.five_le_threshold
  have hVpos := RecursiveAffinePrepare.volume_positive Params.prime_two d hp
  have il := inner_lift capacity (t := t + 2)
  have ol := outer_lift (t := innerCount capacity (t + 2))
  -- the guard's cells
  have gt0 : (guardWith bound).tape 0 = BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits bound) := by
    simp [guardWith, setTape]
  have gh0 : (guardWith bound).head 0 = 1 := by simp [guardWith, setTape]
  have gt1 : (guardWith bound).tape 1 = fun _ => blank := by simp [guardWith, guard, setTape, SharedBank.empty]
  have gh1 : (guardWith bound).head 1 = 0 := by simp [guardWith, guard, setTape, SharedBank.empty]
  have hguard : setTape (guardWith bound) 0 (fun _ => blank) 0 = guard := by
    unfold guardWith
    rw [SharedPlacementAlphabet.setTape_setTape]
    exact SharedPlacementAlphabet.setTape_self guard 0
  have cell : ∀ (y : Tapes (t+2) prime) (j : Fin (t+2)),
      (outer (High.input capacity y)).tape (slot capacity j) = y.tape j ∧
      (outer (High.input capacity y)).head (slot capacity j) = y.head j := fun y j =>
    ⟨(ol.tape _ _).trans (il.tape _ _), (ol.head _ _).trans (il.head _ _)⟩
  have setc : ∀ (y : Tapes (t+2) prime) (j : Fin (t+2)) (f : ℤ → Fin (prime+4)) (p : ℤ),
      setTape (outer (High.input capacity y)) (slot capacity j) f p = outer (High.input capacity (setTape y j f p)) :=
    fun y j f p => by rw [il.set, ol.set]; rfl
  -- write the constant
  have hw := const_hoare bound (rho capacity) (input capacity caller)
    (by rw [input, rho, (cell _ _).1]; simp [Tapes.append, guard, SharedBank.empty])
    (by rw [input, rho, (cell _ _).2]; simp [Tapes.append, guard, SharedBank.empty])
  rw [input, rho, setc, SharedPlacementAlphabet.setTape_append_right] at hw
  change HoareTime _ _ (fun w => w = outer (High.input capacity (caller.append (guardWith bound)))) _ at hw
  -- the branch
  obtain ⟨W, hW⟩ : ∃ W, W = sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x) := ⟨_, rfl⟩
  rw [← hW]
  have hcells : ∀ (y : Tapes t prime) (j : Fin t), (y.append (guardWith bound)).tape (Fin.castAdd 2 j) = y.tape j ∧
      (y.append (guardWith bound)).head (Fin.castAdd 2 j) = y.head j := fun y j =>
    ⟨by simp only [Tapes.append, Fin.addCases_left], by simp only [Tapes.append, Fin.addCases_left]⟩
  have gcells : ∀ (y : Tapes t prime) (j : Fin 2), (y.append (guardWith bound)).tape (Fin.natAdd t j) =
      (guardWith bound).tape j ∧ (y.append (guardWith bound)).head (Fin.natAdd t j) = (guardWith bound).head j :=
    fun y j => ⟨by simp only [Tapes.append, Fin.addCases_right], by simp only [Tapes.append, Fin.addCases_right]⟩
  have hout_set : setTape (caller.append (guardWith bound)) (Fin.castAdd 2 source) W 0 =
      (setTape caller source W 0).append (guardWith bound) :=
    SharedPlacementAlphabet.setTape_append_left _ _ _ _ _
  have hrs := RecursiveChildQuotientsConstant.bits_value bound
  have hes := hv.1 3
  have hwV : d.width ≤ volume prime d := RecursiveHeaderBounds.values_le_volume Params.prime_two d hp 3
  have hcond : (1 ≤ Counter.value (RecursiveChildQuotientsConstant.bits bound) ∧
      Counter.value (RecursiveChildQuotientsConstant.bits bound) < Counter.value (hs 3)) ↔ threshold 2 ≤ d.width := by
    rw [hrs, hes]
    show (1 ≤ threshold 2 - 1 ∧ threshold 2 - 1 < d.width) ↔ threshold 2 ≤ d.width
    omega
  have hrr : (outer (High.input capacity (caller.append (guardWith bound)))).tape (rho capacity) =
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits bound) := by
    rw [rho, (cell _ _).1, (gcells _ 0).1, gt0]
  have hrh : (outer (High.input capacity (caller.append (guardWith bound)))).head (rho capacity) = 1 := by
    rw [rho, (cell _ _).2, (gcells _ 0).2, gh0]
  have her : (outer (High.input capacity (caller.append (guardWith bound)))).tape (width capacity headers) =
      BinaryDescriptorStack.descriptor (hs 3) := by
    rw [width, (cell _ _).1, (hcells _ _).1, ht 3, BinaryDescriptorStackRoundtrip.descriptor_encoded]
  have heh : (outer (High.input capacity (caller.append (guardWith bound)))).head (width capacity headers) = 1 := by
    rw [width, (cell _ _).2, (hcells _ _).2, hh 3]
  have hfr : (outer (High.input capacity (caller.append (guardWith bound)))).tape (flag capacity) = fun _ => blank := by
    rw [flag, (cell _ _).1, (gcells _ 1).1, gt1]
  have hfh : (outer (High.input capacity (caller.append (guardWith bound)))).head (flag capacity) = 0 := by
    rw [flag, (cell _ _).2, (gcells _ 1).2, gh1]
  -- the erasure of the constant
  have he := BinaryDescriptorCleanupList.one_hoare (rho capacity)
    (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound))))
    (RecursiveChildQuotientsConstant.bits bound) (by rw [rho, (cell _ _).1, (gcells _ 0).1, gt0])
    (by rw [rho, (cell _ _).2, (gcells _ 0).2, gh0])
  rw [rho, setc, SharedPlacementAlphabet.setTape_append_right, hguard] at he
  have hVb : 0 < volume prime d + bound := by omega
  have hP1 : (1 : ℝ) ≤ ((max 1 d.width : ℕ) : ℝ) ^ tau₂ HighCost.K :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 d.width) (by linarith [hτ.two])
  have hV0 : (0 : ℝ) ≤ volume prime d := Nat.cast_nonneg _
  have hV1 : 1 ≤ volume prime d := hVpos
  by_cases hg : threshold 2 ≤ d.width
  · obtain ⟨c, hc, hhigh⟩ := hCD (caller.append (guardWith bound)) (fun i => Fin.castAdd 2 (headers i))
      (Fin.castAdd 2 source) d hs hp hg hv (fun i => (hcells _ _).1.trans (ht i))
      (fun i => (hcells _ _).2.trans (hh i)) x ((hcells _ _).1.trans hf) ((hcells _ _).2.trans hhead)
    rw [← hW, hout_set] at hhigh
    have hb := M8.Machine.ArbitraryWidthHighBranchComposition.runs_same_volume (rho capacity)
      (width capacity headers) (flag capacity) (rho_ne_width capacity headers) (rho_ne_flag capacity)
      (width_ne_flag capacity headers)
      (extendOuter (High.program capacity (fun i => Fin.castAdd 2 (headers i)) (Fin.castAdd 2 source)))
      (M8.Machine.ArbitraryWidthOriginalTotalRun.program (fun i => innerSlot capacity (Fin.castAdd 2 (headers i)))
        (innerSlot capacity (Fin.castAdd 2 source)))
      (outer (High.input capacity (caller.append (guardWith bound))))
      (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound)))) c 0
      (volume prime d + bound) hVb (RecursiveChildQuotientsConstant.bits bound) (hs 3)
      (RecursiveChildQuotientsConstant.bits_canonical bound) (hv.2 3) (by rw [hrs]; omega)
      (by rw [hes]; exact hwV.trans (Nat.le_add_right _ _))
      hrr hrh her heh hfr hfh (fun _ => extend_outer hhigh) (fun hn => absurd (hcond.mpr hg) hn)
    rw [ite_eq_left_iff.mpr (fun hn => absurd (hcond.mpr hg) hn)] at hb
    refine ⟨_, ?_, ((hw.seq hb).seq he).consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
    have hmax : max 1 d.width = d.width := max_eq_right (by omega)
    rw [hmax] at hP1 ⊢
    have h1 := cost_arith (w := RecursiveChildQuotientsConstant.cost bound)
      (er := 2 * (RecursiveChildQuotientsConstant.bits bound).length + 4) (n := bound) hV1 rfl hc
    rw [← hL] at h1
    have hB := high_B (C := C) (D := D) (X := C₁ * E) hP1 hV0 (mul_nonneg hC₁.le hE)
    rw [← hA] at hB
    exact bound_le h1 hB hP1 hV0 (Nat.cast_nonneg L)
  · have hfb := M8.Machine.ArbitraryWidthOriginalTotalRun.runs (High.input capacity (caller.append (guardWith bound)))
      (fun i => innerSlot capacity (Fin.castAdd 2 (headers i))) (innerSlot capacity (Fin.castAdd 2 source)) d hs hp hv
      (fun i => (il.tape _ _).trans ((hcells _ _).1.trans (ht i)))
      (fun i => (il.head _ _).trans ((hcells _ _).2.trans (hh i))) x
      ((il.tape _ _).trans ((hcells _ _).1.trans hf)) ((il.head _ _).trans ((hcells _ _).2.trans hhead))
    rw [← hW, ← il.set, hout_set] at hfb
    have hb := M8.Machine.ArbitraryWidthHighBranchComposition.runs_same_volume (rho capacity)
      (width capacity headers) (flag capacity) (rho_ne_width capacity headers) (rho_ne_flag capacity)
      (width_ne_flag capacity headers)
      (extendOuter (High.program capacity (fun i => Fin.castAdd 2 (headers i)) (Fin.castAdd 2 source)))
      (M8.Machine.ArbitraryWidthOriginalTotalRun.program (fun i => innerSlot capacity (Fin.castAdd 2 (headers i)))
        (innerSlot capacity (Fin.castAdd 2 source)))
      (outer (High.input capacity (caller.append (guardWith bound))))
      (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound)))) 0
      (M8.Machine.ArbitraryWidthOriginalTotalRun.cost d hs)
      (volume prime d + bound) hVb (RecursiveChildQuotientsConstant.bits bound) (hs 3)
      (RecursiveChildQuotientsConstant.bits_canonical bound) (hv.2 3) (by rw [hrs]; omega)
      (by rw [hes]; exact hwV.trans (Nat.le_add_right _ _))
      hrr hrh her heh hfr hfh (fun hy => absurd (hcond.mp hy) hg) (fun _ => hfb)
    rw [ite_eq_right_iff.mpr (fun hy => absurd (hcond.mp hy) hg)] at hb
    refine ⟨_, ?_, ((hw.seq hb).seq he).consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
    have hsmall := HighCost.small_le hτ₂ hC₁.le (show d.width < threshold 2 by omega) hV0 (hb₁ d hs hp hv)
    rw [← hEdef] at hsmall
    have h1 := cost_arith (w := RecursiveChildQuotientsConstant.cost bound)
      (er := 2 * (RecursiveChildQuotientsConstant.bits bound).length + 4) (n := bound) hV1 rfl hsmall
    rw [← hL] at h1
    have hB := low_B (C := C) (D := D) (X := C₁ * E) hP1 hV0
    rw [← hA] at hB
    exact bound_le h1 hB hP1 hV0 (Nat.cast_nonneg L)

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Supplier
