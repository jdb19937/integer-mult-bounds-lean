module

public import IntegerMultBounds.MathlibTM2.Fast.CRTLinear
public import IntegerMultBounds.MathlibTM2.Fast.CRTDrive
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Runtime paired-gap reversal

Two unary width streams are traversed from opposite ends. A pair removes its
endpoint widths from the remaining middle counter, executes the actual gap
exchange, and extends the completed prefix and suffix. Consumed entries are
saved for later stream restoration. A unary half-count controls the loop.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Construct the number of endpoint pairs from the runtime axis count,
keeping that count and returning temporary storage unchanged. -/
theorem crtReverseHalf_runs {axes pairs tmp : Fin T}
    (hap : axes ≠ pairs) (hat : axes ≠ tmp) (hpt : pairs ≠ tmp)
    (R : Regs T A) (ht : R tmp = []) (hp : R pairs = []) :
    crtRuns body (udiv 2 axes pairs tmp) R
      (Function.update R pairs (List.replicate ((R axes).length / 2) tick))
      (4 * (R axes).length + 4) := by
  apply crtRuns_of_exec
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := udiv_exec body (by decide : 1 ≤ 2) hap hat hpt v S (hS ▸ ht)
  refine ⟨v', m, hu, by simpa [hS] using hm, ?_⟩
  simpa [hS, hp] using he

/-- One nonempty while iteration followed by a checked tail execution. -/
theorem crtReverseWhile_step {test : Fin T} {p : Pr F T Q A U}
    {R R₁ R₂ : Regs T A} {b c : ℕ} (hne : R test ≠ [])
    (hp : crtRuns body p R R₁ b) (ht : crtRuns body (crtWhile test p) R₁ R₂ c) :
    crtRuns body (crtWhile test p) R R₂ (b + c + 2) := by
  intro v S hS hL
  let v₀ := { v with flag := (S.R test).head?.isSome }
  have hpeek := Exec.act (body := body) (peekR test) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v₁, m, hu, hm, he⟩ := hp v₀ S hS hL
  obtain ⟨v₂, n, hu₂, hn, he₂⟩ := ht v₁ { S with R := R₁ } rfl hL
  unfold crtWhile at he₂
  cases he₂ with
  | seq first tail =>
    cases first
    rename_i n
    refine ⟨v₂, 1 + ((m + 1) + n + 1), hu₂.trans hu, ?_, ?_⟩
    · omega
    · apply Exec.seq hpeek
      apply Exec.loop_true
      · change (S.R test).head?.isSome = true
        rw [hS]
        cases hxs : R test with
        | nil => exact False.elim (hne hxs)
        | cons x xs => rfl
      · exact Exec.seq he (Exec.act (body := body) (peekR test) _)
      · exact tail

/-- Named registers used by one endpoint-pair iteration. -/
inductive CrtReverseReg
  | str | stmp | left | right | leftDone | rightDone
  | pre | gap | post | aJ | aK | e3B | tu | t₁ | t₂ | tmp
  deriving DecidableEq

/-- Consuming the two endpoint widths and removing them from the middle
counter is independent of the physical data exchange. -/
def crtReversePairLoad (r : CrtReverseReg → Fin T) : Pr F T Q A U :=
  .seq (crtPopEnt (r .left) (r .aJ))
    (.seq (crtPopEnt (r .right) (r .aK))
      (.seq (usub (r .aJ) (r .gap) (r .tmp)) (usub (r .aK) (r .gap) (r .tmp))))

def crtReversePairLoadRegs (r : CrtReverseReg → Fin T) (R : Regs T A)
    (aj ak : ℕ) (left right : List ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (r .left) (crtEnts left)) (r .aJ) (List.replicate aj tick))
    (r .right) (crtEnts right)) (r .aK) (List.replicate ak tick))
    (r .gap) ((R (r .gap)).drop aj |>.drop ak)

/-- Actual setup of one pair restores scratch and preserves all data and
completed-width counters. -/
theorem crtReversePairLoad_runs {r : CrtReverseReg → Fin T} (hr : Function.Injective r)
    (R : Regs T A) (aj ak : ℕ) (left right : List ℕ)
    (hl : R (r .left) = crtEnts (aj :: left))
    (hright : R (r .right) = crtEnts (ak :: right))
    (hj : R (r .aJ) = []) (hk : R (r .aK) = []) (ht : R (r .tmp) = []) :
    crtRuns body (crtReversePairLoad r) R (crtReversePairLoadRegs r R aj ak left right)
      (6 * (aj + ak) + 16) := by
  have h₁ := crtPopEnt_runs (body := body) (hr.ne (by decide : CrtReverseReg.left ≠ .aJ))
    R aj left hl hj
  let R₁ := Function.update (Function.update R (r .left) (crtEnts left)) (r .aJ) (List.replicate aj tick)
  have h₂ := crtPopEnt_runs (body := body) (hr.ne (by decide : CrtReverseReg.right ≠ .aK))
    R₁ ak right (by simp [R₁, hr.eq_iff, hright]) (by simp [R₁, hr.eq_iff, hk])
  let R₂ := Function.update (Function.update R₁ (r .right) (crtEnts right)) (r .aK) (List.replicate ak tick)
  have h₃ := crtUsub_runs (body := body) (hr.ne (by decide : CrtReverseReg.aJ ≠ .gap))
    (hr.ne (by decide : CrtReverseReg.aJ ≠ .tmp)) (hr.ne (by decide : CrtReverseReg.gap ≠ .tmp))
    R₂ (by simp [R₂, R₁, hr.eq_iff, ht])
  have hj₂ : (R₂ (r .aJ)).length = aj := by simp [R₂, R₁, hr.eq_iff]
  rw [hj₂] at h₃
  let R₃ := Function.update R₂ (r .gap) ((R₂ (r .gap)).drop aj)
  have h₄ := crtUsub_runs (body := body) (hr.ne (by decide : CrtReverseReg.aK ≠ .gap))
    (hr.ne (by decide : CrtReverseReg.aK ≠ .tmp)) (hr.ne (by decide : CrtReverseReg.gap ≠ .tmp))
    R₃ (by simp [R₃, R₂, R₁, hr.eq_iff, ht])
  have hk₃ : (R₃ (r .aK)).length = ak := by simp [R₃, R₂, R₁, hr.eq_iff]
  rw [hk₃] at h₄
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))) ?_) (by omega)
  simp [crtReversePairLoadRegs, R₃, R₂, R₁, hr.eq_iff]

/-- Extend completed physical widths by the exchanged endpoints, and save
the original endpoint words for exact restoration of both parameter streams. -/
def crtReversePairSave (r : CrtReverseReg → Fin T) : Pr F T Q A U :=
  .seq (ucopy (r .aK) (r .pre) (r .tmp))
    (.seq (ucopy (r .aJ) (r .post) (r .tmp))
      (.seq (crtPushEnt (r .aJ) (r .leftDone)) (crtPushEnt (r .aK) (r .rightDone))))

def crtReversePairSaveRegs (r : CrtReverseReg → Fin T) (R : Regs T A) (aj ak : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update R
    (r .pre) (List.replicate ak tick ++ R (r .pre)))
    (r .post) (List.replicate aj tick ++ R (r .post)))
    (r .aJ) []) (r .leftDone) (crtEnt aj ++ R (r .leftDone)))
    (r .aK) []) (r .rightDone) (crtEnt ak ++ R (r .rightDone))

theorem crtReversePairSave_runs {r : CrtReverseReg → Fin T} (hr : Function.Injective r)
    (R : Regs T A) (aj ak : ℕ) (hj : R (r .aJ) = List.replicate aj tick)
    (hk : R (r .aK) = List.replicate ak tick) (ht : R (r .tmp) = []) :
    crtRuns body (crtReversePairSave r) R (crtReversePairSaveRegs r R aj ak)
      (6 * (aj + ak) + 16) := by
  have h₁ := crtUcopy_runs (body := body) (hr.ne (by decide : CrtReverseReg.aK ≠ .pre))
    (hr.ne (by decide : CrtReverseReg.aK ≠ .tmp)) (hr.ne (by decide : CrtReverseReg.pre ≠ .tmp)) R ht
  rw [hk, List.length_replicate] at h₁
  let R₁ := Function.update R (r .pre) (List.replicate ak tick ++ R (r .pre))
  have h₂ := crtUcopy_runs (body := body) (hr.ne (by decide : CrtReverseReg.aJ ≠ .post))
    (hr.ne (by decide : CrtReverseReg.aJ ≠ .tmp)) (hr.ne (by decide : CrtReverseReg.post ≠ .tmp))
    R₁ (by simp [R₁, hr.eq_iff, ht])
  have hj₁ : R₁ (r .aJ) = List.replicate aj tick := by simp [R₁, hr.eq_iff, hj]
  rw [hj₁, List.length_replicate] at h₂
  let R₂ := Function.update R₁ (r .post) (List.replicate aj tick ++ R₁ (r .post))
  have h₃ := crtPushEnt_runs (body := body) (hr.ne (by decide : CrtReverseReg.aJ ≠ .leftDone))
    R₂ aj (by simp [R₂, R₁, hr.eq_iff, hj])
  let R₃ := Function.update (Function.update R₂ (r .aJ) []) (r .leftDone) (crtEnt aj ++ R₂ (r .leftDone))
  have h₄ := crtPushEnt_runs (body := body) (hr.ne (by decide : CrtReverseReg.aK ≠ .rightDone))
    R₃ ak (by simp [R₃, R₂, R₁, hr.eq_iff, hk])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))) ?_) (by omega)
  simp [crtReversePairSaveRegs, R₃, R₂, R₁, hr.eq_iff]

noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {K : ℕ}

/-- One actual paired endpoint exchange, with runtime width-stream traversal. -/
def crtReversePair (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReverseReg → Fin T) : Pr F T Q (prime + K) U :=
  .seq (crtReversePairLoad r)
    (.seq (crtGapSwapStep hQ ι hι hT (r .str) (r .stmp) (r .pre) (r .gap) (r .post)
      (r .aJ) (r .aK) (r .e3B) (r .tu) (r .t₁) (r .t₂)) (crtReversePairSave r))

/-- Gap-exchange budget with the endpoint-stream overhead included. -/
def crtReversePairCost (T pre gap post aj ak B : ℕ) : ℕ :=
  (T + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ (pre + aj + gap + ak + post) * B)) aj ak +
    (6 * swapT 6 + 10) * (pre + gap + post + 3 * B + aj + ak + 2) +
    34 * (2 ^ (pre + aj + gap + ak + post) * B) + 2 * T + 6 * swapT 6 +
    4 * pre + 4 * gap + 4 * post + 18 * B + aj * (4 * aj + 11) + ak * (4 * ak + 11) + 88 +
    (12 * (aj + ak) + 32)

/-- This is the concrete paired iteration, not a premise asking the caller
for an implementation of an exchange. Only layout and register equalities are
required; the vendored gap swap executes inside the fixed program. -/
theorem crtReversePair_runs {d : ℕ} (a : Fin d → ℕ)
    {body' : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {r : CrtReverseReg → Fin T} (hr : Function.Injective r)
    (hbank : ∀ x j, ι j ≠ r x)
    (pre gap post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k)
    (hjgap : j ∉ gap) (hkgap : k ∉ gap) (hj : a j ≤ a k + 1) (hk : a k ≤ a j + 1)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ z ∈ C y, z.val < 8)
    (x : Fin d → ℕ) (R : Regs T (prime + K)) (left right : List ℕ)
    (hstr : R (r .str) = (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten)
    (hl : R (r .left) = crtEnts (a j :: left)) (hright : R (r .right) = crtEnts (a k :: right))
    (hpre : (R (r .pre)).length = crtW a pre)
    (hgap : (R (r .gap)).length = a j + crtW a gap + a k)
    (hpost : (R (r .post)).length = crtW a post)
    (he3 : R (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hzero : ∀ q ∈ [CrtReverseReg.aJ, .aK, .tmp, .stmp, .tu, .t₁, .t₂], R (r q) = [])
    (hι0 : ∀ q, R (ι q) = []) :
    crtRuns body' (crtReversePair hQ ι hι hT r) R
      (crtReversePairSaveRegs r
        (Function.update (crtReversePairLoadRegs r R (a j) (a k) left right) (r .str)
          (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten) (a j) (a k))
      (crtReversePairCost T (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) B) := by
  have h₁ := crtReversePairLoad_runs (body := body') hr R (a j) (a k) left right hl hright
    (hzero .aJ (by simp)) (hzero .aK (by simp)) (hzero .tmp (by simp))
  let R₁ := crtReversePairLoadRegs r R (a j) (a k) left right
  have hgap₁ : (R₁ (r .gap)).length = crtW a gap := by
    simp only [R₁, crtReversePairLoadRegs, Function.update_self, List.length_drop, hgap]
    omega
  have h₂ := crtGapSwapStep_runs (body := body') a hQ ι hι hT
    (str := r .str) (stmp := r .stmp) (uU := r .pre) (gU := r .gap) (vU := r .post)
    (aJ := r .aJ) (aK := r .aK) (e3B := r .e3B) (tu := r .tu) (t₁ := r .t₁) (t₂ := r .t₂)
    (by simp [List.nodup_cons, hr.eq_iff])
    (by intro q hq z; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals exact hbank _ _)
    pre gap post j k hjk hjgap hkgap hj hk C B hB hC h8 x R₁
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hstr])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hpre]) hgap₁
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hpost])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, he3])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hzero .stmp (by simp)])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hzero .tu (by simp)])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hzero .t₁ (by simp)])
    (by simp [R₁, crtReversePairLoadRegs, hr.eq_iff, hzero .t₂ (by simp)])
    (by intro q; simp [R₁, crtReversePairLoadRegs, hbank, hι0])
  let R₂ := Function.update R₁ (r .str) (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten
  have h₃ := crtReversePairSave_runs (body := body') hr R₂ (a j) (a k)
    (by simp [R₂, R₁, crtReversePairLoadRegs, hr.eq_iff])
    (by simp [R₂, R₁, crtReversePairLoadRegs, hr.eq_iff])
    (by simp [R₂, R₁, crtReversePairLoadRegs, hr.eq_iff, hzero .tmp (by simp)])
  refine crtRuns_mono (crtRuns_seq h₁ (crtRuns_seq h₂ h₃)) ?_
  have hwidth : crtW a (pre ++ j :: (gap ++ k :: post)) =
      crtW a pre + a j + crtW a gap + a k + crtW a post := by
    simp [crtW, List.map_append, List.sum_append]
    omega
  rw [hwidth]
  unfold crtReversePairCost
  omega

/-- The fixed runtime paired loop; its count is constructed by `udiv 2`. -/
def crtReverseLoop (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReverseReg → Fin T) (pairs : Fin T) : Pr F T Q (prime + K) U :=
  crtWhile pairs (.seq (crtPop pairs) (crtReversePair hQ ι hι hT r))

/-- Sum of the exact physical pair budgets in the actual outside-in order. -/
def crtReverseLoopCost {d : ℕ} (T : ℕ) (a : Fin d → ℕ) (B : ℕ)
    (o pre post : List (Fin d)) : ℕ :=
  List.bidirectionalRecOn (C := fun _ => List (Fin d) → List (Fin d) → ℕ) o
    (fun _ _ => 2) (fun _ _ _ => 2)
    (fun j gap k rec pre post =>
      crtReversePairCost T (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) B + 3 +
        rec (pre ++ [k]) (j :: post)) pre post

/-- Registers permitted to change during the paired loop. The source
streams are recoverable from their saved prefixes; all scratch is framed. -/
def crtReverseChanged : List CrtReverseReg :=
  [.str, .left, .right, .leftDone, .rightDone, .pre, .gap, .post]

/-- Exact stream-conservation and frame information needed by cleanup. -/
def CrtReverseLoopFrame (r : CrtReverseReg → Fin T) (pairs : Fin T)
    (R R' : Regs T A) : Prop :=
  R' pairs = [] ∧
  (R' (r .leftDone)).reverse ++ R' (r .left) = (R (r .leftDone)).reverse ++ R (r .left) ∧
  (R' (r .rightDone)).reverse ++ R' (r .right) = (R (r .rightDone)).reverse ++ R (r .right) ∧
  (∀ k, k ≠ pairs → (∀ q ∈ crtReverseChanged, k ≠ r q) → R' k = R k) ∧
  (R' (r .pre)).length + (R' (r .gap)).length + (R' (r .post)).length =
    (R (r .pre)).length + (R (r .gap)).length + (R (r .post)).length

/-- The concrete loop reverses an arbitrary duplicate-free middle layout.
This theorem instantiates the pair geometry; it does not assume body execution.
The runtime count is exactly half the number of middle axes. -/
theorem crtReverseLoop_runs {d : ℕ} (a : Fin d → ℕ)
    {body' : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {r : CrtReverseReg → Fin T} (hr : Function.Injective r)
    (hbank : ∀ z q, ι q ≠ r z) (pairs : Fin T)
    (hpairs : ∀ z, r z ≠ pairs) (hipairs : ∀ q, ι q ≠ pairs)
    (hadj : ∀ j k, a j ≤ a k + 1)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ z ∈ C y, z.val < 8)
    (x : Fin d → ℕ) (o : List (Fin d)) (ho : o.Nodup)
    (pre post : List (Fin d)) (R : Regs T (prime + K)) (left right : List ℕ)
    (hstr : R (r .str) = (crtBox a (pre ++ o ++ post) C x).flatten)
    (hl : R (r .left) = crtEnts (o.map a ++ left))
    (hright : R (r .right) = crtEnts (o.reverse.map a ++ right))
    (hpre : (R (r .pre)).length = crtW a pre)
    (hgap : (R (r .gap)).length = crtW a o)
    (hpost : (R (r .post)).length = crtW a post)
    (hcount : R pairs = List.replicate (o.length / 2) tick)
    (he3 : R (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hzero : ∀ q ∈ [CrtReverseReg.aJ, .aK, .tmp, .stmp, .tu, .t₁, .t₂], R (r q) = [])
    (hι0 : ∀ q, R (ι q) = []) :
    ∃ R', R' (r .str) = (crtBox a (pre ++ o.reverse ++ post) C x).flatten ∧
      CrtReverseLoopFrame r pairs R R' ∧
      crtRuns body' (crtReverseLoop hQ ι hι hT r pairs) R R'
        (crtReverseLoopCost T a B o pre post) := by
  induction o using List.bidirectionalRecOn generalizing pre post R left right with
  | H0 =>
    have hc : R pairs = [] := by simpa using hcount
    refine ⟨R, by simpa using hstr, ⟨hc, rfl, rfl, (fun _ _ _ => rfl), rfl⟩, ?_⟩
    have h := crtWhile_runs (body := body') (r := pairs)
      (p := .seq (crtPop pairs) (crtReversePair hQ ι hι hT r))
      (Ψ := fun _ => R) (N := 0) (b := 0) (by intro j hj; omega) hc
    simpa [crtReverseLoop, crtReverseLoopCost] using h
  | H1 j =>
    have hc : R pairs = [] := by simpa using hcount
    refine ⟨R, by simpa using hstr, ⟨hc, rfl, rfl, (fun _ _ _ => rfl), rfl⟩, ?_⟩
    have h := crtWhile_runs (body := body') (r := pairs)
      (p := .seq (crtPop pairs) (crtReversePair hQ ι hι hT r))
      (Ψ := fun _ => R) (N := 0) (b := 0) (by intro k hk; omega) hc
    simpa [crtReverseLoop, crtReverseLoopCost] using h
  | Hn j gap k ih =>
    have hnd : j ≠ k ∧ j ∉ gap ∧ k ∉ gap ∧ gap.Nodup := by
      simp only [List.nodup_cons, List.mem_append, List.mem_singleton, not_or,
        List.nodup_append] at ho
      grind
    have hhalf : (j :: (gap ++ [k])).length / 2 = gap.length / 2 + 1 := by simp; omega
    let R₀ := Function.update R pairs (R pairs).tail
    have hpop := crtPop_runs (body := body') pairs R
    have h₁ := crtReversePair_runs (body' := body') a hQ ι hι hT hr hbank
      pre gap post j k hnd.1 hnd.2.1 hnd.2.2.1 (hadj j k) (hadj k j)
      C B hB hC h8 x R₀ ((gap.map a ++ [a k]) ++ left) ((gap.reverse.map a ++ [a j]) ++ right)
      (by simpa [R₀, hpairs, List.append_assoc] using hstr)
      (by simpa [R₀, hpairs, List.map_append, List.append_assoc] using hl)
      (by simpa [R₀, hpairs, List.reverse_cons, List.reverse_append, List.map_append,
        List.append_assoc] using hright)
      (by simpa [R₀, hpairs] using hpre)
      (by simpa [R₀, hpairs, crtW, List.map_append, List.sum_append, Nat.add_assoc] using hgap)
      (by simpa [R₀, hpairs] using hpost)
      (by simpa [R₀, hpairs] using he3)
      (by intro q hq; simpa [R₀, hpairs] using hzero q hq)
      (by intro q; simpa [R₀, hipairs] using hι0 q)
    let R₁ := crtReversePairLoadRegs r R₀ (a j) (a k)
      ((gap.map a ++ [a k]) ++ left) ((gap.reverse.map a ++ [a j]) ++ right)
    let R₂ := Function.update R₁ (r .str) (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten
    let R₃ := crtReversePairSaveRegs r R₂ (a j) (a k)
    change crtRuns body' _ R₀ R₃ _ at h₁
    have hsource : R₃ (r .str) = (crtBox a ((pre ++ [k]) ++ gap ++ j :: post) C x).flatten := by
      simp [R₃, R₂, crtReversePairSaveRegs, hr.eq_iff, List.append_assoc]
    have hleft : R₃ (r .left) = crtEnts (gap.map a ++ (a k :: left)) := by
      simp [R₃, R₂, R₁, crtReversePairSaveRegs, crtReversePairLoadRegs, hr.eq_iff, List.append_assoc]
    have hright' : R₃ (r .right) = crtEnts (gap.reverse.map a ++ (a j :: right)) := by
      simp [R₃, R₂, R₁, crtReversePairSaveRegs, crtReversePairLoadRegs, hr.eq_iff, List.append_assoc]
    have hpre' : (R₃ (r .pre)).length = crtW a (pre ++ [k]) := by
      simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
        hr.eq_iff, hpairs, hpre, crtW, List.map_append, List.sum_append]
      omega
    have hgap' : (R₃ (r .gap)).length = crtW a gap := by
      simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
        hr.eq_iff, hpairs, hgap, crtW, List.map_append, List.sum_append]
      omega
    have hpost' : (R₃ (r .post)).length = crtW a (j :: post) := by
      simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
        hr.eq_iff, hpairs, hpost]
    have hcount' : R₃ pairs = List.replicate (gap.length / 2) tick := by
      simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
        fun q => (hpairs q).symm, hcount]
      omega
    have he3' : R₃ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol := by
      simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
        hr.eq_iff, hpairs, he3]
    have hzero' : ∀ q ∈ [CrtReverseReg.aJ, .aK, .tmp, .stmp, .tu, .t₁, .t₂], R₃ (r q) = [] := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
        hr.eq_iff, hpairs]
      all_goals exact hzero _ (by simp)
    have hι0' : ∀ q, R₃ (ι q) = [] := by
      intro q
      simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs, hbank, hipairs, hι0]
    obtain ⟨R', hout, hframe, htail⟩ := ih hnd.2.2.2 (pre ++ [k]) (j :: post) R₃
      (a k :: left) (a j :: right) hsource hleft hright' hpre' hgap' hpost' hcount' he3' hzero' hι0'
    refine ⟨R', ?_, ?_, ?_⟩
    · simpa [List.reverse_cons, List.reverse_append, List.append_assoc] using hout
    · refine ⟨hframe.1, ?_, ?_, ?_, ?_⟩
      · rw [hframe.2.1]
        simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
          hr.eq_iff, hpairs, hl, crtEnts_cons, List.reverse_append, crtEnt_reverse, List.append_assoc]
      · rw [hframe.2.2.1]
        simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
          hr.eq_iff, hpairs, hright, crtEnts_cons, List.reverse_append, crtEnt_reverse,
          List.reverse_cons, List.map_append, List.append_assoc]
      · intro z hz hzs
        rw [hframe.2.2.2.1 z hz hzs]
        by_cases hjz : z = r .aJ
        · subst z
          simp [R₃, crtReversePairSaveRegs, hr.eq_iff, hzero .aJ (by simp)]
        · by_cases hkz : z = r .aK
          · subst z
            simp [R₃, crtReversePairSaveRegs, hr.eq_iff, hzero .aK (by simp)]
          · have hn : ∀ q ∈ crtReverseChanged, z ≠ r q := hzs
            simp only [crtReverseChanged, List.mem_cons, List.not_mem_nil, or_false,
              forall_eq_or_imp, forall_eq] at hn
            obtain ⟨hstrz, hlz, hrz, hldz, hrdz, hpz, hgz, hpoz⟩ := hn
            simp [R₃, R₂, R₁, R₀, crtReversePairSaveRegs, crtReversePairLoadRegs,
              hjz, hkz, hz, hstrz, hlz, hrz, hldz, hrdz, hpz, hgz, hpoz]
      · rw [hframe.2.2.2.2]
        simp only [hpre', hgap', hpost']
        rw [hpre, hgap, hpost]
        simp [crtW, List.map_append, List.sum_append]
        omega
    · have hne : R pairs ≠ [] := by
        rw [hcount, hhalf]
        simp
      have hrun := crtReverseWhile_step hne (crtRuns_seq hpop h₁) htail
      apply crtRuns_mono hrun
      simp only [crtReverseLoopCost, List.bidirectionalRecOn, List.bidirectionalRec_cons_append]
      omega


/-- Restore both preserved width streams and release all three geometry counters. -/
def crtReverseCleanup (r : CrtReverseReg → Fin T) : Pr F T Q A U :=
  .seq (crtMv (r .leftDone) (r .left))
    (.seq (crtMv (r .rightDone) (r .right))
      (.seq (uclear (r .pre)) (.seq (uclear (r .gap)) (uclear (r .post)))))

def crtReverseCleanupRegs (r : CrtReverseReg → Fin T) (R : Regs T A) : Regs T A :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update R
      (r .leftDone) []) (r .left) ((R (r .leftDone)).reverse ++ R (r .left)))
      (r .rightDone) []) (r .right) ((R (r .rightDone)).reverse ++ R (r .right)))
      (r .pre) []) (r .gap) []) (r .post) []

def crtReverseCleanupCost (r : CrtReverseReg → Fin T) (R : Regs T A) : ℕ :=
  2 * ((R (r .leftDone)).length + (R (r .rightDone)).length +
    (R (r .pre)).length + (R (r .gap)).length + (R (r .post)).length) + 10

theorem crtReverseCleanup_runs {r : CrtReverseReg → Fin T}
    (hr : Function.Injective r) (R : Regs T A) :
    crtRuns body (crtReverseCleanup r) R (crtReverseCleanupRegs r R)
      (crtReverseCleanupCost r R) := by
  have h₁ := crtMv_runs (body := body) (hr.ne (by decide : CrtReverseReg.leftDone ≠ .left)) R
  let R₁ := Function.update (Function.update R (r .leftDone) []) (r .left)
    ((R (r .leftDone)).reverse ++ R (r .left))
  let R₂ := Function.update (Function.update R₁ (r .rightDone) []) (r .right)
    ((R₁ (r .rightDone)).reverse ++ R₁ (r .right))
  let R₃ := Function.update R₂ (r .pre) []
  let R₄ := Function.update R₃ (r .gap) []
  have h₂ := crtMv_runs (body := body) (hr.ne (by decide : CrtReverseReg.rightDone ≠ .right)) R₁
  have h₃ := crtClear_runs (body := body) (r .pre) R₂
  have h₄ := crtClear_runs (body := body) (r .gap) R₃
  have h₅ := crtClear_runs (body := body) (r .post) R₄
  have h := crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ (crtRuns_seq h₄ h₅)))
  convert h using 1 <;> simp [crtReverseCleanup, crtReverseCleanupRegs,
    crtReverseCleanupCost, R₁, R₂, R₃, R₄, hr.eq_iff]; omega

/-- Stream conservation gives exact recovery, while cleanup leaves the data
and all unrelated registers unchanged. -/
theorem crtReverseCleanup_frame {r : CrtReverseReg → Fin T}
    (hr : Function.Injective r) {pairs : Fin T} (hpairs : ∀ q, r q ≠ pairs)
    {R R' : Regs T A} (hf : CrtReverseLoopFrame r pairs R R')
    (hl : R (r .leftDone) = []) (hright : R (r .rightDone) = []) :
    let R'' := crtReverseCleanupRegs r R'
    R'' (r .str) = R' (r .str) ∧ R'' (r .left) = R (r .left) ∧
      R'' (r .right) = R (r .right) ∧ R'' pairs = [] ∧
      (∀ q ∈ [CrtReverseReg.leftDone, .rightDone, .pre, .gap, .post], R'' (r q) = []) ∧
      (∀ k, k ≠ pairs → (∀ q ∈ crtReverseChanged, k ≠ r q) → R'' k = R k) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [crtReverseCleanupRegs, hr.eq_iff]
  · simpa [crtReverseCleanupRegs, hr.eq_iff, hl] using hf.2.1
  · simpa [crtReverseCleanupRegs, hr.eq_iff, hright] using hf.2.2.1
  · simpa [crtReverseCleanupRegs, fun q => (hpairs q).symm] using hf.1
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals simp [crtReverseCleanupRegs, hr.eq_iff]
  · intro k hk hq
    have he := hf.2.2.2.1 k hk hq
    simp only [crtReverseChanged, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hq
    obtain ⟨hs, hl, hr, hld, hrd, hp, hg, hpo⟩ := hq
    simpa [crtReverseCleanupRegs, hl, hr, hld, hrd, hp, hg, hpo] using he


end

end IntegerMultBounds.MathlibTM2.Fast
