module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectDrive
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlTarget
import IntegerMultBounds.MathlibTM2.Fast.CRTControlDriverSpec
public import IntegerMultBounds.MathlibTM2.Fast.CRTReverseFull
import IntegerMultBounds.MathlibTM2.Fast.CRTMachine
public import IntegerMultBounds.MathlibTM2.Fast.CRTSpec
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # The concrete direct CRT driver -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}

/-- The target's first 31 slots embed in a shared 38-register driver allocation. -/
def crtDirectMachineTarget : Fin 31 → Fin 38 := Fin.castAdd 7

def crtDirectMachineDriver : CrtDirectReg → Fin 38
  | .str => 0 | .wT => 31 | .sT => 32 | .mT => 33 | .wD => 34 | .sD => 35 | .mD => 36
  | .aI => 4 | .sI => 9 | .muI => 10 | .lower => 6 | .upper => 7 | .index => 3 | .tmp => 37

lemma crtDirectMachineTarget_injective : Function.Injective crtDirectMachineTarget := by
  intro i j h; exact Fin.ext (by simpa [crtDirectMachineTarget] using congrArg Fin.val h)
lemma crtDirectMachineDriver_injective : Function.Injective crtDirectMachineDriver := by
  intro i j h; cases i <;> cases j <;> simp_all [crtDirectMachineDriver]

/-- Immutable target inputs and returned target/arithmetic workspaces. -/
structure CrtDirectMachineReady {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 38 → Fin T)
    (a s : Fin (d + 1) → ℕ) (c : ℕ) (wl nl : List (Fin (prime + K + 4)))
    (R : Regs T (prime + K)) : Prop where
  widths : R (e 1) = crtEnts (List.ofFn a)
  moduli : R (e 2) = crtEnts (List.ofFn s)
  zeroWidth : (R (e 5)).length = a 0
  totalWidth : (R (e 8)).length = crtPre a (d + 1)
  slotWidth : (R (e 11)).length = c
  tripleWidth : R (e 12) = (GrowingCounterData.advance (3 * c) []).map bitSymbol
  empty : ∀ j : Fin 38, 13 ≤ j.val → j.val ≤ 30 → R (e j) = []
  width : R (rg .wr) = wl
  count : R (rg .wn) = nl
  vars : ∀ j, R (rg (.v j)) = []
  scratch : ∀ j, R (rg (.z j)) = []
  acc : R (rg .acc) = []

/-- Any register outside the driver allocation keeps its baseline value at a call. -/
lemma crtDirectCallState_off {d A : ℕ} (a s m : Fin d → ℕ) (r : CrtDirectReg → Fin T)
    (R : Regs T A) (data : List (Fin (A + 4))) (i : ℕ) (hi : i < d)
    (z : Fin T) (hz : ∀ q, z ≠ r q) :
    crtDirectCallState a s m r R data i hi z = R z := by
  simp [crtDirectCallState, crtDirectLoadRegs, crtDirectState, hz]

/-- Target slots that are not current counters/triples are untouched by loading. -/
lemma crtDirectMachine_static {d A : ℕ} (a s m : Fin d → ℕ)
    (e : Fin 38 → Fin T) (he : Function.Injective e) (R : Regs T A)
    (data : List (Fin (A + 4))) (i : ℕ) (hi : i < d) (j : Fin 31)
    (hj : j ≠ 0 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 6 ∧ j ≠ 7 ∧ j ≠ 9 ∧ j ≠ 10) :
    crtDirectCallState a s m (e ∘ crtDirectMachineDriver) R data i hi
      (e (crtDirectMachineTarget j)) = R (e (crtDirectMachineTarget j)) := by
  apply crtDirectCallState_off
  intro q
  apply he.ne
  intro h
  have hv := congrArg Fin.val h
  have hjlt := j.isLt
  cases q <;> simp [crtDirectMachineDriver, crtDirectMachineTarget] at hv
  all_goals simp only [ne_eq, Fin.ext_iff] at hj
  all_goals omega

/-- Every call of the unary driver meets the concrete target contract. -/
theorem crtDirectMachineTarget_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 38 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j ≤ 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg e a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = []) (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (i : ℕ) (hi : i < d + 1) (hi0 : i ≠ 0) (fwd : Bool) :
    let r := e ∘ crtDirectMachineDriver
    let S := crtDirectCallState a s m r R
      (crtBox a (crtRevAx (d := d + 1) (d + 1)) C 0).flatten i hi
    crtRuns body (crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) fwd) S
      (Function.update S (r .str)
        (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtRotC s i hi (m ⟨i, hi⟩) fwd C) 0).flatten)
      (crtControlTargetCost (K := K) T B w c a s ⟨i, hi⟩ (m ⟨i, hi⟩)) := by
  let r := e ∘ crtDirectMachineDriver
  let t := e ∘ crtDirectMachineTarget
  let data := (crtBox a (crtRevAx (d := d + 1) (d + 1)) C 0).flatten
  let S := crtDirectCallState a s m r R data i hi
  have hr : Function.Injective r := he.comp crtDirectMachineDriver_injective
  have hstatic : ∀ j : Fin 31,
      j ≠ 0 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 6 ∧ j ≠ 7 ∧ j ≠ 9 ∧ j ≠ 10 → S (t j) = R (t j) :=
    crtDirectMachine_static a s m e he R data i hi
  have hbank : ∀ k, S (rg k) = R (rg k) := by
    intro k; apply crtDirectCallState_off; intro q; exact hrge k _
  have hswap : ∀ k, S (ι k) = R (ι k) := by
    intro k; apply crtDirectCallState_off; intro q; exact hιe k _
  apply crtControlTarget_runs hQ ι hι hT rg hrg t (he.comp crtDirectMachineTarget_injective)
    (fun k j => hrge k _) (fun k j => hιe k _) a s ⟨i, hi⟩
    (fun h => hi0 (congrArg Fin.val h)) ⟨hadj _ _, hadj _ _⟩ (fun j => (hs j).2)
    (hs ⟨i, hi⟩).1 (m ⟨i, hi⟩) (hm ⟨i, hi⟩) fwd hB hd c hc wl nl hwl hnl hw C hC h8 S
  · simp [S, data, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff]
  · rw [hstatic 1 (by decide)]; exact hR.widths
  · rw [hstatic 2 (by decide)]; exact hR.moduli
  · simp [S, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff]
  · simp [S, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff]
  · rw [hstatic 5 (by decide)]; exact hR.zeroWidth
  · simp [S, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff, crtPre_succ a hi]
  · simp [S, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff, crtControlRoutingPre_width]
  · rw [hstatic 8 (by decide)]; exact hR.totalWidth
  · simp [S, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff]
  · simp [S, crtDirectCallState, crtDirectLoadRegs, crtDirectState,
      r, t, crtDirectMachineTarget, crtDirectMachineDriver, he.eq_iff]
  · rw [hstatic 11 (by decide)]; exact hR.slotWidth
  · rw [hstatic 12 (by decide)]; exact hR.tripleWidth
  · intro j hj
    rw [hstatic j (by
      simp only [ne_eq, Fin.ext_iff]
      have := j.isLt
      omega)]
    exact hR.empty (crtDirectMachineTarget j) hj (by have := j.isLt; simpa [crtDirectMachineTarget] using (show j.val ≤ 30 by omega))
  · rw [hbank]; exact hR.width
  · rw [hbank]; exact hR.count
  · intro j; rw [hbank]; exact hR.vars j
  · intro j; rw [hbank]; exact hR.scratch j
  · rw [hbank]; exact hR.acc
  · intro j; rw [hswap]; exact hι0 j

/-- Target zero is skipped and costs only the driver's branch; nonzero entries
retain their individual concrete target cost. -/
def crtDirectMachineBudget {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) : ℕ :=
  if i = 0 then 1 else crtControlTargetCost (K := K) T B w c a s i (m i)

def crtDirectMachineLoopCost {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ) : ℕ :=
  ((List.finRange (d + 1)).map (fun j =>
    crtDirectMachineBudget (K := K) T B w c a s m j + 12 * a j + 4 * s j + 4 * m j + 37)).sum + 2

lemma crtDirectMachineBudget_pos {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) : 1 ≤ crtDirectMachineBudget (K := K) T B w c a s m i := by
  unfold crtDirectMachineBudget
  split_ifs
  · exact le_rfl
  · unfold crtControlTargetCost
    omega

/-- Forward contents indexed by the still-unprocessed original-axis prefix. -/
lemma crtDirectMachine_forward_step {d : ℕ} {α : Type*} (s m : Fin (d + 1) → ℕ)
    (C : (Fin (d + 1) → ℕ) → α) (i : ℕ) (hi : i < d + 1) :
    crtFwdC s m C (d + 1 - i) =
      crtRotC s i hi (m ⟨i, hi⟩) true (crtFwdC s m C (d + 1 - (i + 1))) := by
  have h : d + 1 - i = (d + 1 - (i + 1)) + 1 := by omega
  rw [h, crtFwdC_succ s m C (by omega)]
  have hn : d + 1 - 1 - (d + 1 - (i + 1)) = i := by omega
  funext y
  simp only [crtRotC, hn]

/-- The concrete forward loop implements the original forward content recurrence
on the fixed reversed physical layout. -/
theorem crtDirectMachineForwardLoop_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 38 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j ≤ 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg e a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = []) (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R ((e ∘ crtDirectMachineDriver) q) = []) :
    let r := e ∘ crtDirectMachineDriver
    let p : Pr F T Q (prime + K) U := crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) true
    crtRuns body (crtWhile (r .wT) (crtDirectStep true r p))
      (crtDirectState a s m r R (crtBox a (crtRevAx (d := d + 1) (d + 1)) C 0).flatten (d + 1))
      (crtDirectState a s m r R
        (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtFwdC s m C (d + 1)) 0).flatten 0)
      (crtDirectMachineLoopCost (K := K) T B w c a s m) := by
  let r := e ∘ crtDirectMachineDriver
  let p : Pr F T Q (prime + K) U := crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) true
  let data := fun n => (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtFwdC s m C (d + 1 - n)) 0).flatten
  have hzero : data 0 = data 1 := by
    have h := crtDirectMachine_forward_step s m C 0 (by omega)
    rw [crtControlRot_zero] at h
    exact congrArg (fun D => (crtBox a (crtRevAx (d := d + 1) (d + 1)) D 0).flatten) h
  have hbody : ∀ i (hi : i < d + 1), i ≠ 0 →
      crtRuns body p (crtDirectCallState a s m r R (data (i + 1)) i hi)
        (Function.update (crtDirectCallState a s m r R (data (i + 1)) i hi) (r .str) (data i))
        (crtDirectMachineBudget (K := K) T B w c a s m ⟨i, hi⟩) := by
    intro i hi hi0
    have h := crtDirectMachineTarget_runs (body := body) hQ ι hι hT rg hrg e he hrge hιe a s m hadj hs hm hB hd
      c hc wl nl hwl hnl hw R hR hι0 (crtFwdC s m C (d + 1 - (i + 1)))
      (crtFwdC_mem s m (fun x => x.length = c) C hC _)
      (crtFwdC_mem s m (fun x => ∀ z ∈ x, z.val < 8) C h8 _) i hi hi0 true
    have hi' : (⟨i, hi⟩ : Fin (d + 1)) ≠ 0 := fun h => hi0 (congrArg Fin.val h)
    simpa only [crtDirectMachineBudget, ite_eq_right hi', data, crtDirectMachine_forward_step s m C i hi] using h
  have h := crtDirectForwardLoop_weighted a s m (he.comp crtDirectMachineDriver_injective) p R hz data
    (crtDirectMachineBudget (K := K) T B w c a s m) (crtDirectMachineBudget_pos T B w c a s m) hzero hbody
  simpa only [data, Nat.sub_self, crtFwdC, Nat.sub_zero, crtDirectMachineLoopCost] using h

/-- The concrete inverse loop implements the original inverse content recurrence. -/
theorem crtDirectMachineInverseLoop_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 38 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j ≤ 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg e a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = []) (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R ((e ∘ crtDirectMachineDriver) q) = []) :
    let r := e ∘ crtDirectMachineDriver
    let p : Pr F T Q (prime + K) U := crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) false
    crtRuns body (crtWhile (r .wD) (crtDirectStep false r p))
      (crtDirectState a s m r R (crtBox a (crtRevAx (d := d + 1) (d + 1)) C 0).flatten 0)
      (crtDirectState a s m r R
        (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtInvC s m C (d + 1)) 0).flatten (d + 1))
      (crtDirectMachineLoopCost (K := K) T B w c a s m) := by
  let r := e ∘ crtDirectMachineDriver
  let p : Pr F T Q (prime + K) U := crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) false
  let data := fun n => (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtInvC s m C n) 0).flatten
  have hzero : data 1 = data 0 := by
    simp only [data, crtInvC_succ s m C (by omega : 0 < d + 1), crtControlRot_zero]
  have hbody : ∀ i (hi : i < d + 1), i ≠ 0 →
      crtRuns body p (crtDirectCallState a s m r R (data i) i hi)
        (Function.update (crtDirectCallState a s m r R (data i) i hi) (r .str) (data (i + 1)))
        (crtDirectMachineBudget (K := K) T B w c a s m ⟨i, hi⟩) := by
    intro i hi hi0
    have h := crtDirectMachineTarget_runs (body := body) hQ ι hι hT rg hrg e he hrge hιe a s m hadj hs hm hB hd
      c hc wl nl hwl hnl hw R hR hι0 (crtInvC s m C i)
      (crtInvC_mem s m (fun x => x.length = c) C hC _)
      (crtInvC_mem s m (fun x => ∀ z ∈ x, z.val < 8) C h8 _) i hi hi0 false
    have hi' : (⟨i, hi⟩ : Fin (d + 1)) ≠ 0 := fun h => hi0 (congrArg Fin.val h)
    simpa only [crtDirectMachineBudget, ite_eq_right hi', data, crtInvC_succ s m C hi] using h
  have h := crtDirectInverseLoop_weighted a s m (he.comp crtDirectMachineDriver_injective) p R hz data
    (crtDirectMachineBudget (K := K) T B w c a s m) (crtDirectMachineBudget_pos T B w c a s m) hzero hbody
  simpa only [data, crtInvC, crtDirectMachineLoopCost] using h

/-- The complete wrapper adds a preserved signature tape and a generated axis count. -/
def crtDirectMachineCore : Fin 38 → Fin 40 := Fin.castAdd 2

lemma crtDirectMachineCore_injective : Function.Injective crtDirectMachineCore := by
  intro i j h; exact Fin.ext (by simpa [crtDirectMachineCore] using congrArg Fin.val h)

/-- Reversal reuses target scratch after every target has returned it empty. -/
def crtDirectMachineReverse (ascending : Bool) : CrtReverseReg → Fin 40
  | .str => 0 | .left => if ascending then 1 else 31 | .right => 13
  | .leftDone => 14 | .rightDone => 15 | .pre => 16 | .gap => 17 | .post => 18
  | .aJ => 19 | .aK => 20 | .e3B => 12 | .tu => 21 | .t₁ => 22 | .t₂ => 23
  | .tmp => 24 | .stmp => 25

lemma crtDirectMachineReverse_injective (ascending : Bool) :
    Function.Injective (crtDirectMachineReverse ascending) := by
  intro i j h
  cases ascending <;> cases i <;> cases j <;> simp_all [crtDirectMachineReverse]

def crtDirectMachineOrder {d : ℕ} (ascending : Bool) : List (Fin d) :=
  if ascending then List.finRange d else crtRevAx d

lemma crtDirectMachineOrder_width {d : ℕ} (a : Fin d → ℕ) (ascending : Bool) :
    crtW a (crtDirectMachineOrder ascending) = crtPre a d := by
  have h := crtW_revAx a d le_rfl
  cases ascending
  · exact h
  · simpa [crtDirectMachineOrder, crtRevAx_full, crtW] using h

/-- The terminal forward reversal and initial inverse reversal are concrete
full-file operations with all width streams and scratch preserved. -/
theorem crtDirectMachineReverse_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (e : Fin 40 → Fin T) (he : Function.Injective e) (hιe : ∀ j k, ι j ≠ e k)
    {d : ℕ} (a : Fin (d + 1) → ℕ) (hadj : ∀ j k, a j ≤ a k + 1)
    (c : ℕ) (hc : 0 < c) (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (ascending : Bool) (R : Regs T (prime + K))
    (hsource : R (e 0) = (crtBox a (crtDirectMachineOrder ascending) C 0).flatten)
    (hwidths : R (e 31) = crtEnts ((crtRevAx (d := d + 1) (d + 1)).map a))
    (hasc : R (e 1) = crtEnts (List.ofFn a))
    (haxes : (R (e 39)).length = d + 1) (htotal : (R (e 8)).length = crtPre a (d + 1))
    (hthree : R (e 12) = (GrowingCounterData.advance (3 * c) []).map bitSymbol)
    (hempty : ∀ j : Fin 40, 13 ≤ j.val → j.val ≤ 30 → R (e j) = [])
    (hι0 : ∀ j, R (ι j) = []) :
    crtRuns body (crtReverseFull hQ ι hι hT (e ∘ crtDirectMachineReverse ascending) (e 39) (e 8) (e 26)) R
      (Function.update R (e 0) (crtBox a (crtDirectMachineOrder ascending).reverse C 0).flatten)
      (crtReverseLoopCost T a c (crtDirectMachineOrder ascending) [] [] +
        14 * (crtEnts (A := prime + K) ((crtDirectMachineOrder ascending).map a)).length +
        6 * crtPre a (d + 1) + 4 * (d + 1) + 28) := by
  let r := e ∘ crtDirectMachineReverse ascending
  have hr : Function.Injective r := he.comp (crtDirectMachineReverse_injective ascending)
  have hl : R (r .left) = crtEnts ((crtDirectMachineOrder ascending).map a) := by
    cases ascending
    · exact hwidths
    · change R (e 1) = crtEnts ((List.finRange (d + 1)).map a)
      rw [← List.ofFn_eq_map]; exact hasc
  have h := crtReverseFull_runs (body' := body) a hQ ι hι hT hr
    (fun z q => hιe q _) (e 39) (e 8) (e 26)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
    (by intro q; apply he.ne; cases q <;> cases ascending <;> decide)
    (by intro q; apply he.ne; cases q <;> cases ascending <;> decide)
    (by intro q; apply he.ne; cases q <;> cases ascending <;> decide)
    (fun q => hιe q 26) hadj C c hc hC h8 0 (crtDirectMachineOrder ascending)
    (by cases ascending <;> simp [crtDirectMachineOrder, crtRevAx_full, List.nodup_finRange]) R hsource hl
    (by cases ascending <;> simpa [crtDirectMachineOrder, crtRevAx_full] using haxes)
    (by rw [crtDirectMachineOrder_width]; exact htotal) hthree
    (by intro q h0 hl he3
        cases q <;> simp only [ne_eq, not_true_eq_false] at h0 hl he3
        all_goals simp [r, crtDirectMachineReverse, hempty])
    (hempty 26 (by decide) (by decide)) hι0
  rw [hl, htotal, haxes] at h
  simpa only [r, Function.comp_apply, crtDirectMachineReverse] using h

/-- The legacy pad/delete scanner reuses returned target scratch. -/
def crtDirectMachineScan (e : Fin 40 → Fin T) : CrtAL T :=
  ⟨e 13, e 14, e 15, e 38, e 8, e 16, e 17, e 18, e 19, e 20, e 21⟩

lemma crtDirectMachineScan_ok (e : Fin 40 → Fin T) (he : Function.Injective e) :
    (crtDirectMachineScan e).Ok := by
  simp [crtDirectMachineScan, CrtAL.Ok, List.nodup_cons, he.eq_iff]

/-- Padding retains the previous machine's exact semantics and byte bound. -/
theorem crtDirectMachinePad_runs {d : ℕ} (e : Fin 40 → Fin T) (he : Function.Injective e)
    (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (l : List (List (Fin (prime + K + 4)))) (z : List (Fin (prime + K + 4))) (c : ℕ)
    (hl : l.length = crtProd s d) (hlc : ∀ x ∈ l, x.length = c) (hzc : z.length = c)
    (R : Regs T (prime + K)) (hstr : R (e 0) = l.flatten) (hzr : R (e 11) = z)
    (hsig : R (e 38) = binSyms (crtPre a d) (crtSig a s d))
    (hmask : R (e 8) = binSyms (crtPre a d) (crtMask a d))
    (hempty : ∀ j : Fin 40, 13 ≤ j.val → j.val ≤ 30 → R (e j) = []) :
    crtRuns body (crtPadP (crtDirectMachineScan e) (e 0) (e 22) (e 11) (e 23) (e 24) (e 25) (e 26)) R
      (Function.update R (e 0) (crtBox a (crtRevAx d) (crtPadC s l z) 0).flatten)
      (2 ^ crtPre a d * (10 * c + 10 * crtPre a d + 29) + 25 * crtPre a d + 6 * c + 29) := by
  apply crtPad_runs a s (crtDirectMachineScan e) (crtDirectMachineScan_ok e he)
    (by simp [List.nodup_cons, he.eq_iff]) (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [crtDirectMachineScan, CrtAL.Prot, he.eq_iff]) hs l z c hl hlc hzc R hstr hzr
  all_goals try simp only [crtDirectMachineScan]
  all_goals first | exact hsig | exact hmask | exact hempty _ (by decide) (by decide)

/-- Deletion also retains the original scan semantics, including invalid-slot removal. -/
theorem crtDirectMachineDel_runs {d : ℕ} (e : Fin 40 → Fin T) (he : Function.Injective e)
    (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (D : (Fin d → ℕ) → List (Fin (prime + K + 4))) (c : ℕ) (hD : ∀ x, (D x).length = c)
    (R : Regs T (prime + K)) (hstr : R (e 0) = (crtBox a (crtRevAx d) D 0).flatten)
    (hzr : (R (e 11)).length = c)
    (hsig : R (e 38) = binSyms (crtPre a d) (crtSig a s d))
    (hmask : R (e 8) = binSyms (crtPre a d) (crtMask a d))
    (hempty : ∀ j : Fin 40, 13 ≤ j.val → j.val ≤ 30 → R (e j) = []) :
    crtRuns body (crtDelP (crtDirectMachineScan e) (e 0) (e 22) (e 11) (e 23) (e 24)) R
      (Function.update R (e 0) ((List.range (crtProd s d)).map fun k => D (crtUnrank s k)).flatten)
      (2 ^ crtPre a d * (10 * c + 10 * crtPre a d + 29) + 25 * crtPre a d + 6 * c + 29) := by
  apply crtDel_runs a s (crtDirectMachineScan e) (crtDirectMachineScan_ok e he)
    (by simp [List.nodup_cons, he.eq_iff]) (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals simp [crtDirectMachineScan, CrtAL.Prot, he.eq_iff]) hs D c hD R hstr hzr
  all_goals try simp only [crtDirectMachineScan]
  all_goals first | exact hsig | exact hmask | exact hempty _ (by decide) (by decide)

/-- Provision the two forward countdowns without consuming their inputs. -/
def crtDirectMachineForwardInit (r : CrtDirectReg → Fin T) (axes width : Fin T) : Pr F T Q (prime + K) U :=
  .seq (ucopy axes (r .index) (r .tmp)) (ucopy width (r .lower) (r .tmp))

theorem crtDirectMachineForwardInit_runs {d : ℕ} (a s m : Fin d → ℕ)
    (r : CrtDirectReg → Fin T) (hr : Function.Injective r) (axes width : Fin T)
    (ha : ∀ q, axes ≠ r q) (hw : ∀ q, width ≠ r q) (R : Regs T (prime + K))
    (haxes : (R axes).length = d) (hwidth : (R width).length = crtPre a d)
    (hwt : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hst : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmt : R (r .mT) = crtEnts ((crtRevAx d).map m))
    (hz : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index, .tmp], R (r q) = []) :
    crtRuns body (crtDirectMachineForwardInit r axes width) R
      (crtDirectState a s m r R (R (r .str)) d) (4 * d + 4 * crtPre a d + 8) := by
  let R₁ := Function.update R (r .index) (List.replicate d tick)
  have h₁ := crtUcopy_runs (body := body) (ha .index) (ha .tmp) (hr.ne (by decide)) R (hz .tmp (by simp))
  rw [haxes, hz .index (by simp), List.append_nil] at h₁
  have h₂ := crtUcopy_runs (body := body) (hw .lower) (hw .tmp) (hr.ne (by decide)) R₁
    (by simp [R₁, hr.eq_iff, hz .tmp (by simp)])
  have hwidth' : (R₁ width).length = crtPre a d := by simp [R₁, hw, hwidth]
  rw [hwidth', show R₁ (r .lower) = [] from by simp [R₁, hr.eq_iff, hz .lower (by simp)], List.append_nil] at h₂
  have hout : Function.update R₁ (r .lower) (List.replicate (crtPre a d) tick) =
      crtDirectState a s m r R (R (r .str)) d := by
    funext z
    by_cases hz' : ∃ q, r q = z
    · obtain ⟨q, rfl⟩ := hz'
      cases q <;> simp [R₁, crtDirectState, hr.eq_iff, hwt, hst, hmt,
        hz .wD (by simp), hz .sD (by simp), hz .mD (by simp), hz .upper (by simp), crtW, List.drop_eq_nil_of_le, List.length_finRange]
    · have hn : ∀ q, z ≠ r q := by intro q h; exact hz' ⟨q, h.symm⟩
      simp [R₁, crtDirectState, hn]
  exact crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ h₂) hout) (by omega)

/-- Prepare the ascending inverse streams while retaining the external format
for the final endpoint restoration. -/
def crtDirectMachineInverseInit (r : CrtDirectReg → Fin T) (width : Fin T) : Pr F T Q (prime + K) U :=
  .seq (ucopy width (r .upper) (r .tmp)) <|
  .seq (crtMv (r .wT) (r .wD)) <|
  .seq (crtMv (r .sT) (r .sD)) (crtMv (r .mT) (r .mD))

theorem crtDirectMachineInverseInit_runs {d : ℕ} (a s m : Fin d → ℕ)
    (r : CrtDirectReg → Fin T) (hr : Function.Injective r) (width : Fin T)
    (hw : ∀ q, width ≠ r q) (R : Regs T (prime + K))
    (hwidth : (R width).length = crtPre a d)
    (hwt : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hst : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmt : R (r .mT) = crtEnts ((crtRevAx d).map m))
    (hz : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index, .tmp], R (r q) = []) :
    crtRuns body (crtDirectMachineInverseInit r width) R
      (crtDirectState a s m r R (R (r .str)) 0)
      (4 * crtPre a d + 2 * ((crtEnts (A := prime + K) ((crtRevAx d).map a)).length +
        (crtEnts (A := prime + K) ((crtRevAx d).map s)).length +
        (crtEnts (A := prime + K) ((crtRevAx d).map m)).length) + 10) := by
  let R₁ := Function.update R (r .upper) (List.replicate (crtPre a d) tick)
  let R₂ := Function.update (Function.update R₁ (r .wT) []) (r .wD) (R (r .wT)).reverse
  let R₃ := Function.update (Function.update R₂ (r .sT) []) (r .sD) (R (r .sT)).reverse
  let R₄ := Function.update (Function.update R₃ (r .mT) []) (r .mD) (R (r .mT)).reverse
  have h₁ := crtUcopy_runs (body := body) (hw .upper) (hw .tmp) (hr.ne (by decide)) R (hz .tmp (by simp))
  rw [hwidth, hz .upper (by simp), List.append_nil] at h₁
  have h₂ := crtMv_runs (body := body) (hr.ne (by decide : CrtDirectReg.wT ≠ .wD)) R₁
  have h₃ := crtMv_runs (body := body) (hr.ne (by decide : CrtDirectReg.sT ≠ .sD)) R₂
  have h₄ := crtMv_runs (body := body) (hr.ne (by decide : CrtDirectReg.mT ≠ .mD)) R₃
  simp only [R₁, Function.update_of_ne (hr.ne (by decide : CrtDirectReg.wT ≠ .upper)),
    Function.update_of_ne (hr.ne (by decide : CrtDirectReg.wD ≠ .upper)), hz .wD (by simp), List.append_nil] at h₂
  simp only [R₂, R₁, Function.update_of_ne (hr.ne (by decide : CrtDirectReg.sT ≠ .wD)),
    Function.update_of_ne (hr.ne (by decide : CrtDirectReg.sT ≠ .wT)),
    Function.update_of_ne (hr.ne (by decide : CrtDirectReg.sT ≠ .upper)),
    Function.update_of_ne (hr.ne (by decide : CrtDirectReg.sD ≠ .wD)),
    Function.update_of_ne (hr.ne (by decide : CrtDirectReg.sD ≠ .wT)),
    Function.update_of_ne (hr.ne (by decide : CrtDirectReg.sD ≠ .upper)), hz .sD (by simp), List.append_nil] at h₃
  have h₄' : crtRuns body (crtMv (r .mT) (r .mD)) R₃ R₄ (2 * (R (r .mT)).length + 2) := by
    simpa [R₃, R₂, R₁, R₄, hr.eq_iff, hz .mD (by simp)] using h₄
  have hout : R₄ = crtDirectState a s m r R (R (r .str)) 0 := by
    have hwfull : crtW a (List.finRange d) = crtPre a d := crtDirectMachineOrder_width a true
    have hrev : ∀ f : Fin d → ℕ, (crtEnts (A := prime + K) ((crtRevAx d).map f)).reverse =
        crtEnts ((List.finRange d).map f) := by intro f; simp [crtEnts_reverse, crtRevAx_full, List.map_reverse]
    funext z
    by_cases hz' : ∃ q, r q = z
    · obtain ⟨q, rfl⟩ := hz'
      cases q <;> simp [R₄, R₃, R₂, R₁, crtDirectState, hr.eq_iff, hwt, hst, hmt, 
        hz .lower (by simp), hz .index (by simp), crtPre, crtLow, crtRevAx, hwfull, List.take_of_length_le (by simp : (List.finRange d).length ≤ d)]
      all_goals rw [crtEnts_reverse, List.reverse_reverse]
    · have hn : ∀ q, z ≠ r q := by intro q h; exact hz' ⟨q, h.symm⟩
      simp [R₄, R₃, R₂, R₁, crtDirectState, hn]
  apply crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄'))) hout)
  rw [hwt, hst, hmt]
  omega

end
end IntegerMultBounds.MathlibTM2.Fast
