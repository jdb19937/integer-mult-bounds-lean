module

import IntegerMultBounds.MathlibTM2.Fast.CRTReverse
public import IntegerMultBounds.MathlibTM2.Fast.CRTDrive
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Unary traversal for the direct CRT target driver

Only parameter traversal is implemented here. A target operation is supplied
separately, with an exact data-only effect. Forward traversal visits descending
indices, inverse traversal ascending indices; the physical layout between
calls is therefore the fixed reversed layout required by the target contract.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- The immutable ascending parameter copies and target workspaces live outside
this interface and are preserved by every traversal primitive. -/
inductive CrtDirectReg
  | str | wT | sT | mT | wD | sD | mD | aI | sI | muI | lower | upper | index | tmp
  deriving DecidableEq

/-- Exchange source/destination parameter streams and lower/upper counters.
Applying the same primitives through this embedding gives inverse traversal. -/
def crtDirectFlip : CrtDirectReg → CrtDirectReg
  | .wT => .wD | .wD => .wT | .sT => .sD | .sD => .sT | .mT => .mD | .mD => .mT
  | .lower => .upper | .upper => .lower | q => q

lemma crtDirectFlip_involutive : Function.Involutive crtDirectFlip := by intro q; cases q <;> rfl

lemma crtDirectFlip_injective : Function.Injective crtDirectFlip := crtDirectFlip_involutive.injective

/-- Axis zero has no triangular shear, so its target call is skipped at runtime. -/
def crtDirectTarget (r : CrtDirectReg → Fin T) (p : Pr F T Q A U) : Pr F T Q A U :=
  crtIfR (r .index) p (.act .done)

theorem crtDirectTarget_zero {r : CrtDirectReg → Fin T} (p : Pr F T Q A U)
    (R : Regs T A) (hi : R (r .index) = []) :
    crtRuns body (crtDirectTarget r p) R R 3 := by
  apply crtIfR_runs
  · intro h; exact False.elim (h hi)
  · intro _ v S hS _
    subst R
    exact ⟨v, 1, rfl, le_rfl, Exec.act .done (mk v S)⟩

/-- Pop the target triple and remove its width from the remaining side. -/
def crtDirectLoad (r : CrtDirectReg → Fin T) : Pr F T Q A U :=
  .seq (crtPopEnt (r .wT) (r .aI))
    (.seq (crtPopEnt (r .sT) (r .sI))
      (.seq (crtPopEnt (r .mT) (r .muI)) (usub (r .aI) (r .lower) (r .tmp))))

def crtDirectLoadRegs (r : CrtDirectReg → Fin T) (R : Regs T A)
    (a s m : ℕ) (ws ss ms : List ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update R (r .wT) (crtEnts ws)) (r .aI) (List.replicate a tick))
      (r .sT) (crtEnts ss)) (r .sI) (List.replicate s tick))
      (r .mT) (crtEnts ms)) (r .muI) (List.replicate m tick)) (r .lower) ((R (r .lower)).drop a)

theorem crtDirectLoad_runs {r : CrtDirectReg → Fin T} (hr : Function.Injective r)
    (R : Regs T A) (a s m : ℕ) (ws ss ms : List ℕ)
    (hw : R (r .wT) = crtEnts (a :: ws)) (hs : R (r .sT) = crtEnts (s :: ss))
    (hm : R (r .mT) = crtEnts (m :: ms))
    (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R (r q) = []) :
    crtRuns body (crtDirectLoad r) R (crtDirectLoadRegs r R a s m ws ss ms)
      (6 * a + 2 * s + 2 * m + 16) := by
  have h₁ := crtPopEnt_runs (body := body) (hr.ne (by decide : CrtDirectReg.wT ≠ .aI))
    R a ws hw (hz .aI (by simp))
  let R₁ := Function.update (Function.update R (r .wT) (crtEnts ws)) (r .aI) (List.replicate a tick)
  have h₂ := crtPopEnt_runs (body := body) (hr.ne (by decide : CrtDirectReg.sT ≠ .sI))
    R₁ s ss (by simp [R₁, hr.eq_iff, hs]) (by simp [R₁, hr.eq_iff, hz .sI (by simp)])
  let R₂ := Function.update (Function.update R₁ (r .sT) (crtEnts ss)) (r .sI) (List.replicate s tick)
  have h₃ := crtPopEnt_runs (body := body) (hr.ne (by decide : CrtDirectReg.mT ≠ .muI))
    R₂ m ms (by simp [R₂, R₁, hr.eq_iff, hm]) (by simp [R₂, R₁, hr.eq_iff, hz .muI (by simp)])
  let R₃ := Function.update (Function.update R₂ (r .mT) (crtEnts ms)) (r .muI) (List.replicate m tick)
  have h₄ := crtUsub_runs (body := body) (hr.ne (by decide : CrtDirectReg.aI ≠ .lower))
    (hr.ne (by decide : CrtDirectReg.aI ≠ .tmp)) (hr.ne (by decide : CrtDirectReg.lower ≠ .tmp)) R₃
    (by simp [R₃, R₂, R₁, hr.eq_iff, hz .tmp (by simp)])
  have h := crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))
  refine crtRuns_mono (crtRuns_congr h ?_) ?_
  · simp [crtDirectLoadRegs, R₃, R₂, R₁, hr.eq_iff]
  · simp [R₃, R₂, R₁, hr.eq_iff]; omega

/-- Account for the completed target and save all three entries. -/
def crtDirectSave (r : CrtDirectReg → Fin T) : Pr F T Q A U :=
  .seq (ucopy (r .aI) (r .upper) (r .tmp))
    (.seq (crtPushEnt (r .aI) (r .wD))
      (.seq (crtPushEnt (r .sI) (r .sD)) (crtPushEnt (r .muI) (r .mD))))

def crtDirectSaveRegs (r : CrtDirectReg → Fin T) (R : Regs T A) (a s m : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update R (r .upper) (List.replicate a tick ++ R (r .upper)))
      (r .aI) []) (r .wD) (crtEnt a ++ R (r .wD)))
      (r .sI) []) (r .sD) (crtEnt s ++ R (r .sD)))
      (r .muI) []) (r .mD) (crtEnt m ++ R (r .mD))

theorem crtDirectSave_runs {r : CrtDirectReg → Fin T} (hr : Function.Injective r)
    (R : Regs T A) (a s m : ℕ)
    (ha : R (r .aI) = List.replicate a tick) (hs : R (r .sI) = List.replicate s tick)
    (hm : R (r .muI) = List.replicate m tick) (ht : R (r .tmp) = []) :
    crtRuns body (crtDirectSave r) R (crtDirectSaveRegs r R a s m)
      (6 * a + 2 * s + 2 * m + 16) := by
  have h₁ := crtUcopy_runs (body := body) (hr.ne (by decide : CrtDirectReg.aI ≠ .upper))
    (hr.ne (by decide : CrtDirectReg.aI ≠ .tmp)) (hr.ne (by decide : CrtDirectReg.upper ≠ .tmp)) R ht
  rw [ha, List.length_replicate] at h₁
  let R₁ := Function.update R (r .upper) (List.replicate a tick ++ R (r .upper))
  have h₂ := crtPushEnt_runs (body := body) (hr.ne (by decide : CrtDirectReg.aI ≠ .wD)) R₁ a
    (by simp [R₁, hr.eq_iff, ha])
  let R₂ := Function.update (Function.update R₁ (r .aI) []) (r .wD) (crtEnt a ++ R₁ (r .wD))
  have h₃ := crtPushEnt_runs (body := body) (hr.ne (by decide : CrtDirectReg.sI ≠ .sD)) R₂ s
    (by simp [R₂, R₁, hr.eq_iff, hs])
  let R₃ := Function.update (Function.update R₂ (r .sI) []) (r .sD) (crtEnt s ++ R₂ (r .sD))
  have h₄ := crtPushEnt_runs (body := body) (hr.ne (by decide : CrtDirectReg.muI ≠ .mD)) R₃ m
    (by simp [R₃, R₂, R₁, hr.eq_iff, hm])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))) ?_) (by omega)
  simp [crtDirectSaveRegs, R₃, R₂, R₁, hr.eq_iff]

/-- Forward index update happens before the call; inverse update afterwards. -/
def crtDirectStep (forward : Bool) (r : CrtDirectReg → Fin T) (p : Pr F T Q A U) : Pr F T Q A U :=
  if forward then
    .seq (crtPop (r .index)) (.seq (crtDirectLoad r) (.seq (crtDirectTarget r p) (crtDirectSave r)))
  else
    .seq (crtDirectLoad (r ∘ crtDirectFlip))
      (.seq (crtDirectTarget r p) (.seq (crtDirectSave (r ∘ crtDirectFlip)) (crtPush (r .index) tick)))


/-- The complete traversal invariant. The data argument can denote any fixed
physical layout, while the streams retain the old descending/ascending order. -/
def crtDirectState {d : ℕ} (a s m : Fin d → ℕ) (r : CrtDirectReg → Fin T)
    (R : Regs T A) (data : List (Fin (A + 4))) (n : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update R
      (r .str) data) (r .wT) (crtEnts ((crtRevAx n).map a)))
      (r .sT) (crtEnts ((crtRevAx n).map s))) (r .mT) (crtEnts ((crtRevAx n).map m)))
      (r .wD) (crtEnts (((List.finRange d).drop n).map a)))
      (r .sD) (crtEnts (((List.finRange d).drop n).map s)))
      (r .mD) (crtEnts (((List.finRange d).drop n).map m)))
      (r .lower) (List.replicate (crtPre a n) tick))
      (r .upper) (List.replicate (crtW a ((List.finRange d).drop n)) tick))
      (r .index) (List.replicate n tick)

/-- State presented to the target: index, current triple, and both strict
side-width sums are populated; all other registers retain the baseline frame. -/
def crtDirectCallState {d : ℕ} (a s m : Fin d → ℕ) (r : CrtDirectReg → Fin T)
    (R : Regs T A) (data : List (Fin (A + 4))) (i : ℕ) (hi : i < d) : Regs T A :=
  crtDirectLoadRegs r
    (Function.update (crtDirectState a s m r R data (i + 1)) (r .index) (List.replicate i tick))
    (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
    ((crtRevAx i).map a) ((crtRevAx i).map s) ((crtRevAx i).map m)

/-- The forward parameter iteration is concrete; only the nonzero target's
data operation is supplied by a separate contract. -/
theorem crtDirectForwardStep_runs {d : ℕ} (a s m : Fin d → ℕ)
    {r : CrtDirectReg → Fin T} (hr : Function.Injective r) (p : Pr F T Q A U)
    (R : Regs T A) (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R (r q) = [])
    (input output : List (Fin (A + 4))) (i : ℕ) (hi : i < d) (b : ℕ) (hb : 1 ≤ b)
    (hzero : i = 0 → output = input)
    (hbody : i ≠ 0 → crtRuns body p (crtDirectCallState a s m r R input i hi)
      (Function.update (crtDirectCallState a s m r R input i hi) (r .str) output) b) :
    crtRuns body (crtDirectStep true r p)
      (crtDirectState a s m r R input (i + 1)) (crtDirectState a s m r R output i)
      (b + 12 * a ⟨i, hi⟩ + 4 * s ⟨i, hi⟩ + 4 * m ⟨i, hi⟩ + 35) := by
  let R₀ := crtDirectState a s m r R input (i + 1)
  let R₁ := Function.update R₀ (r .index) (List.replicate i tick)
  let R₂ := crtDirectCallState a s m r R input i hi
  let R₃ := Function.update R₂ (r .str) output
  have hpop := crtPop_runs (body := body) (r .index) R₀
  have hind : (R₀ (r .index)).tail = List.replicate i tick := by simp [R₀, crtDirectState]
  rw [hind] at hpop
  have hload := crtDirectLoad_runs (body := body) hr R₁ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
    ((crtRevAx i).map a) ((crtRevAx i).map s) ((crtRevAx i).map m)
    (by simp [R₁, R₀, crtDirectState, hr.eq_iff, crtRevAx_succ hi])
    (by simp [R₁, R₀, crtDirectState, hr.eq_iff, crtRevAx_succ hi])
    (by simp [R₁, R₀, crtDirectState, hr.eq_iff, crtRevAx_succ hi])
    (by intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        all_goals simp [R₁, R₀, crtDirectState, hr.eq_iff, hz .aI (by simp), hz .sI (by simp), hz .muI (by simp), hz .tmp (by simp)])
  have htarget : crtRuns body (crtDirectTarget r p) R₂ R₃ (b + 2) := by
    apply crtIfR_runs
    · intro hn
      apply hbody
      intro h
      subst i
      exact hn (by simp [R₂, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    · intro he
      have hi0 : i = 0 := by simpa [R₂, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff] using he
      have hdata : R₂ (r .str) = input := by
        simp [R₂, crtDirectCallState, crtDirectLoadRegs, crtDirectState, hr.eq_iff]
      have hid : R₃ = R₂ := by
        funext z
        by_cases hz : z = r .str
        · subst z; simp [R₃, hzero hi0, hdata]
        · simp [R₃, hz]
      rw [hid]
      apply crtRuns_mono (b := 1) _ hb
      intro v S hS _
      exact ⟨v, 1, rfl, le_rfl, by simpa [← hS] using (Exec.act (body := body) .done (mk v S))⟩
  have hsave := crtDirectSave_runs (body := body) hr R₃ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
    (by simp [R₃, R₂, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    (by simp [R₃, R₂, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    (by simp [R₃, R₂, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    (by simp [R₃, R₂, crtDirectCallState, crtDirectLoadRegs, crtDirectState, hr.eq_iff, hz .tmp (by simp)])
  have hresult : crtDirectSaveRegs r R₃ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩) =
      crtDirectState a s m r R output i := by
    funext z
    by_cases he : ∃ q, z = r q
    · obtain ⟨q, rfl⟩ := he
      cases q <;> simp [R₃, R₂, crtDirectCallState, crtDirectLoadRegs, crtDirectSaveRegs,
        crtDirectState, hr.eq_iff, crt_drop_finRange hi, crtPre_succ a hi, crtW,
        crtEnts_cons, hz .aI (by simp), hz .sI (by simp), hz .muI (by simp), hz .tmp (by simp)]
    · have hn : ∀ q, z ≠ r q := by simpa using he
      simp [R₃, R₂, crtDirectCallState, crtDirectLoadRegs, crtDirectSaveRegs, crtDirectState, hn]
  have h := crtRuns_seq hpop (crtRuns_seq hload (crtRuns_seq htarget hsave))
  rw [hresult] at h
  exact crtRuns_mono h (by omega)


/-- Restore saved ascending entries to the external descending streams. -/
def crtDirectRestore (r : CrtDirectReg → Fin T) : Pr F T Q A U :=
  .seq (crtMv (r .wD) (r .wT))
    (.seq (crtMv (r .sD) (r .sT))
      (.seq (crtMv (r .mD) (r .mT)) (.seq (uclear (r .upper)) (uclear (r .index)))))

/-- Source streams are restored exactly, including all separators. -/
theorem crtDirectRestore_runs {d : ℕ} (a s m : Fin d → ℕ)
    {r : CrtDirectReg → Fin T} (hr : Function.Injective r)
    (R : Regs T A) (data : List (Fin (A + 4)))
    (hw : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hs : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hm : R (r .mT) = crtEnts ((crtRevAx d).map m))
    (hz : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index], R (r q) = []) :
    crtRuns body (crtDirectRestore r) (crtDirectState a s m r R data 0)
      (Function.update R (r .str) data)
      (2 * ((crtEnts (A := A) ((List.finRange d).map a)).length +
        (crtEnts (A := A) ((List.finRange d).map s)).length +
        (crtEnts (A := A) ((List.finRange d).map m)).length + crtW a (List.finRange d)) + 10) := by
  let R₀ := crtDirectState a s m r R data 0
  let R₁ := Function.update (Function.update R₀ (r .wD) []) (r .wT)
    ((R₀ (r .wD)).reverse ++ R₀ (r .wT))
  let R₂ := Function.update (Function.update R₁ (r .sD) []) (r .sT)
    ((R₁ (r .sD)).reverse ++ R₁ (r .sT))
  let R₃ := Function.update (Function.update R₂ (r .mD) []) (r .mT)
    ((R₂ (r .mD)).reverse ++ R₂ (r .mT))
  let R₄ := Function.update R₃ (r .upper) []
  have h₁ := crtMv_runs (body := body) (hr.ne (by decide : CrtDirectReg.wD ≠ .wT)) R₀
  have h₂ := crtMv_runs (body := body) (hr.ne (by decide : CrtDirectReg.sD ≠ .sT)) R₁
  have h₃ := crtMv_runs (body := body) (hr.ne (by decide : CrtDirectReg.mD ≠ .mT)) R₂
  have h₄ := crtClear_runs (body := body) (r .upper) R₃
  have h₅ := crtClear_runs (body := body) (r .index) R₄
  have hout : Function.update R₄ (r .index) [] = Function.update R (r .str) data := by
    have hfull : crtRevAx (d := d) d = (List.finRange d).reverse := by
      unfold crtRevAx
      rw [List.take_of_length_le (by simp)]
    have hnil : crtRevAx (d := d) 0 = [] := rfl
    have hrev : ∀ g : Fin d → ℕ, (crtEnts (A := A) ((List.finRange d).map g)).reverse =
        crtEnts ((crtRevAx d).map g) := by
      intro g
      simp [crtEnts_reverse, hfull, List.map_reverse]
    funext z
    by_cases he : ∃ q, z = r q
    · obtain ⟨q, rfl⟩ := he
      cases q <;> simp [R₄, R₃, R₂, R₁, R₀, crtDirectState, hr.eq_iff, hrev,
        hfull, hnil, List.map_reverse, crtPre, crtLow, hw, hs, hm,
        hz .wD (by simp), hz .sD (by simp), hz .mD (by simp),
        hz .lower (by simp), hz .upper (by simp), hz .index (by simp)]
    · have hn : ∀ q, z ≠ r q := by simpa using he
      simp [R₄, R₃, R₂, R₁, R₀, crtDirectState, hn]
  have h := crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ (crtRuns_seq h₄ h₅)))
  rw [hout] at h
  apply crtRuns_mono h
  simp [R₄, R₃, R₂, R₁, R₀, crtDirectState, hr.eq_iff]
  omega


/-- Per-target costs are summed, avoiding an extra dimension factor from
replacing the weighted routing cost by a uniform maximum. -/
theorem crtDirectForwardLoop_weighted {d : ℕ} (a s m : Fin d → ℕ)
    {r : CrtDirectReg → Fin T} (hr : Function.Injective r) (p : Pr F T Q A U)
    (R : Regs T A) (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R (r q) = [])
    (data : ℕ → List (Fin (A + 4))) (b : Fin d → ℕ) (hb : ∀ j, 1 ≤ b j)
    (hzero : data 0 = data 1)
    (hbody : ∀ i (hi : i < d), i ≠ 0 →
      crtRuns body p (crtDirectCallState a s m r R (data (i + 1)) i hi)
        (Function.update (crtDirectCallState a s m r R (data (i + 1)) i hi) (r .str) (data i))
        (b ⟨i, hi⟩)) :
    crtRuns body (crtWhile (r .wT) (crtDirectStep true r p))
      (crtDirectState a s m r R (data d) d) (crtDirectState a s m r R (data 0) 0)
      (((List.finRange d).map (fun j => b j + 12 * a j + 4 * s j + 4 * m j + 37)).sum + 2) := by
  have hprefix : ∀ n, n ≤ d →
      crtRuns body (crtWhile (r .wT) (crtDirectStep true r p))
        (crtDirectState a s m r R (data n) n) (crtDirectState a s m r R (data 0) 0)
        (((crtRevAx n).map (fun j => b j + 12 * a j + 4 * s j + 4 * m j + 37)).sum + 2) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h := crtWhile_runs (body := body) (r := r .wT) (p := crtDirectStep true r p)
        (Ψ := fun _ => crtDirectState a s m r R (data 0) 0) (N := 0) (b := 0)
        (by intro k hk; omega) (by simp [crtDirectState, hr.eq_iff, crtRevAx])
      simpa [crtRevAx] using h
    | succ n ih =>
      intro hn
      have hi : n < d := by omega
      have htail := ih (by omega)
      have hstep := crtDirectForwardStep_runs a s m hr p R hz (data (n + 1)) (data n) n hi
        (b ⟨n, hi⟩) (hb _) (by intro h; simpa [h] using hzero) (hbody n hi)
      have hne : crtDirectState a s m r R (data (n + 1)) (n + 1) (r .wT) ≠ [] := by
        simp [crtDirectState, hr.eq_iff, crtRevAx_succ hi, crtEnts_cons, crtEnt]
      have h := crtReverseWhile_step hne hstep htail
      apply crtRuns_mono h
      simp [crtRevAx_succ hi]
      omega
  have h := hprefix d le_rfl
  have hfull : crtRevAx (d := d) d = (List.finRange d).reverse := by
    unfold crtRevAx
    rw [List.take_of_length_le (by simp)]
  simpa [hfull, List.map_reverse] using h

/-- Ascending inverse iteration, with the same strict-side call state as the
forward traversal and an exact data-only target operation. -/
theorem crtDirectInverseStep_runs {d : ℕ} (a s m : Fin d → ℕ)
    {r : CrtDirectReg → Fin T} (hr : Function.Injective r) (p : Pr F T Q A U)
    (R : Regs T A) (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R (r q) = [])
    (input output : List (Fin (A + 4))) (i : ℕ) (hi : i < d) (b : ℕ) (hb : 1 ≤ b)
    (hzero : i = 0 → output = input)
    (hbody : i ≠ 0 → crtRuns body p (crtDirectCallState a s m r R input i hi)
      (Function.update (crtDirectCallState a s m r R input i hi) (r .str) output) b) :
    crtRuns body (crtDirectStep false r p)
      (crtDirectState a s m r R input i) (crtDirectState a s m r R output (i + 1))
      (b + 12 * a ⟨i, hi⟩ + 4 * s ⟨i, hi⟩ + 4 * m ⟨i, hi⟩ + 35) := by
  let rr := r ∘ crtDirectFlip
  have hrr : Function.Injective rr := hr.comp crtDirectFlip_injective
  let R₀ := crtDirectState a s m r R input i
  let R₁ := crtDirectLoadRegs rr R₀ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
    (((List.finRange d).drop (i + 1)).map a) (((List.finRange d).drop (i + 1)).map s)
    (((List.finRange d).drop (i + 1)).map m)
  let R₂ := Function.update R₁ (r .str) output
  let R₃ := crtDirectSaveRegs rr R₂ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
  have hload := crtDirectLoad_runs (body := body) hrr R₀ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
    (((List.finRange d).drop (i + 1)).map a) (((List.finRange d).drop (i + 1)).map s)
    (((List.finRange d).drop (i + 1)).map m)
    (by simp [R₀, rr, Function.comp_def, crtDirectFlip, crtDirectState, hr.eq_iff, crt_drop_finRange hi])
    (by simp [R₀, rr, Function.comp_def, crtDirectFlip, crtDirectState, hr.eq_iff, crt_drop_finRange hi])
    (by simp [R₀, rr, Function.comp_def, crtDirectFlip, crtDirectState, hr.eq_iff, crt_drop_finRange hi])
    (by intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        all_goals simp [R₀, rr, Function.comp_def, crtDirectFlip, crtDirectState, hr.eq_iff,
          hz .aI (by simp), hz .sI (by simp), hz .muI (by simp), hz .tmp (by simp)])
  have hcall : R₁ = crtDirectCallState a s m r R input i hi := by
    funext z
    by_cases he : ∃ q, z = r q
    · obtain ⟨q, rfl⟩ := he
      cases q <;> simp [R₁, R₀, rr, Function.comp_def, crtDirectFlip, crtDirectCallState,
        crtDirectLoadRegs, crtDirectState, hr.eq_iff, crt_drop_finRange hi, crtPre_succ a hi, crtW]
    · have hn : ∀ q, z ≠ r q := by simpa using he
      simp [R₁, R₀, rr, Function.comp_def, crtDirectFlip, crtDirectCallState,
        crtDirectLoadRegs, crtDirectState, hn]
  have htarget : crtRuns body (crtDirectTarget r p) R₁ R₂ (b + 2) := by
    apply crtIfR_runs
    · intro hn
      have hi0 : i ≠ 0 := by
        intro h; subst i
        exact hn (by simp [hcall, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
      simpa [R₂, hcall] using hbody hi0
    · intro he
      have hi0 : i = 0 := by
        simpa [hcall, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff] using he
      have hdata : R₁ (r .str) = input := by
        simp [hcall, crtDirectCallState, crtDirectLoadRegs, crtDirectState, hr.eq_iff]
      have hid : R₂ = R₁ := by
        funext z
        by_cases hz : z = r .str
        · subst z; simp [R₂, hzero hi0, hdata]
        · simp [R₂, hz]
      rw [hid]
      apply crtRuns_mono (b := 1) _ hb
      intro v S hS _
      exact ⟨v, 1, rfl, le_rfl, by simpa [← hS] using (Exec.act (body := body) .done (mk v S))⟩
  have hsave := crtDirectSave_runs (body := body) hrr R₂ (a ⟨i, hi⟩) (s ⟨i, hi⟩) (m ⟨i, hi⟩)
    (by simp [R₂, hcall, rr, Function.comp_def, crtDirectFlip, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    (by simp [R₂, hcall, rr, Function.comp_def, crtDirectFlip, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    (by simp [R₂, hcall, rr, Function.comp_def, crtDirectFlip, crtDirectCallState, crtDirectLoadRegs, hr.eq_iff])
    (by simp [R₂, hcall, rr, Function.comp_def, crtDirectFlip, crtDirectCallState, crtDirectLoadRegs,
      crtDirectState, hr.eq_iff, hz .tmp (by simp)])
  have hpush := crtPush_runs (body := body) (r .index) tick R₃
  have hresult : Function.update R₃ (r .index) (tick :: R₃ (r .index)) =
      crtDirectState a s m r R output (i + 1) := by
    funext z
    by_cases he : ∃ q, z = r q
    · obtain ⟨q, rfl⟩ := he
      cases q <;> simp [R₃, R₂, R₁, R₀, rr, Function.comp_def, crtDirectFlip,
        crtDirectLoadRegs, crtDirectSaveRegs, crtDirectState, hr.eq_iff, crt_drop_finRange hi,
        crtPre_succ a hi, crtRevAx_succ hi, crtW, crtEnts_cons, List.replicate_succ, Nat.add_comm,
        hz .aI (by simp), hz .sI (by simp), hz .muI (by simp), hz .tmp (by simp)]
    · have hn : ∀ q, z ≠ r q := by simpa using he
      simp [R₃, R₂, R₁, R₀, rr, Function.comp_def, crtDirectFlip, crtDirectLoadRegs,
        crtDirectSaveRegs, crtDirectState, hn]
  have h := crtRuns_seq hload (crtRuns_seq htarget (crtRuns_seq hsave hpush))
  rw [hresult] at h
  exact crtRuns_mono h (by omega)


/-- Ascending traversal retains the exact sum of individual target budgets. -/
theorem crtDirectInverseLoop_weighted {d : ℕ} (a s m : Fin d → ℕ)
    {r : CrtDirectReg → Fin T} (hr : Function.Injective r) (p : Pr F T Q A U)
    (R : Regs T A) (hz : ∀ q ∈ [CrtDirectReg.aI, .sI, .muI, .tmp], R (r q) = [])
    (data : ℕ → List (Fin (A + 4))) (b : Fin d → ℕ) (hb : ∀ j, 1 ≤ b j)
    (hzero : data 1 = data 0)
    (hbody : ∀ i (hi : i < d), i ≠ 0 →
      crtRuns body p (crtDirectCallState a s m r R (data i) i hi)
        (Function.update (crtDirectCallState a s m r R (data i) i hi) (r .str) (data (i + 1)))
        (b ⟨i, hi⟩)) :
    crtRuns body (crtWhile (r .wD) (crtDirectStep false r p))
      (crtDirectState a s m r R (data 0) 0) (crtDirectState a s m r R (data d) d)
      (((List.finRange d).map (fun j => b j + 12 * a j + 4 * s j + 4 * m j + 37)).sum + 2) := by
  have hsuffix : ∀ k n, n + k = d →
      crtRuns body (crtWhile (r .wD) (crtDirectStep false r p))
        (crtDirectState a s m r R (data n) n) (crtDirectState a s m r R (data d) d)
        ((((List.finRange d).drop n).map (fun j => b j + 12 * a j + 4 * s j + 4 * m j + 37)).sum + 2) := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have he : n = d := by omega
      subst n
      have h := crtWhile_runs (body := body) (r := r .wD) (p := crtDirectStep false r p)
        (Ψ := fun _ => crtDirectState a s m r R (data d) d) (N := 0) (b := 0)
        (by intro k hk; omega) (by simp [crtDirectState, hr.eq_iff, List.drop_eq_nil_of_le])
      simpa [List.drop_eq_nil_of_le] using h
    | succ k ih =>
      intro n hn
      have hi : n < d := by omega
      have htail := ih (n + 1) (by omega)
      have hstep := crtDirectInverseStep_runs a s m hr p R hz (data n) (data (n + 1)) n hi
        (b ⟨n, hi⟩) (hb _) (by intro h; simpa [h] using hzero) (hbody n hi)
      have hne : crtDirectState a s m r R (data n) n (r .wD) ≠ [] := by
        simp [crtDirectState, hr.eq_iff, crt_drop_finRange hi, crtEnts_cons, crtEnt]
      have h := crtReverseWhile_step hne hstep htail
      apply crtRuns_mono h
      simp [crt_drop_finRange hi]
      omega
  simpa using hsuffix d 0 (by omega)

/-- The inverse loop already reconstructs descending external streams. Its
endpoint cleanup only releases the lower-width and target-index counters. -/
def crtDirectInverseCleanup (r : CrtDirectReg → Fin T) : Pr F T Q A U :=
  .seq (uclear (r .lower)) (uclear (r .index))

theorem crtDirectInverseCleanup_runs {d : ℕ} (a s m : Fin d → ℕ)
    {r : CrtDirectReg → Fin T} (hr : Function.Injective r)
    (R : Regs T A) (data : List (Fin (A + 4)))
    (hw : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hs : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hm : R (r .mT) = crtEnts ((crtRevAx d).map m))
    (hz : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index], R (r q) = []) :
    crtRuns body (crtDirectInverseCleanup r) (crtDirectState a s m r R data d)
      (Function.update R (r .str) data) (2 * crtPre a d + 2 * d + 4) := by
  let R₀ := crtDirectState a s m r R data d
  let R₁ := Function.update R₀ (r .lower) []
  have h₁ := crtClear_runs (body := body) (r .lower) R₀
  have h₂ := crtClear_runs (body := body) (r .index) R₁
  have hout : Function.update R₁ (r .index) [] = Function.update R (r .str) data := by
    funext z
    by_cases he : ∃ q, z = r q
    · obtain ⟨q, rfl⟩ := he
      cases q <;> simp [R₁, R₀, crtDirectState, hr.eq_iff, hw, hs, hm, crtW, List.drop_eq_nil_of_le,
        hz .wD (by simp), hz .sD (by simp), hz .mD (by simp),
        hz .lower (by simp), hz .upper (by simp), hz .index (by simp)]
    · have hn : ∀ q, z ≠ r q := by simpa using he
      simp [R₁, R₀, crtDirectState, hn]
  have h := crtRuns_seq h₁ h₂
  rw [hout] at h
  apply crtRuns_mono h
  simp [R₁, R₀, crtDirectState, hr.eq_iff]
  omega

end IntegerMultBounds.MathlibTM2.Fast
