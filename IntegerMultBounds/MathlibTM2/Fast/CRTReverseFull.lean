module

public import IntegerMultBounds.MathlibTM2.Fast.CRTReverse

/-! # Complete runtime paired reversal
The original width stream, unary axis count, unary total width, and binary
record exponent are preserved. The opposite stream and all temporary counters
are constructed at runtime and erased again after the physical reversal.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Prepare the opposite width stream and both unary runtime controls. -/
def crtReverseSetup (r : CrtReverseReg → Fin T) (axes width pairs : Fin T) : Pr F T Q A U :=
  .seq (bcopy (r .left) (r .stmp) (r .t₁) (r .t₂))
    (.seq (crtMv (r .stmp) (r .right))
      (.seq (ucopy width (r .gap) (r .tmp)) (udiv 2 axes pairs (r .tmp))))

def crtReverseSetupRegs (r : CrtReverseReg → Fin T) (axes width pairs : Fin T)
    (R : Regs T A) : Regs T A :=
  Function.update (Function.update (Function.update R (r .right) (R (r .left)).reverse)
    (r .gap) (List.replicate (R width).length tick))
    pairs (List.replicate ((R axes).length / 2) tick)

def crtReverseSetupCost (r : CrtReverseReg → Fin T) (axes width : Fin T)
    (R : Regs T A) : ℕ :=
  8 * (R (r .left)).length + 4 * (R width).length + 4 * (R axes).length + 16

theorem crtReverseSetup_runs {r : CrtReverseReg → Fin T} (hr : Function.Injective r)
    (axes width pairs : Fin T) (_haw : axes ≠ width) (hap : axes ≠ pairs)
    (_hwp : width ≠ pairs) (ha : ∀ q, r q ≠ axes) (hw : ∀ q, r q ≠ width)
    (hp : ∀ q, r q ≠ pairs) (R : Regs T A)
    (hz : ∀ q ∈ [CrtReverseReg.stmp, .right, .t₁, .t₂, .gap, .tmp], R (r q) = [])
    (hpc : R pairs = []) :
    crtRuns body (crtReverseSetup r axes width pairs) R
      (crtReverseSetupRegs r axes width pairs R) (crtReverseSetupCost r axes width R) := by
  have h₁ := crtBcopy_runs (body := body)
    (show [r .left, r .stmp, r .t₁, r .t₂].Nodup by simp [hr.eq_iff]) R
    (hz _ (by simp)) (hz _ (by simp))
  let R₁ := Function.update R (r .stmp) (R (r .left) ++ R (r .stmp))
  let R₂ := Function.update (Function.update R₁ (r .stmp) []) (r .right)
    ((R₁ (r .stmp)).reverse ++ R₁ (r .right))
  let R₃ := Function.update R₂ (r .gap)
    (List.replicate (R₂ width).length tick ++ R₂ (r .gap))
  have h₂ := crtMv_runs (body := body) (hr.ne (by decide : CrtReverseReg.stmp ≠ .right)) R₁
  have h₃ := crtUcopy_runs (body := body) (hw .gap).symm (hw .tmp).symm
    (hr.ne (by decide : CrtReverseReg.gap ≠ .tmp)) R₂
    (by simp [R₂, R₁, hr.eq_iff, hz .tmp (by simp)])
  have h₄ := crtReverseHalf_runs (body := body) hap (ha .tmp).symm (hp .tmp).symm R₃
    (by simp [R₃, R₂, R₁, hr.eq_iff, hz .tmp (by simp)])
    (by simp [R₃, R₂, R₁, fun q => (hp q).symm, hpc])
  have h := crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))
  have hres : Function.update R₃ pairs (List.replicate ((R₃ axes).length / 2) tick) =
      crtReverseSetupRegs r axes width pairs R := by
    have he : Function.update R (r .stmp) [] = R := by
      funext z
      by_cases h : z = r .stmp
      · subst z; simp [hz .stmp (by simp)]
      · simp [h]
    simp [R₃, R₂, R₁, crtReverseSetupRegs, hr.eq_iff, fun q => (ha q).symm,
      fun q => (hw q).symm, hz .stmp (by simp), hz .right (by simp), hz .gap (by simp), he]
  rw [hres] at h
  apply crtRuns_mono (show crtRuns body (crtReverseSetup r axes width pairs) R _ _ from h)
  simp [R₃, R₂, R₁, crtReverseSetupCost, hr.eq_iff, fun q => (ha q).symm,
    fun q => (hw q).symm, hz .stmp (by simp)]
  omega

noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {K : ℕ}

/-- Fixed runtime program; the list of axes is never compiled into control. -/
def crtReverseFull (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReverseReg → Fin T) (axes width pairs : Fin T) : Pr F T Q (prime + K) U :=
  .seq (crtReverseSetup r axes width pairs)
    (.seq (crtReverseLoop hQ ι hι hT r pairs)
      (.seq (crtReverseCleanup r) (uclear (r .right))))


/-- Complete reversal changes only the data register. All input parameters and
width entries are preserved, and every temporary is empty on return. -/
theorem crtReverseFull_runs {d : ℕ} (a : Fin d → ℕ)
    {body' : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {r : CrtReverseReg → Fin T} (hr : Function.Injective r)
    (hbank : ∀ z q, ι q ≠ r z) (axes width pairs : Fin T)
    (haw : axes ≠ width) (hap : axes ≠ pairs) (hwp : width ≠ pairs)
    (ha : ∀ q, r q ≠ axes) (hw : ∀ q, r q ≠ width) (hp : ∀ q, r q ≠ pairs)
    (hip : ∀ q, ι q ≠ pairs)
    (hadj : ∀ j k, a j ≤ a k + 1)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ z ∈ C y, z.val < 8)
    (x : Fin d → ℕ) (o : List (Fin d)) (ho : o.Nodup)
    (R : Regs T (prime + K))
    (hstr : R (r .str) = (crtBox a o C x).flatten)
    (hl : R (r .left) = crtEnts (o.map a))
    (haxes : (R axes).length = o.length) (hwidth : (R width).length = crtW a o)
    (he3 : R (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hz : ∀ q, q ≠ .str → q ≠ .left → q ≠ .e3B → R (r q) = [])
    (hpc : R pairs = []) (hι0 : ∀ q, R (ι q) = []) :
    crtRuns body' (crtReverseFull hQ ι hι hT r axes width pairs) R
      (Function.update R (r .str) (crtBox a o.reverse C x).flatten)
      (crtReverseLoopCost T a B o [] [] + 14 * (R (r .left)).length +
        6 * (R width).length + 4 * (R axes).length + 28) := by
  let R₀ := crtReverseSetupRegs r axes width pairs R
  have hsetup := crtReverseSetup_runs (body := body') hr axes width pairs haw hap hwp ha hw hp R
    (by intro q hq; apply hz q <;> grind) hpc
  have hzero : ∀ q ∈ [CrtReverseReg.aJ, .aK, .tmp, .stmp, .tu, .t₁, .t₂], R₀ (r q) = [] := by
    intro q hq
    have hqz := hz q (by grind) (by grind) (by grind)
    have hn : q ≠ .right ∧ q ≠ .gap := by grind
    simpa [R₀, crtReverseSetupRegs, hp, hr.eq_iff, hn.1, hn.2] using hqz
  obtain ⟨R₁, hout, hf, hloop⟩ := crtReverseLoop_runs (body' := body') a hQ ι hι hT hr hbank pairs hp hip
    hadj C B hB hC h8 x o ho [] [] R₀ [] []
    (by simpa [R₀, crtReverseSetupRegs, hp, hr.eq_iff] using hstr)
    (by simpa [R₀, crtReverseSetupRegs, hp, hr.eq_iff] using hl)
    (by simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff, hl, crtEnts_reverse, List.map_reverse])
    (by simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff, hz .pre (by decide) (by decide) (by decide), crtW])
    (by simp [R₀, crtReverseSetupRegs, hp, hwidth])
    (by simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff, hz .post (by decide) (by decide) (by decide), crtW])
    (by simp [R₀, crtReverseSetupRegs, haxes])
    (by simpa [R₀, crtReverseSetupRegs, hp, hr.eq_iff] using he3) hzero
    (by intro q; simp [R₀, crtReverseSetupRegs, hip, hbank, hι0])
  have hld : R₀ (r .leftDone) = [] := by
    simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff, hz .leftDone (by decide) (by decide) (by decide)]
  have hrd : R₀ (r .rightDone) = [] := by
    simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff, hz .rightDone (by decide) (by decide) (by decide)]
  let R₂ := crtReverseCleanupRegs r R₁
  let R₃ := Function.update R₂ (r .right) []
  have hc := crtReverseCleanup_runs (body := body') hr R₁
  have hframe := crtReverseCleanup_frame hr hp hf hld hrd
  dsimp only at hframe
  change R₂ (r .str) = R₁ (r .str) ∧ R₂ (r .left) = R₀ (r .left) ∧
    R₂ (r .right) = R₀ (r .right) ∧ R₂ pairs = [] ∧
    (∀ q ∈ [CrtReverseReg.leftDone, .rightDone, .pre, .gap, .post], R₂ (r q) = []) ∧
    (∀ z, z ≠ pairs → (∀ q ∈ crtReverseChanged, z ≠ r q) → R₂ z = R₀ z) at hframe
  have hclear := crtClear_runs (body := body') (r .right) R₂
  have hresult : R₃ = Function.update R (r .str) (crtBox a o.reverse C x).flatten := by
    funext z
    by_cases hs : z = r .str
    · subst z
      simpa [R₃, hr.eq_iff, hframe.1] using hout
    by_cases hpz : z = pairs
    · subst z
      simp [R₃, (hp .right).symm, (hp .str).symm, hframe.2.2.2.1, hpc]
    by_cases hlz : z = r .left
    · subst z
      simp [R₃, hr.eq_iff, hframe.2.1, R₀, crtReverseSetupRegs, hp]
    by_cases hrz : z = r .right
    · subst z
      simp [R₃, hr.eq_iff, hz .right (by decide) (by decide) (by decide)]
    by_cases hldz : z = r .leftDone
    · subst z
      simp [R₃, hr.eq_iff, hframe.2.2.2.2.1 .leftDone (by simp),
        hz .leftDone (by decide) (by decide) (by decide)]
    by_cases hrdz : z = r .rightDone
    · subst z
      simp [R₃, hr.eq_iff, hframe.2.2.2.2.1 .rightDone (by simp),
        hz .rightDone (by decide) (by decide) (by decide)]
    by_cases hprez : z = r .pre
    · subst z
      simp [R₃, hr.eq_iff, hframe.2.2.2.2.1 .pre (by simp),
        hz .pre (by decide) (by decide) (by decide)]
    by_cases hgapz : z = r .gap
    · subst z
      simp [R₃, hr.eq_iff, hframe.2.2.2.2.1 .gap (by simp),
        hz .gap (by decide) (by decide) (by decide)]
    by_cases hpostz : z = r .post
    · subst z
      simp [R₃, hr.eq_iff, hframe.2.2.2.2.1 .post (by simp),
        hz .post (by decide) (by decide) (by decide)]
    have he := hframe.2.2.2.2.2 z hpz
      (by intro q hq; simp only [crtReverseChanged, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    simpa [R₃, hrz, hs, R₀, crtReverseSetupRegs, hpz, hgapz] using he
  have hleftlen : (R₁ (r .leftDone)).length ≤ (R (r .left)).length := by
    have h := congrArg List.length hf.2.1
    rw [hld] at h
    simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff] at h
    omega
  have hrightlen : (R₁ (r .rightDone)).length ≤ (R (r .left)).length := by
    have h := congrArg List.length hf.2.2.1
    rw [hrd] at h
    simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff] at h
    omega
  have hwidthsum := hf.2.2.2.2
  simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff,
    hz .pre (by decide) (by decide) (by decide),
    hz .post (by decide) (by decide) (by decide)] at hwidthsum
  have hrightsize : (R₂ (r .right)).length = (R (r .left)).length := by
    rw [hframe.2.2.1]
    simp [R₀, crtReverseSetupRegs, hp, hr.eq_iff]
  have hall := crtRuns_seq hsetup (crtRuns_seq hloop (crtRuns_seq hc hclear))
  change crtRuns body' (crtReverseFull hQ ι hι hT r axes width pairs) R R₃ _ at hall
  rw [hresult] at hall
  apply crtRuns_mono hall
  simp only [crtReverseSetupCost, crtReverseCleanupCost, hrightsize]
  omega

end

end IntegerMultBounds.MathlibTM2.Fast
