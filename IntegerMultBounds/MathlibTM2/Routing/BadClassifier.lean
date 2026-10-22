module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedCopy
public import IntegerMultBounds.MathlibTM2.Routing.PaddedSpread
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveRepairSpec

/-!
# The concrete physical bad-address classifier

The target copy and both spread borrowed fields include one high zero. The
existing automaton therefore flushes the final segment even with no suffix.
No field-width assumption is made on the complete spectator field.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

inductive BadReg where
  | fld (f : Fin 5)
  | mask | phase
  | word (k : Fin 3)
  | ts | tm | dst
  | spare (k : Fin 4)
  | st
  deriving DecidableEq

variable {T Q A : ℕ} {P U : Type}

def badClassifierInputs (ι : BadReg → Fin T) : Fin 4 → Fin T :=
  ![ι (.word 0), ι (.word 1), ι (.word 2), ι .phase]

def badClassifier (ι : BadReg → Fin T) (hA : 4 ≤ A) : Pr P T Q A U :=
  .seq (paddedCopy (ι (.fld 1)) (ι (.word 0)) (ι .ts) (ι .tm))
    (.seq (spread (ι (.fld 3)) (ι .mask) (ι .ts) (ι .tm) (ι .dst) (ι (.word 1)))
      (.seq (spread (ι (.fld 2)) (ι .mask) (ι .ts) (ι .tm) (ι .dst) (ι (.word 2)))
        (.seq (codePass (badClassifierInputs ι) (fun k => ι (.spare k)) (ι .st) (badC A hA))
          (.seq (bclear (ι (.word 0))) (.seq (bclear (ι (.word 1))) (bclear (ι (.word 2))))))))

def badClassifierCost (width : ℕ) : ℕ := 34 * width + 62

def BadInv (p : Par) (X : ℕ) (ι : BadReg → Fin T)
    (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  ∀ r : BadReg, r ≠ .st → R (ι r) = match r with
    | .fld f => binSyms (selectiveLen p X f) (digit (selectiveLen p X) f i)
    | .mask => binSyms (p.wy + 1) (mAV p)
    | .phase => binSyms (p.wy + 1) (mkV p)
    | _ => []

/-- The fixed physical classifier restores its whole register file, including
source counters and installed masks; only its scan-slot code changes. -/
theorem badClassifier_spec (p : Par) (X : ℕ) (ι : BadReg → Fin T)
    (hι : Function.Injective ι) (hA : 4 ≤ A) (hG : 0 < p.G) (hguard : p.G + 1 < p.K)
    (body : P → Pr P T Q A U) :
    CodeSpec body (badClassifier ι hA) (fun f => ι (.fld f)) (selectiveLen p X) (ι .st)
      (fun k => ∃ r, ι r = k) (BadInv p X ι) (codeSel (badC A hA))
      (selectiveBadCode p X) (badClassifierCost p.wy) where
  runs i v S hI := by
    have hGK : p.G < p.K := by omega
    have hblank (k : Fin 3) : S.R (ι (.word k)) = [] := hI (.word k) (by simp)
    have hfields (f : Fin 5) := hI (.fld f) (by simp)
    let vals := badVals p (selectiveView p X i)
    obtain ⟨v₁, hu₁, he₁⟩ := paddedCopy_exec body
      (src := ι (.fld 1)) (dst := ι (.word 0)) (tmp := ι .ts) (ctmp := ι .tm)
      (by simp [hι.eq_iff]) p.wy (selectiveView p X i).y (selectiveView_fits p X i).y
      v S (hfields 1) (hblank 0) (hI .ts (by simp)) (hI .tm (by simp))
    let R₁ := Function.update S.R (ι (.word 0)) (binSyms (p.wy + 1) (vals 0))
    have hk₁ (r : BadReg) (hr : r ≠ .word 0) : R₁ (ι r) = S.R (ι r) := by
      simp [R₁, hι.eq_iff, hr]
    have hregs (f : Fin 5) (k : Fin 3) :
        GSRegs (ι (.fld f)) (ι .mask) (ι .ts) (ι .tm) (ι .dst) (ι (.word k)) := by
      simp [GSRegs, hι.eq_iff]
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := spreadPadded_exec p hG hGK body (hregs 3 1)
      (selectiveView p X i).u v₁ { S with R := R₁ }
      (by dsimp only; rw [hk₁ _ (by simp)]; exact hI .mask (by simp))
      (by dsimp only; rw [hk₁ _ (by simp)]; exact hfields 3)
      (by dsimp only; rw [hk₁ _ (by simp)]; exact hI .ts (by simp))
      (by dsimp only; rw [hk₁ _ (by simp)]; exact hI .tm (by simp))
      (by dsimp only; rw [hk₁ _ (by simp)]; exact hI .dst (by simp))
    dsimp only at he₂
    rw [hk₁ _ (by simp), hblank 1, List.append_nil] at he₂
    let R₂ := Function.update R₁ (ι (.word 1)) (binSyms (p.wy + 1) (vals 1))
    have hk₂ (r : BadReg) (hr₀ : r ≠ .word 0) (hr₁ : r ≠ .word 1) :
        R₂ (ι r) = S.R (ι r) := by simp [R₂, hι.eq_iff, hr₁, hk₁ r hr₀]
    obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := spreadPadded_exec p hG hGK body (hregs 2 2)
      (selectiveView p X i).t v₂ { S with R := R₂ }
      (by dsimp only; rw [hk₂ _ (by simp) (by simp)]; exact hI .mask (by simp))
      (by dsimp only; rw [hk₂ _ (by simp) (by simp)]; exact hfields 2)
      (by dsimp only; rw [hk₂ _ (by simp) (by simp)]; exact hI .ts (by simp))
      (by dsimp only; rw [hk₂ _ (by simp) (by simp)]; exact hI .tm (by simp))
      (by dsimp only; rw [hk₂ _ (by simp) (by simp)]; exact hI .dst (by simp))
    dsimp only at he₃
    rw [hk₂ _ (by simp) (by simp), hblank 2, List.append_nil] at he₃
    let R₃ := Function.update R₂ (ι (.word 2)) (binSyms (p.wy + 1) (vals 2))
    have hk₃ (r : BadReg) (hr₀ : r ≠ .word 0) (hr₁ : r ≠ .word 1) (hr₂ : r ≠ .word 2) :
        R₃ (ι r) = S.R (ι r) := by simp [R₃, hι.eq_iff, hr₂, hk₂ r hr₀ hr₁]
    have hlay : CodeLayout (badClassifierInputs ι) (fun k => ι (.spare k)) (ι .st) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r t he; fin_cases r <;> fin_cases t <;> simp_all [badClassifierInputs, hι.eq_iff]
      · intro r t he; simpa using hι he
      · intro r t; fin_cases r <;> simp [badClassifierInputs, hι.eq_iff]
      · intro r; fin_cases r <;> simp [badClassifierInputs, hι.eq_iff]
      · intro r; simp [hι.eq_iff]
    obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := codePass_exec body hlay (badC A hA) (p.wy + 1) vals
      v₃ { S with R := R₃ }
      (fun r => by
        fin_cases r
        · simp [badClassifierInputs, R₃, R₂, R₁, hι.eq_iff]
        · simp [badClassifierInputs, R₃, R₂, hι.eq_iff]
        · simp [badClassifierInputs, R₃]
        · simpa [badClassifierInputs, vals, badVals] using
            ((hk₃ .phase (by simp) (by simp) (by simp)).trans (hI .phase (by simp))))
      (fun k => by
        dsimp only
        rw [hk₃ _ (by simp) (by simp) (by simp)]
        exact hI (.spare k) (by simp))
    obtain ⟨v₅, hu₅, hsc₅, he₅⟩ := bclear_exec body (ι (.word 0)) v₄ { S with R := R₃ }
    let R₄ := Function.update R₃ (ι (.word 0)) []
    obtain ⟨v₆, hu₆, hsc₆, he₆⟩ := bclear_exec body (ι (.word 1)) v₅ { S with R := R₄ }
    let R₅ := Function.update R₄ (ι (.word 1)) []
    obtain ⟨v₇, hu₇, hsc₇, he₇⟩ := bclear_exec body (ι (.word 2)) v₆ { S with R := R₅ }
    have hfin : Function.update R₅ (ι (.word 2)) [] = S.R := by
      funext k
      by_cases h₀ : k = ι (.word 0)
      · subst k; simp [R₅, R₄, R₃, R₂, R₁, hι.eq_iff, hblank]
      by_cases h₁ : k = ι (.word 1)
      · subst k; simp [R₅, R₄, R₃, R₂, R₁, hι.eq_iff, hblank]
      by_cases h₂ : k = ι (.word 2)
      · subst k; simp [hblank]
      simp [R₅, R₄, R₃, R₂, R₁, h₀, h₁, h₂]
    have hl₀ : (R₃ (ι (.word 0))).length = p.wy + 1 := by simp [R₃, R₂, R₁, hι.eq_iff]
    have hl₁ : (R₄ (ι (.word 1))).length = p.wy + 1 := by simp [R₄, R₃, R₂, hι.eq_iff]
    have hl₂ : (R₅ (ι (.word 2))).length = p.wy + 1 := by simp [R₅, R₄, R₃, hι.eq_iff]
    refine ⟨v₇, (1 + (6 * p.wy + 6)) + (m₂ + (m₃ + ((6 * (p.wy + 1) + 4) +
      ((2 * (R₃ (ι (.word 0))).length + 2) + ((2 * (R₄ (ι (.word 1))).length + 2) +
        (2 * (R₅ (ι (.word 2))).length + 2)))))),
      hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))), ?_, ?_, ?_⟩
    · rw [hl₀, hl₁, hl₂]
      unfold badClassifierCost
      omega
    · rw [hsc₇, hsc₆, hsc₅, hsc₄, codeSel_val]
      exact selectiveBadCode_padded p X hG hA hguard i
    · exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄
        (Exec.seq he₅ (Exec.seq he₆ (Exec.cast he₇ rfl (by simp only [hfin])))))))
  cf_inj := fun f g he => by simpa using hι he
  cf_Y := fun f => ⟨.fld f, rfl⟩
  digits := fun R i hI f => hI (.fld f) (by simp)
  frame := by
    intro R R' i hI hR r hr
    rw [hR (ι r) ⟨r, rfl⟩]
    exact hI r hr
  reidx := by
    intro R R' i j hI hfields hother r hr
    cases r <;> first
      | exact hfields _
      | contradiction
      | (rw [hother _ (fun f => hι.ne (by simp))]; exact hI _ (by simp))

end IntegerMultBounds.MathlibTM2.Routing
