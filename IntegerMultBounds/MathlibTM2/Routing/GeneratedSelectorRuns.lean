module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySelectorZeroFrame
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunCompile

/-! Generate the reusable absent-selector frame once, expand the whole compact
stream, restore that input, and erase the frame. Only dense output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

def generatedSelectorRunsProgram (zero : BinaryZeroReg → Fin T) (rg : SelectorRunReg → Fin T) : Pr P T Q A U :=
  .seq (binarySelectorZeroFrameProgram zero) (.seq (selectorRunCompileProgram rg) (bclear (rg .block)))

theorem generatedSelectorRuns_exec (body : P → Pr P T Q A U)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg) (hblockReg : zero .dst = rg .block)
    (Lw Lg L : ℕ) (hL : L < 2 ^ Lw)
    (runs : List (SparseSelectorRun W)) (hfit : ∀ run ∈ runs, run.gap < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (zero .width) = binSyms Lw L) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hsrc : S.R (rg .src) = selectorRunFrames Lg L runs)
    (harchive : S.R (rg .archive) = []) (hblock : S.R (rg .block) = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (Lw * (4 * L + 11) + 8 * L + 13) + selectorRunLoopCost Lg L runs +
        2 * (selectorRunFrames (A := A) Lg L runs).length + 3 + (2 * (L + 1) + 2) ∧
      Exec body (generatedSelectorRunsProgram zero rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (descriptorSelectorFrames L (SparseSelectorRun.expand runs.reverse) ++ S.R (rg .dst)) }) := by
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := binarySelectorZeroFrame_exec body zero hzero Lw L hL v S hwidth hunary hscratch
  rw [hblockReg, hblock] at he₁
  let frame : List (Fin (A + 4)) := binSyms L 0 ++ [separator]
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .block) frame }
  have hk (r : SelectorRunReg) (hr : r ≠ .block) : S₁.R (rg r) = S.R (rg r) :=
    Function.update_of_ne (hrg.ne hr) _ _
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := selectorRunCompile_exec body rg hrg Lg L runs hfit v₁ S₁
    ((hk .src (by decide)).trans hsrc) ((hk .archive (by decide)).trans harchive)
    (by simp [S₁, frame])
    (by intro r hs ha hb hd; rw [hk r hb]; exact hblank r hs ha hb hd)
  have hd : S₁.R (rg .dst) = S.R (rg .dst) := hk .dst (by decide)
  rw [hd] at he₂
  let out := descriptorSelectorFrames (A := A) L (SparseSelectorRun.expand runs.reverse) ++ S.R (rg .dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .block) v₂ S₂
  have hb : S₂.R (rg .block) = frame := by simp [S₂, S₁, hrg.eq_iff]
  have hf : Function.update S₂.R (rg .block) [] = Function.update S.R (rg .dst) out := by
    funext j
    by_cases hj : j = rg .block
    · subst j; simp [hrg.eq_iff, hblock]
    · by_cases hd : j = rg .dst
      · subst j; simp [S₂, S₁, hj]
      · simp [S₂, S₁, hj, hd]
  rw [hf, hb] at he₃
  have hl : frame.length = L + 1 := by simp [frame]
  rw [hl] at he₃
  exact ⟨v₃, n₁ + (n₂ + (2 * (L + 1) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
