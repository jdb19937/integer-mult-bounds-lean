module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorCompileCall

/-! Structural input, output and frame algebra for the descriptor compiler. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

def descriptorSelectorFrames {A M : ℕ} (L : ℕ) : List (Fin M) → List (Fin (A + 4))
  | [] => []
  | q :: qs => binSyms L q.val ++ separator :: descriptorSelectorFrames L qs

def descriptorRows {A M : ℕ} (qs : List (Fin M)) : List (Fin (A + 4)) :=
  (qs.map (fun q => binSyms M (2 ^ q.val))).flatten

theorem descriptorRows_append {A M : ℕ} (qs rs : List (Fin M)) :
    descriptorRows (A := A) (qs ++ rs) = descriptorRows qs ++ descriptorRows rs := by
  simp [descriptorRows]

theorem descriptorSelectorFrames_cons_ne_nil {A M : ℕ} (L : ℕ) (q : Fin M) (qs : List (Fin M)) :
    descriptorSelectorFrames (A := A) L (q :: qs) ≠ [] := by
  intro he
  have h := congrArg List.length he
  simp [descriptorSelectorFrames] at h

def descriptorCompileLoopBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (src saved out : Fin T) (input rows : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src []) saved (input.reverse ++ R saved)) out (rows ++ R out)

theorem descriptorCompileStep_keep {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : BinaryMaskReg → Fin T) (src saved out : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (frame row rest : List (Fin (A + 4))) (r : BinaryMaskReg) :
    descriptorCompileStepBank R src saved out frame row rest (rg r) = R (rg r) := by
  simp [descriptorCompileStepBank, (hsrc r).symm, (hsaved r).symm, (hout r).symm]

theorem descriptorCompileStep_ready {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : BinaryMaskReg → Fin T) (src saved out : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (frame row rest : List (Fin (A + 4))) (L M : ℕ) (hready : DescriptorCompileReady rg R L M) :
    DescriptorCompileReady rg (descriptorCompileStepBank R src saved out frame row rest) L M := by
  constructor
  · rw [descriptorCompileStep_keep R rg src saved out hsrc hsaved hout]; exact hready.width
  · intro r hr; rw [descriptorCompileStep_keep R rg src saved out hsrc hsaved hout]; exact hready.blank r hr

theorem descriptorCompileLoopBank_step {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out)
    (frame row rest input rows : List (Fin (A + 4))) :
    descriptorCompileLoopBank (descriptorCompileStepBank R src saved out frame row rest)
      src saved out input rows = descriptorCompileLoopBank R src saved out (frame ++ input) (rows ++ row) := by
  funext j
  by_cases ho : j = out
  · subst j; simp [descriptorCompileLoopBank, descriptorCompileStepBank, List.append_assoc]
  · by_cases ha : j = saved
    · subst j; simp [descriptorCompileLoopBank, descriptorCompileStepBank, hao, List.reverse_append, List.append_assoc]
    · by_cases hs : j = src
      · subst j; simp [descriptorCompileLoopBank, descriptorCompileStepBank, hss, hso]
      · simp [descriptorCompileLoopBank, descriptorCompileStepBank, ho, ha, hs]

theorem descriptorCompileLoopBank_nil {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out) (hinput : R src = []) :
    descriptorCompileLoopBank R src saved out [] [] = R := by
  funext j
  by_cases ho : j = out
  · subst j; simp [descriptorCompileLoopBank]
  · by_cases ha : j = saved
    · subst j; simp [descriptorCompileLoopBank, hao]
    · by_cases hs : j = src
      · subst j; simp [descriptorCompileLoopBank, hinput, hss, hso]
      · simp [descriptorCompileLoopBank, ho, ha, hs]

end IntegerMultBounds.MathlibTM2.Routing
