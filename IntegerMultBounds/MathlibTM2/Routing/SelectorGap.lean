module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorSelectorFrames
public import IntegerMultBounds.MathlibTM2.Routing.BinaryWordRepeat

/-! A binary-sized run of absent selectors is emitted by one fixed loop.
The reusable zero frame and the binary count are restored, as is all scratch.
Constructing the zero frame and walking sparse entries are separate phases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

theorem wordCopies_selectorFrame {M : ℕ} (L : ℕ) (q : Fin M) (n : ℕ) :
    wordCopies ((binSyms L q.val : List (Fin (A + 4))) ++ [separator]) n =
      descriptorSelectorFrames L (List.replicate n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordCopies, ih, List.replicate_succ, descriptorSelectorFrames]
    have hc : descriptorSelectorFrames (A := A) L (List.replicate n q) ++
        (binSyms L q.val ++ [separator]) =
        (binSyms L q.val ++ [separator]) ++ descriptorSelectorFrames L (List.replicate n q) := by
      change descriptorSelectorFrames L (List.replicate n q) ++ descriptorSelectorFrames L [q] =
        descriptorSelectorFrames L [q] ++ descriptorSelectorFrames L (List.replicate n q)
      rw [← descriptorSelectorFrames_append, ← descriptorSelectorFrames_append]
      congr 1
      rw [← List.replicate_succ', List.replicate_succ]
      rfl
    simpa only [List.append_assoc, List.singleton_append] using hc

theorem selectorGap_exec (body : P → Pr P T Q A U)
    (src count saved block dst work tmp ctmp : Fin T)
    (hreg : [src, count, saved, block, dst, work, tmp, ctmp].Nodup)
    (Lg gap L : ℕ) (hgap : gap < 2 ^ Lg) (W : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lg gap)
    (hblock : S.R block = binSyms L 0 ++ [separator])
    (hcount : S.R count = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryWordRepeatCost Lg gap (L + 1) ∧
      Exec body (binaryWordRepeatProgram src count saved block dst work tmp ctmp)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (descriptorSelectorFrames L (List.replicate gap (0 : Fin (W + 1))) ++ S.R dst) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := binaryWordRepeat_exec body src count saved block dst work tmp ctmp
    hreg Lg gap hgap (binSyms L 0 ++ [separator]) v S hsrc hblock hcount hsaved hwork htmp hctmp
  have hw : ((binSyms L 0 : List (Fin (A + 4))) ++ [separator]).length = L + 1 := by simp
  rw [hw] at ht
  have hf := wordCopies_selectorFrame (A := A) L (0 : Fin (W + 1)) gap
  simp only [Fin.val_zero] at hf
  rw [hf] at he
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
