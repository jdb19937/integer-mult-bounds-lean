module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationLoad
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupBank

/-! Load a compact sparse entry: a binary gap followed by a binary selector.
The fixed scanner archives both complete frames for later rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def selectorRunLoadProgram (src saved gap entry tmp : Fin T) : Pr P T Q A U :=
  .seq (configurationLoad src gap tmp saved configurationIsBit false)
    (configurationLoad src entry tmp saved configurationIsBit false)

def selectorRunLoaded (R : Fin T → List (Fin (A + 4))) (src saved gap entry : Fin T)
    (gapWord entryWord rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R src rest)
    saved ((gapWord ++ separator :: (entryWord ++ [separator])).reverse ++ R saved)) gap gapWord) entry entryWord

theorem selectorRunLoaded_keep (R : Fin T → List (Fin (A + 4)))
    (src saved gap entry j : Fin T) (gapWord entryWord rest : List (Fin (A + 4)))
    (hs : j ≠ src) (ha : j ≠ saved) (hg : j ≠ gap) (he : j ≠ entry) :
    selectorRunLoaded R src saved gap entry gapWord entryWord rest j = R j := by
  simp [selectorRunLoaded, hs, ha, hg, he]

theorem selectorRunLoaded_operands (R : Fin T → List (Fin (A + 4)))
    (src saved gap entry : Fin T) (hreg : [src, saved, gap, entry].Nodup)
    (gapWord entryWord rest : List (Fin (A + 4))) :
    let bank := selectorRunLoaded R src saved gap entry gapWord entryWord rest
    bank src = rest ∧ bank gap = gapWord ∧ bank entry = entryWord ∧
      bank saved = (gapWord ++ separator :: (entryWord ++ [separator])).reverse ++ R saved := by
  have hn := hreg
  regs_ne hn
  simp [selectorRunLoaded, ‹src ≠ saved›, ‹src ≠ gap›, ‹src ≠ entry›,
    ‹gap ≠ entry›, ‹saved ≠ gap›, ‹saved ≠ entry›]

theorem selectorRunLoad_exec (body : P → Pr P T Q A U)
    (src saved gap entry tmp : Fin T) (hreg : [src, saved, gap, entry, tmp].Nodup)
    (Lg L g q : ℕ) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lg g ++ separator :: (binSyms L q ++ separator :: rest))
    (hgap : S.R gap = []) (hentry : S.R entry = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (selectorRunLoadProgram src saved gap entry tmp) (mk v S) (4 * Lg + 4 * L + 12)
        (mk v' { S with R := selectorRunLoaded S.R src saved gap entry (binSyms Lg g) (binSyms L q) rest }) := by
  have hn := hreg
  regs_ne hn
  have hbits (w x : ℕ) : ∀ a ∈ (binSyms w x : List (Fin (A + 4))), configurationIsBit a = true := by
    intro a ha
    rw [binSyms_eq] at ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact configurationIsBit_bit b
  obtain ⟨v₁, hu₁, he₁⟩ := configurationLoad_exec body src gap tmp saved
    ‹src ≠ tmp› ‹src ≠ saved› (Ne.symm ‹saved ≠ tmp›) ‹src ≠ gap›
    (Ne.symm ‹gap ≠ tmp›) ‹saved ≠ gap› configurationIsBit configurationIsBit_separator false
    (binSyms Lg g) (binSyms L q ++ separator :: rest) (hbits Lg g) v S hsrc htmp hgap
  let S₁ : Stacks T A := { S with R := configurationLoaded S.R src gap tmp saved (binSyms Lg g) (binSyms L q ++ separator :: rest) false }
  obtain ⟨v₂, hu₂, he₂⟩ := configurationLoad_exec body src entry tmp saved
    ‹src ≠ tmp› ‹src ≠ saved› (Ne.symm ‹saved ≠ tmp›) ‹src ≠ entry›
    (Ne.symm ‹entry ≠ tmp›) ‹saved ≠ entry› configurationIsBit configurationIsBit_separator false
    (binSyms L q) rest (hbits L q) v₁ S₁
    (by simp [S₁, configurationLoaded, ‹src ≠ gap›, ‹src ≠ saved›, ‹src ≠ tmp›])
    (by simp [S₁, configurationLoaded, Ne.symm ‹gap ≠ tmp›, Ne.symm ‹saved ≠ tmp›])
    (by simp [S₁, configurationLoaded, Ne.symm ‹src ≠ entry›, Ne.symm ‹saved ≠ entry›, ‹entry ≠ tmp›, Ne.symm ‹gap ≠ entry›, hentry])
  have hf : configurationLoaded S₁.R src entry tmp saved (binSyms L q) rest false =
      selectorRunLoaded S.R src saved gap entry (binSyms Lg g) (binSyms L q) rest := by
    funext j
    by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hg : j = gap <;>
      by_cases he : j = entry <;> by_cases ht : j = tmp <;>
      simp_all [S₁, configurationLoaded, selectorRunLoaded, List.reverse_append, List.append_assoc]
  rw [hf] at he₂
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  have he := Exec.seq he₁ he₂
  simp only [length_binSyms] at he
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
