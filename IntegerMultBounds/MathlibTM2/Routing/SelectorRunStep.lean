module

public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad
public import IntegerMultBounds.MathlibTM2.Routing.SelectorEntry
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! One fixed sparse-selector iteration loads a compact pair, emits its dense
run and clears both operands. Consumed input is archived for final rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive SelectorRunReg where
  | src | archive | gap | entry | loadTmp | count | saved | block | dst | work | tmp | ctmp
  deriving DecidableEq

variable {T Q A M : ℕ} {P U : Type}

def selectorRunStepProgram (rg : SelectorRunReg → Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg .src) (rg .archive) (rg .gap) (rg .entry) (rg .loadTmp))
    (.seq (selectorEntryProgram (rg .gap) (rg .count) (rg .saved) (rg .block) (rg .entry)
      (rg .dst) (rg .work) (rg .tmp) (rg .ctmp)) (metadataClean [rg .gap, rg .entry]))

def selectorRunStepBank (R : Fin T → List (Fin (A + 4))) (rg : SelectorRunReg → Fin T)
    (Lg L gap : ℕ) (q : Fin (M + 1)) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R (rg .src) rest)
    (rg .archive) ((binSyms Lg gap ++ separator :: (binSyms L q.val ++ [separator])).reverse ++ R (rg .archive)))
    (rg .dst) (descriptorSelectorFrames L (List.replicate gap 0 ++ [q]) ++ R (rg .dst))

theorem selectorRunStepBank_keep (R : Fin T → List (Fin (A + 4))) (rg : SelectorRunReg → Fin T)
    (Lg L gap : ℕ) (q : Fin (M + 1)) (rest : List (Fin (A + 4))) (j : Fin T)
    (hs : j ≠ rg .src) (ha : j ≠ rg .archive) (hd : j ≠ rg .dst) :
    selectorRunStepBank R rg Lg L gap q rest j = R j := by
  simp [selectorRunStepBank, hs, ha, hd]

theorem selectorRunStepBank_blank (R : Fin T → List (Fin (A + 4)))
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (Lg L gap : ℕ) (q : Fin (M + 1)) (rest : List (Fin (A + 4)))
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → R (rg r) = []) :
    ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst →
      selectorRunStepBank R rg Lg L gap q rest (rg r) = [] := by
  intro r hs ha hb hd
  rw [selectorRunStepBank_keep R rg Lg L gap q rest (rg r)
    (hrg.ne hs) (hrg.ne ha) (hrg.ne hd)]
  exact hblank r hs ha hb hd

theorem selectorRunStep_exec (body : P → Pr P T Q A U)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (Lg L gap : ℕ) (hgap : gap < 2 ^ Lg) (q : Fin (M + 1))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = binSyms Lg gap ++ separator :: (binSyms L q.val ++ separator :: rest))
    (hblock : S.R (rg .block) = binSyms L 0 ++ [separator])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Lg + 4 * L + 12) + (6 * L + 8) +
        binaryWordRepeatCost Lg gap (L + 1) + (2 * Lg + 2 * L + 5) ∧
      Exec body (selectorRunStepProgram rg) (mk v S) steps
        (mk v' { S with R := selectorRunStepBank S.R rg Lg L gap q rest }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := selectorRunLoad_exec body (rg .src) (rg .archive) (rg .gap) (rg .entry) (rg .loadTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) Lg L gap q.val rest v S hsrc
    (hblank .gap (by decide) (by decide) (by decide) (by decide))
    (hblank .entry (by decide) (by decide) (by decide) (by decide))
    (hblank .loadTmp (by decide) (by decide) (by decide) (by decide))
  let S₁ : Stacks T A := { S with R := selectorRunLoaded S.R (rg .src) (rg .archive) (rg .gap) (rg .entry) (binSyms Lg gap) (binSyms L q.val) rest }
  have hk (r : SelectorRunReg) (hs : r ≠ .src) (ha : r ≠ .archive) (hg : r ≠ .gap) (he : r ≠ .entry) :
      S₁.R (rg r) = S.R (rg r) := by simp [S₁, selectorRunLoaded, hrg.eq_iff, hs, ha, hg, he]
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := selectorEntry_exec body (rg .gap) (rg .count) (rg .saved) (rg .block)
    (rg .entry) (rg .dst) (rg .work) (rg .tmp) (rg .ctmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) Lg gap L hgap q v₁ S₁
    (by simp [S₁, selectorRunLoaded, hrg.eq_iff]) (by simp [S₁, selectorRunLoaded])
    ((hk .block (by decide) (by decide) (by decide) (by decide)).trans hblock)
    (by rw [hk .count (by decide) (by decide) (by decide) (by decide)]; exact hblank _ (by decide) (by decide) (by decide) (by decide))
    (by rw [hk .saved (by decide) (by decide) (by decide) (by decide)]; exact hblank _ (by decide) (by decide) (by decide) (by decide))
    (by rw [hk .work (by decide) (by decide) (by decide) (by decide)]; exact hblank _ (by decide) (by decide) (by decide) (by decide))
    (by rw [hk .tmp (by decide) (by decide) (by decide) (by decide)]; exact hblank _ (by decide) (by decide) (by decide) (by decide))
    (by rw [hk .ctmp (by decide) (by decide) (by decide) (by decide)]; exact hblank _ (by decide) (by decide) (by decide) (by decide))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) (descriptorSelectorFrames L (List.replicate gap 0 ++ [q]) ++ S₁.R (rg .dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body [rg .gap, rg .entry] (by simp [hrg.eq_iff]) v₂ S₂
  have hc : metadataCleanCost S₂.R [rg .gap, rg .entry] = 2 * Lg + 2 * L + 5 := by
    simp [metadataCleanCost, S₂, S₁, selectorRunLoaded, hrg.eq_iff]
    omega
  have hf : metadataCleared S₂.R [rg .gap, rg .entry] = selectorRunStepBank S.R rg Lg L gap q rest := by
    funext j
    by_cases hg : j = rg .gap
    · subst j; simp [metadataCleared, selectorRunStepBank, hrg.eq_iff, hblank]
    · by_cases he : j = rg .entry
      · subst j; simp [metadataCleared, selectorRunStepBank, hrg.eq_iff, hblank]
      · by_cases hd : j = rg .dst
        · subst j; simp [metadataCleared, selectorRunStepBank, S₂, S₁, selectorRunLoaded, hrg.eq_iff]
        · simp [metadataCleared, selectorRunStepBank, S₂, S₁, selectorRunLoaded, hg, he, hd]
  rw [hf, hc] at he₃
  exact ⟨v₃, (4 * Lg + 4 * L + 12) + (n₂ + (2 * Lg + 2 * L + 5)), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
