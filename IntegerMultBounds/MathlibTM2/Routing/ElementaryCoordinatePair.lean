module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerBank
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatchClean

/-!
# Framed target/source pairs for the uniform instruction compiler

The pair loader has two fixed destinations. Coordinate values and the number of
pairs are input data; the same compiler bank and right-stack archive are reused.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def elementaryPairSlots (rg : ElementaryCompilerReg → Fin T) : List (ConfigurationSlot T) :=
  [⟨rg (.coordinate .target), false⟩, ⟨rg (.coordinate .source), false⟩]

def elementaryPairWords (L target source : ℕ) : List (List (Fin (A + 4))) :=
  [binSyms L target, binSyms L source]

def elementaryPairLoad (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  configurationBatch src (rg (.coordinate (.scratch 3))) saved configurationIsBit (elementaryPairSlots rg)

def elementaryPairLoaded (R : Fin T → List (Fin (A + 4))) (rg : ElementaryCompilerReg → Fin T)
    (src saved : Fin T) (L target source : ℕ) (rest : List (Fin (A + 4))) :=
  configurationBatchLoaded R src (rg (.coordinate (.scratch 3))) saved (elementaryPairSlots rg)
    (elementaryPairWords L target source) rest

theorem elementaryPairSlots_separate (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) :
    ∀ slot ∈ elementaryPairSlots rg,
      src ≠ slot.dst ∧ rg (.coordinate (.scratch 3)) ≠ slot.dst ∧ saved ≠ slot.dst := by
  intro slot hs
  simp only [elementaryPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> exact ⟨hsrc _, by simp [hrg.eq_iff], hsaved _⟩

/-- The loader produces the exact two binary operands used by the compiler. -/
theorem elementaryPairLoaded_data (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg) (src saved : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L target source : ℕ) (rest : List (Fin (A + 4))) :
    elementaryPairLoaded R rg src saved L target source rest (rg (.coordinate .target)) = binSyms L target ∧
    elementaryPairLoaded R rg src saved L target source rest (rg (.coordinate .source)) = binSyms L source := by
  have h := configurationBatchLoaded_data R src (rg (.coordinate (.scratch 3))) saved
    (elementaryPairSlots rg) (by simp [elementaryPairSlots, List.nodup_cons, hrg.eq_iff])
    (elementaryPairSlots_separate rg hrg src saved hsrc hsaved)
    (elementaryPairWords L target source) rfl rest
  cases h with
  | cons ht hs =>
    cases hs with
    | cons hs _ => exact ⟨ht, hs⟩

/-- All compiler registers other than the two operands and loader scratch survive. -/
theorem elementaryPairLoaded_keep (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg) (src saved : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L target source : ℕ) (rest : List (Fin (A + 4))) (r : ElementaryCompilerReg)
    (ht : r ≠ .coordinate .target) (hs : r ≠ .coordinate .source)
    (hw : r ≠ .coordinate (.scratch 3)) :
    elementaryPairLoaded R rg src saved L target source rest (rg r) = R (rg r) := by
  apply configurationBatchLoaded_keep
  · exact (hsrc r).symm
  · exact fun he => hw (hrg he)
  · exact (hsaved r).symm
  · simp [elementaryPairSlots, hrg.eq_iff, ht, hs]

/-- Loading operands preserves the compiler's blank private-work invariant. -/
theorem elementaryPairLoaded_blank (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg) (src saved : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L target source : ℕ) (rest : List (Fin (A + 4)))
    (hblank : ∀ r, r ∉ elementaryCompilerInputs → R (rg r) = []) :
    ∀ r, r ∉ elementaryCompilerInputs → elementaryPairLoaded R rg src saved L target source rest (rg r) = [] := by
  intro r hr
  by_cases hw : r = .coordinate (.scratch 3)
  · subst r
    apply configurationBatchLoaded_tmp
    · exact (hsaved _).symm
    · rfl
    · intro slot hs
      exact (elementaryPairSlots_separate rg hrg src saved hsrc hsaved slot hs).2.1
    · exact hblank _ (by simp [elementaryCompilerInputs])
  · rw [elementaryPairLoaded_keep R rg hrg src saved hsrc hsaved L target source rest r]
    · exact hblank r hr
    · intro he; subst r; exact hr (by simp [elementaryCompilerInputs])
    · intro he; subst r; exact hr (by simp [elementaryCompilerInputs])
    · exact hw

/-- After emitting an instruction, clear its coordinate operands to restore the
reusable bank; only the raw cursor, rewind archive and output stream differ. -/
theorem elementaryPairLoaded_restore (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg) (src saved : Fin T)
    (hss : src ≠ saved) (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L target source : ℕ) (rest out : List (Fin (A + 4)))
    (hinput : R src = configurationWords (elementaryPairWords L target source) ++ rest)
    (htmp : R (rg (.coordinate (.scratch 3))) = [])
    (htarget : R (rg (.coordinate .target)) = []) (hsource : R (rg (.coordinate .source)) = []) :
    metadataCleared (Function.update (elementaryPairLoaded R rg src saved L target source rest) (rg .output) out)
      ((elementaryPairSlots rg).map ConfigurationSlot.dst) =
      Function.update (Function.update (Function.update R src rest) saved
        ((configurationWords (elementaryPairWords L target source)).reverse ++ R saved)) (rg .output) out := by
  unfold elementaryPairLoaded
  rw [metadataCleared_update]
  · rw [configurationBatchClean_restore R src (rg (.coordinate (.scratch 3))) saved
      (hsrc _) hss (hsaved _).symm (elementaryPairSlots rg) (elementaryPairWords L target source) rfl
      (elementaryPairSlots_separate rg hrg src saved hsrc hsaved) rest hinput htmp]
    intro slot hs
    simp only [elementaryPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact htarget
    · exact hsource
  · simp [elementaryPairSlots, hrg.eq_iff]

/-- Read a target/source pair using one fixed loader and charge both words. -/
theorem elementaryPairLoad_exec (body : P → Pr P T Q A U) (rg : ElementaryCompilerReg → Fin T)
    (hrg : Function.Injective rg) (src saved : Fin T) (hss : src ≠ saved)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L target source : ℕ) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R src = configurationWords (elementaryPairWords L target source) ++ rest)
    (htmp : S.R (rg (.coordinate (.scratch 3))) = [])
    (htarget : S.R (rg (.coordinate .target)) = []) (hsource : S.R (rg (.coordinate .source)) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (elementaryPairLoad rg src saved) (mk v S) (8 * L + 13)
        (mk v' { S with R := elementaryPairLoaded S.R rg src saved L target source rest }) := by
  obtain ⟨v', hu, he⟩ := configurationBatch_exec body src (rg (.coordinate (.scratch 3))) saved
    (hsrc _) hss (hsaved _).symm configurationIsBit configurationIsBit_separator
    (elementaryPairSlots rg) (by simp [elementaryPairSlots, List.nodup_cons, hrg.eq_iff])
    (by
      intro slot hs
      simp only [elementaryPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact ⟨hsrc _, by simp [hrg.eq_iff], hsaved _⟩)
    (elementaryPairWords L target source) rfl
    (by
      intro word hw x hx
      simp only [elementaryPairWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> rw [binSyms_eq] at hx <;>
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx <;> exact configurationIsBit_bit b)
    rest v S hinput htmp
    (by
      intro slot hs
      simp only [elementaryPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact htarget
      · exact hsource)
  refine ⟨v', hu, ?_⟩
  have hc : configurationBatchCost (elementaryPairWords (A := A) L target source) = 8 * L + 13 := by
    simp [elementaryPairWords, configurationBatchCost]
    omega
  simpa only [elementaryPairLoad, elementaryPairLoaded, hc] using he

end IntegerMultBounds.MathlibTM2.Routing
