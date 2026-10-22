module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerBank

/-! Exact serialization words and restoration of the compiler's private bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A n : ℕ}

theorem elementaryCompilerReady_word (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (L : ℕ) (target source : Fin n) (rowBits triple : List Bool) (key : Fin 6) :
    elementaryCompilerReady R rg L target source rowBits triple (rg (elementaryCompilerWord key)) =
      elementaryConfigWord n ((elementarySwapSpec target).coordinate source).val
        (elementaryCompilerWords rowBits triple target) key := by
  fin_cases key <;>
    simp [elementaryCompilerReady, elementaryCompilerHeaders, elementaryHeaderBank,
      elementaryCompilerHeader, elementaryCompilerWord, elementaryConfigWord, hrg.eq_iff]

/-- The compiled header bank satisfies the executed elementary instruction contract. -/
theorem elementaryCompilerWords_valid (target source : Fin n) (hne : source ≠ target)
    (rowBits triple : List Bool) (rows B : ℕ)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrows : Counter.value rowBits = rows) (htriple : GrowingCounterData.Canonical triple)
    (hB : Counter.value triple = 3 * B) :
    (ElementaryInstruction.mk target source hne (elementaryCompilerWords rowBits triple target)).Valid rows B := by
  have hgap : target.val - 1 = target.val - (elementarySwapSpec target).w := by
    by_cases ht : target.val = 0 <;> simp [elementarySwapSpec, ht]
  have hgate : (List.replicate target.val (bitSymbol (a := 0) true)).head?.isSome = decide (target.val ≠ 0) := by
    cases target.val <;> simp
  have h := elementaryHeaderInstruction_valid target source hne rowBits triple
    (n - (target.val + (elementarySwapSpec target).w)) (target.val - 1) rows B
    (List.replicate target.val (bitSymbol (a := 0) true)) hrow hrowNe hrows htriple hB rfl hgap (by simp)
  simpa only [hgate, elementaryCompilerWords] using h

theorem elementaryCompilerReady_keep (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (L : ℕ) (target source : Fin n) (rowBits triple : List Bool)
    (j : Fin T) (hj : j ∉ elementaryCompilerPrivate.map rg) :
    elementaryCompilerReady R rg L target source rowBits triple j = R j := by
  simp only [elementaryCompilerPrivate, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hj
  rcases hj with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  simp only [elementaryCompilerReady, elementaryCompilerHeaders, elementaryHeaderBank,
    elementaryCompilerHeader, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
    elementaryCoordinateInitialBank, Function.update_of_ne h0, Function.update_of_ne h1,
    Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
    Function.update_of_ne h5, Function.update_of_ne h6, Function.update_of_ne h7,
    Function.update_of_ne h8, Function.update_of_ne h9, Function.update_of_ne h10,
    Function.update_of_ne h11, Function.update_of_ne h12]

theorem elementaryCompilerPrivate_disjoint :
    List.Disjoint elementaryCompilerPrivate elementaryCompilerInputs := by
  simp [List.disjoint_left, elementaryCompilerPrivate, elementaryCompilerInputs]

/-- Clear every generated word, preserving the serialized stream and all inputs. -/
theorem elementaryCompiler_restore (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (L : ℕ) (target source : Fin n) (rowBits triple : List Bool) (out : List (Fin (A + 4)))
    (hblank : ∀ r, r ∉ elementaryCompilerInputs → R (rg r) = []) :
    metadataCleared (Function.update (elementaryCompilerReady R rg L target source rowBits triple) (rg .output) out)
      (elementaryCompilerPrivate.map rg) = Function.update R (rg .output) out := by
  have hout : rg .output ∉ elementaryCompilerPrivate.map rg := by
    simp [elementaryCompilerPrivate, hrg.eq_iff]
  rw [metadataCleared_update _ _ _ _ hout]
  congr 1
  funext j
  by_cases hj : j ∈ elementaryCompilerPrivate.map rg
  · rw [metadataCleared_at _ _ j hj]
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hj
    exact (hblank r (List.disjoint_left.mp elementaryCompilerPrivate_disjoint hr)).symm
  · rw [metadataCleared_keep _ _ j hj]
    exact elementaryCompilerReady_keep R rg L target source rowBits triple j hj

end IntegerMultBounds.MathlibTM2.Routing
