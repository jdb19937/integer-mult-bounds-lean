module

public import IntegerMultBounds.Networks.Shared50FiniteInterchange
public import IntegerMultBounds.Machine.RadixRational

/-! Literal coefficient machines for the actual fixed rational control lists.
All coefficient denominators are certified by the already chosen schedule
prime; no extra denominator or implementation contract is assumed. These are
individual arithmetic kernels, not yet a tape implementation of a matrix sweep. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Shared50CoefficientMachines

noncomputable section
open Swap.Shear
open ModularFrameSchedule
open Shared50ModularSchedule (Index)
open Shared50ModularControl (prime)
open Shared50FiniteInterchange (rationalFieldPrograms)
open Machine.RadixDigits

section Generic
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Every coefficient of a whole-group transform has a denominator below Q. -/
def CoeffBound (Q : ℕ) : Op ι ℚ → Prop
  | .transformH E => ∀ i j, (E i j).den < Q
  | .transformD E => ∀ i j, (E i j).den < Q
  | _ => True

omit [LinearOrder ι] in
private theorem coefficient_mem (E : Matrix ι ι ℚ) (i j : ι) :
    (E i j).den ∈ Swap.Modular.denominators E := by
  classical
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

omit [Fintype ι] [LinearOrder ι] in
private theorem pivots_bound (Q : ℕ) (L : List (ι × ι)) :
    ∀ op ∈ pivotsProgram (R := ℚ) L, CoeffBound Q op := by
  induction L with
  | nil => simp [pivotsProgram]
  | cons p rest ih => simpa [pivotsProgram,pivotProgram,CoeffBound] using ih

/-- Factor coefficients belong to the very denominator set used to choose the prime. -/
theorem rational_program_bound (Q : ℕ) (e : Edge ι)
    (hd : ∀ d ∈ edgeDenominators e, d < Q) :
    ∀ op ∈ ModularProgramShape.rationalProgram e, CoeffBound Q op := by
  have hf : ∀ E ∈ [(factors e).E₁,(factors e).E₁',(factors e).E₂,(factors e).E₂'],
      ∀ i j, (E i j).den < Q := by
    intro E hE i j
    apply hd
    apply Finset.mem_union_right
    have hc := coefficient_mem E i j
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hc)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hc))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
    · exact Finset.mem_union_right _ hc
  intro op hop
  simp only [ModularProgramShape.rationalProgram,shearProgram,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hop
  rcases hop with (h | h) | h
  · rcases h with rfl | rfl
    · exact hf _ (by simp)
    · exact hf _ (by simp)
  · exact pivots_bound Q _ op h
  · rcases h with rfl | rfl
    · exact hf _ (by simp)
    · exact hf _ (by simp)

omit [LinearOrder ι] in
private theorem post_bound (Q : ℕ) :
    ∀ op ∈ Shared50FiniteInterchange.postFields (ι := ι) (R := ℚ), CoeffBound Q op := by
  intro op hop
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hop
  trivial

private theorem pre_bound (Q : ℕ) (hQ : 1 < Q) :
    ∀ op ∈ Shared50FiniteInterchange.preFields (ι := ι) (R := ℚ), CoeffBound Q op := by
  intro op hop
  simp only [Shared50FiniteInterchange.preFields,List.mem_append,List.mem_singleton] at hop
  rcases hop with h | rfl
  · exact post_bound Q op h
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa using hQ
    · simpa [Matrix.one_apply,hij] using hQ

end Generic

/-- Every transform in the actual complete interchange has protected coefficients,
including the surrounding negative-identity transform. -/
theorem actual_coefficients : ∀ p ∈ rationalFieldPrograms, ∀ op ∈ p, CoeffBound prime op := by
  intro p hp
  simp only [rationalFieldPrograms,List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact pre_bound prime (by have hh := Shared50ModularControl.prime_odd; omega)
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact rational_program_bound prime e (Shared50ModularControl.edge_bound Shared50ModularControl.prime_bound he)
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact post_bound prime

/-- Membership in an actual transform, as opposed to an arbitrary rational matrix. -/
def Occurs (A : Matrix Index Index ℚ) : Prop :=
  ∃ p ∈ rationalFieldPrograms, Op.transformH A ∈ p ∨ Op.transformD A ∈ p

theorem coefficient_bound (A : Matrix Index Index ℚ) (hA : Occurs A) (i j : Index) :
    (A i j).den < prime := by
  obtain ⟨p,hp,hA⟩ := hA
  rcases hA with h | h
  · exact actual_coefficients p hp _ h i j
  · exact actual_coefficients p hp _ h i j

local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

end
end IntegerMultBounds.Networks.Shared50CoefficientMachines
